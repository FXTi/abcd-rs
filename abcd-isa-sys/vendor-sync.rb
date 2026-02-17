#!/usr/bin/env ruby
# frozen_string_literal: true

# abcd-isa-sys/vendor-sync.rb — Sync vendored arkcompiler files from upstream
#
# Usage: ruby abcd-isa-sys/vendor-sync.rb [--dry-run] [--verbose]

require 'optparse'
require 'fileutils'
require 'digest'
require 'yaml'
require 'net/http'
require 'uri'

BASE_URL = 'https://raw.gitcode.com/openharmony/arkcompiler_runtime_core/raw/master'

VENDOR_DIR  = File.expand_path('vendor', __dir__)
METADATA    = File.join(VENDOR_DIR, '.sync-metadata.yml')

# vendor local path => upstream path within runtime_core/
FILE_MAP = {
  'isa/gen.rb'                     => 'isa/gen.rb',
  'isa/isapi.rb'                   => 'isa/isapi.rb',
  'isa/combine.rb'                 => 'isa/combine.rb',
  'isa/isa.yaml'                   => 'isa/isa.yaml',
  'libpandafile/pandafile_isapi.rb' =>
    'libpandafile/pandafile_isapi.rb',
  'libpandafile/templates/bytecode_instruction_enum_gen.h.erb' =>
    'libpandafile/templates/bytecode_instruction_enum_gen.h.erb',
  'libpandafile/templates/bytecode_instruction-inl_gen.h.erb' =>
    'libpandafile/templates/bytecode_instruction-inl_gen.h.erb',
  'libpandafile/bytecode_instruction.h' =>
    'libpandafile/bytecode_instruction.h',
  'libpandafile/bytecode_instruction-inl.h' =>
    'libpandafile/bytecode_instruction-inl.h',
  'libpandafile/bytecode_emitter.h' =>
    'libpandafile/bytecode_emitter.h',
  'libpandafile/bytecode_emitter.cpp' =>
    'libpandafile/bytecode_emitter.cpp',
  'libpandafile/templates/bytecode_emitter_def_gen.h.erb' =>
    'libpandafile/templates/bytecode_emitter_def_gen.h.erb',
  'libpandafile/templates/bytecode_emitter_gen.h.erb' =>
    'libpandafile/templates/bytecode_emitter_gen.h.erb',
  'libpandafile/templates/file_format_version.h.erb' =>
    'libpandafile/templates/file_format_version.h.erb',
  'libpandabase/macros.h'           => 'libpandabase/include/libpandabase/macros.h',
  'libpandabase/globals.h'          => 'libpandabase/include/libpandabase/globals.h',
  'libpandabase/panda_visibility.h' => 'libpandabase/include/libpandabase/panda_visibility.h',
  'libpandabase/utils/debug.h'      => 'libpandabase/include/libpandabase/utils/debug.h',
  'libpandabase/utils/bit_helpers.h' => 'libpandabase/include/libpandabase/utils/bit_helpers.h',
  'libpandabase/utils/bit_utils.h'  => 'libpandabase/include/libpandabase/utils/bit_utils.h',
  'libpandabase/utils/span.h'       => 'libpandabase/include/libpandabase/utils/span.h',
  'libpandabase/os/stacktrace.h'    => 'libpandabase/include/libpandabase/os/stacktrace.h',
}.freeze

def fetch(url, limit = 5)
  raise "too many redirects" if limit == 0

  uri = URI(url)
  http = Net::HTTP.new(uri.host, uri.port)
  http.use_ssl = (uri.scheme == 'https')
  http.open_timeout = 10
  http.read_timeout = 30

  resp = http.get(uri.request_uri)
  case resp
  when Net::HTTPSuccess     then resp.body
  when Net::HTTPRedirection then fetch(resp['location'], limit - 1)
  else raise "HTTP #{resp.code}"
  end
end

def sha256(content)
  Digest::SHA256.hexdigest(content)
end

def load_metadata
  return {} unless File.exist?(METADATA)
  YAML.safe_load_file(METADATA) || {}
rescue StandardError
  {}
end

def diff_stat(old_content, new_content)
  old_lines = old_content.lines
  new_lines = new_content.lines
  added = (new_lines - old_lines).size
  removed = (old_lines - new_lines).size
  "+#{added} -#{removed}"
end

class VendorSync
  Result = Struct.new(:local_path, :status, :content, :detail, keyword_init: true)

  def initialize(dry_run: false, verbose: false)
    @dry_run = dry_run
    @verbose = verbose
  end

  def run
    puts "Fetching #{FILE_MAP.size} files from upstream..."
    results = fetch_all
    report(results)

    changed  = results.count { |r| %i[modified new].include?(r.status) }
    errors   = results.count { |r| r.status == :fetch_error }

    if errors == FILE_MAP.size
      $stderr.puts "\nERROR: All files failed to fetch. Upstream may be unavailable."
      $stderr.puts "No local files were modified."
      exit 2
    end

    unless @dry_run
      apply(results)
      update_metadata(results)
    end

    if errors > 0
      $stderr.puts "\nWARNING: #{errors} file(s) failed to fetch."
      exit 1
    end

    exit 0
  end

  private

  def fetch_all
    meta = load_metadata
    meta_files = meta['files'] || {}

    FILE_MAP.each_with_index.map do |(local_path, upstream_path), idx|
      prefix = "  [#{idx + 1}/#{FILE_MAP.size}]"
      label  = local_path.ljust(52)

      local_file = File.join(VENDOR_DIR, local_path)
      local_content = File.exist?(local_file) ? File.binread(local_file) : nil

      # Check for local modifications vs last sync
      if local_content && meta_files[local_path]
        expected = meta_files[local_path]['sha256']
        if expected && sha256(local_content) != expected
          $stderr.puts "#{prefix} WARNING: #{local_path} has local modifications"
        end
      end

      # Fetch upstream
      url = "#{BASE_URL}/#{upstream_path}"
      begin
        upstream_content = fetch(url)
      rescue StandardError => e
        puts "#{prefix} #{label} FETCH ERROR (#{e.message})"
        next Result.new(local_path: local_path, status: :fetch_error, detail: e.message)
      end

      # Compare
      if local_content.nil?
        puts "#{prefix} #{label} NEW"
        Result.new(local_path: local_path, status: :new, content: upstream_content)
      elsif sha256(local_content) == sha256(upstream_content)
        puts "#{prefix} #{label} unchanged" if @verbose
        Result.new(local_path: local_path, status: :unchanged)
      else
        stat = diff_stat(local_content, upstream_content)
        puts "#{prefix} #{label} MODIFIED (#{stat})"
        Result.new(local_path: local_path, status: :modified, content: upstream_content, detail: stat)
      end
    end
  end

  def report(results)
    changed   = results.count { |r| %i[modified new].include?(r.status) }
    unchanged = results.count { |r| r.status == :unchanged }
    errors    = results.count { |r| r.status == :fetch_error }

    parts = []
    parts << "#{changed} file(s) modified" if changed > 0
    parts << "#{unchanged} unchanged" if unchanged > 0
    parts << "#{errors} failed" if errors > 0
    puts "\n#{parts.join(', ')}."
  end

  def apply(results)
    results.each do |r|
      next unless %i[modified new].include?(r.status)
      dest = File.join(VENDOR_DIR, r.local_path)
      FileUtils.mkdir_p(File.dirname(dest))
      File.binwrite(dest, r.content)
    end
  end

  def update_metadata(results)
    files = {}
    FILE_MAP.each_key do |local_path|
      local_file = File.join(VENDOR_DIR, local_path)
      next unless File.exist?(local_file)
      files[local_path] = { 'sha256' => sha256(File.binread(local_file)) }
    end

    data = {
      'synced_at' => Time.now.iso8601,
      'base_url'  => BASE_URL,
      'files'     => files,
    }
    File.write(METADATA, data.to_yaml)
    puts "Updated vendor/.sync-metadata.yml"
  end
end

# --- CLI ---

options = {}
OptionParser.new do |opts|
  opts.banner = "Usage: ruby #{$PROGRAM_NAME} [options]"
  opts.on('-n', '--dry-run', 'Show changes without writing files')  { options[:dry_run] = true }
  opts.on('-v', '--verbose', 'Verbose output')                      { options[:verbose] = true }
  opts.on('-h', '--help',    'Show this help')                      { puts opts; exit }
end.parse!

VendorSync.new(**options).run
