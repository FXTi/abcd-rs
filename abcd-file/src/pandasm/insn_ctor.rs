//! Mnemonic → [`Bytecode`] construction table for the pandasm parser.
//!
//! GENERATED from the vendored ISA (abcd-isa-sys's build-time `bytecode.rs`,
//! itself generated from `isa.yaml`) — regenerate when the vendored ISA
//! changes. Each [`construct`] arm validates the operand count and kinds and
//! delegates to the typed `insn::*` constructor; [`dummy`] builds a
//! zero-valued instance so the parser can read operand KINDS and flags back
//! at runtime (`Bytecode::operands()` / `Bytecode::has_flag`) instead of
//! duplicating the ISA's operand table.

use abcd_isa::insn;
use abcd_isa::{Bytecode, EntityId, Imm, Label, Reg};

use super::parse::RawOperand;
use super::parse::RawOperand::{E, I, L, R};

/// Every pandasm mnemonic the ISA knows (sorted), for the parser's
/// instruction-spec table.
pub(crate) const MNEMONICS: &[&str] = &[
    "add2",
    "and2",
    "apply",
    "ashr2",
    "asyncfunctionawaituncaught",
    "asyncfunctionenter",
    "asyncfunctionreject",
    "asyncfunctionresolve",
    "asyncgeneratorreject",
    "asyncgeneratorresolve",
    "callarg0",
    "callarg1",
    "callargs2",
    "callargs3",
    "callrange",
    "callruntime.callinit",
    "callruntime.createprivateproperty",
    "callruntime.definefieldbyindex",
    "callruntime.definefieldbyvalue",
    "callruntime.defineprivateproperty",
    "callruntime.definesendableclass",
    "callruntime.isfalse",
    "callruntime.istrue",
    "callruntime.ldlazymodulevar",
    "callruntime.ldlazysendablemodulevar",
    "callruntime.ldsendableclass",
    "callruntime.ldsendableexternalmodulevar",
    "callruntime.ldsendablelocalmodulevar",
    "callruntime.ldsendablevar",
    "callruntime.newsendableenv",
    "callruntime.notifyconcurrentresult",
    "callruntime.stsendablevar",
    "callruntime.supercallforwardallargs",
    "callruntime.topropertykey",
    "callruntime.wideldlazymodulevar",
    "callruntime.wideldlazysendablemodulevar",
    "callruntime.wideldsendableexternalmodulevar",
    "callruntime.wideldsendablelocalmodulevar",
    "callruntime.wideldsendablevar",
    "callruntime.widenewsendableenv",
    "callruntime.widestsendablevar",
    "callthis0",
    "callthis0withname",
    "callthis1",
    "callthis1withname",
    "callthis2",
    "callthis2withname",
    "callthis3",
    "callthis3withname",
    "callthisrange",
    "callthisrangewithname",
    "closeiterator",
    "copydataproperties",
    "copyrestargs",
    "createarraywithbuffer",
    "createasyncgeneratorobj",
    "createemptyarray",
    "createemptyobject",
    "creategeneratorobj",
    "createiterresultobj",
    "createobjectwithbuffer",
    "createobjectwithexcludedkeys",
    "createregexpwithliteral",
    "debugger",
    "dec",
    "defineclasswithbuffer",
    "definefieldbyname",
    "definefunc",
    "definegettersetterbyvalue",
    "definemethod",
    "definepropertybyname",
    "delobjprop",
    "deprecated.asyncfunctionawaituncaught",
    "deprecated.asyncfunctionreject",
    "deprecated.asyncfunctionresolve",
    "deprecated.asyncgeneratorreject",
    "deprecated.callarg0",
    "deprecated.callarg1",
    "deprecated.callargs2",
    "deprecated.callargs3",
    "deprecated.callrange",
    "deprecated.callspread",
    "deprecated.callthisrange",
    "deprecated.copydataproperties",
    "deprecated.createarraywithbuffer",
    "deprecated.createobjecthavingmethod",
    "deprecated.createobjectwithbuffer",
    "deprecated.dec",
    "deprecated.defineclasswithbuffer",
    "deprecated.delobjprop",
    "deprecated.dynamicimport",
    "deprecated.getiteratornext",
    "deprecated.getmodulenamespace",
    "deprecated.getresumemode",
    "deprecated.gettemplateobject",
    "deprecated.inc",
    "deprecated.ldhomeobject",
    "deprecated.ldlexenv",
    "deprecated.ldmodulevar",
    "deprecated.ldobjbyindex",
    "deprecated.ldobjbyname",
    "deprecated.ldobjbyvalue",
    "deprecated.ldsuperbyname",
    "deprecated.ldsuperbyvalue",
    "deprecated.neg",
    "deprecated.not",
    "deprecated.poplexenv",
    "deprecated.resumegenerator",
    "deprecated.setobjectwithproto",
    "deprecated.stclasstoglobalrecord",
    "deprecated.stconsttoglobalrecord",
    "deprecated.stlettoglobalrecord",
    "deprecated.stlexvar",
    "deprecated.stmodulevar",
    "deprecated.suspendgenerator",
    "deprecated.tonumber",
    "deprecated.tonumeric",
    "div2",
    "dynamicimport",
    "eq",
    "exp",
    "fldai",
    "getasynciterator",
    "getiterator",
    "getmodulenamespace",
    "getnextpropname",
    "getpropiterator",
    "getresumemode",
    "gettemplateobject",
    "getunmappedargs",
    "greater",
    "greatereq",
    "inc",
    "instanceof",
    "isfalse",
    "isin",
    "istrue",
    "jeq",
    "jeqnull",
    "jequndefined",
    "jeqz",
    "jmp",
    "jne",
    "jnenull",
    "jneundefined",
    "jnez",
    "jnstricteq",
    "jnstricteqnull",
    "jnstrictequndefined",
    "jnstricteqz",
    "jstricteq",
    "jstricteqnull",
    "jstrictequndefined",
    "jstricteqz",
    "lda",
    "lda.str",
    "ldai",
    "ldbigint",
    "ldexternalmodulevar",
    "ldfalse",
    "ldfunction",
    "ldglobal",
    "ldglobalvar",
    "ldhole",
    "ldinfinity",
    "ldlexvar",
    "ldlocalmodulevar",
    "ldnan",
    "ldnewtarget",
    "ldnull",
    "ldobjbyindex",
    "ldobjbyname",
    "ldobjbyvalue",
    "ldprivateproperty",
    "ldsuperbyname",
    "ldsuperbyvalue",
    "ldsymbol",
    "ldthis",
    "ldthisbyname",
    "ldthisbyvalue",
    "ldtrue",
    "ldundefined",
    "less",
    "lesseq",
    "mod2",
    "mov",
    "mul2",
    "neg",
    "newlexenv",
    "newlexenvwithname",
    "newobjapply",
    "newobjrange",
    "nop",
    "not",
    "noteq",
    "or2",
    "poplexenv",
    "resumegenerator",
    "return",
    "returnundefined",
    "setgeneratorstate",
    "setobjectwithproto",
    "shl2",
    "shr2",
    "sta",
    "starrayspread",
    "stconsttoglobalrecord",
    "stglobalvar",
    "stlexvar",
    "stmodulevar",
    "stobjbyindex",
    "stobjbyname",
    "stobjbyvalue",
    "stownbyindex",
    "stownbyname",
    "stownbynamewithnameset",
    "stownbyvalue",
    "stownbyvaluewithnameset",
    "stprivateproperty",
    "stricteq",
    "strictnoteq",
    "stsuperbyname",
    "stsuperbyvalue",
    "stthisbyname",
    "stthisbyvalue",
    "sttoglobalrecord",
    "sub2",
    "supercallarrowrange",
    "supercallspread",
    "supercallthisrange",
    "suspendgenerator",
    "testin",
    "throw",
    "throw.constassignment",
    "throw.deletesuperproperty",
    "throw.ifnotobject",
    "throw.ifsupernotcorrectcall",
    "throw.notexists",
    "throw.patternnoncoercible",
    "throw.undefinedifhole",
    "throw.undefinedifholewithname",
    "tonumber",
    "tonumeric",
    "tryldglobalbyname",
    "trystglobalbyname",
    "typeof",
    "wide.callrange",
    "wide.callthisrange",
    "wide.callthisrangewithname",
    "wide.copyrestargs",
    "wide.createobjectwithexcludedkeys",
    "wide.getmodulenamespace",
    "wide.ldexternalmodulevar",
    "wide.ldlexvar",
    "wide.ldlocalmodulevar",
    "wide.ldobjbyindex",
    "wide.ldpatchvar",
    "wide.newlexenv",
    "wide.newlexenvwithname",
    "wide.newobjrange",
    "wide.stlexvar",
    "wide.stmodulevar",
    "wide.stobjbyindex",
    "wide.stownbyindex",
    "wide.stpatchvar",
    "wide.supercallarrowrange",
    "wide.supercallthisrange",
    "xor2",
];

/// A zero-valued instruction of the given mnemonic (operand introspection).
pub(crate) fn dummy(mnemonic: &str) -> Option<Bytecode> {
    Some(match mnemonic {
        "add2" => insn::Add2::new(Imm(0), Reg(0)),
        "and2" => insn::And2::new(Imm(0), Reg(0)),
        "apply" => insn::Apply::new(Imm(0), Reg(0), Reg(0)),
        "ashr2" => insn::Ashr2::new(Imm(0), Reg(0)),
        "asyncfunctionawaituncaught" => insn::Asyncfunctionawaituncaught::new(Reg(0)),
        "asyncfunctionenter" => insn::Asyncfunctionenter::new(),
        "asyncfunctionreject" => insn::Asyncfunctionreject::new(Reg(0)),
        "asyncfunctionresolve" => insn::Asyncfunctionresolve::new(Reg(0)),
        "asyncgeneratorreject" => insn::Asyncgeneratorreject::new(Reg(0)),
        "asyncgeneratorresolve" => insn::Asyncgeneratorresolve::new(Reg(0), Reg(0), Reg(0)),
        "callarg0" => insn::Callarg0::new(Imm(0)),
        "callarg1" => insn::Callarg1::new(Imm(0), Reg(0)),
        "callargs2" => insn::Callargs2::new(Imm(0), Reg(0), Reg(0)),
        "callargs3" => insn::Callargs3::new(Imm(0), Reg(0), Reg(0), Reg(0)),
        "callrange" => insn::Callrange::new(Imm(0), Imm(0), Reg(0)),
        "callruntime.callinit" => insn::CallruntimeCallinit::new(Imm(0), Reg(0)),
        "callruntime.createprivateproperty" => {
            insn::CallruntimeCreateprivateproperty::new(Imm(0), EntityId(0))
        }
        "callruntime.definefieldbyindex" => {
            insn::CallruntimeDefinefieldbyindex::new(Imm(0), Imm(0), Reg(0))
        }
        "callruntime.definefieldbyvalue" => {
            insn::CallruntimeDefinefieldbyvalue::new(Imm(0), Reg(0), Reg(0))
        }
        "callruntime.defineprivateproperty" => {
            insn::CallruntimeDefineprivateproperty::new(Imm(0), Imm(0), Imm(0), Reg(0))
        }
        "callruntime.definesendableclass" => insn::CallruntimeDefinesendableclass::new(
            Imm(0),
            EntityId(0),
            EntityId(0),
            Imm(0),
            Reg(0),
        ),
        "callruntime.isfalse" => insn::CallruntimeIsfalse::new(Imm(0)),
        "callruntime.istrue" => insn::CallruntimeIstrue::new(Imm(0)),
        "callruntime.ldlazymodulevar" => insn::CallruntimeLdlazymodulevar::new(Imm(0)),
        "callruntime.ldlazysendablemodulevar" => {
            insn::CallruntimeLdlazysendablemodulevar::new(Imm(0))
        }
        "callruntime.ldsendableclass" => insn::CallruntimeLdsendableclass::new(Imm(0)),
        "callruntime.ldsendableexternalmodulevar" => {
            insn::CallruntimeLdsendableexternalmodulevar::new(Imm(0))
        }
        "callruntime.ldsendablelocalmodulevar" => {
            insn::CallruntimeLdsendablelocalmodulevar::new(Imm(0))
        }
        "callruntime.ldsendablevar" => insn::CallruntimeLdsendablevar::new(Imm(0), Imm(0)),
        "callruntime.newsendableenv" => insn::CallruntimeNewsendableenv::new(Imm(0)),
        "callruntime.notifyconcurrentresult" => insn::CallruntimeNotifyconcurrentresult::new(),
        "callruntime.stsendablevar" => insn::CallruntimeStsendablevar::new(Imm(0), Imm(0)),
        "callruntime.supercallforwardallargs" => {
            insn::CallruntimeSupercallforwardallargs::new(Reg(0))
        }
        "callruntime.topropertykey" => insn::CallruntimeTopropertykey::new(),
        "callruntime.wideldlazymodulevar" => insn::CallruntimeWideldlazymodulevar::new(Imm(0)),
        "callruntime.wideldlazysendablemodulevar" => {
            insn::CallruntimeWideldlazysendablemodulevar::new(Imm(0))
        }
        "callruntime.wideldsendableexternalmodulevar" => {
            insn::CallruntimeWideldsendableexternalmodulevar::new(Imm(0))
        }
        "callruntime.wideldsendablelocalmodulevar" => {
            insn::CallruntimeWideldsendablelocalmodulevar::new(Imm(0))
        }
        "callruntime.wideldsendablevar" => insn::CallruntimeWideldsendablevar::new(Imm(0), Imm(0)),
        "callruntime.widenewsendableenv" => insn::CallruntimeWidenewsendableenv::new(Imm(0)),
        "callruntime.widestsendablevar" => insn::CallruntimeWidestsendablevar::new(Imm(0), Imm(0)),
        "callthis0" => insn::Callthis0::new(Imm(0), Reg(0)),
        "callthis0withname" => insn::Callthis0withname::new(Imm(0), EntityId(0), Reg(0)),
        "callthis1" => insn::Callthis1::new(Imm(0), Reg(0), Reg(0)),
        "callthis1withname" => insn::Callthis1withname::new(Imm(0), EntityId(0), Reg(0), Reg(0)),
        "callthis2" => insn::Callthis2::new(Imm(0), Reg(0), Reg(0), Reg(0)),
        "callthis2withname" => {
            insn::Callthis2withname::new(Imm(0), EntityId(0), Reg(0), Reg(0), Reg(0))
        }
        "callthis3" => insn::Callthis3::new(Imm(0), Reg(0), Reg(0), Reg(0), Reg(0)),
        "callthis3withname" => {
            insn::Callthis3withname::new(Imm(0), EntityId(0), Reg(0), Reg(0), Reg(0), Reg(0))
        }
        "callthisrange" => insn::Callthisrange::new(Imm(0), Imm(0), Reg(0)),
        "callthisrangewithname" => {
            insn::Callthisrangewithname::new(Imm(0), Imm(0), EntityId(0), Reg(0))
        }
        "closeiterator" => insn::Closeiterator::new(Imm(0), Reg(0)),
        "copydataproperties" => insn::Copydataproperties::new(Reg(0)),
        "copyrestargs" => insn::Copyrestargs::new(Imm(0)),
        "createarraywithbuffer" => insn::Createarraywithbuffer::new(Imm(0), EntityId(0)),
        "createasyncgeneratorobj" => insn::Createasyncgeneratorobj::new(Reg(0)),
        "createemptyarray" => insn::Createemptyarray::new(Imm(0)),
        "createemptyobject" => insn::Createemptyobject::new(),
        "creategeneratorobj" => insn::Creategeneratorobj::new(Reg(0)),
        "createiterresultobj" => insn::Createiterresultobj::new(Reg(0), Reg(0)),
        "createobjectwithbuffer" => insn::Createobjectwithbuffer::new(Imm(0), EntityId(0)),
        "createobjectwithexcludedkeys" => {
            insn::Createobjectwithexcludedkeys::new(Imm(0), Reg(0), Reg(0))
        }
        "createregexpwithliteral" => {
            insn::Createregexpwithliteral::new(Imm(0), EntityId(0), Imm(0))
        }
        "debugger" => insn::Debugger::new(),
        "dec" => insn::Dec::new(Imm(0)),
        "defineclasswithbuffer" => {
            insn::Defineclasswithbuffer::new(Imm(0), EntityId(0), EntityId(0), Imm(0), Reg(0))
        }
        "definefieldbyname" => insn::Definefieldbyname::new(Imm(0), EntityId(0), Reg(0)),
        "definefunc" => insn::Definefunc::new(Imm(0), EntityId(0), Imm(0)),
        "definegettersetterbyvalue" => {
            insn::Definegettersetterbyvalue::new(Reg(0), Reg(0), Reg(0), Reg(0))
        }
        "definemethod" => insn::Definemethod::new(Imm(0), EntityId(0), Imm(0)),
        "definepropertybyname" => insn::Definepropertybyname::new(Imm(0), EntityId(0), Reg(0)),
        "delobjprop" => insn::Delobjprop::new(Reg(0)),
        "deprecated.asyncfunctionawaituncaught" => {
            insn::DeprecatedAsyncfunctionawaituncaught::new(Reg(0), Reg(0))
        }
        "deprecated.asyncfunctionreject" => {
            insn::DeprecatedAsyncfunctionreject::new(Reg(0), Reg(0), Reg(0))
        }
        "deprecated.asyncfunctionresolve" => {
            insn::DeprecatedAsyncfunctionresolve::new(Reg(0), Reg(0), Reg(0))
        }
        "deprecated.asyncgeneratorreject" => {
            insn::DeprecatedAsyncgeneratorreject::new(Reg(0), Reg(0))
        }
        "deprecated.callarg0" => insn::DeprecatedCallarg0::new(Reg(0)),
        "deprecated.callarg1" => insn::DeprecatedCallarg1::new(Reg(0), Reg(0)),
        "deprecated.callargs2" => insn::DeprecatedCallargs2::new(Reg(0), Reg(0), Reg(0)),
        "deprecated.callargs3" => insn::DeprecatedCallargs3::new(Reg(0), Reg(0), Reg(0), Reg(0)),
        "deprecated.callrange" => insn::DeprecatedCallrange::new(Imm(0), Reg(0)),
        "deprecated.callspread" => insn::DeprecatedCallspread::new(Reg(0), Reg(0), Reg(0)),
        "deprecated.callthisrange" => insn::DeprecatedCallthisrange::new(Imm(0), Reg(0)),
        "deprecated.copydataproperties" => insn::DeprecatedCopydataproperties::new(Reg(0), Reg(0)),
        "deprecated.createarraywithbuffer" => insn::DeprecatedCreatearraywithbuffer::new(Imm(0)),
        "deprecated.createobjecthavingmethod" => {
            insn::DeprecatedCreateobjecthavingmethod::new(Imm(0))
        }
        "deprecated.createobjectwithbuffer" => insn::DeprecatedCreateobjectwithbuffer::new(Imm(0)),
        "deprecated.dec" => insn::DeprecatedDec::new(Reg(0)),
        "deprecated.defineclasswithbuffer" => {
            insn::DeprecatedDefineclasswithbuffer::new(EntityId(0), Imm(0), Imm(0), Reg(0), Reg(0))
        }
        "deprecated.delobjprop" => insn::DeprecatedDelobjprop::new(Reg(0), Reg(0)),
        "deprecated.dynamicimport" => insn::DeprecatedDynamicimport::new(Reg(0)),
        "deprecated.getiteratornext" => insn::DeprecatedGetiteratornext::new(Reg(0), Reg(0)),
        "deprecated.getmodulenamespace" => insn::DeprecatedGetmodulenamespace::new(EntityId(0)),
        "deprecated.getresumemode" => insn::DeprecatedGetresumemode::new(Reg(0)),
        "deprecated.gettemplateobject" => insn::DeprecatedGettemplateobject::new(Reg(0)),
        "deprecated.inc" => insn::DeprecatedInc::new(Reg(0)),
        "deprecated.ldhomeobject" => insn::DeprecatedLdhomeobject::new(),
        "deprecated.ldlexenv" => insn::DeprecatedLdlexenv::new(),
        "deprecated.ldmodulevar" => insn::DeprecatedLdmodulevar::new(EntityId(0), Imm(0)),
        "deprecated.ldobjbyindex" => insn::DeprecatedLdobjbyindex::new(Reg(0), Imm(0)),
        "deprecated.ldobjbyname" => insn::DeprecatedLdobjbyname::new(EntityId(0), Reg(0)),
        "deprecated.ldobjbyvalue" => insn::DeprecatedLdobjbyvalue::new(Reg(0), Reg(0)),
        "deprecated.ldsuperbyname" => insn::DeprecatedLdsuperbyname::new(EntityId(0), Reg(0)),
        "deprecated.ldsuperbyvalue" => insn::DeprecatedLdsuperbyvalue::new(Reg(0), Reg(0)),
        "deprecated.neg" => insn::DeprecatedNeg::new(Reg(0)),
        "deprecated.not" => insn::DeprecatedNot::new(Reg(0)),
        "deprecated.poplexenv" => insn::DeprecatedPoplexenv::new(),
        "deprecated.resumegenerator" => insn::DeprecatedResumegenerator::new(Reg(0)),
        "deprecated.setobjectwithproto" => insn::DeprecatedSetobjectwithproto::new(Reg(0), Reg(0)),
        "deprecated.stclasstoglobalrecord" => {
            insn::DeprecatedStclasstoglobalrecord::new(EntityId(0))
        }
        "deprecated.stconsttoglobalrecord" => {
            insn::DeprecatedStconsttoglobalrecord::new(EntityId(0))
        }
        "deprecated.stlettoglobalrecord" => insn::DeprecatedStlettoglobalrecord::new(EntityId(0)),
        "deprecated.stlexvar" => insn::DeprecatedStlexvar::new(Imm(0), Imm(0), Reg(0)),
        "deprecated.stmodulevar" => insn::DeprecatedStmodulevar::new(EntityId(0)),
        "deprecated.suspendgenerator" => insn::DeprecatedSuspendgenerator::new(Reg(0), Reg(0)),
        "deprecated.tonumber" => insn::DeprecatedTonumber::new(Reg(0)),
        "deprecated.tonumeric" => insn::DeprecatedTonumeric::new(Reg(0)),
        "div2" => insn::Div2::new(Imm(0), Reg(0)),
        "dynamicimport" => insn::Dynamicimport::new(),
        "eq" => insn::Eq::new(Imm(0), Reg(0)),
        "exp" => insn::Exp::new(Imm(0), Reg(0)),
        "fldai" => insn::Fldai::new(Imm(0)),
        "getasynciterator" => insn::Getasynciterator::new(Imm(0)),
        "getiterator" => insn::Getiterator::new(Imm(0)),
        "getmodulenamespace" => insn::Getmodulenamespace::new(Imm(0)),
        "getnextpropname" => insn::Getnextpropname::new(Reg(0)),
        "getpropiterator" => insn::Getpropiterator::new(),
        "getresumemode" => insn::Getresumemode::new(),
        "gettemplateobject" => insn::Gettemplateobject::new(Imm(0)),
        "getunmappedargs" => insn::Getunmappedargs::new(),
        "greater" => insn::Greater::new(Imm(0), Reg(0)),
        "greatereq" => insn::Greatereq::new(Imm(0), Reg(0)),
        "inc" => insn::Inc::new(Imm(0)),
        "instanceof" => insn::Instanceof::new(Imm(0), Reg(0)),
        "isfalse" => insn::Isfalse::new(),
        "isin" => insn::Isin::new(Imm(0), Reg(0)),
        "istrue" => insn::Istrue::new(),
        "jeq" => insn::Jeq::new(Reg(0), Label(0)),
        "jeqnull" => insn::Jeqnull::new(Label(0)),
        "jequndefined" => insn::Jequndefined::new(Label(0)),
        "jeqz" => insn::Jeqz::new(Label(0)),
        "jmp" => insn::Jmp::new(Label(0)),
        "jne" => insn::Jne::new(Reg(0), Label(0)),
        "jnenull" => insn::Jnenull::new(Label(0)),
        "jneundefined" => insn::Jneundefined::new(Label(0)),
        "jnez" => insn::Jnez::new(Label(0)),
        "jnstricteq" => insn::Jnstricteq::new(Reg(0), Label(0)),
        "jnstricteqnull" => insn::Jnstricteqnull::new(Label(0)),
        "jnstrictequndefined" => insn::Jnstrictequndefined::new(Label(0)),
        "jnstricteqz" => insn::Jnstricteqz::new(Label(0)),
        "jstricteq" => insn::Jstricteq::new(Reg(0), Label(0)),
        "jstricteqnull" => insn::Jstricteqnull::new(Label(0)),
        "jstrictequndefined" => insn::Jstrictequndefined::new(Label(0)),
        "jstricteqz" => insn::Jstricteqz::new(Label(0)),
        "lda" => insn::Lda::new(Reg(0)),
        "lda.str" => insn::LdaStr::new(EntityId(0)),
        "ldai" => insn::Ldai::new(Imm(0)),
        "ldbigint" => insn::Ldbigint::new(EntityId(0)),
        "ldexternalmodulevar" => insn::Ldexternalmodulevar::new(Imm(0)),
        "ldfalse" => insn::Ldfalse::new(),
        "ldfunction" => insn::Ldfunction::new(),
        "ldglobal" => insn::Ldglobal::new(),
        "ldglobalvar" => insn::Ldglobalvar::new(Imm(0), EntityId(0)),
        "ldhole" => insn::Ldhole::new(),
        "ldinfinity" => insn::Ldinfinity::new(),
        "ldlexvar" => insn::Ldlexvar::new(Imm(0), Imm(0)),
        "ldlocalmodulevar" => insn::Ldlocalmodulevar::new(Imm(0)),
        "ldnan" => insn::Ldnan::new(),
        "ldnewtarget" => insn::Ldnewtarget::new(),
        "ldnull" => insn::Ldnull::new(),
        "ldobjbyindex" => insn::Ldobjbyindex::new(Imm(0), Imm(0)),
        "ldobjbyname" => insn::Ldobjbyname::new(Imm(0), EntityId(0)),
        "ldobjbyvalue" => insn::Ldobjbyvalue::new(Imm(0), Reg(0)),
        "ldprivateproperty" => insn::Ldprivateproperty::new(Imm(0), Imm(0), Imm(0)),
        "ldsuperbyname" => insn::Ldsuperbyname::new(Imm(0), EntityId(0)),
        "ldsuperbyvalue" => insn::Ldsuperbyvalue::new(Imm(0), Reg(0)),
        "ldsymbol" => insn::Ldsymbol::new(),
        "ldthis" => insn::Ldthis::new(),
        "ldthisbyname" => insn::Ldthisbyname::new(Imm(0), EntityId(0)),
        "ldthisbyvalue" => insn::Ldthisbyvalue::new(Imm(0)),
        "ldtrue" => insn::Ldtrue::new(),
        "ldundefined" => insn::Ldundefined::new(),
        "less" => insn::Less::new(Imm(0), Reg(0)),
        "lesseq" => insn::Lesseq::new(Imm(0), Reg(0)),
        "mod2" => insn::Mod2::new(Imm(0), Reg(0)),
        "mov" => insn::Mov::new(Reg(0), Reg(0)),
        "mul2" => insn::Mul2::new(Imm(0), Reg(0)),
        "neg" => insn::Neg::new(Imm(0)),
        "newlexenv" => insn::Newlexenv::new(Imm(0)),
        "newlexenvwithname" => insn::Newlexenvwithname::new(Imm(0), EntityId(0)),
        "newobjapply" => insn::Newobjapply::new(Imm(0), Reg(0)),
        "newobjrange" => insn::Newobjrange::new(Imm(0), Imm(0), Reg(0)),
        "nop" => insn::Nop::new(),
        "not" => insn::Not::new(Imm(0)),
        "noteq" => insn::Noteq::new(Imm(0), Reg(0)),
        "or2" => insn::Or2::new(Imm(0), Reg(0)),
        "poplexenv" => insn::Poplexenv::new(),
        "resumegenerator" => insn::Resumegenerator::new(),
        "return" => insn::Return::new(),
        "returnundefined" => insn::Returnundefined::new(),
        "setgeneratorstate" => insn::Setgeneratorstate::new(Imm(0)),
        "setobjectwithproto" => insn::Setobjectwithproto::new(Imm(0), Reg(0)),
        "shl2" => insn::Shl2::new(Imm(0), Reg(0)),
        "shr2" => insn::Shr2::new(Imm(0), Reg(0)),
        "sta" => insn::Sta::new(Reg(0)),
        "starrayspread" => insn::Starrayspread::new(Reg(0), Reg(0)),
        "stconsttoglobalrecord" => insn::Stconsttoglobalrecord::new(Imm(0), EntityId(0)),
        "stglobalvar" => insn::Stglobalvar::new(Imm(0), EntityId(0)),
        "stlexvar" => insn::Stlexvar::new(Imm(0), Imm(0)),
        "stmodulevar" => insn::Stmodulevar::new(Imm(0)),
        "stobjbyindex" => insn::Stobjbyindex::new(Imm(0), Reg(0), Imm(0)),
        "stobjbyname" => insn::Stobjbyname::new(Imm(0), EntityId(0), Reg(0)),
        "stobjbyvalue" => insn::Stobjbyvalue::new(Imm(0), Reg(0), Reg(0)),
        "stownbyindex" => insn::Stownbyindex::new(Imm(0), Reg(0), Imm(0)),
        "stownbyname" => insn::Stownbyname::new(Imm(0), EntityId(0), Reg(0)),
        "stownbynamewithnameset" => insn::Stownbynamewithnameset::new(Imm(0), EntityId(0), Reg(0)),
        "stownbyvalue" => insn::Stownbyvalue::new(Imm(0), Reg(0), Reg(0)),
        "stownbyvaluewithnameset" => insn::Stownbyvaluewithnameset::new(Imm(0), Reg(0), Reg(0)),
        "stprivateproperty" => insn::Stprivateproperty::new(Imm(0), Imm(0), Imm(0), Reg(0)),
        "stricteq" => insn::Stricteq::new(Imm(0), Reg(0)),
        "strictnoteq" => insn::Strictnoteq::new(Imm(0), Reg(0)),
        "stsuperbyname" => insn::Stsuperbyname::new(Imm(0), EntityId(0), Reg(0)),
        "stsuperbyvalue" => insn::Stsuperbyvalue::new(Imm(0), Reg(0), Reg(0)),
        "stthisbyname" => insn::Stthisbyname::new(Imm(0), EntityId(0)),
        "stthisbyvalue" => insn::Stthisbyvalue::new(Imm(0), Reg(0)),
        "sttoglobalrecord" => insn::Sttoglobalrecord::new(Imm(0), EntityId(0)),
        "sub2" => insn::Sub2::new(Imm(0), Reg(0)),
        "supercallarrowrange" => insn::Supercallarrowrange::new(Imm(0), Imm(0), Reg(0)),
        "supercallspread" => insn::Supercallspread::new(Imm(0), Reg(0)),
        "supercallthisrange" => insn::Supercallthisrange::new(Imm(0), Imm(0), Reg(0)),
        "suspendgenerator" => insn::Suspendgenerator::new(Reg(0)),
        "testin" => insn::Testin::new(Imm(0), Imm(0), Imm(0)),
        "throw" => insn::Throw::new(),
        "throw.constassignment" => insn::ThrowConstassignment::new(Reg(0)),
        "throw.deletesuperproperty" => insn::ThrowDeletesuperproperty::new(),
        "throw.ifnotobject" => insn::ThrowIfnotobject::new(Reg(0)),
        "throw.ifsupernotcorrectcall" => insn::ThrowIfsupernotcorrectcall::new(Imm(0)),
        "throw.notexists" => insn::ThrowNotexists::new(),
        "throw.patternnoncoercible" => insn::ThrowPatternnoncoercible::new(),
        "throw.undefinedifhole" => insn::ThrowUndefinedifhole::new(Reg(0), Reg(0)),
        "throw.undefinedifholewithname" => insn::ThrowUndefinedifholewithname::new(EntityId(0)),
        "tonumber" => insn::Tonumber::new(Imm(0)),
        "tonumeric" => insn::Tonumeric::new(Imm(0)),
        "tryldglobalbyname" => insn::Tryldglobalbyname::new(Imm(0), EntityId(0)),
        "trystglobalbyname" => insn::Trystglobalbyname::new(Imm(0), EntityId(0)),
        "typeof" => insn::Typeof::new(Imm(0)),
        "wide.callrange" => insn::WideCallrange::new(Imm(0), Reg(0)),
        "wide.callthisrange" => insn::WideCallthisrange::new(Imm(0), Reg(0)),
        "wide.callthisrangewithname" => {
            insn::WideCallthisrangewithname::new(Imm(0), EntityId(0), Reg(0))
        }
        "wide.copyrestargs" => insn::WideCopyrestargs::new(Imm(0)),
        "wide.createobjectwithexcludedkeys" => {
            insn::WideCreateobjectwithexcludedkeys::new(Imm(0), Reg(0), Reg(0))
        }
        "wide.getmodulenamespace" => insn::WideGetmodulenamespace::new(Imm(0)),
        "wide.ldexternalmodulevar" => insn::WideLdexternalmodulevar::new(Imm(0)),
        "wide.ldlexvar" => insn::WideLdlexvar::new(Imm(0), Imm(0)),
        "wide.ldlocalmodulevar" => insn::WideLdlocalmodulevar::new(Imm(0)),
        "wide.ldobjbyindex" => insn::WideLdobjbyindex::new(Imm(0)),
        "wide.ldpatchvar" => insn::WideLdpatchvar::new(Imm(0)),
        "wide.newlexenv" => insn::WideNewlexenv::new(Imm(0)),
        "wide.newlexenvwithname" => insn::WideNewlexenvwithname::new(Imm(0), EntityId(0)),
        "wide.newobjrange" => insn::WideNewobjrange::new(Imm(0), Reg(0)),
        "wide.stlexvar" => insn::WideStlexvar::new(Imm(0), Imm(0)),
        "wide.stmodulevar" => insn::WideStmodulevar::new(Imm(0)),
        "wide.stobjbyindex" => insn::WideStobjbyindex::new(Reg(0), Imm(0)),
        "wide.stownbyindex" => insn::WideStownbyindex::new(Reg(0), Imm(0)),
        "wide.stpatchvar" => insn::WideStpatchvar::new(Imm(0)),
        "wide.supercallarrowrange" => insn::WideSupercallarrowrange::new(Imm(0), Reg(0)),
        "wide.supercallthisrange" => insn::WideSupercallthisrange::new(Imm(0), Reg(0)),
        "xor2" => insn::Xor2::new(Imm(0), Reg(0)),
        _ => return None,
    })
}

/// Build the [`Bytecode`] for `mnemonic` from already-typed operands.
/// `None` on an unknown mnemonic or an operand kind/count mismatch (the
/// caller turns that into a structured parse error).
pub(crate) fn construct(mnemonic: &str, ops: &[RawOperand]) -> Option<Bytecode> {
    Some(match mnemonic {
        "add2" => {
            let [I(a0), R(a1)] = *ops else { return None };
            insn::Add2::new(Imm(a0), Reg(a1))
        }
        "and2" => {
            let [I(a0), R(a1)] = *ops else { return None };
            insn::And2::new(Imm(a0), Reg(a1))
        }
        "apply" => {
            let [I(a0), R(a1), R(a2)] = *ops else {
                return None;
            };
            insn::Apply::new(Imm(a0), Reg(a1), Reg(a2))
        }
        "ashr2" => {
            let [I(a0), R(a1)] = *ops else { return None };
            insn::Ashr2::new(Imm(a0), Reg(a1))
        }
        "asyncfunctionawaituncaught" => {
            let [R(a0)] = *ops else { return None };
            insn::Asyncfunctionawaituncaught::new(Reg(a0))
        }
        "asyncfunctionenter" if ops.is_empty() => insn::Asyncfunctionenter::new(),
        "asyncfunctionreject" => {
            let [R(a0)] = *ops else { return None };
            insn::Asyncfunctionreject::new(Reg(a0))
        }
        "asyncfunctionresolve" => {
            let [R(a0)] = *ops else { return None };
            insn::Asyncfunctionresolve::new(Reg(a0))
        }
        "asyncgeneratorreject" => {
            let [R(a0)] = *ops else { return None };
            insn::Asyncgeneratorreject::new(Reg(a0))
        }
        "asyncgeneratorresolve" => {
            let [R(a0), R(a1), R(a2)] = *ops else {
                return None;
            };
            insn::Asyncgeneratorresolve::new(Reg(a0), Reg(a1), Reg(a2))
        }
        "callarg0" => {
            let [I(a0)] = *ops else { return None };
            insn::Callarg0::new(Imm(a0))
        }
        "callarg1" => {
            let [I(a0), R(a1)] = *ops else { return None };
            insn::Callarg1::new(Imm(a0), Reg(a1))
        }
        "callargs2" => {
            let [I(a0), R(a1), R(a2)] = *ops else {
                return None;
            };
            insn::Callargs2::new(Imm(a0), Reg(a1), Reg(a2))
        }
        "callargs3" => {
            let [I(a0), R(a1), R(a2), R(a3)] = *ops else {
                return None;
            };
            insn::Callargs3::new(Imm(a0), Reg(a1), Reg(a2), Reg(a3))
        }
        "callrange" => {
            let [I(a0), I(a1), R(a2)] = *ops else {
                return None;
            };
            insn::Callrange::new(Imm(a0), Imm(a1), Reg(a2))
        }
        "callruntime.callinit" => {
            let [I(a0), R(a1)] = *ops else { return None };
            insn::CallruntimeCallinit::new(Imm(a0), Reg(a1))
        }
        "callruntime.createprivateproperty" => {
            let [I(a0), E(a1)] = *ops else { return None };
            insn::CallruntimeCreateprivateproperty::new(Imm(a0), EntityId(a1))
        }
        "callruntime.definefieldbyindex" => {
            let [I(a0), I(a1), R(a2)] = *ops else {
                return None;
            };
            insn::CallruntimeDefinefieldbyindex::new(Imm(a0), Imm(a1), Reg(a2))
        }
        "callruntime.definefieldbyvalue" => {
            let [I(a0), R(a1), R(a2)] = *ops else {
                return None;
            };
            insn::CallruntimeDefinefieldbyvalue::new(Imm(a0), Reg(a1), Reg(a2))
        }
        "callruntime.defineprivateproperty" => {
            let [I(a0), I(a1), I(a2), R(a3)] = *ops else {
                return None;
            };
            insn::CallruntimeDefineprivateproperty::new(Imm(a0), Imm(a1), Imm(a2), Reg(a3))
        }
        "callruntime.definesendableclass" => {
            let [I(a0), E(a1), E(a2), I(a3), R(a4)] = *ops else {
                return None;
            };
            insn::CallruntimeDefinesendableclass::new(
                Imm(a0),
                EntityId(a1),
                EntityId(a2),
                Imm(a3),
                Reg(a4),
            )
        }
        "callruntime.isfalse" => {
            let [I(a0)] = *ops else { return None };
            insn::CallruntimeIsfalse::new(Imm(a0))
        }
        "callruntime.istrue" => {
            let [I(a0)] = *ops else { return None };
            insn::CallruntimeIstrue::new(Imm(a0))
        }
        "callruntime.ldlazymodulevar" => {
            let [I(a0)] = *ops else { return None };
            insn::CallruntimeLdlazymodulevar::new(Imm(a0))
        }
        "callruntime.ldlazysendablemodulevar" => {
            let [I(a0)] = *ops else { return None };
            insn::CallruntimeLdlazysendablemodulevar::new(Imm(a0))
        }
        "callruntime.ldsendableclass" => {
            let [I(a0)] = *ops else { return None };
            insn::CallruntimeLdsendableclass::new(Imm(a0))
        }
        "callruntime.ldsendableexternalmodulevar" => {
            let [I(a0)] = *ops else { return None };
            insn::CallruntimeLdsendableexternalmodulevar::new(Imm(a0))
        }
        "callruntime.ldsendablelocalmodulevar" => {
            let [I(a0)] = *ops else { return None };
            insn::CallruntimeLdsendablelocalmodulevar::new(Imm(a0))
        }
        "callruntime.ldsendablevar" => {
            let [I(a0), I(a1)] = *ops else { return None };
            insn::CallruntimeLdsendablevar::new(Imm(a0), Imm(a1))
        }
        "callruntime.newsendableenv" => {
            let [I(a0)] = *ops else { return None };
            insn::CallruntimeNewsendableenv::new(Imm(a0))
        }
        "callruntime.notifyconcurrentresult" if ops.is_empty() => {
            insn::CallruntimeNotifyconcurrentresult::new()
        }
        "callruntime.stsendablevar" => {
            let [I(a0), I(a1)] = *ops else { return None };
            insn::CallruntimeStsendablevar::new(Imm(a0), Imm(a1))
        }
        "callruntime.supercallforwardallargs" => {
            let [R(a0)] = *ops else { return None };
            insn::CallruntimeSupercallforwardallargs::new(Reg(a0))
        }
        "callruntime.topropertykey" if ops.is_empty() => insn::CallruntimeTopropertykey::new(),
        "callruntime.wideldlazymodulevar" => {
            let [I(a0)] = *ops else { return None };
            insn::CallruntimeWideldlazymodulevar::new(Imm(a0))
        }
        "callruntime.wideldlazysendablemodulevar" => {
            let [I(a0)] = *ops else { return None };
            insn::CallruntimeWideldlazysendablemodulevar::new(Imm(a0))
        }
        "callruntime.wideldsendableexternalmodulevar" => {
            let [I(a0)] = *ops else { return None };
            insn::CallruntimeWideldsendableexternalmodulevar::new(Imm(a0))
        }
        "callruntime.wideldsendablelocalmodulevar" => {
            let [I(a0)] = *ops else { return None };
            insn::CallruntimeWideldsendablelocalmodulevar::new(Imm(a0))
        }
        "callruntime.wideldsendablevar" => {
            let [I(a0), I(a1)] = *ops else { return None };
            insn::CallruntimeWideldsendablevar::new(Imm(a0), Imm(a1))
        }
        "callruntime.widenewsendableenv" => {
            let [I(a0)] = *ops else { return None };
            insn::CallruntimeWidenewsendableenv::new(Imm(a0))
        }
        "callruntime.widestsendablevar" => {
            let [I(a0), I(a1)] = *ops else { return None };
            insn::CallruntimeWidestsendablevar::new(Imm(a0), Imm(a1))
        }
        "callthis0" => {
            let [I(a0), R(a1)] = *ops else { return None };
            insn::Callthis0::new(Imm(a0), Reg(a1))
        }
        "callthis0withname" => {
            let [I(a0), E(a1), R(a2)] = *ops else {
                return None;
            };
            insn::Callthis0withname::new(Imm(a0), EntityId(a1), Reg(a2))
        }
        "callthis1" => {
            let [I(a0), R(a1), R(a2)] = *ops else {
                return None;
            };
            insn::Callthis1::new(Imm(a0), Reg(a1), Reg(a2))
        }
        "callthis1withname" => {
            let [I(a0), E(a1), R(a2), R(a3)] = *ops else {
                return None;
            };
            insn::Callthis1withname::new(Imm(a0), EntityId(a1), Reg(a2), Reg(a3))
        }
        "callthis2" => {
            let [I(a0), R(a1), R(a2), R(a3)] = *ops else {
                return None;
            };
            insn::Callthis2::new(Imm(a0), Reg(a1), Reg(a2), Reg(a3))
        }
        "callthis2withname" => {
            let [I(a0), E(a1), R(a2), R(a3), R(a4)] = *ops else {
                return None;
            };
            insn::Callthis2withname::new(Imm(a0), EntityId(a1), Reg(a2), Reg(a3), Reg(a4))
        }
        "callthis3" => {
            let [I(a0), R(a1), R(a2), R(a3), R(a4)] = *ops else {
                return None;
            };
            insn::Callthis3::new(Imm(a0), Reg(a1), Reg(a2), Reg(a3), Reg(a4))
        }
        "callthis3withname" => {
            let [I(a0), E(a1), R(a2), R(a3), R(a4), R(a5)] = *ops else {
                return None;
            };
            insn::Callthis3withname::new(Imm(a0), EntityId(a1), Reg(a2), Reg(a3), Reg(a4), Reg(a5))
        }
        "callthisrange" => {
            let [I(a0), I(a1), R(a2)] = *ops else {
                return None;
            };
            insn::Callthisrange::new(Imm(a0), Imm(a1), Reg(a2))
        }
        "callthisrangewithname" => {
            let [I(a0), I(a1), E(a2), R(a3)] = *ops else {
                return None;
            };
            insn::Callthisrangewithname::new(Imm(a0), Imm(a1), EntityId(a2), Reg(a3))
        }
        "closeiterator" => {
            let [I(a0), R(a1)] = *ops else { return None };
            insn::Closeiterator::new(Imm(a0), Reg(a1))
        }
        "copydataproperties" => {
            let [R(a0)] = *ops else { return None };
            insn::Copydataproperties::new(Reg(a0))
        }
        "copyrestargs" => {
            let [I(a0)] = *ops else { return None };
            insn::Copyrestargs::new(Imm(a0))
        }
        "createarraywithbuffer" => {
            let [I(a0), E(a1)] = *ops else { return None };
            insn::Createarraywithbuffer::new(Imm(a0), EntityId(a1))
        }
        "createasyncgeneratorobj" => {
            let [R(a0)] = *ops else { return None };
            insn::Createasyncgeneratorobj::new(Reg(a0))
        }
        "createemptyarray" => {
            let [I(a0)] = *ops else { return None };
            insn::Createemptyarray::new(Imm(a0))
        }
        "createemptyobject" if ops.is_empty() => insn::Createemptyobject::new(),
        "creategeneratorobj" => {
            let [R(a0)] = *ops else { return None };
            insn::Creategeneratorobj::new(Reg(a0))
        }
        "createiterresultobj" => {
            let [R(a0), R(a1)] = *ops else { return None };
            insn::Createiterresultobj::new(Reg(a0), Reg(a1))
        }
        "createobjectwithbuffer" => {
            let [I(a0), E(a1)] = *ops else { return None };
            insn::Createobjectwithbuffer::new(Imm(a0), EntityId(a1))
        }
        "createobjectwithexcludedkeys" => {
            let [I(a0), R(a1), R(a2)] = *ops else {
                return None;
            };
            insn::Createobjectwithexcludedkeys::new(Imm(a0), Reg(a1), Reg(a2))
        }
        "createregexpwithliteral" => {
            let [I(a0), E(a1), I(a2)] = *ops else {
                return None;
            };
            insn::Createregexpwithliteral::new(Imm(a0), EntityId(a1), Imm(a2))
        }
        "debugger" if ops.is_empty() => insn::Debugger::new(),
        "dec" => {
            let [I(a0)] = *ops else { return None };
            insn::Dec::new(Imm(a0))
        }
        "defineclasswithbuffer" => {
            let [I(a0), E(a1), E(a2), I(a3), R(a4)] = *ops else {
                return None;
            };
            insn::Defineclasswithbuffer::new(Imm(a0), EntityId(a1), EntityId(a2), Imm(a3), Reg(a4))
        }
        "definefieldbyname" => {
            let [I(a0), E(a1), R(a2)] = *ops else {
                return None;
            };
            insn::Definefieldbyname::new(Imm(a0), EntityId(a1), Reg(a2))
        }
        "definefunc" => {
            let [I(a0), E(a1), I(a2)] = *ops else {
                return None;
            };
            insn::Definefunc::new(Imm(a0), EntityId(a1), Imm(a2))
        }
        "definegettersetterbyvalue" => {
            let [R(a0), R(a1), R(a2), R(a3)] = *ops else {
                return None;
            };
            insn::Definegettersetterbyvalue::new(Reg(a0), Reg(a1), Reg(a2), Reg(a3))
        }
        "definemethod" => {
            let [I(a0), E(a1), I(a2)] = *ops else {
                return None;
            };
            insn::Definemethod::new(Imm(a0), EntityId(a1), Imm(a2))
        }
        "definepropertybyname" => {
            let [I(a0), E(a1), R(a2)] = *ops else {
                return None;
            };
            insn::Definepropertybyname::new(Imm(a0), EntityId(a1), Reg(a2))
        }
        "delobjprop" => {
            let [R(a0)] = *ops else { return None };
            insn::Delobjprop::new(Reg(a0))
        }
        "deprecated.asyncfunctionawaituncaught" => {
            let [R(a0), R(a1)] = *ops else { return None };
            insn::DeprecatedAsyncfunctionawaituncaught::new(Reg(a0), Reg(a1))
        }
        "deprecated.asyncfunctionreject" => {
            let [R(a0), R(a1), R(a2)] = *ops else {
                return None;
            };
            insn::DeprecatedAsyncfunctionreject::new(Reg(a0), Reg(a1), Reg(a2))
        }
        "deprecated.asyncfunctionresolve" => {
            let [R(a0), R(a1), R(a2)] = *ops else {
                return None;
            };
            insn::DeprecatedAsyncfunctionresolve::new(Reg(a0), Reg(a1), Reg(a2))
        }
        "deprecated.asyncgeneratorreject" => {
            let [R(a0), R(a1)] = *ops else { return None };
            insn::DeprecatedAsyncgeneratorreject::new(Reg(a0), Reg(a1))
        }
        "deprecated.callarg0" => {
            let [R(a0)] = *ops else { return None };
            insn::DeprecatedCallarg0::new(Reg(a0))
        }
        "deprecated.callarg1" => {
            let [R(a0), R(a1)] = *ops else { return None };
            insn::DeprecatedCallarg1::new(Reg(a0), Reg(a1))
        }
        "deprecated.callargs2" => {
            let [R(a0), R(a1), R(a2)] = *ops else {
                return None;
            };
            insn::DeprecatedCallargs2::new(Reg(a0), Reg(a1), Reg(a2))
        }
        "deprecated.callargs3" => {
            let [R(a0), R(a1), R(a2), R(a3)] = *ops else {
                return None;
            };
            insn::DeprecatedCallargs3::new(Reg(a0), Reg(a1), Reg(a2), Reg(a3))
        }
        "deprecated.callrange" => {
            let [I(a0), R(a1)] = *ops else { return None };
            insn::DeprecatedCallrange::new(Imm(a0), Reg(a1))
        }
        "deprecated.callspread" => {
            let [R(a0), R(a1), R(a2)] = *ops else {
                return None;
            };
            insn::DeprecatedCallspread::new(Reg(a0), Reg(a1), Reg(a2))
        }
        "deprecated.callthisrange" => {
            let [I(a0), R(a1)] = *ops else { return None };
            insn::DeprecatedCallthisrange::new(Imm(a0), Reg(a1))
        }
        "deprecated.copydataproperties" => {
            let [R(a0), R(a1)] = *ops else { return None };
            insn::DeprecatedCopydataproperties::new(Reg(a0), Reg(a1))
        }
        "deprecated.createarraywithbuffer" => {
            let [I(a0)] = *ops else { return None };
            insn::DeprecatedCreatearraywithbuffer::new(Imm(a0))
        }
        "deprecated.createobjecthavingmethod" => {
            let [I(a0)] = *ops else { return None };
            insn::DeprecatedCreateobjecthavingmethod::new(Imm(a0))
        }
        "deprecated.createobjectwithbuffer" => {
            let [I(a0)] = *ops else { return None };
            insn::DeprecatedCreateobjectwithbuffer::new(Imm(a0))
        }
        "deprecated.dec" => {
            let [R(a0)] = *ops else { return None };
            insn::DeprecatedDec::new(Reg(a0))
        }
        "deprecated.defineclasswithbuffer" => {
            let [E(a0), I(a1), I(a2), R(a3), R(a4)] = *ops else {
                return None;
            };
            insn::DeprecatedDefineclasswithbuffer::new(
                EntityId(a0),
                Imm(a1),
                Imm(a2),
                Reg(a3),
                Reg(a4),
            )
        }
        "deprecated.delobjprop" => {
            let [R(a0), R(a1)] = *ops else { return None };
            insn::DeprecatedDelobjprop::new(Reg(a0), Reg(a1))
        }
        "deprecated.dynamicimport" => {
            let [R(a0)] = *ops else { return None };
            insn::DeprecatedDynamicimport::new(Reg(a0))
        }
        "deprecated.getiteratornext" => {
            let [R(a0), R(a1)] = *ops else { return None };
            insn::DeprecatedGetiteratornext::new(Reg(a0), Reg(a1))
        }
        "deprecated.getmodulenamespace" => {
            let [E(a0)] = *ops else { return None };
            insn::DeprecatedGetmodulenamespace::new(EntityId(a0))
        }
        "deprecated.getresumemode" => {
            let [R(a0)] = *ops else { return None };
            insn::DeprecatedGetresumemode::new(Reg(a0))
        }
        "deprecated.gettemplateobject" => {
            let [R(a0)] = *ops else { return None };
            insn::DeprecatedGettemplateobject::new(Reg(a0))
        }
        "deprecated.inc" => {
            let [R(a0)] = *ops else { return None };
            insn::DeprecatedInc::new(Reg(a0))
        }
        "deprecated.ldhomeobject" if ops.is_empty() => insn::DeprecatedLdhomeobject::new(),
        "deprecated.ldlexenv" if ops.is_empty() => insn::DeprecatedLdlexenv::new(),
        "deprecated.ldmodulevar" => {
            let [E(a0), I(a1)] = *ops else { return None };
            insn::DeprecatedLdmodulevar::new(EntityId(a0), Imm(a1))
        }
        "deprecated.ldobjbyindex" => {
            let [R(a0), I(a1)] = *ops else { return None };
            insn::DeprecatedLdobjbyindex::new(Reg(a0), Imm(a1))
        }
        "deprecated.ldobjbyname" => {
            let [E(a0), R(a1)] = *ops else { return None };
            insn::DeprecatedLdobjbyname::new(EntityId(a0), Reg(a1))
        }
        "deprecated.ldobjbyvalue" => {
            let [R(a0), R(a1)] = *ops else { return None };
            insn::DeprecatedLdobjbyvalue::new(Reg(a0), Reg(a1))
        }
        "deprecated.ldsuperbyname" => {
            let [E(a0), R(a1)] = *ops else { return None };
            insn::DeprecatedLdsuperbyname::new(EntityId(a0), Reg(a1))
        }
        "deprecated.ldsuperbyvalue" => {
            let [R(a0), R(a1)] = *ops else { return None };
            insn::DeprecatedLdsuperbyvalue::new(Reg(a0), Reg(a1))
        }
        "deprecated.neg" => {
            let [R(a0)] = *ops else { return None };
            insn::DeprecatedNeg::new(Reg(a0))
        }
        "deprecated.not" => {
            let [R(a0)] = *ops else { return None };
            insn::DeprecatedNot::new(Reg(a0))
        }
        "deprecated.poplexenv" if ops.is_empty() => insn::DeprecatedPoplexenv::new(),
        "deprecated.resumegenerator" => {
            let [R(a0)] = *ops else { return None };
            insn::DeprecatedResumegenerator::new(Reg(a0))
        }
        "deprecated.setobjectwithproto" => {
            let [R(a0), R(a1)] = *ops else { return None };
            insn::DeprecatedSetobjectwithproto::new(Reg(a0), Reg(a1))
        }
        "deprecated.stclasstoglobalrecord" => {
            let [E(a0)] = *ops else { return None };
            insn::DeprecatedStclasstoglobalrecord::new(EntityId(a0))
        }
        "deprecated.stconsttoglobalrecord" => {
            let [E(a0)] = *ops else { return None };
            insn::DeprecatedStconsttoglobalrecord::new(EntityId(a0))
        }
        "deprecated.stlettoglobalrecord" => {
            let [E(a0)] = *ops else { return None };
            insn::DeprecatedStlettoglobalrecord::new(EntityId(a0))
        }
        "deprecated.stlexvar" => {
            let [I(a0), I(a1), R(a2)] = *ops else {
                return None;
            };
            insn::DeprecatedStlexvar::new(Imm(a0), Imm(a1), Reg(a2))
        }
        "deprecated.stmodulevar" => {
            let [E(a0)] = *ops else { return None };
            insn::DeprecatedStmodulevar::new(EntityId(a0))
        }
        "deprecated.suspendgenerator" => {
            let [R(a0), R(a1)] = *ops else { return None };
            insn::DeprecatedSuspendgenerator::new(Reg(a0), Reg(a1))
        }
        "deprecated.tonumber" => {
            let [R(a0)] = *ops else { return None };
            insn::DeprecatedTonumber::new(Reg(a0))
        }
        "deprecated.tonumeric" => {
            let [R(a0)] = *ops else { return None };
            insn::DeprecatedTonumeric::new(Reg(a0))
        }
        "div2" => {
            let [I(a0), R(a1)] = *ops else { return None };
            insn::Div2::new(Imm(a0), Reg(a1))
        }
        "dynamicimport" if ops.is_empty() => insn::Dynamicimport::new(),
        "eq" => {
            let [I(a0), R(a1)] = *ops else { return None };
            insn::Eq::new(Imm(a0), Reg(a1))
        }
        "exp" => {
            let [I(a0), R(a1)] = *ops else { return None };
            insn::Exp::new(Imm(a0), Reg(a1))
        }
        "fldai" => {
            let [I(a0)] = *ops else { return None };
            insn::Fldai::new(Imm(a0))
        }
        "getasynciterator" => {
            let [I(a0)] = *ops else { return None };
            insn::Getasynciterator::new(Imm(a0))
        }
        "getiterator" => {
            let [I(a0)] = *ops else { return None };
            insn::Getiterator::new(Imm(a0))
        }
        "getmodulenamespace" => {
            let [I(a0)] = *ops else { return None };
            insn::Getmodulenamespace::new(Imm(a0))
        }
        "getnextpropname" => {
            let [R(a0)] = *ops else { return None };
            insn::Getnextpropname::new(Reg(a0))
        }
        "getpropiterator" if ops.is_empty() => insn::Getpropiterator::new(),
        "getresumemode" if ops.is_empty() => insn::Getresumemode::new(),
        "gettemplateobject" => {
            let [I(a0)] = *ops else { return None };
            insn::Gettemplateobject::new(Imm(a0))
        }
        "getunmappedargs" if ops.is_empty() => insn::Getunmappedargs::new(),
        "greater" => {
            let [I(a0), R(a1)] = *ops else { return None };
            insn::Greater::new(Imm(a0), Reg(a1))
        }
        "greatereq" => {
            let [I(a0), R(a1)] = *ops else { return None };
            insn::Greatereq::new(Imm(a0), Reg(a1))
        }
        "inc" => {
            let [I(a0)] = *ops else { return None };
            insn::Inc::new(Imm(a0))
        }
        "instanceof" => {
            let [I(a0), R(a1)] = *ops else { return None };
            insn::Instanceof::new(Imm(a0), Reg(a1))
        }
        "isfalse" if ops.is_empty() => insn::Isfalse::new(),
        "isin" => {
            let [I(a0), R(a1)] = *ops else { return None };
            insn::Isin::new(Imm(a0), Reg(a1))
        }
        "istrue" if ops.is_empty() => insn::Istrue::new(),
        "jeq" => {
            let [R(a0), L(a1)] = *ops else { return None };
            insn::Jeq::new(Reg(a0), Label(a1))
        }
        "jeqnull" => {
            let [L(a0)] = *ops else { return None };
            insn::Jeqnull::new(Label(a0))
        }
        "jequndefined" => {
            let [L(a0)] = *ops else { return None };
            insn::Jequndefined::new(Label(a0))
        }
        "jeqz" => {
            let [L(a0)] = *ops else { return None };
            insn::Jeqz::new(Label(a0))
        }
        "jmp" => {
            let [L(a0)] = *ops else { return None };
            insn::Jmp::new(Label(a0))
        }
        "jne" => {
            let [R(a0), L(a1)] = *ops else { return None };
            insn::Jne::new(Reg(a0), Label(a1))
        }
        "jnenull" => {
            let [L(a0)] = *ops else { return None };
            insn::Jnenull::new(Label(a0))
        }
        "jneundefined" => {
            let [L(a0)] = *ops else { return None };
            insn::Jneundefined::new(Label(a0))
        }
        "jnez" => {
            let [L(a0)] = *ops else { return None };
            insn::Jnez::new(Label(a0))
        }
        "jnstricteq" => {
            let [R(a0), L(a1)] = *ops else { return None };
            insn::Jnstricteq::new(Reg(a0), Label(a1))
        }
        "jnstricteqnull" => {
            let [L(a0)] = *ops else { return None };
            insn::Jnstricteqnull::new(Label(a0))
        }
        "jnstrictequndefined" => {
            let [L(a0)] = *ops else { return None };
            insn::Jnstrictequndefined::new(Label(a0))
        }
        "jnstricteqz" => {
            let [L(a0)] = *ops else { return None };
            insn::Jnstricteqz::new(Label(a0))
        }
        "jstricteq" => {
            let [R(a0), L(a1)] = *ops else { return None };
            insn::Jstricteq::new(Reg(a0), Label(a1))
        }
        "jstricteqnull" => {
            let [L(a0)] = *ops else { return None };
            insn::Jstricteqnull::new(Label(a0))
        }
        "jstrictequndefined" => {
            let [L(a0)] = *ops else { return None };
            insn::Jstrictequndefined::new(Label(a0))
        }
        "jstricteqz" => {
            let [L(a0)] = *ops else { return None };
            insn::Jstricteqz::new(Label(a0))
        }
        "lda" => {
            let [R(a0)] = *ops else { return None };
            insn::Lda::new(Reg(a0))
        }
        "lda.str" => {
            let [E(a0)] = *ops else { return None };
            insn::LdaStr::new(EntityId(a0))
        }
        "ldai" => {
            let [I(a0)] = *ops else { return None };
            insn::Ldai::new(Imm(a0))
        }
        "ldbigint" => {
            let [E(a0)] = *ops else { return None };
            insn::Ldbigint::new(EntityId(a0))
        }
        "ldexternalmodulevar" => {
            let [I(a0)] = *ops else { return None };
            insn::Ldexternalmodulevar::new(Imm(a0))
        }
        "ldfalse" if ops.is_empty() => insn::Ldfalse::new(),
        "ldfunction" if ops.is_empty() => insn::Ldfunction::new(),
        "ldglobal" if ops.is_empty() => insn::Ldglobal::new(),
        "ldglobalvar" => {
            let [I(a0), E(a1)] = *ops else { return None };
            insn::Ldglobalvar::new(Imm(a0), EntityId(a1))
        }
        "ldhole" if ops.is_empty() => insn::Ldhole::new(),
        "ldinfinity" if ops.is_empty() => insn::Ldinfinity::new(),
        "ldlexvar" => {
            let [I(a0), I(a1)] = *ops else { return None };
            insn::Ldlexvar::new(Imm(a0), Imm(a1))
        }
        "ldlocalmodulevar" => {
            let [I(a0)] = *ops else { return None };
            insn::Ldlocalmodulevar::new(Imm(a0))
        }
        "ldnan" if ops.is_empty() => insn::Ldnan::new(),
        "ldnewtarget" if ops.is_empty() => insn::Ldnewtarget::new(),
        "ldnull" if ops.is_empty() => insn::Ldnull::new(),
        "ldobjbyindex" => {
            let [I(a0), I(a1)] = *ops else { return None };
            insn::Ldobjbyindex::new(Imm(a0), Imm(a1))
        }
        "ldobjbyname" => {
            let [I(a0), E(a1)] = *ops else { return None };
            insn::Ldobjbyname::new(Imm(a0), EntityId(a1))
        }
        "ldobjbyvalue" => {
            let [I(a0), R(a1)] = *ops else { return None };
            insn::Ldobjbyvalue::new(Imm(a0), Reg(a1))
        }
        "ldprivateproperty" => {
            let [I(a0), I(a1), I(a2)] = *ops else {
                return None;
            };
            insn::Ldprivateproperty::new(Imm(a0), Imm(a1), Imm(a2))
        }
        "ldsuperbyname" => {
            let [I(a0), E(a1)] = *ops else { return None };
            insn::Ldsuperbyname::new(Imm(a0), EntityId(a1))
        }
        "ldsuperbyvalue" => {
            let [I(a0), R(a1)] = *ops else { return None };
            insn::Ldsuperbyvalue::new(Imm(a0), Reg(a1))
        }
        "ldsymbol" if ops.is_empty() => insn::Ldsymbol::new(),
        "ldthis" if ops.is_empty() => insn::Ldthis::new(),
        "ldthisbyname" => {
            let [I(a0), E(a1)] = *ops else { return None };
            insn::Ldthisbyname::new(Imm(a0), EntityId(a1))
        }
        "ldthisbyvalue" => {
            let [I(a0)] = *ops else { return None };
            insn::Ldthisbyvalue::new(Imm(a0))
        }
        "ldtrue" if ops.is_empty() => insn::Ldtrue::new(),
        "ldundefined" if ops.is_empty() => insn::Ldundefined::new(),
        "less" => {
            let [I(a0), R(a1)] = *ops else { return None };
            insn::Less::new(Imm(a0), Reg(a1))
        }
        "lesseq" => {
            let [I(a0), R(a1)] = *ops else { return None };
            insn::Lesseq::new(Imm(a0), Reg(a1))
        }
        "mod2" => {
            let [I(a0), R(a1)] = *ops else { return None };
            insn::Mod2::new(Imm(a0), Reg(a1))
        }
        "mov" => {
            let [R(a0), R(a1)] = *ops else { return None };
            insn::Mov::new(Reg(a0), Reg(a1))
        }
        "mul2" => {
            let [I(a0), R(a1)] = *ops else { return None };
            insn::Mul2::new(Imm(a0), Reg(a1))
        }
        "neg" => {
            let [I(a0)] = *ops else { return None };
            insn::Neg::new(Imm(a0))
        }
        "newlexenv" => {
            let [I(a0)] = *ops else { return None };
            insn::Newlexenv::new(Imm(a0))
        }
        "newlexenvwithname" => {
            let [I(a0), E(a1)] = *ops else { return None };
            insn::Newlexenvwithname::new(Imm(a0), EntityId(a1))
        }
        "newobjapply" => {
            let [I(a0), R(a1)] = *ops else { return None };
            insn::Newobjapply::new(Imm(a0), Reg(a1))
        }
        "newobjrange" => {
            let [I(a0), I(a1), R(a2)] = *ops else {
                return None;
            };
            insn::Newobjrange::new(Imm(a0), Imm(a1), Reg(a2))
        }
        "nop" if ops.is_empty() => insn::Nop::new(),
        "not" => {
            let [I(a0)] = *ops else { return None };
            insn::Not::new(Imm(a0))
        }
        "noteq" => {
            let [I(a0), R(a1)] = *ops else { return None };
            insn::Noteq::new(Imm(a0), Reg(a1))
        }
        "or2" => {
            let [I(a0), R(a1)] = *ops else { return None };
            insn::Or2::new(Imm(a0), Reg(a1))
        }
        "poplexenv" if ops.is_empty() => insn::Poplexenv::new(),
        "resumegenerator" if ops.is_empty() => insn::Resumegenerator::new(),
        "return" if ops.is_empty() => insn::Return::new(),
        "returnundefined" if ops.is_empty() => insn::Returnundefined::new(),
        "setgeneratorstate" => {
            let [I(a0)] = *ops else { return None };
            insn::Setgeneratorstate::new(Imm(a0))
        }
        "setobjectwithproto" => {
            let [I(a0), R(a1)] = *ops else { return None };
            insn::Setobjectwithproto::new(Imm(a0), Reg(a1))
        }
        "shl2" => {
            let [I(a0), R(a1)] = *ops else { return None };
            insn::Shl2::new(Imm(a0), Reg(a1))
        }
        "shr2" => {
            let [I(a0), R(a1)] = *ops else { return None };
            insn::Shr2::new(Imm(a0), Reg(a1))
        }
        "sta" => {
            let [R(a0)] = *ops else { return None };
            insn::Sta::new(Reg(a0))
        }
        "starrayspread" => {
            let [R(a0), R(a1)] = *ops else { return None };
            insn::Starrayspread::new(Reg(a0), Reg(a1))
        }
        "stconsttoglobalrecord" => {
            let [I(a0), E(a1)] = *ops else { return None };
            insn::Stconsttoglobalrecord::new(Imm(a0), EntityId(a1))
        }
        "stglobalvar" => {
            let [I(a0), E(a1)] = *ops else { return None };
            insn::Stglobalvar::new(Imm(a0), EntityId(a1))
        }
        "stlexvar" => {
            let [I(a0), I(a1)] = *ops else { return None };
            insn::Stlexvar::new(Imm(a0), Imm(a1))
        }
        "stmodulevar" => {
            let [I(a0)] = *ops else { return None };
            insn::Stmodulevar::new(Imm(a0))
        }
        "stobjbyindex" => {
            let [I(a0), R(a1), I(a2)] = *ops else {
                return None;
            };
            insn::Stobjbyindex::new(Imm(a0), Reg(a1), Imm(a2))
        }
        "stobjbyname" => {
            let [I(a0), E(a1), R(a2)] = *ops else {
                return None;
            };
            insn::Stobjbyname::new(Imm(a0), EntityId(a1), Reg(a2))
        }
        "stobjbyvalue" => {
            let [I(a0), R(a1), R(a2)] = *ops else {
                return None;
            };
            insn::Stobjbyvalue::new(Imm(a0), Reg(a1), Reg(a2))
        }
        "stownbyindex" => {
            let [I(a0), R(a1), I(a2)] = *ops else {
                return None;
            };
            insn::Stownbyindex::new(Imm(a0), Reg(a1), Imm(a2))
        }
        "stownbyname" => {
            let [I(a0), E(a1), R(a2)] = *ops else {
                return None;
            };
            insn::Stownbyname::new(Imm(a0), EntityId(a1), Reg(a2))
        }
        "stownbynamewithnameset" => {
            let [I(a0), E(a1), R(a2)] = *ops else {
                return None;
            };
            insn::Stownbynamewithnameset::new(Imm(a0), EntityId(a1), Reg(a2))
        }
        "stownbyvalue" => {
            let [I(a0), R(a1), R(a2)] = *ops else {
                return None;
            };
            insn::Stownbyvalue::new(Imm(a0), Reg(a1), Reg(a2))
        }
        "stownbyvaluewithnameset" => {
            let [I(a0), R(a1), R(a2)] = *ops else {
                return None;
            };
            insn::Stownbyvaluewithnameset::new(Imm(a0), Reg(a1), Reg(a2))
        }
        "stprivateproperty" => {
            let [I(a0), I(a1), I(a2), R(a3)] = *ops else {
                return None;
            };
            insn::Stprivateproperty::new(Imm(a0), Imm(a1), Imm(a2), Reg(a3))
        }
        "stricteq" => {
            let [I(a0), R(a1)] = *ops else { return None };
            insn::Stricteq::new(Imm(a0), Reg(a1))
        }
        "strictnoteq" => {
            let [I(a0), R(a1)] = *ops else { return None };
            insn::Strictnoteq::new(Imm(a0), Reg(a1))
        }
        "stsuperbyname" => {
            let [I(a0), E(a1), R(a2)] = *ops else {
                return None;
            };
            insn::Stsuperbyname::new(Imm(a0), EntityId(a1), Reg(a2))
        }
        "stsuperbyvalue" => {
            let [I(a0), R(a1), R(a2)] = *ops else {
                return None;
            };
            insn::Stsuperbyvalue::new(Imm(a0), Reg(a1), Reg(a2))
        }
        "stthisbyname" => {
            let [I(a0), E(a1)] = *ops else { return None };
            insn::Stthisbyname::new(Imm(a0), EntityId(a1))
        }
        "stthisbyvalue" => {
            let [I(a0), R(a1)] = *ops else { return None };
            insn::Stthisbyvalue::new(Imm(a0), Reg(a1))
        }
        "sttoglobalrecord" => {
            let [I(a0), E(a1)] = *ops else { return None };
            insn::Sttoglobalrecord::new(Imm(a0), EntityId(a1))
        }
        "sub2" => {
            let [I(a0), R(a1)] = *ops else { return None };
            insn::Sub2::new(Imm(a0), Reg(a1))
        }
        "supercallarrowrange" => {
            let [I(a0), I(a1), R(a2)] = *ops else {
                return None;
            };
            insn::Supercallarrowrange::new(Imm(a0), Imm(a1), Reg(a2))
        }
        "supercallspread" => {
            let [I(a0), R(a1)] = *ops else { return None };
            insn::Supercallspread::new(Imm(a0), Reg(a1))
        }
        "supercallthisrange" => {
            let [I(a0), I(a1), R(a2)] = *ops else {
                return None;
            };
            insn::Supercallthisrange::new(Imm(a0), Imm(a1), Reg(a2))
        }
        "suspendgenerator" => {
            let [R(a0)] = *ops else { return None };
            insn::Suspendgenerator::new(Reg(a0))
        }
        "testin" => {
            let [I(a0), I(a1), I(a2)] = *ops else {
                return None;
            };
            insn::Testin::new(Imm(a0), Imm(a1), Imm(a2))
        }
        "throw" if ops.is_empty() => insn::Throw::new(),
        "throw.constassignment" => {
            let [R(a0)] = *ops else { return None };
            insn::ThrowConstassignment::new(Reg(a0))
        }
        "throw.deletesuperproperty" if ops.is_empty() => insn::ThrowDeletesuperproperty::new(),
        "throw.ifnotobject" => {
            let [R(a0)] = *ops else { return None };
            insn::ThrowIfnotobject::new(Reg(a0))
        }
        "throw.ifsupernotcorrectcall" => {
            let [I(a0)] = *ops else { return None };
            insn::ThrowIfsupernotcorrectcall::new(Imm(a0))
        }
        "throw.notexists" if ops.is_empty() => insn::ThrowNotexists::new(),
        "throw.patternnoncoercible" if ops.is_empty() => insn::ThrowPatternnoncoercible::new(),
        "throw.undefinedifhole" => {
            let [R(a0), R(a1)] = *ops else { return None };
            insn::ThrowUndefinedifhole::new(Reg(a0), Reg(a1))
        }
        "throw.undefinedifholewithname" => {
            let [E(a0)] = *ops else { return None };
            insn::ThrowUndefinedifholewithname::new(EntityId(a0))
        }
        "tonumber" => {
            let [I(a0)] = *ops else { return None };
            insn::Tonumber::new(Imm(a0))
        }
        "tonumeric" => {
            let [I(a0)] = *ops else { return None };
            insn::Tonumeric::new(Imm(a0))
        }
        "tryldglobalbyname" => {
            let [I(a0), E(a1)] = *ops else { return None };
            insn::Tryldglobalbyname::new(Imm(a0), EntityId(a1))
        }
        "trystglobalbyname" => {
            let [I(a0), E(a1)] = *ops else { return None };
            insn::Trystglobalbyname::new(Imm(a0), EntityId(a1))
        }
        "typeof" => {
            let [I(a0)] = *ops else { return None };
            insn::Typeof::new(Imm(a0))
        }
        "wide.callrange" => {
            let [I(a0), R(a1)] = *ops else { return None };
            insn::WideCallrange::new(Imm(a0), Reg(a1))
        }
        "wide.callthisrange" => {
            let [I(a0), R(a1)] = *ops else { return None };
            insn::WideCallthisrange::new(Imm(a0), Reg(a1))
        }
        "wide.callthisrangewithname" => {
            let [I(a0), E(a1), R(a2)] = *ops else {
                return None;
            };
            insn::WideCallthisrangewithname::new(Imm(a0), EntityId(a1), Reg(a2))
        }
        "wide.copyrestargs" => {
            let [I(a0)] = *ops else { return None };
            insn::WideCopyrestargs::new(Imm(a0))
        }
        "wide.createobjectwithexcludedkeys" => {
            let [I(a0), R(a1), R(a2)] = *ops else {
                return None;
            };
            insn::WideCreateobjectwithexcludedkeys::new(Imm(a0), Reg(a1), Reg(a2))
        }
        "wide.getmodulenamespace" => {
            let [I(a0)] = *ops else { return None };
            insn::WideGetmodulenamespace::new(Imm(a0))
        }
        "wide.ldexternalmodulevar" => {
            let [I(a0)] = *ops else { return None };
            insn::WideLdexternalmodulevar::new(Imm(a0))
        }
        "wide.ldlexvar" => {
            let [I(a0), I(a1)] = *ops else { return None };
            insn::WideLdlexvar::new(Imm(a0), Imm(a1))
        }
        "wide.ldlocalmodulevar" => {
            let [I(a0)] = *ops else { return None };
            insn::WideLdlocalmodulevar::new(Imm(a0))
        }
        "wide.ldobjbyindex" => {
            let [I(a0)] = *ops else { return None };
            insn::WideLdobjbyindex::new(Imm(a0))
        }
        "wide.ldpatchvar" => {
            let [I(a0)] = *ops else { return None };
            insn::WideLdpatchvar::new(Imm(a0))
        }
        "wide.newlexenv" => {
            let [I(a0)] = *ops else { return None };
            insn::WideNewlexenv::new(Imm(a0))
        }
        "wide.newlexenvwithname" => {
            let [I(a0), E(a1)] = *ops else { return None };
            insn::WideNewlexenvwithname::new(Imm(a0), EntityId(a1))
        }
        "wide.newobjrange" => {
            let [I(a0), R(a1)] = *ops else { return None };
            insn::WideNewobjrange::new(Imm(a0), Reg(a1))
        }
        "wide.stlexvar" => {
            let [I(a0), I(a1)] = *ops else { return None };
            insn::WideStlexvar::new(Imm(a0), Imm(a1))
        }
        "wide.stmodulevar" => {
            let [I(a0)] = *ops else { return None };
            insn::WideStmodulevar::new(Imm(a0))
        }
        "wide.stobjbyindex" => {
            let [R(a0), I(a1)] = *ops else { return None };
            insn::WideStobjbyindex::new(Reg(a0), Imm(a1))
        }
        "wide.stownbyindex" => {
            let [R(a0), I(a1)] = *ops else { return None };
            insn::WideStownbyindex::new(Reg(a0), Imm(a1))
        }
        "wide.stpatchvar" => {
            let [I(a0)] = *ops else { return None };
            insn::WideStpatchvar::new(Imm(a0))
        }
        "wide.supercallarrowrange" => {
            let [I(a0), R(a1)] = *ops else { return None };
            insn::WideSupercallarrowrange::new(Imm(a0), Reg(a1))
        }
        "wide.supercallthisrange" => {
            let [I(a0), R(a1)] = *ops else { return None };
            insn::WideSupercallthisrange::new(Imm(a0), Reg(a1))
        }
        "xor2" => {
            let [I(a0), R(a1)] = *ops else { return None };
            insn::Xor2::new(Imm(a0), Reg(a1))
        }
        _ => return None,
    })
}

#[cfg(test)]
mod tests {
    //! Unit coverage for the construction table (the CI coverage job skips
    //! the asm corpus gates, so these tests carry the table's coverage):
    //! every MNEMONICS entry constructs from its canonical operand vector —
    //! the shape `parse::build_body` feeds — wrong shapes count as `None`,
    //! and unknown mnemonics map to `None`. The corpus-absent arms
    //! (`deprecated.*`, `wide.*`, the legacy jumps, …) additionally
    //! round-trip through abcd_isa encode/decode.
    use super::*;
    use abcd_isa::Operand;

    /// The RawOperand vector `build_body` would feed `construct` for
    /// `mnemonic`: one operand per the dummy instance's operand kinds.
    fn canonical_ops(mnemonic: &str) -> Vec<RawOperand> {
        dummy(mnemonic)
            .unwrap_or_else(|| panic!("{mnemonic} must have a dummy arm"))
            .operands()
            .iter()
            .map(|op| match *op {
                Operand::Reg(_) => R(1),
                Operand::Imm(_) => I(1),
                Operand::Entity(_, _) => E(1),
                Operand::Label(_) => L(0),
            })
            .collect()
    }

    /// The operand view a canonical construction must produce (dummy's
    /// kinds with the canonical payloads).
    fn canonical_operands(mnemonic: &str) -> Vec<Operand> {
        dummy(mnemonic)
            .unwrap()
            .operands()
            .iter()
            .map(|op| match *op {
                Operand::Reg(_) => Operand::Reg(1),
                Operand::Imm(_) => Operand::Imm(1),
                Operand::Entity(kind, _) => Operand::Entity(kind, 1),
                Operand::Label(_) => Operand::Label(0),
            })
            .collect()
    }

    #[test]
    fn mnemonics_table_is_sorted_and_unique() {
        // build_body looks specs up by name; keep the table binary-search
        // friendly and free of shadowed entries.
        let mut sorted = MNEMONICS.to_vec();
        sorted.sort_unstable();
        sorted.dedup();
        assert_eq!(sorted, MNEMONICS, "MNEMONICS must be sorted and unique");
    }

    #[test]
    fn dummy_covers_every_mnemonic() {
        for &mnemonic in MNEMONICS {
            assert!(dummy(mnemonic).is_some(), "dummy({mnemonic})");
        }
        assert!(dummy("bogus").is_none());
        assert!(dummy("").is_none());
        // Case matters: the table is exact-match.
        assert!(dummy("Ldai").is_none());
    }

    #[test]
    fn construct_every_mnemonic_mainline() {
        for &mnemonic in MNEMONICS {
            let ops = canonical_ops(mnemonic);
            let bc = construct(mnemonic, &ops)
                .unwrap_or_else(|| panic!("construct({mnemonic}, canonical ops)"));
            assert_eq!(bc.mnemonic(), mnemonic, "constructed variant");
            assert_eq!(
                bc.operands(),
                canonical_operands(mnemonic),
                "constructed operands for {mnemonic}"
            );
        }
    }

    #[test]
    fn construct_rejects_wrong_operand_shapes() {
        for &mnemonic in MNEMONICS {
            let ops = canonical_ops(mnemonic);
            if ops.is_empty() {
                // `mnemonic` guards on `ops.is_empty()`: any operand must
                // fall through to the catch-all.
                assert!(
                    construct(mnemonic, &[I(0)]).is_none(),
                    "{mnemonic} with an operand"
                );
            } else {
                // Operand-count mismatch (one short) is always rejected.
                assert!(
                    construct(mnemonic, &ops[..ops.len() - 1]).is_none(),
                    "{mnemonic} short"
                );
                // Kind mismatch in the first position is always rejected
                // (no ISA operand list starts with a different-kind prefix
                // of itself).
                let mut wrong = ops.clone();
                wrong[0] = match wrong[0] {
                    R(_) => I(0),
                    I(_) | E(_) | L(_) => R(0),
                };
                assert!(
                    construct(mnemonic, &wrong).is_none(),
                    "{mnemonic} wrong first kind"
                );
            }
        }
    }

    #[test]
    fn construct_unknown_mnemonic_is_none() {
        assert!(construct("bogus", &[]).is_none());
        assert!(construct("bogus", &[R(1), I(1), E(1), L(0)]).is_none());
        assert!(construct("LDai", &[I(1)]).is_none());
    }

    /// The 88 corpus-absent construct arms (42 `deprecated.*`, 17 `wide.*`,
    /// 14 legacy jumps, plus the scattered rest) with their canonical
    /// operand vectors: construct must succeed and the instruction must
    /// survive an encode/decode round-trip unchanged.
    #[test]
    fn corpus_absent_arms_construct_and_roundtrip() {
        let cases: &[(&str, &[RawOperand])] = &[
            ("callruntime.notifyconcurrentresult", &[]),
            ("closeiterator", &[I(1), R(1)]),
            ("createregexpwithliteral", &[I(1), E(1), I(1)]),
            ("deprecated.asyncfunctionawaituncaught", &[R(1), R(1)]),
            ("deprecated.asyncfunctionreject", &[R(1), R(1), R(1)]),
            ("deprecated.asyncfunctionresolve", &[R(1), R(1), R(1)]),
            ("deprecated.asyncgeneratorreject", &[R(1), R(1)]),
            ("deprecated.callarg0", &[R(1)]),
            ("deprecated.callarg1", &[R(1), R(1)]),
            ("deprecated.callargs2", &[R(1), R(1), R(1)]),
            ("deprecated.callargs3", &[R(1), R(1), R(1), R(1)]),
            ("deprecated.callrange", &[I(1), R(1)]),
            ("deprecated.callspread", &[R(1), R(1), R(1)]),
            ("deprecated.callthisrange", &[I(1), R(1)]),
            ("deprecated.copydataproperties", &[R(1), R(1)]),
            ("deprecated.createarraywithbuffer", &[I(1)]),
            ("deprecated.createobjecthavingmethod", &[I(1)]),
            ("deprecated.createobjectwithbuffer", &[I(1)]),
            ("deprecated.dec", &[R(1)]),
            (
                "deprecated.defineclasswithbuffer",
                &[E(1), I(1), I(1), R(1), R(1)],
            ),
            ("deprecated.delobjprop", &[R(1), R(1)]),
            ("deprecated.dynamicimport", &[R(1)]),
            ("deprecated.getiteratornext", &[R(1), R(1)]),
            ("deprecated.getmodulenamespace", &[E(1)]),
            ("deprecated.getresumemode", &[R(1)]),
            ("deprecated.gettemplateobject", &[R(1)]),
            ("deprecated.inc", &[R(1)]),
            ("deprecated.ldmodulevar", &[E(1), I(1)]),
            ("deprecated.ldobjbyindex", &[R(1), I(1)]),
            ("deprecated.ldobjbyname", &[E(1), R(1)]),
            ("deprecated.ldobjbyvalue", &[R(1), R(1)]),
            ("deprecated.ldsuperbyname", &[E(1), R(1)]),
            ("deprecated.ldsuperbyvalue", &[R(1), R(1)]),
            ("deprecated.neg", &[R(1)]),
            ("deprecated.not", &[R(1)]),
            ("deprecated.resumegenerator", &[R(1)]),
            ("deprecated.setobjectwithproto", &[R(1), R(1)]),
            ("deprecated.stclasstoglobalrecord", &[E(1)]),
            ("deprecated.stconsttoglobalrecord", &[E(1)]),
            ("deprecated.stlettoglobalrecord", &[E(1)]),
            ("deprecated.stlexvar", &[I(1), I(1), R(1)]),
            ("deprecated.stmodulevar", &[E(1)]),
            ("deprecated.suspendgenerator", &[R(1), R(1)]),
            ("deprecated.tonumber", &[R(1)]),
            ("deprecated.tonumeric", &[R(1)]),
            ("jeq", &[R(1), L(0)]),
            ("jeqnull", &[L(0)]),
            ("jequndefined", &[L(0)]),
            ("jne", &[R(1), L(0)]),
            ("jnenull", &[L(0)]),
            ("jneundefined", &[L(0)]),
            ("jnstricteq", &[R(1), L(0)]),
            ("jnstricteqnull", &[L(0)]),
            ("jnstrictequndefined", &[L(0)]),
            ("jnstricteqz", &[L(0)]),
            ("jstricteq", &[R(1), L(0)]),
            ("jstricteqnull", &[L(0)]),
            ("jstrictequndefined", &[L(0)]),
            ("jstricteqz", &[L(0)]),
            ("ldobjbyindex", &[I(1), I(1)]),
            ("ldthisbyname", &[I(1), E(1)]),
            ("ldthisbyvalue", &[I(1)]),
            ("newobjapply", &[I(1), R(1)]),
            ("setobjectwithproto", &[I(1), R(1)]),
            ("stobjbyindex", &[I(1), R(1), I(1)]),
            ("stownbynamewithnameset", &[I(1), E(1), R(1)]),
            ("stownbyvalue", &[I(1), R(1), R(1)]),
            ("stthisbyname", &[I(1), E(1)]),
            ("stthisbyvalue", &[I(1), R(1)]),
            ("supercallarrowrange", &[I(1), I(1), R(1)]),
            ("throw.undefinedifhole", &[R(1), R(1)]),
            ("wide.callthisrange", &[I(1), R(1)]),
            ("wide.copyrestargs", &[I(1)]),
            ("wide.createobjectwithexcludedkeys", &[I(1), R(1), R(1)]),
            ("wide.getmodulenamespace", &[I(1)]),
            ("wide.ldexternalmodulevar", &[I(1)]),
            ("wide.ldlexvar", &[I(1), I(1)]),
            ("wide.ldobjbyindex", &[I(1)]),
            ("wide.ldpatchvar", &[I(1)]),
            ("wide.newlexenv", &[I(1)]),
            ("wide.newlexenvwithname", &[I(1), E(1)]),
            ("wide.newobjrange", &[I(1), R(1)]),
            ("wide.stlexvar", &[I(1), I(1)]),
            ("wide.stobjbyindex", &[R(1), I(1)]),
            ("wide.stownbyindex", &[R(1), I(1)]),
            ("wide.stpatchvar", &[I(1)]),
            ("wide.supercallarrowrange", &[I(1), R(1)]),
            ("wide.supercallthisrange", &[I(1), R(1)]),
        ];
        assert_eq!(cases.len(), 88, "the corpus-absent arm inventory");
        for &(mnemonic, ops) in cases {
            let bc = construct(mnemonic, ops)
                .unwrap_or_else(|| panic!("construct({mnemonic}) must succeed"));
            assert_eq!(bc.mnemonic(), mnemonic);
            let (bytes, _) =
                abcd_isa::encode(&[bc]).unwrap_or_else(|e| panic!("{mnemonic} must encode: {e}"));
            let decoded =
                abcd_isa::decode(&bytes).unwrap_or_else(|e| panic!("{mnemonic} must decode: {e}"));
            assert_eq!(decoded.len(), 1, "{mnemonic} decodes to one insn");
            assert_eq!(
                decoded[0].0.mnemonic(),
                mnemonic,
                "{mnemonic} mnemonic round-trip"
            );
            assert_eq!(
                decoded[0].0.operands(),
                bc.operands(),
                "{mnemonic} operands round-trip"
            );
        }
    }
}
