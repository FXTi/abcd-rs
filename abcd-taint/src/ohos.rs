//! Curated OpenHarmony (`@ohos.*` / `@kit.*`) taint rule pack (`design/analysis.md`).
//!
//! Provides a versioned, zero-dependency preset ([`ohos_preset`] /
//! [`apply_ohos_preset`]) covering OpenHarmony Stage/FA lifecycle `Want`
//! inputs, privacy-sensitive SDK sources, network/WebView/file/IPC/RDB/logging
//! sinks, and ArkUI declarative render/event callback propagation.
//!
//! Canonical `@ohos.*` names are paired with [`crate::names`]'s `@kit.*` and
//! two-step factory/constructor normalization so one rule set matches both
//! `@ohos.*` and HarmonyOS NEXT `@kit.*` imports across synchronous calls,
//! `Promise.then(...)`, `async`/`await`, and `(err, data)` callbacks.

use crate::driver::{SinkSpec, SourceSpec, TaintConfig};
use crate::summary::{Endpoint, Summary};
use abcd_analysis::ohos_lifecycle::OHOS_WANT_GLOBAL;

/// Semantic version of the built-in OpenHarmony taint rule pack.
pub const OHOS_PRESET_VERSION: &str = "1.0.0";

/// Build a [`TaintConfig`] preloaded with the OpenHarmony source, sink, and
/// framework summary rule pack.
pub fn ohos_preset() -> TaintConfig {
    let mut cfg = TaintConfig::default();
    apply_ohos_preset(&mut cfg);
    cfg
}

/// Merge the OpenHarmony rule pack into an existing [`TaintConfig`]
/// (idempotent with respect to duplicate source/sink entries).
pub fn apply_ohos_preset(config: &mut TaintConfig) {
    config.ohos_lifecycle = true;
    for src in ohos_sources() {
        if !config.sources.contains(&src) {
            config.sources.push(src);
        }
    }
    for snk in ohos_sinks() {
        if !config.sinks.contains(&snk) {
            config.sinks.push(snk);
        }
    }
    for (name, arity, summary) in ohos_summaries() {
        if !config
            .extra_summaries
            .iter()
            .any(|(n, a, _)| n == name && *a == arity)
        {
            config
                .extra_summaries
                .push((name.to_owned(), arity, summary));
        }
    }
}

/// OpenHarmony privacy and untrusted-input taint sources.
pub fn ohos_sources() -> Vec<SourceSpec> {
    let call_sources = [
        // Location (`@ohos.geoLocationManager` / `@kit.LocationKit`)
        "@ohos.geoLocationManager.getCurrentLocation",
        "@ohos.geoLocationManager.getLastLocation",
        "@ohos.geoLocationManager.getAddressesFromLocation",
        "@ohos.geoLocationManager.getAddressesFromLocationName",
        // Pasteboard (`@ohos.pasteboard` / `@kit.BasicServicesKit`)
        "@ohos.pasteboard.SystemPasteboard.getData",
        "@ohos.pasteboard.SystemPasteboard.getDataSync",
        "@ohos.pasteboard.SystemPasteboard.getUnifiedData",
        "@ohos.pasteboard.SystemPasteboard.getUnifiedDataSync",
        "@ohos.pasteboard.PasteData.getPrimaryText",
        "@ohos.pasteboard.PasteData.getPrimaryHtml",
        "@ohos.pasteboard.PasteData.getPrimaryUri",
        // Device / OAID / Telephony (`@ohos.identifier.oaid`, `@ohos.telephony.*`)
        "@ohos.identifier.oaid.getOAID",
        "@ohos.telephony.sim.getSimAccountInfo",
        "@ohos.telephony.sim.getSimTelephoneNumber",
        "@ohos.telephony.sim.getISOCountryCodeForSim",
        "@ohos.telephony.sim.getSimSpn",
        "@ohos.telephony.radio.getIMEI",
        "@ohos.telephony.radio.getIMEISV",
        "@ohos.telephony.radio.getMEID",
        "@ohos.telephony.radio.getUniqueDeviceId",
        "@ohos.telephony.radio.getNetworkState",
        "@ohos.telephony.radio.getSignalInformation",
        "@ohos.telephony.call.getCallState",
        "@ohos.telephony.sms.createMessage",
        // Contacts (`@ohos.contact` / `@kit.ContactsKit`)
        "@ohos.contact.selectContacts",
        "@ohos.contact.selectContact",
        "@ohos.contact.queryContacts",
        "@ohos.contact.queryContact",
        "@ohos.contact.queryContactsByEmail",
        "@ohos.contact.queryContactsByPhoneNumber",
        "@ohos.contact.queryMyCard",
        // Persistent storage reads (`@ohos.data.preferences`, `@ohos.data.relationalStore`)
        "@ohos.data.preferences.Preferences.get",
        "@ohos.data.preferences.Preferences.getSync",
        "@ohos.data.preferences.Preferences.getAll",
        "@ohos.data.preferences.Preferences.getAllSync",
        "@ohos.data.relationalStore.RdbStore.query",
        "@ohos.data.relationalStore.RdbStore.querySql",
        "@ohos.data.relationalStore.RdbStore.querySqlSync",
        // Router parameters (`@ohos.router`)
        "@ohos.router.getParams",
    ];

    let mut out = Vec::with_capacity(call_sources.len() + 3);
    // Stage / FA Ability & ExtensionAbility `Want` (`want`, `want.uri`, `want.parameters.*`).
    out.push(SourceSpec::GlobalLoad {
        name: OHOS_WANT_GLOBAL.to_owned(),
    });
    // `@ohos.deviceInfo` / `@kit.BasicServicesKit` (`deviceInfo.ODID`, `deviceInfo.serial`, ...).
    out.push(SourceSpec::ModuleImport {
        specifier: "@ohos.deviceInfo".to_owned(),
        import_name: None,
    });
    out.push(SourceSpec::ModuleImport {
        specifier: "@kit.BasicServicesKit".to_owned(),
        import_name: Some("deviceInfo".to_owned()),
    });
    for name in call_sources {
        out.push(SourceSpec::CallReturn {
            name: name.to_owned(),
        });
    }
    out
}

/// OpenHarmony exfiltration, injection, IPC, storage, and logging sinks.
pub fn ohos_sinks() -> Vec<SinkSpec> {
    let call_sinks = [
        // Network exfiltration (`@ohos.net.http`, `@ohos.net.socket`)
        "@ohos.net.http.HttpRequest.request",
        "@ohos.net.http.HttpRequest.requestInStream",
        "@ohos.net.socket.TCPSocket.send",
        "@ohos.net.socket.UDPSocket.send",
        "@ohos.net.socket.TLSSocket.send",
        // WebView navigation & JS execution (`@ohos.web.webview`)
        "@ohos.web.webview.WebviewController.loadUrl",
        "@ohos.web.webview.WebviewController.loadData",
        "@ohos.web.webview.WebviewController.runJavaScript",
        "@ohos.web.webview.WebviewController.runJavaScriptExt",
        // File write (`@ohos.file.fs`)
        "@ohos.file.fs.write",
        "@ohos.file.fs.writeSync",
        // IPC / Ability launch (`UIAbilityContext`, `@ohos.commonEventManager`)
        "UIAbilityContext.startAbility",
        "UIAbilityContext.startAbilityForResult",
        "UIAbilityContext.connectServiceExtensionAbility",
        "@ohos.commonEventManager.publish",
        // RelationalStore SQL execution (`@ohos.data.relationalStore`)
        "@ohos.data.relationalStore.RdbStore.executeSql",
        "@ohos.data.relationalStore.RdbStore.execute",
        "@ohos.data.relationalStore.RdbStore.querySql",
        "@ohos.data.relationalStore.RdbStore.querySqlSync",
        "@ohos.data.relationalStore.RdbStore.insert",
        "@ohos.data.relationalStore.RdbStore.batchInsert",
        // Logging (`@ohos.hilog`)
        "@ohos.hilog.debug",
        "@ohos.hilog.info",
        "@ohos.hilog.warn",
        "@ohos.hilog.error",
        "@ohos.hilog.fatal",
    ];
    call_sinks
        .into_iter()
        .map(|name| SinkSpec::Call {
            name: name.to_owned(),
        })
        .collect()
}

/// Framework propagation and callback-spawning summaries for OpenHarmony & ArkUI.
pub fn ohos_summaries() -> Vec<(&'static str, Option<usize>, Summary)> {
    use Endpoint::*;
    let mut out = vec![
        // ArkUI `ViewPU` declarative render / branch / loop closures.
        (
            "ViewPU.observeComponentCreation2",
            None,
            Summary::new("ArkUI ViewPU render closure").spawn_callback(0),
        ),
        (
            "ViewPU.observeComponentCreation",
            None,
            Summary::new("ArkUI ViewPU legacy render closure").spawn_callback(0),
        ),
        (
            "ViewPU.observeRecycleComponentCreation",
            None,
            Summary::new("ArkUI recycle component closure").spawn_callback(1),
        ),
        (
            "ViewPU.ifElseBranchUpdateFunction",
            None,
            Summary::new("ArkUI If branch closure").spawn_callback(1),
        ),
        (
            "ViewPU.forEachUpdateFunction",
            None,
            Summary::new("ArkUI ForEach item generator closure").spawn_callback(2),
        ),
        // Pasteboard helpers.
        (
            "@ohos.pasteboard.createData",
            None,
            Summary::new("ohos pasteboard createData; payload -> PasteData").flow(Param(1), Return),
        ),
        (
            "@ohos.pasteboard.PasteData.getPrimaryText",
            Some(0),
            Summary::new("ohos PasteData.getPrimaryText; base -> string").flow(Base, Return),
        ),
        (
            "@ohos.pasteboard.PasteData.getPrimaryHtml",
            Some(0),
            Summary::new("ohos PasteData.getPrimaryHtml; base -> string").flow(Base, Return),
        ),
        (
            "@ohos.pasteboard.PasteData.getPrimaryUri",
            Some(0),
            Summary::new("ohos PasteData.getPrimaryUri; base -> string").flow(Base, Return),
        ),
        // URI encoding helpers frequently wrapping exfiltrated query strings.
        (
            "encodeURIComponent",
            Some(1),
            Summary::new("URI component encoding preserves taint").flow(Param(0), Return),
        ),
        (
            "decodeURIComponent",
            Some(1),
            Summary::new("URI component decoding preserves taint").flow(Param(0), Return),
        ),
        (
            "encodeURI",
            Some(1),
            Summary::new("URI encoding preserves taint").flow(Param(0), Return),
        ),
        (
            "decodeURI",
            Some(1),
            Summary::new("URI decoding preserves taint").flow(Param(0), Return),
        ),
        // HiLog sinks return void and do not taint their return slot.
        (
            "@ohos.hilog.debug",
            None,
            Summary::new("ohos hilog.debug; void sink"),
        ),
        (
            "@ohos.hilog.info",
            None,
            Summary::new("ohos hilog.info; void sink"),
        ),
        (
            "@ohos.hilog.warn",
            None,
            Summary::new("ohos hilog.warn; void sink"),
        ),
        (
            "@ohos.hilog.error",
            None,
            Summary::new("ohos hilog.error; void sink"),
        ),
        (
            "@ohos.hilog.fatal",
            None,
            Summary::new("ohos hilog.fatal; void sink"),
        ),
    ];

    const UI_COMPONENTS_CLICK: &[&str] = &[
        "Button.onClick",
        "Text.onClick",
        "Row.onClick",
        "Column.onClick",
        "Image.onClick",
        "ListItem.onClick",
        "__Common__.onClick",
        "Button.onTouch",
        "Row.onTouch",
        "Column.onTouch",
        "__Common__.onTouch",
        "Row.onAppear",
        "Column.onAppear",
        "__Common__.onAppear",
        "TextInput.onChange",
        "TextInput.onSubmit",
        "TextArea.onChange",
        "Search.onChange",
        "Search.onSubmit",
        "Toggle.onChange",
        "Slider.onChange",
        "Web.onPageBegin",
        "Web.onPageEnd",
    ];
    for &ui_ev in UI_COMPONENTS_CLICK {
        out.push((
            ui_ev,
            None,
            Summary::new("ArkUI component event callback").spawn_callback(0),
        ));
    }

    out
}
