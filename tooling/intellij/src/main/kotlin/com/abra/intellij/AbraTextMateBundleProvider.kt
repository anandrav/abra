package com.abra.intellij

import com.intellij.ide.plugins.PluginManagerCore
import com.intellij.openapi.extensions.PluginId
import org.jetbrains.plugins.textmate.api.TextMateBundleProvider
import org.jetbrains.plugins.textmate.api.TextMateBundleProvider.PluginBundle

class AbraTextMateBundleProvider : TextMateBundleProvider {
    override fun getBundles(): List<PluginBundle> {
        val descriptor = PluginManagerCore.getPlugin(PluginId.getId("com.abra.intellij"))
            ?: return emptyList()
        val bundlePath = descriptor.pluginPath.resolve("textmate/abra.tmbundle")
        return listOf(PluginBundle("Abra", bundlePath))
    }
}
