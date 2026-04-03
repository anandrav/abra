package com.abra.intellij

import com.intellij.openapi.fileTypes.LanguageFileType
import javax.swing.Icon

object AbraFileType : LanguageFileType(AbraLanguage) {
    override fun getName(): String = "Abra"
    override fun getDescription(): String = "Abra language file"
    override fun getDefaultExtension(): String = "abra"
    override fun getIcon(): Icon = AbraIcons.FILE
}
