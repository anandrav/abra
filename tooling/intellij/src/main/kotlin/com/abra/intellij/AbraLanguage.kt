package com.abra.intellij

import com.intellij.lang.Language

object AbraLanguage : Language("Abra") {
    private fun readResolve(): Any = AbraLanguage
    override fun getDisplayName(): String = "Abra"
}
