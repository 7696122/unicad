## 什么是 Unicad? ##

Unicad 自动编码识别器的缩写。他是基于一个 Mozilla 语言/编码识别扩展的 Emacs-Lisp 程序。

## Unicad 能做什么? ##

Unicad 可以帮助 Emacs 在打开文件的时候猜测语言编码，用正确的编码系统打开文件，避免乱码现象。

## Unicad 支持什么语言/编码系统? ##

  * 简体中文 (gb18030, gbk, gb2312, hz-gb-2312, iso-2022-cn)
  * 繁体中文 (big5, gb18030, gbk, euc-tw)
  * 日语 (sjis, euc-jp, iso-2022-jp)
  * 韩语 (euc-kr, iso-2022-kr)
  * 希腊语 (iso-8859-7, windows-1253)
  * 俄语 (iso-8859-5, windows-1251, koi8-r, ibm855)
  * 保加利亚语 (iso-8859-5, windows-1251)
  * 西欧语言，如德语、法语、西班牙语、意大利语、挪威语、瑞典语、葡萄牙语等等 (latin-1)
  * 中欧语言，如波兰语、罗马尼亚语、斯洛伐克语、斯洛文尼亚语、捷克语等等 (latin-2)
  * Unicode (utf-8, 包含或不包含BOM的ucs2编码utf-16le, utf-16be)

## 谁应该使用 Unicad? ##

  1. **Emacs 用户**. Unicad 是一个 Emacs 扩展，所以首先是给 Emacs 用户使用的。
  1. **多语言用户**. 如果你只需要编辑英语文件，只需要使用ASCII编码，那么你不需要在 Emacs 上使用 Unicad。反之，如果你使用多种语言，多种编码，那么 Unicad 肯定可以帮你识别文件编码。
  1. 如果你经常碰到**乱码**文件，因为一般的编辑器没有那么聪明来选择正确的编码系统，你应该尝试一下世界上最强大的编辑器 Emacs 和最聪明的编码识别器 Unicad。

## 怎样使用 Unicad? ##

[下载](http://code.google.com/p/unicad/downloads/list)最新版的 unicad.el, 复制到你的 Emacs load path (例如 site-lisp 目录), 在你的 ~/.emacs 文件里加上:
```
(require 'unicad)
```

推荐 byte-compile 这个文件来加速检测编码和打开文件的速度。

## Unicad 和 Mozilla 语言/编码识别扩展有什么不同？ ##

虽然 Unicad 是基于 Mozilla 语言/编码识别扩展的，但还是有一些不同之处：

  * 优化了检测短文件的能力。
  * 增加了对中欧语言、编码的支持。
  * 增加了对采用gbk编码的繁体中文文件的支持。
  * 增加了对采用sjis编码的只含有半角平假名的支持。
  * 具有检测不含BOM的utf-16le和utf-16be的能力。



