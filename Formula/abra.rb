class Abra < Formula
  desc "Abra programming language"
  homepage "https://github.com/anandrav/abra"
  license "MPL-2.0"
  head "https://github.com/anandrav/abra.git", branch: "main"

  depends_on "rust" => :build

  def install
    system "cargo", "build", "--release"
    bin.install "target/release/abra", "target/release/abra-lsp"
    share_abra = share/"abra"
    share_abra.install "Cargo.toml", "modules"
    (share_abra/"target/release").install Dir["target/release/lib*.dylib", "target/release/lib*.so"]
  end

  test do
    (testpath/"hello.abra").write 'println("hi")'
    assert_match "hi", shell_output("#{bin}/abra #{testpath}/hello.abra")
  end
end
