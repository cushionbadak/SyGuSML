(set-logic BV)
(synth-fun f ((x (_ BitVec 64))) (_ BitVec 64)
  ((Start (_ BitVec 64)) (StartBool Bool))
  ((Start (_ BitVec 64)
            (
              (bvnot Start)
              (bvxor Start Start)
              (bvand Start Start)
              (bvor Start Start)
              (bvneg Start)
              (bvadd Start Start)
              (bvmul Start Start)
              (bvudiv Start Start)
              (bvurem Start Start)
              (bvlshr Start Start)
              (bvashr Start Start)
              (bvshl Start Start)
              (bvsdiv Start Start)
              (bvsrem Start Start)
              (bvsub Start Start)
              x
              #x0000000000000000
              #x0000000000000001
              #x0000000000000002
              #x0000000000000003
              #x0000000000000004
              #x0000000000000005
              #x0000000000000006
              #x0000000000000007
              #x0000000000000008
              #x0000000000000009
              #x0000000000000009
              #x0000000000000009
              #x000000000000000A
              #x000000000000000B
              #x000000000000000C
              #x000000000000000D
              #x000000000000000E
              #x000000000000000F
              #x0000000000000010
              #x0000000000000011
              #x0000000000000012
              #x0000000000000013
              #x0000000000000014
              #x0000000000000015
              #x0000000000000016
              #x0000000000000017
              #x0000000000000018
              #x0000000000000019
              #x000000000000001A
              #x000000000000001B
              #x000000000000001C
              #x000000000000001D
              #x000000000000001E
              #x000000000000001F
              (ite StartBool Start Start)
            ))
  (StartBool Bool
            (
              (= Start Start)
              (not StartBool)
              (and StartBool StartBool)
              (or StartBool StartBool)
              (xor StartBool StartBool)
            ))
            ))
(constraint (= (f #xD506A5A29E73BF23) #xAA0D4B453CE77E47))
(constraint (= (f #xB2EEDDF9ACAF21E3) #x65DDBBF3595E43C7))
(constraint (= (f #x06E175099F7CFFFF) #x0DC2EA133EF9FFFF))
(constraint (= (f #x3DFBBC0B8F33C917) #x7BF778171E67922F))
(constraint (= (f #x74B17A6D64F99901) #xE962F4DAC9F33203))
(constraint (= (f #x800000000000FFFF) #x0800000000000FFF))
(constraint (= (f #x000000000000FFFF) #x0000000000000FFF))
(constraint (= (f #xA69C1C3731EC4B7A) #x0A69C1C3731EC4B7))
(constraint (= (f #xEABB89CC855E15AD) #x0EABB89CC855E15A))
(constraint (= (f #xC654FFD8BF1AD443) #x0C654FFD8BF1AD44))
(constraint (= (f #x7AF85A6943A2DE5B) #x07AF85A6943A2DE5))
(constraint (= (f #x108569420CA66816) #x0108569420CA6681))
(constraint (= (f #x0000000000008CED) #x00000000000008CE))
(constraint (= (f #x000000000000D16F) #x0000000000000D16))
(constraint (= (f #x000000000000ECBA) #x0000000000000ECB))
(constraint (= (f #x800000000000E27A) #x0800000000000E27))
(constraint (= (f #x8000000000009EA6) #x08000000000009EA))
(check-synth)
