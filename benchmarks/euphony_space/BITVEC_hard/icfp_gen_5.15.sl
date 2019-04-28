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
(constraint (= (f #xAF9258C821A4F481) #x506DA737DE5B0B7E))
(constraint (= (f #x88E9D930C897CFC9) #x771626CF37683036))
(constraint (= (f #xB3AD9E0C65BB8DDF) #x4C5261F39A447220))
(constraint (= (f #xA159C6EC3A7913BF) #x5EA63913C586EC40))
(constraint (= (f #x7A46E94938FACF59) #x85B916B6C70530A6))
(constraint (= (f #x9432472888EFB3F0) #x0000000000000000))
(constraint (= (f #x90E0BEDDD5DF90DE) #x0000000000000000))
(constraint (= (f #xB445E035E8D3E2A4) #x0000000000000000))
(constraint (= (f #x120C8F64505D9DB4) #x0000000000000000))
(constraint (= (f #x4720413405E36880) #x0000000000000000))
(constraint (= (f #xC2967C638FABC873) #x3D69839C7054378C))
(constraint (= (f #xB9F5FB06A81D7FDD) #x460A04F957E28022))
(constraint (= (f #x387C61EA8A33710B) #xC7839E1575CC8EF4))
(constraint (= (f #x0B724A5F7C8C52B9) #xF48DB5A08373AD46))
(constraint (= (f #xFC809B6AA52F9971) #x037F64955AD0668E))
(constraint (= (f #xA06AA1336D16F12E) #xA06AA1336D16F12E))
(constraint (= (f #xFC932172940A59CE) #xFC932172940A59CE))
(constraint (= (f #x9A159C57C93ABB6A) #x9A159C57C93ABB6A))
(constraint (= (f #x116372DF540F6F8C) #x116372DF540F6F8C))
(constraint (= (f #xF02C0B8A46260550) #xF02C0B8A46260550))
(constraint (= (f #x7FFFFFFFFFF32539) #xFFFFFFFFFFFFFFFF))
(constraint (= (f #xFFFFFFFFFFF2EB31) #xFFFFFFFFFFFFFFFF))
(constraint (= (f #x7FFFFFFFFFF22175) #xFFFFFFFFFFFFFFFF))
(constraint (= (f #xFFFFFFFFFFF25EED) #xFFFFFFFFFFFFFFFF))
(constraint (= (f #x7FFFFFFFFFF7B39D) #xFFFFFFFFFFFFFFFF))
(constraint (= (f #x7FFFFFFFFFF4452A) #x7FFFFFFFFFF4452A))
(constraint (= (f #xFFFFFFFFFFF19D68) #xFFFFFFFFFFF19D68))
(constraint (= (f #x7FFFFFFFFFF08B9E) #x7FFFFFFFFFF08B9E))
(constraint (= (f #xFFFFFFFFFFF0D018) #xFFFFFFFFFFF0D018))
(constraint (= (f #xFFFFFFFFFFF3871C) #xFFFFFFFFFFF3871C))
(check-synth)