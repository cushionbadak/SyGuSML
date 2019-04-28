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
(constraint (= (f #xC51C227332BF4CE4) #xD855CC5333E10CA9))
(constraint (= (f #x7D240830B78D4500) #x4449F3B6ECAC187F))
(constraint (= (f #xC188262B752FD768) #xDDB3C6BED0383CE3))
(constraint (= (f #xCB23FC078425B5BC) #xCF4A05F4B9C76F65))
(constraint (= (f #xD369119C666666BC) #xC2E26595666665E5))
(constraint (= (f #xE78B8329BF753EFE) #x18747CD6408AC101))
(constraint (= (f #x8A31EFF1F12B49FE) #x75CE100E0ED4B601))
(constraint (= (f #xE8A4426AA38822AE) #x175BBD955C77DD51))
(constraint (= (f #x13486AAA1B426DD2) #xECB79555E4BD922D))
(constraint (= (f #x215F250764AAFE86) #xDEA0DAF89B550179))
(constraint (= (f #xF0F0F0F0F0F0F0F2) #x0F0F0F0F0F0F0F0D))
(constraint (= (f #xD995724C7D588DC9) #x2262889300227222))
(constraint (= (f #x137008B9237643ED) #xEC88F7444C889800))
(constraint (= (f #x82552B65C35798E5) #x758A840820880610))
(constraint (= (f #x53A31A2B7C6D7DC1) #xA844C45400100022))
(constraint (= (f #xD32E347FA2C63545) #x20C10880051188AA))
(constraint (= (f #x93127A0F1E19987F) #x64CC805000066600))
(constraint (= (f #xAF9054A1B9655897) #x5006AA144408A260))
(constraint (= (f #x08830EA9B8689757) #xF774C11444116088))
(constraint (= (f #x3124448C57D6455D) #xCCC9BB3328009AA2))
(constraint (= (f #x11FBD8F0BEDFCFD7) #xEE00020040000000))
(constraint (= (f #x0000000000000001) #xFFFFFFFFFFFFFFFE))
(constraint (= (f #x79C3862E4795A9A0) #x495AB6BA949F818F))
(constraint (= (f #xEF4C5D0FEC9F3855) #x100322200120042A))
(constraint (= (f #xB0314CF2F3CD582A) #x4FCEB30D0C32A7D5))
(constraint (= (f #xB2D9CE8B7C2CD261) #x4402211400112098))
(constraint (= (f #x4E75C196362EAB4F) #xB108226088911400))
(constraint (= (f #x9C5565D6C901F23E) #x63AA9A2936FE0DC1))
(constraint (= (f #x63153834A5148A80) #x6B602BB10861303F))
(constraint (= (f #xF0DE2201095E254E) #x0F21DDFEF6A1DAB1))
(constraint (= (f #x610F784FE8D8788E) #x9EF087B017278771))
(constraint (= (f #xBAF40A83F2365A6A) #x450BF57C0DC9A595))
(constraint (= (f #x0000000000000001) #xFFFFFFFFFFFFFFFE))
(constraint (= (f #xF0F0F0F0F0F0F0F2) #x0F0F0F0F0F0F0F0D))
(check-synth)