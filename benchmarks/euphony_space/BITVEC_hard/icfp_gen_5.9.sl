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
(constraint (= (f #x616E012A65CE8FA2) #x616E012A65CE8FA3))
(constraint (= (f #xCEDDDA51BB3B8932) #xCEDDDA51BB3B8933))
(constraint (= (f #x4275343E7755DBB0) #x4275343E7755DBB1))
(constraint (= (f #xC5006F2DB1822E5D) #xC5006F2DB1822E5D))
(constraint (= (f #x4BFFFA81CDD1D768) #x4BFFFA81CDD1D769))
(constraint (= (f #x083FFA02D82A30C8) #xF7C005FD27D5CF37))
(constraint (= (f #x4B6D44B940B32705) #xB492BB46BF4CD8FA))
(constraint (= (f #x5D62A75A98087B5D) #xA29D58A567F784A2))
(constraint (= (f #xB72FC974123C82E1) #x48D0368BEDC37D1E))
(constraint (= (f #xC522B2F3B673C255) #x3ADD4D0C498C3DAA))
(constraint (= (f #x7FFFFFFFFFFFFFFE) #x8000000000000001))
(constraint (= (f #x830D02C20D0050D3) #x830D02C20D0050D3))
(constraint (= (f #xB4A49487092C1415) #xB4A49487092C1415))
(constraint (= (f #x48296818070F0853) #x48296818070F0853))
(constraint (= (f #x78401E02870C2493) #x78401E02870C2493))
(constraint (= (f #x5A1C21690F0F0E17) #x5A1C21690F0F0E17))
(constraint (= (f #x0000000000000001) #xFFFFFFFFFFFFFFFE))
(constraint (= (f #x000000000000000D) #xFFFFFFFFFFFFFFF2))
(constraint (= (f #x000000000000000A) #xFFFFFFFFFFFFFFF5))
(constraint (= (f #x0000000000000002) #xFFFFFFFFFFFFFFFD))
(constraint (= (f #x501C2520D0382091) #x0FAB909D8F579E4C))
(constraint (= (f #x2C0108414A125853) #x7BFCE73C21C8F706))
(constraint (= (f #x1485A52484284871) #xC26F1092738726AC))
(constraint (= (f #xF04184B086050E17) #x2F3B71EE6DF0D5BA))
(constraint (= (f #x421C1A414834B435) #x39ABB13C2761E360))
(check-synth)
