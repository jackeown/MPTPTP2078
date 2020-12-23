%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:20 EST 2020

% Result     : Theorem 34.64s
% Output     : Refutation 34.64s
% Verified   : 
% Statistics : Number of formulae       :  335 ( 829 expanded)
%              Number of leaves         :   76 ( 422 expanded)
%              Depth                    :    8
%              Number of atoms          :  922 (1898 expanded)
%              Number of equality atoms :  269 ( 763 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f67823,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f46,f50,f54,f58,f90,f97,f114,f127,f133,f141,f160,f164,f218,f222,f226,f230,f234,f514,f518,f522,f527,f535,f543,f555,f1427,f1431,f1498,f1502,f1919,f1923,f2169,f2322,f2326,f2498,f2502,f2511,f2926,f2987,f2991,f3055,f3619,f3780,f3820,f3844,f5942,f6091,f6722,f6730,f6742,f6770,f6774,f6838,f16709,f17356,f17360,f17372,f26830,f27273,f31522,f34115,f46987,f62433,f64735,f67768])).

fof(f67768,plain,
    ( ~ spl2_2
    | ~ spl2_3
    | ~ spl2_17
    | ~ spl2_21
    | ~ spl2_28
    | ~ spl2_34
    | spl2_47
    | ~ spl2_162
    | ~ spl2_222 ),
    inference(avatar_contradiction_clause,[],[f67767])).

fof(f67767,plain,
    ( $false
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_17
    | ~ spl2_21
    | ~ spl2_28
    | ~ spl2_34
    | spl2_47
    | ~ spl2_162
    | ~ spl2_222 ),
    inference(subsumption_resolution,[],[f2510,f67766])).

fof(f67766,plain,
    ( ! [X180,X179] : k5_xboole_0(X179,X180) = k4_xboole_0(k5_xboole_0(X179,k4_xboole_0(X180,X179)),k5_xboole_0(X179,k4_xboole_0(X179,X180)))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_17
    | ~ spl2_21
    | ~ spl2_28
    | ~ spl2_34
    | ~ spl2_162
    | ~ spl2_222 ),
    inference(forward_demodulation,[],[f67356,f67572])).

fof(f67572,plain,
    ( ! [X52,X53] : k5_xboole_0(X52,k4_xboole_0(X52,X53)) = k4_xboole_0(X52,k5_xboole_0(X52,X53))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_17
    | ~ spl2_21
    | ~ spl2_28
    | ~ spl2_34
    | ~ spl2_222 ),
    inference(forward_demodulation,[],[f67571,f1314])).

fof(f1314,plain,
    ( ! [X10,X11,X9] : k5_xboole_0(X11,k4_xboole_0(X9,X10)) = k5_xboole_0(X9,k5_xboole_0(X11,k5_xboole_0(X10,k4_xboole_0(X10,X9))))
    | ~ spl2_3
    | ~ spl2_17
    | ~ spl2_21
    | ~ spl2_28 ),
    inference(backward_demodulation,[],[f563,f1251])).

fof(f1251,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k5_xboole_0(X0,k4_xboole_0(X0,X1))
    | ~ spl2_3
    | ~ spl2_28 ),
    inference(superposition,[],[f542,f49])).

fof(f49,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl2_3
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f542,plain,
    ( ! [X4,X5] : k4_xboole_0(X4,X5) = k5_xboole_0(X4,k5_xboole_0(X4,k4_xboole_0(X4,X5)))
    | ~ spl2_28 ),
    inference(avatar_component_clause,[],[f541])).

fof(f541,plain,
    ( spl2_28
  <=> ! [X5,X4] : k4_xboole_0(X4,X5) = k5_xboole_0(X4,k5_xboole_0(X4,k4_xboole_0(X4,X5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).

fof(f563,plain,
    ( ! [X10,X11,X9] : k5_xboole_0(X9,k5_xboole_0(X11,k4_xboole_0(X10,k4_xboole_0(X10,X9)))) = k5_xboole_0(X11,k4_xboole_0(X9,X10))
    | ~ spl2_17
    | ~ spl2_21 ),
    inference(superposition,[],[f513,f225])).

fof(f225,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f224])).

fof(f224,plain,
    ( spl2_17
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f513,plain,
    ( ! [X4,X5,X3] : k5_xboole_0(X3,k5_xboole_0(X4,X5)) = k5_xboole_0(X4,k5_xboole_0(X3,X5))
    | ~ spl2_21 ),
    inference(avatar_component_clause,[],[f512])).

fof(f512,plain,
    ( spl2_21
  <=> ! [X3,X5,X4] : k5_xboole_0(X3,k5_xboole_0(X4,X5)) = k5_xboole_0(X4,k5_xboole_0(X3,X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f67571,plain,
    ( ! [X52,X53] : k4_xboole_0(X52,k5_xboole_0(X52,X53)) = k5_xboole_0(X52,k5_xboole_0(X52,k5_xboole_0(X53,k4_xboole_0(X53,X52))))
    | ~ spl2_2
    | ~ spl2_34
    | ~ spl2_222 ),
    inference(forward_demodulation,[],[f67305,f45])).

fof(f45,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl2_2
  <=> ! [X1,X0,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f67305,plain,
    ( ! [X52,X53] : k4_xboole_0(X52,k5_xboole_0(X52,X53)) = k5_xboole_0(X52,k5_xboole_0(k5_xboole_0(X52,X53),k4_xboole_0(X53,X52)))
    | ~ spl2_34
    | ~ spl2_222 ),
    inference(superposition,[],[f1426,f64734])).

fof(f64734,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k5_xboole_0(X1,X0),X1)
    | ~ spl2_222 ),
    inference(avatar_component_clause,[],[f64733])).

fof(f64733,plain,
    ( spl2_222
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(k5_xboole_0(X1,X0),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_222])])).

fof(f1426,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,X0)))
    | ~ spl2_34 ),
    inference(avatar_component_clause,[],[f1425])).

fof(f1425,plain,
    ( spl2_34
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).

fof(f67356,plain,
    ( ! [X180,X179] : k5_xboole_0(X179,X180) = k4_xboole_0(k5_xboole_0(X179,k4_xboole_0(X180,X179)),k4_xboole_0(X179,k5_xboole_0(X179,X180)))
    | ~ spl2_162
    | ~ spl2_222 ),
    inference(superposition,[],[f34114,f64734])).

fof(f34114,plain,
    ( ! [X6,X5] : k4_xboole_0(k5_xboole_0(X5,k4_xboole_0(X6,X5)),k4_xboole_0(X5,X6)) = X6
    | ~ spl2_162 ),
    inference(avatar_component_clause,[],[f34113])).

fof(f34113,plain,
    ( spl2_162
  <=> ! [X5,X6] : k4_xboole_0(k5_xboole_0(X5,k4_xboole_0(X6,X5)),k4_xboole_0(X5,X6)) = X6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_162])])).

fof(f2510,plain,
    ( k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl2_47 ),
    inference(avatar_component_clause,[],[f2508])).

fof(f2508,plain,
    ( spl2_47
  <=> k5_xboole_0(sK0,sK1) = k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_47])])).

fof(f64735,plain,
    ( spl2_222
    | ~ spl2_135
    | ~ spl2_220 ),
    inference(avatar_split_clause,[],[f63901,f62431,f16707,f64733])).

fof(f16707,plain,
    ( spl2_135
  <=> ! [X38,X39] : k5_xboole_0(X39,X38) = k5_xboole_0(k4_xboole_0(X38,X39),k4_xboole_0(X39,X38)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_135])])).

fof(f62431,plain,
    ( spl2_220
  <=> ! [X29,X28,X30] : k4_xboole_0(X30,X28) = k4_xboole_0(k5_xboole_0(k4_xboole_0(X30,X28),k4_xboole_0(X28,X29)),X28) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_220])])).

fof(f63901,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k5_xboole_0(X1,X0),X1)
    | ~ spl2_135
    | ~ spl2_220 ),
    inference(superposition,[],[f62432,f16708])).

fof(f16708,plain,
    ( ! [X39,X38] : k5_xboole_0(X39,X38) = k5_xboole_0(k4_xboole_0(X38,X39),k4_xboole_0(X39,X38))
    | ~ spl2_135 ),
    inference(avatar_component_clause,[],[f16707])).

fof(f62432,plain,
    ( ! [X30,X28,X29] : k4_xboole_0(X30,X28) = k4_xboole_0(k5_xboole_0(k4_xboole_0(X30,X28),k4_xboole_0(X28,X29)),X28)
    | ~ spl2_220 ),
    inference(avatar_component_clause,[],[f62431])).

fof(f62433,plain,
    ( spl2_220
    | ~ spl2_11
    | ~ spl2_141
    | ~ spl2_185 ),
    inference(avatar_split_clause,[],[f47772,f46985,f17370,f139,f62431])).

fof(f139,plain,
    ( spl2_11
  <=> ! [X5,X4] : k4_xboole_0(X5,X4) = k4_xboole_0(k4_xboole_0(X5,X4),X4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f17370,plain,
    ( spl2_141
  <=> ! [X29,X28,X30] : k4_xboole_0(X29,X30) = k4_xboole_0(k4_xboole_0(X29,X30),k4_xboole_0(X28,X29)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_141])])).

fof(f46985,plain,
    ( spl2_185
  <=> ! [X49,X51,X50] : k4_xboole_0(k5_xboole_0(X51,k4_xboole_0(k4_xboole_0(X49,X50),X51)),X49) = k4_xboole_0(X51,X49) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_185])])).

fof(f47772,plain,
    ( ! [X30,X28,X29] : k4_xboole_0(X30,X28) = k4_xboole_0(k5_xboole_0(k4_xboole_0(X30,X28),k4_xboole_0(X28,X29)),X28)
    | ~ spl2_11
    | ~ spl2_141
    | ~ spl2_185 ),
    inference(forward_demodulation,[],[f47552,f140])).

fof(f140,plain,
    ( ! [X4,X5] : k4_xboole_0(X5,X4) = k4_xboole_0(k4_xboole_0(X5,X4),X4)
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f139])).

fof(f47552,plain,
    ( ! [X30,X28,X29] : k4_xboole_0(k4_xboole_0(X30,X28),X28) = k4_xboole_0(k5_xboole_0(k4_xboole_0(X30,X28),k4_xboole_0(X28,X29)),X28)
    | ~ spl2_141
    | ~ spl2_185 ),
    inference(superposition,[],[f46986,f17371])).

fof(f17371,plain,
    ( ! [X30,X28,X29] : k4_xboole_0(X29,X30) = k4_xboole_0(k4_xboole_0(X29,X30),k4_xboole_0(X28,X29))
    | ~ spl2_141 ),
    inference(avatar_component_clause,[],[f17370])).

fof(f46986,plain,
    ( ! [X50,X51,X49] : k4_xboole_0(k5_xboole_0(X51,k4_xboole_0(k4_xboole_0(X49,X50),X51)),X49) = k4_xboole_0(X51,X49)
    | ~ spl2_185 ),
    inference(avatar_component_clause,[],[f46985])).

fof(f46987,plain,
    ( spl2_185
    | ~ spl2_37
    | ~ spl2_41
    | ~ spl2_49
    | ~ spl2_103 ),
    inference(avatar_split_clause,[],[f7827,f6772,f2985,f2320,f1500,f46985])).

fof(f1500,plain,
    ( spl2_37
  <=> ! [X1,X0] : k4_xboole_0(k4_xboole_0(X0,X1),X0) = k5_xboole_0(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).

fof(f2320,plain,
    ( spl2_41
  <=> ! [X22,X23] : k5_xboole_0(X23,k5_xboole_0(X22,X22)) = X23 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_41])])).

fof(f2985,plain,
    ( spl2_49
  <=> ! [X5,X4] : k5_xboole_0(X5,X5) = k4_xboole_0(k5_xboole_0(X5,X5),X4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_49])])).

fof(f6772,plain,
    ( spl2_103
  <=> ! [X1,X0,X2] : k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X2) = k5_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X0,X2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_103])])).

fof(f7827,plain,
    ( ! [X50,X51,X49] : k4_xboole_0(k5_xboole_0(X51,k4_xboole_0(k4_xboole_0(X49,X50),X51)),X49) = k4_xboole_0(X51,X49)
    | ~ spl2_37
    | ~ spl2_41
    | ~ spl2_49
    | ~ spl2_103 ),
    inference(forward_demodulation,[],[f7826,f2321])).

fof(f2321,plain,
    ( ! [X23,X22] : k5_xboole_0(X23,k5_xboole_0(X22,X22)) = X23
    | ~ spl2_41 ),
    inference(avatar_component_clause,[],[f2320])).

fof(f7826,plain,
    ( ! [X50,X51,X49] : k4_xboole_0(k5_xboole_0(X51,k4_xboole_0(k4_xboole_0(X49,X50),X51)),X49) = k5_xboole_0(k4_xboole_0(X51,X49),k5_xboole_0(X49,X49))
    | ~ spl2_37
    | ~ spl2_49
    | ~ spl2_103 ),
    inference(forward_demodulation,[],[f7721,f2986])).

fof(f2986,plain,
    ( ! [X4,X5] : k5_xboole_0(X5,X5) = k4_xboole_0(k5_xboole_0(X5,X5),X4)
    | ~ spl2_49 ),
    inference(avatar_component_clause,[],[f2985])).

fof(f7721,plain,
    ( ! [X50,X51,X49] : k4_xboole_0(k5_xboole_0(X51,k4_xboole_0(k4_xboole_0(X49,X50),X51)),X49) = k5_xboole_0(k4_xboole_0(X51,X49),k4_xboole_0(k5_xboole_0(X49,X49),k4_xboole_0(X51,X49)))
    | ~ spl2_37
    | ~ spl2_103 ),
    inference(superposition,[],[f6773,f1501])).

fof(f1501,plain,
    ( ! [X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X0) = k5_xboole_0(X0,X0)
    | ~ spl2_37 ),
    inference(avatar_component_clause,[],[f1500])).

fof(f6773,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X2) = k5_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X0,X2)))
    | ~ spl2_103 ),
    inference(avatar_component_clause,[],[f6772])).

fof(f34115,plain,
    ( spl2_162
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_48
    | ~ spl2_137
    | ~ spl2_153
    | ~ spl2_155 ),
    inference(avatar_split_clause,[],[f31737,f31520,f27271,f17354,f2924,f52,f40,f34113])).

fof(f40,plain,
    ( spl2_1
  <=> ! [X1,X0] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f52,plain,
    ( spl2_4
  <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f2924,plain,
    ( spl2_48
  <=> ! [X3,X2] : k4_xboole_0(X2,k5_xboole_0(X3,X3)) = X2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_48])])).

fof(f17354,plain,
    ( spl2_137
  <=> ! [X117,X116] : k5_xboole_0(k4_xboole_0(X116,X117),X117) = k5_xboole_0(k4_xboole_0(X117,X116),X116) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_137])])).

fof(f27271,plain,
    ( spl2_153
  <=> ! [X63,X64] : k5_xboole_0(X63,X63) = k4_xboole_0(k5_xboole_0(X64,X63),k5_xboole_0(X63,X64)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_153])])).

fof(f31520,plain,
    ( spl2_155
  <=> ! [X22,X19] : k4_xboole_0(k5_xboole_0(X22,k4_xboole_0(X19,X22)),X19) = k4_xboole_0(X22,X19) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_155])])).

fof(f31737,plain,
    ( ! [X6,X5] : k4_xboole_0(k5_xboole_0(X5,k4_xboole_0(X6,X5)),k4_xboole_0(X5,X6)) = X6
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_48
    | ~ spl2_137
    | ~ spl2_153
    | ~ spl2_155 ),
    inference(forward_demodulation,[],[f31736,f2925])).

fof(f2925,plain,
    ( ! [X2,X3] : k4_xboole_0(X2,k5_xboole_0(X3,X3)) = X2
    | ~ spl2_48 ),
    inference(avatar_component_clause,[],[f2924])).

fof(f31736,plain,
    ( ! [X6,X5] : k4_xboole_0(X6,k5_xboole_0(X5,X5)) = k4_xboole_0(k5_xboole_0(X5,k4_xboole_0(X6,X5)),k4_xboole_0(X5,X6))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_137
    | ~ spl2_153
    | ~ spl2_155 ),
    inference(forward_demodulation,[],[f31593,f31717])).

fof(f31717,plain,
    ( ! [X80,X79] : k5_xboole_0(X79,X79) = k4_xboole_0(X80,k5_xboole_0(X79,k4_xboole_0(X80,X79)))
    | ~ spl2_1
    | ~ spl2_137
    | ~ spl2_153
    | ~ spl2_155 ),
    inference(forward_demodulation,[],[f31572,f31195])).

fof(f31195,plain,
    ( ! [X218,X219] : k5_xboole_0(X219,X219) = k4_xboole_0(k5_xboole_0(X218,k4_xboole_0(X219,X218)),k5_xboole_0(X219,k4_xboole_0(X218,X219)))
    | ~ spl2_1
    | ~ spl2_137
    | ~ spl2_153 ),
    inference(forward_demodulation,[],[f30842,f41])).

fof(f41,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f30842,plain,
    ( ! [X218,X219] : k5_xboole_0(X219,X219) = k4_xboole_0(k5_xboole_0(k4_xboole_0(X219,X218),X218),k5_xboole_0(X219,k4_xboole_0(X218,X219)))
    | ~ spl2_137
    | ~ spl2_153 ),
    inference(superposition,[],[f27272,f17355])).

fof(f17355,plain,
    ( ! [X116,X117] : k5_xboole_0(k4_xboole_0(X116,X117),X117) = k5_xboole_0(k4_xboole_0(X117,X116),X116)
    | ~ spl2_137 ),
    inference(avatar_component_clause,[],[f17354])).

fof(f27272,plain,
    ( ! [X64,X63] : k5_xboole_0(X63,X63) = k4_xboole_0(k5_xboole_0(X64,X63),k5_xboole_0(X63,X64))
    | ~ spl2_153 ),
    inference(avatar_component_clause,[],[f27271])).

fof(f31572,plain,
    ( ! [X80,X79] : k4_xboole_0(X80,k5_xboole_0(X79,k4_xboole_0(X80,X79))) = k4_xboole_0(k5_xboole_0(X80,k4_xboole_0(X79,X80)),k5_xboole_0(X79,k4_xboole_0(X80,X79)))
    | ~ spl2_155 ),
    inference(superposition,[],[f31521,f31521])).

fof(f31521,plain,
    ( ! [X19,X22] : k4_xboole_0(k5_xboole_0(X22,k4_xboole_0(X19,X22)),X19) = k4_xboole_0(X22,X19)
    | ~ spl2_155 ),
    inference(avatar_component_clause,[],[f31520])).

fof(f31593,plain,
    ( ! [X6,X5] : k4_xboole_0(X6,k4_xboole_0(X6,k5_xboole_0(X5,k4_xboole_0(X6,X5)))) = k4_xboole_0(k5_xboole_0(X5,k4_xboole_0(X6,X5)),k4_xboole_0(X5,X6))
    | ~ spl2_4
    | ~ spl2_155 ),
    inference(superposition,[],[f53,f31521])).

fof(f53,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f52])).

fof(f31522,plain,
    ( spl2_155
    | ~ spl2_41
    | ~ spl2_49
    | ~ spl2_54
    | ~ spl2_103 ),
    inference(avatar_split_clause,[],[f7812,f6772,f3617,f2985,f2320,f31520])).

fof(f3617,plain,
    ( spl2_54
  <=> ! [X27,X29,X28] : k4_xboole_0(X28,X28) = k4_xboole_0(k5_xboole_0(X29,X29),X27) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_54])])).

fof(f7812,plain,
    ( ! [X19,X22] : k4_xboole_0(k5_xboole_0(X22,k4_xboole_0(X19,X22)),X19) = k4_xboole_0(X22,X19)
    | ~ spl2_41
    | ~ spl2_49
    | ~ spl2_54
    | ~ spl2_103 ),
    inference(forward_demodulation,[],[f7811,f2321])).

fof(f7811,plain,
    ( ! [X19,X22,X20] : k4_xboole_0(k5_xboole_0(X22,k4_xboole_0(X19,X22)),X19) = k5_xboole_0(k4_xboole_0(X22,X19),k5_xboole_0(X20,X20))
    | ~ spl2_49
    | ~ spl2_54
    | ~ spl2_103 ),
    inference(forward_demodulation,[],[f7810,f2986])).

fof(f7810,plain,
    ( ! [X19,X22,X20] : k4_xboole_0(k5_xboole_0(X22,k4_xboole_0(X19,X22)),X19) = k5_xboole_0(k4_xboole_0(X22,X19),k4_xboole_0(k5_xboole_0(X20,X20),k4_xboole_0(X22,X19)))
    | ~ spl2_49
    | ~ spl2_54
    | ~ spl2_103 ),
    inference(forward_demodulation,[],[f7711,f2986])).

fof(f7711,plain,
    ( ! [X21,X19,X22,X20] : k4_xboole_0(k5_xboole_0(X22,k4_xboole_0(X19,X22)),X19) = k5_xboole_0(k4_xboole_0(X22,X19),k4_xboole_0(k4_xboole_0(k5_xboole_0(X20,X20),X21),k4_xboole_0(X22,X19)))
    | ~ spl2_54
    | ~ spl2_103 ),
    inference(superposition,[],[f6773,f3618])).

fof(f3618,plain,
    ( ! [X28,X29,X27] : k4_xboole_0(X28,X28) = k4_xboole_0(k5_xboole_0(X29,X29),X27)
    | ~ spl2_54 ),
    inference(avatar_component_clause,[],[f3617])).

fof(f27273,plain,
    ( spl2_153
    | ~ spl2_16
    | ~ spl2_37
    | ~ spl2_61
    | ~ spl2_90
    | ~ spl2_148 ),
    inference(avatar_split_clause,[],[f27168,f26828,f6720,f3778,f1500,f220,f27271])).

fof(f220,plain,
    ( spl2_16
  <=> ! [X3,X5,X4] : k5_xboole_0(X3,k5_xboole_0(X4,X5)) = k5_xboole_0(X5,k5_xboole_0(X3,X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f3778,plain,
    ( spl2_61
  <=> ! [X9,X11,X10] : k5_xboole_0(X10,k5_xboole_0(X11,X9)) = k5_xboole_0(X10,k5_xboole_0(X9,X11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_61])])).

fof(f6720,plain,
    ( spl2_90
  <=> ! [X13,X15,X14] : k5_xboole_0(X14,X15) = k5_xboole_0(X13,k5_xboole_0(X15,k5_xboole_0(X14,X13))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_90])])).

fof(f26828,plain,
    ( spl2_148
  <=> ! [X131,X130,X132] : k5_xboole_0(X132,X131) = k4_xboole_0(k5_xboole_0(X131,X132),k5_xboole_0(X130,X130)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_148])])).

fof(f27168,plain,
    ( ! [X64,X63] : k5_xboole_0(X63,X63) = k4_xboole_0(k5_xboole_0(X64,X63),k5_xboole_0(X63,X64))
    | ~ spl2_16
    | ~ spl2_37
    | ~ spl2_61
    | ~ spl2_90
    | ~ spl2_148 ),
    inference(forward_demodulation,[],[f27167,f6721])).

fof(f6721,plain,
    ( ! [X14,X15,X13] : k5_xboole_0(X14,X15) = k5_xboole_0(X13,k5_xboole_0(X15,k5_xboole_0(X14,X13)))
    | ~ spl2_90 ),
    inference(avatar_component_clause,[],[f6720])).

fof(f27167,plain,
    ( ! [X64,X63] : k5_xboole_0(X64,k5_xboole_0(X63,k5_xboole_0(X63,X64))) = k4_xboole_0(k5_xboole_0(X64,X63),k5_xboole_0(X63,X64))
    | ~ spl2_16
    | ~ spl2_37
    | ~ spl2_61
    | ~ spl2_148 ),
    inference(forward_demodulation,[],[f27166,f3779])).

fof(f3779,plain,
    ( ! [X10,X11,X9] : k5_xboole_0(X10,k5_xboole_0(X11,X9)) = k5_xboole_0(X10,k5_xboole_0(X9,X11))
    | ~ spl2_61 ),
    inference(avatar_component_clause,[],[f3778])).

fof(f27166,plain,
    ( ! [X64,X63] : k5_xboole_0(X64,k5_xboole_0(k5_xboole_0(X63,X64),X63)) = k4_xboole_0(k5_xboole_0(X64,X63),k5_xboole_0(X63,X64))
    | ~ spl2_16
    | ~ spl2_37
    | ~ spl2_148 ),
    inference(forward_demodulation,[],[f26994,f221])).

fof(f221,plain,
    ( ! [X4,X5,X3] : k5_xboole_0(X3,k5_xboole_0(X4,X5)) = k5_xboole_0(X5,k5_xboole_0(X3,X4))
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f220])).

fof(f26994,plain,
    ( ! [X64,X63] : k5_xboole_0(k5_xboole_0(X63,X64),k5_xboole_0(X63,X64)) = k4_xboole_0(k5_xboole_0(X64,X63),k5_xboole_0(X63,X64))
    | ~ spl2_37
    | ~ spl2_148 ),
    inference(superposition,[],[f1501,f26829])).

fof(f26829,plain,
    ( ! [X132,X130,X131] : k5_xboole_0(X132,X131) = k4_xboole_0(k5_xboole_0(X131,X132),k5_xboole_0(X130,X130))
    | ~ spl2_148 ),
    inference(avatar_component_clause,[],[f26828])).

fof(f26830,plain,
    ( spl2_148
    | ~ spl2_41
    | ~ spl2_49
    | ~ spl2_102
    | ~ spl2_138 ),
    inference(avatar_split_clause,[],[f25869,f17358,f6768,f2985,f2320,f26828])).

fof(f6768,plain,
    ( spl2_102
  <=> ! [X42,X44,X43] : k5_xboole_0(X44,X42) = k5_xboole_0(k5_xboole_0(X43,X43),k5_xboole_0(X42,X44)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_102])])).

fof(f17358,plain,
    ( spl2_138
  <=> ! [X69,X68] : k4_xboole_0(X69,X68) = k5_xboole_0(k5_xboole_0(X68,X69),k4_xboole_0(X68,X69)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_138])])).

fof(f25869,plain,
    ( ! [X132,X130,X131] : k5_xboole_0(X132,X131) = k4_xboole_0(k5_xboole_0(X131,X132),k5_xboole_0(X130,X130))
    | ~ spl2_41
    | ~ spl2_49
    | ~ spl2_102
    | ~ spl2_138 ),
    inference(forward_demodulation,[],[f25868,f2321])).

fof(f25868,plain,
    ( ! [X132,X130,X131] : k4_xboole_0(k5_xboole_0(X131,X132),k5_xboole_0(X130,X130)) = k5_xboole_0(k5_xboole_0(X132,X131),k5_xboole_0(X130,X130))
    | ~ spl2_49
    | ~ spl2_102
    | ~ spl2_138 ),
    inference(forward_demodulation,[],[f25684,f2986])).

fof(f25684,plain,
    ( ! [X132,X130,X131] : k4_xboole_0(k5_xboole_0(X131,X132),k5_xboole_0(X130,X130)) = k5_xboole_0(k5_xboole_0(X132,X131),k4_xboole_0(k5_xboole_0(X130,X130),k5_xboole_0(X131,X132)))
    | ~ spl2_102
    | ~ spl2_138 ),
    inference(superposition,[],[f17359,f6769])).

fof(f6769,plain,
    ( ! [X43,X44,X42] : k5_xboole_0(X44,X42) = k5_xboole_0(k5_xboole_0(X43,X43),k5_xboole_0(X42,X44))
    | ~ spl2_102 ),
    inference(avatar_component_clause,[],[f6768])).

fof(f17359,plain,
    ( ! [X68,X69] : k4_xboole_0(X69,X68) = k5_xboole_0(k5_xboole_0(X68,X69),k4_xboole_0(X68,X69))
    | ~ spl2_138 ),
    inference(avatar_component_clause,[],[f17358])).

fof(f17372,plain,
    ( spl2_141
    | ~ spl2_7
    | ~ spl2_119 ),
    inference(avatar_split_clause,[],[f16568,f6836,f95,f17370])).

fof(f95,plain,
    ( spl2_7
  <=> ! [X3,X2] : k4_xboole_0(X2,k4_xboole_0(X3,X2)) = X2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f6836,plain,
    ( spl2_119
  <=> ! [X13,X12,X14] : k4_xboole_0(X13,X12) = k4_xboole_0(k4_xboole_0(X13,X12),k4_xboole_0(X12,X14)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_119])])).

fof(f16568,plain,
    ( ! [X30,X28,X29] : k4_xboole_0(X29,X30) = k4_xboole_0(k4_xboole_0(X29,X30),k4_xboole_0(X28,X29))
    | ~ spl2_7
    | ~ spl2_119 ),
    inference(superposition,[],[f96,f6837])).

fof(f6837,plain,
    ( ! [X14,X12,X13] : k4_xboole_0(X13,X12) = k4_xboole_0(k4_xboole_0(X13,X12),k4_xboole_0(X12,X14))
    | ~ spl2_119 ),
    inference(avatar_component_clause,[],[f6836])).

fof(f96,plain,
    ( ! [X2,X3] : k4_xboole_0(X2,k4_xboole_0(X3,X2)) = X2
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f95])).

fof(f17360,plain,
    ( spl2_138
    | ~ spl2_42
    | ~ spl2_95 ),
    inference(avatar_split_clause,[],[f8215,f6740,f2324,f17358])).

fof(f2324,plain,
    ( spl2_42
  <=> ! [X49,X48] : k5_xboole_0(k5_xboole_0(X48,X49),X48) = X49 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).

fof(f6740,plain,
    ( spl2_95
  <=> ! [X36,X35] : k5_xboole_0(X35,X36) = k5_xboole_0(k4_xboole_0(X35,X36),k4_xboole_0(X36,X35)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_95])])).

fof(f8215,plain,
    ( ! [X68,X69] : k4_xboole_0(X69,X68) = k5_xboole_0(k5_xboole_0(X68,X69),k4_xboole_0(X68,X69))
    | ~ spl2_42
    | ~ spl2_95 ),
    inference(superposition,[],[f2325,f6741])).

fof(f6741,plain,
    ( ! [X35,X36] : k5_xboole_0(X35,X36) = k5_xboole_0(k4_xboole_0(X35,X36),k4_xboole_0(X36,X35))
    | ~ spl2_95 ),
    inference(avatar_component_clause,[],[f6740])).

fof(f2325,plain,
    ( ! [X48,X49] : k5_xboole_0(k5_xboole_0(X48,X49),X48) = X49
    | ~ spl2_42 ),
    inference(avatar_component_clause,[],[f2324])).

fof(f17356,plain,
    ( spl2_137
    | ~ spl2_38
    | ~ spl2_92 ),
    inference(avatar_split_clause,[],[f7340,f6728,f1917,f17354])).

fof(f1917,plain,
    ( spl2_38
  <=> ! [X3,X4] : k5_xboole_0(k4_xboole_0(X4,X3),k5_xboole_0(X3,k4_xboole_0(X3,X4))) = X4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).

fof(f6728,plain,
    ( spl2_92
  <=> ! [X25,X27,X26] : k5_xboole_0(X26,X27) = k5_xboole_0(X25,k5_xboole_0(X26,k5_xboole_0(X27,X25))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_92])])).

fof(f7340,plain,
    ( ! [X116,X117] : k5_xboole_0(k4_xboole_0(X116,X117),X117) = k5_xboole_0(k4_xboole_0(X117,X116),X116)
    | ~ spl2_38
    | ~ spl2_92 ),
    inference(superposition,[],[f6729,f1918])).

fof(f1918,plain,
    ( ! [X4,X3] : k5_xboole_0(k4_xboole_0(X4,X3),k5_xboole_0(X3,k4_xboole_0(X3,X4))) = X4
    | ~ spl2_38 ),
    inference(avatar_component_clause,[],[f1917])).

fof(f6729,plain,
    ( ! [X26,X27,X25] : k5_xboole_0(X26,X27) = k5_xboole_0(X25,k5_xboole_0(X26,k5_xboole_0(X27,X25)))
    | ~ spl2_92 ),
    inference(avatar_component_clause,[],[f6728])).

fof(f16709,plain,
    ( spl2_135
    | ~ spl2_71
    | ~ spl2_90 ),
    inference(avatar_split_clause,[],[f6895,f6720,f3818,f16707])).

fof(f3818,plain,
    ( spl2_71
  <=> ! [X7,X8] : k4_xboole_0(X7,X8) = k5_xboole_0(X8,k5_xboole_0(X7,k4_xboole_0(X8,X7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_71])])).

fof(f6895,plain,
    ( ! [X39,X38] : k5_xboole_0(X39,X38) = k5_xboole_0(k4_xboole_0(X38,X39),k4_xboole_0(X39,X38))
    | ~ spl2_71
    | ~ spl2_90 ),
    inference(superposition,[],[f6721,f3819])).

fof(f3819,plain,
    ( ! [X8,X7] : k4_xboole_0(X7,X8) = k5_xboole_0(X8,k5_xboole_0(X7,k4_xboole_0(X8,X7)))
    | ~ spl2_71 ),
    inference(avatar_component_clause,[],[f3818])).

fof(f6838,plain,
    ( spl2_119
    | ~ spl2_7
    | ~ spl2_88 ),
    inference(avatar_split_clause,[],[f6096,f6089,f95,f6836])).

fof(f6089,plain,
    ( spl2_88
  <=> ! [X29,X28,X30] : k4_xboole_0(X29,k4_xboole_0(k4_xboole_0(X28,X29),X30)) = X29 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_88])])).

fof(f6096,plain,
    ( ! [X14,X12,X13] : k4_xboole_0(X13,X12) = k4_xboole_0(k4_xboole_0(X13,X12),k4_xboole_0(X12,X14))
    | ~ spl2_7
    | ~ spl2_88 ),
    inference(superposition,[],[f6090,f96])).

fof(f6090,plain,
    ( ! [X30,X28,X29] : k4_xboole_0(X29,k4_xboole_0(k4_xboole_0(X28,X29),X30)) = X29
    | ~ spl2_88 ),
    inference(avatar_component_clause,[],[f6089])).

fof(f6774,plain,(
    spl2_103 ),
    inference(avatar_split_clause,[],[f36,f6772])).

fof(f36,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X2) = k5_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f28,f21,f21])).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f28,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).

fof(f6770,plain,
    ( spl2_102
    | ~ spl2_22
    | ~ spl2_41 ),
    inference(avatar_split_clause,[],[f2369,f2320,f516,f6768])).

fof(f516,plain,
    ( spl2_22
  <=> ! [X9,X7,X8] : k5_xboole_0(X9,k5_xboole_0(X7,X8)) = k5_xboole_0(X8,k5_xboole_0(X7,X9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f2369,plain,
    ( ! [X43,X44,X42] : k5_xboole_0(X44,X42) = k5_xboole_0(k5_xboole_0(X43,X43),k5_xboole_0(X42,X44))
    | ~ spl2_22
    | ~ spl2_41 ),
    inference(superposition,[],[f517,f2321])).

fof(f517,plain,
    ( ! [X8,X7,X9] : k5_xboole_0(X9,k5_xboole_0(X7,X8)) = k5_xboole_0(X8,k5_xboole_0(X7,X9))
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f516])).

fof(f6742,plain,
    ( spl2_95
    | ~ spl2_39
    | ~ spl2_40 ),
    inference(avatar_split_clause,[],[f2181,f2167,f1921,f6740])).

fof(f1921,plain,
    ( spl2_39
  <=> ! [X7,X8] : k5_xboole_0(X7,k5_xboole_0(k4_xboole_0(X7,X8),k4_xboole_0(X8,X7))) = X8 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_39])])).

fof(f2167,plain,
    ( spl2_40
  <=> ! [X29,X30] : k5_xboole_0(X29,k5_xboole_0(X29,X30)) = X30 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_40])])).

fof(f2181,plain,
    ( ! [X35,X36] : k5_xboole_0(X35,X36) = k5_xboole_0(k4_xboole_0(X35,X36),k4_xboole_0(X36,X35))
    | ~ spl2_39
    | ~ spl2_40 ),
    inference(superposition,[],[f2168,f1922])).

fof(f1922,plain,
    ( ! [X8,X7] : k5_xboole_0(X7,k5_xboole_0(k4_xboole_0(X7,X8),k4_xboole_0(X8,X7))) = X8
    | ~ spl2_39 ),
    inference(avatar_component_clause,[],[f1921])).

fof(f2168,plain,
    ( ! [X30,X29] : k5_xboole_0(X29,k5_xboole_0(X29,X30)) = X30
    | ~ spl2_40 ),
    inference(avatar_component_clause,[],[f2167])).

fof(f6730,plain,
    ( spl2_92
    | ~ spl2_16
    | ~ spl2_40 ),
    inference(avatar_split_clause,[],[f2177,f2167,f220,f6728])).

fof(f2177,plain,
    ( ! [X26,X27,X25] : k5_xboole_0(X26,X27) = k5_xboole_0(X25,k5_xboole_0(X26,k5_xboole_0(X27,X25)))
    | ~ spl2_16
    | ~ spl2_40 ),
    inference(superposition,[],[f2168,f221])).

fof(f6722,plain,
    ( spl2_90
    | ~ spl2_22
    | ~ spl2_40 ),
    inference(avatar_split_clause,[],[f2173,f2167,f516,f6720])).

fof(f2173,plain,
    ( ! [X14,X15,X13] : k5_xboole_0(X14,X15) = k5_xboole_0(X13,k5_xboole_0(X15,k5_xboole_0(X14,X13)))
    | ~ spl2_22
    | ~ spl2_40 ),
    inference(superposition,[],[f2168,f517])).

fof(f6091,plain,
    ( spl2_88
    | ~ spl2_16
    | ~ spl2_28
    | ~ spl2_37
    | ~ spl2_87 ),
    inference(avatar_split_clause,[],[f6052,f5940,f1500,f541,f220,f6089])).

fof(f5940,plain,
    ( spl2_87
  <=> ! [X25,X23,X24] : k4_xboole_0(X25,k5_xboole_0(X23,k4_xboole_0(X23,k4_xboole_0(X24,X25)))) = X25 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_87])])).

fof(f6052,plain,
    ( ! [X30,X28,X29] : k4_xboole_0(X29,k4_xboole_0(k4_xboole_0(X28,X29),X30)) = X29
    | ~ spl2_16
    | ~ spl2_28
    | ~ spl2_37
    | ~ spl2_87 ),
    inference(forward_demodulation,[],[f6051,f542])).

fof(f6051,plain,
    ( ! [X30,X28,X29] : k4_xboole_0(X29,k5_xboole_0(k4_xboole_0(X28,X29),k5_xboole_0(k4_xboole_0(X28,X29),k4_xboole_0(k4_xboole_0(X28,X29),X30)))) = X29
    | ~ spl2_16
    | ~ spl2_37
    | ~ spl2_87 ),
    inference(forward_demodulation,[],[f6050,f221])).

fof(f6050,plain,
    ( ! [X30,X28,X29] : k4_xboole_0(X29,k5_xboole_0(k4_xboole_0(X28,X29),k5_xboole_0(k4_xboole_0(k4_xboole_0(X28,X29),X30),k4_xboole_0(X28,X29)))) = X29
    | ~ spl2_16
    | ~ spl2_37
    | ~ spl2_87 ),
    inference(forward_demodulation,[],[f5977,f221])).

fof(f5977,plain,
    ( ! [X30,X28,X29] : k4_xboole_0(X29,k5_xboole_0(k4_xboole_0(k4_xboole_0(X28,X29),X30),k5_xboole_0(k4_xboole_0(X28,X29),k4_xboole_0(X28,X29)))) = X29
    | ~ spl2_37
    | ~ spl2_87 ),
    inference(superposition,[],[f5941,f1501])).

fof(f5941,plain,
    ( ! [X24,X23,X25] : k4_xboole_0(X25,k5_xboole_0(X23,k4_xboole_0(X23,k4_xboole_0(X24,X25)))) = X25
    | ~ spl2_87 ),
    inference(avatar_component_clause,[],[f5940])).

fof(f5942,plain,
    ( spl2_87
    | ~ spl2_7
    | ~ spl2_77 ),
    inference(avatar_split_clause,[],[f5752,f3842,f95,f5940])).

fof(f3842,plain,
    ( spl2_77
  <=> ! [X1,X0,X2] : k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_77])])).

fof(f5752,plain,
    ( ! [X24,X23,X25] : k4_xboole_0(X25,k5_xboole_0(X23,k4_xboole_0(X23,k4_xboole_0(X24,X25)))) = X25
    | ~ spl2_7
    | ~ spl2_77 ),
    inference(superposition,[],[f96,f3843])).

fof(f3843,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))
    | ~ spl2_77 ),
    inference(avatar_component_clause,[],[f3842])).

fof(f3844,plain,
    ( spl2_77
    | ~ spl2_3
    | ~ spl2_28 ),
    inference(avatar_split_clause,[],[f1332,f541,f48,f3842])).

fof(f1332,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))
    | ~ spl2_3
    | ~ spl2_28 ),
    inference(forward_demodulation,[],[f1279,f1251])).

fof(f1279,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),X2)
    | ~ spl2_3
    | ~ spl2_28 ),
    inference(backward_demodulation,[],[f34,f1251])).

fof(f34,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f26,f23,f23])).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f26,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f3820,plain,
    ( spl2_71
    | ~ spl2_21
    | ~ spl2_34 ),
    inference(avatar_split_clause,[],[f1442,f1425,f512,f3818])).

fof(f1442,plain,
    ( ! [X8,X7] : k4_xboole_0(X7,X8) = k5_xboole_0(X8,k5_xboole_0(X7,k4_xboole_0(X8,X7)))
    | ~ spl2_21
    | ~ spl2_34 ),
    inference(superposition,[],[f1426,f513])).

fof(f3780,plain,
    ( spl2_61
    | ~ spl2_16
    | ~ spl2_21 ),
    inference(avatar_split_clause,[],[f576,f512,f220,f3778])).

fof(f576,plain,
    ( ! [X10,X11,X9] : k5_xboole_0(X10,k5_xboole_0(X11,X9)) = k5_xboole_0(X10,k5_xboole_0(X9,X11))
    | ~ spl2_16
    | ~ spl2_21 ),
    inference(superposition,[],[f513,f221])).

fof(f3619,plain,
    ( spl2_54
    | ~ spl2_50
    | ~ spl2_51 ),
    inference(avatar_split_clause,[],[f3243,f3053,f2989,f3617])).

fof(f2989,plain,
    ( spl2_50
  <=> ! [X44,X43] : k5_xboole_0(X44,X44) = k4_xboole_0(k5_xboole_0(X43,X43),X44) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_50])])).

fof(f3053,plain,
    ( spl2_51
  <=> ! [X3,X4] : k5_xboole_0(X3,X3) = k4_xboole_0(X4,X4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_51])])).

fof(f3243,plain,
    ( ! [X28,X29,X27] : k4_xboole_0(X28,X28) = k4_xboole_0(k5_xboole_0(X29,X29),X27)
    | ~ spl2_50
    | ~ spl2_51 ),
    inference(superposition,[],[f2990,f3054])).

fof(f3054,plain,
    ( ! [X4,X3] : k5_xboole_0(X3,X3) = k4_xboole_0(X4,X4)
    | ~ spl2_51 ),
    inference(avatar_component_clause,[],[f3053])).

fof(f2990,plain,
    ( ! [X43,X44] : k5_xboole_0(X44,X44) = k4_xboole_0(k5_xboole_0(X43,X43),X44)
    | ~ spl2_50 ),
    inference(avatar_component_clause,[],[f2989])).

fof(f3055,plain,
    ( spl2_51
    | ~ spl2_4
    | ~ spl2_48
    | ~ spl2_49 ),
    inference(avatar_split_clause,[],[f3038,f2985,f2924,f52,f3053])).

fof(f3038,plain,
    ( ! [X4,X3] : k5_xboole_0(X3,X3) = k4_xboole_0(X4,X4)
    | ~ spl2_4
    | ~ spl2_48
    | ~ spl2_49 ),
    inference(forward_demodulation,[],[f3006,f2925])).

fof(f3006,plain,
    ( ! [X4,X3] : k5_xboole_0(X3,X3) = k4_xboole_0(X4,k4_xboole_0(X4,k5_xboole_0(X3,X3)))
    | ~ spl2_4
    | ~ spl2_49 ),
    inference(superposition,[],[f2986,f53])).

fof(f2991,plain,
    ( spl2_50
    | ~ spl2_10
    | ~ spl2_34
    | ~ spl2_44
    | ~ spl2_45 ),
    inference(avatar_split_clause,[],[f2792,f2500,f2496,f1425,f131,f2989])).

fof(f131,plain,
    ( spl2_10
  <=> ! [X0] : k4_xboole_0(X0,k5_xboole_0(X0,X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f2496,plain,
    ( spl2_44
  <=> ! [X53,X52] : k5_xboole_0(k5_xboole_0(X52,X52),X53) = X53 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).

fof(f2500,plain,
    ( spl2_45
  <=> ! [X53,X54] : k5_xboole_0(X53,X53) = k5_xboole_0(X54,X54) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_45])])).

fof(f2792,plain,
    ( ! [X43,X44] : k5_xboole_0(X44,X44) = k4_xboole_0(k5_xboole_0(X43,X43),X44)
    | ~ spl2_10
    | ~ spl2_34
    | ~ spl2_44
    | ~ spl2_45 ),
    inference(backward_demodulation,[],[f2597,f2700])).

fof(f2700,plain,
    ( ! [X2,X3] : k4_xboole_0(X2,k5_xboole_0(X3,X3)) = X2
    | ~ spl2_10
    | ~ spl2_45 ),
    inference(superposition,[],[f132,f2501])).

fof(f2501,plain,
    ( ! [X54,X53] : k5_xboole_0(X53,X53) = k5_xboole_0(X54,X54)
    | ~ spl2_45 ),
    inference(avatar_component_clause,[],[f2500])).

fof(f132,plain,
    ( ! [X0] : k4_xboole_0(X0,k5_xboole_0(X0,X0)) = X0
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f131])).

fof(f2597,plain,
    ( ! [X43,X44] : k5_xboole_0(X44,k4_xboole_0(X44,k5_xboole_0(X43,X43))) = k4_xboole_0(k5_xboole_0(X43,X43),X44)
    | ~ spl2_34
    | ~ spl2_44 ),
    inference(superposition,[],[f2497,f1426])).

fof(f2497,plain,
    ( ! [X52,X53] : k5_xboole_0(k5_xboole_0(X52,X52),X53) = X53
    | ~ spl2_44 ),
    inference(avatar_component_clause,[],[f2496])).

fof(f2987,plain,
    ( spl2_49
    | ~ spl2_13
    | ~ spl2_45 ),
    inference(avatar_split_clause,[],[f2701,f2500,f162,f2985])).

fof(f162,plain,
    ( spl2_13
  <=> ! [X0] : k5_xboole_0(X0,X0) = k4_xboole_0(k5_xboole_0(X0,X0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f2701,plain,
    ( ! [X4,X5] : k5_xboole_0(X5,X5) = k4_xboole_0(k5_xboole_0(X5,X5),X4)
    | ~ spl2_13
    | ~ spl2_45 ),
    inference(superposition,[],[f163,f2501])).

fof(f163,plain,
    ( ! [X0] : k5_xboole_0(X0,X0) = k4_xboole_0(k5_xboole_0(X0,X0),X0)
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f162])).

fof(f2926,plain,
    ( spl2_48
    | ~ spl2_10
    | ~ spl2_45 ),
    inference(avatar_split_clause,[],[f2700,f2500,f131,f2924])).

fof(f2511,plain,
    ( ~ spl2_47
    | ~ spl2_34
    | spl2_36
    | ~ spl2_40 ),
    inference(avatar_split_clause,[],[f2284,f2167,f1495,f1425,f2508])).

fof(f1495,plain,
    ( spl2_36
  <=> k5_xboole_0(sK0,sK1) = k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(sK1,k4_xboole_0(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_36])])).

fof(f2284,plain,
    ( k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl2_34
    | spl2_36
    | ~ spl2_40 ),
    inference(backward_demodulation,[],[f1497,f2179])).

fof(f2179,plain,
    ( ! [X31,X32] : k5_xboole_0(X32,k4_xboole_0(X32,X31)) = k5_xboole_0(X31,k4_xboole_0(X31,X32))
    | ~ spl2_34
    | ~ spl2_40 ),
    inference(superposition,[],[f2168,f1426])).

fof(f1497,plain,
    ( k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(sK1,k4_xboole_0(sK1,sK0)))
    | spl2_36 ),
    inference(avatar_component_clause,[],[f1495])).

fof(f2502,plain,
    ( spl2_45
    | ~ spl2_40
    | ~ spl2_41 ),
    inference(avatar_split_clause,[],[f2373,f2320,f2167,f2500])).

fof(f2373,plain,
    ( ! [X54,X53] : k5_xboole_0(X53,X53) = k5_xboole_0(X54,X54)
    | ~ spl2_40
    | ~ spl2_41 ),
    inference(superposition,[],[f2168,f2321])).

fof(f2498,plain,
    ( spl2_44
    | ~ spl2_16
    | ~ spl2_21
    | ~ spl2_22
    | ~ spl2_23
    | ~ spl2_40 ),
    inference(avatar_split_clause,[],[f2310,f2167,f520,f516,f512,f220,f2496])).

fof(f520,plain,
    ( spl2_23
  <=> ! [X9,X10] : k5_xboole_0(X10,X9) = k5_xboole_0(k5_xboole_0(X9,X9),k5_xboole_0(X10,X9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f2310,plain,
    ( ! [X52,X53] : k5_xboole_0(k5_xboole_0(X52,X52),X53) = X53
    | ~ spl2_16
    | ~ spl2_21
    | ~ spl2_22
    | ~ spl2_23
    | ~ spl2_40 ),
    inference(forward_demodulation,[],[f2309,f2173])).

fof(f2309,plain,
    ( ! [X52,X53] : k5_xboole_0(k5_xboole_0(X53,k5_xboole_0(X52,k5_xboole_0(X52,X53))),X53) = X53
    | ~ spl2_16
    | ~ spl2_21
    | ~ spl2_23
    | ~ spl2_40 ),
    inference(forward_demodulation,[],[f2308,f576])).

fof(f2308,plain,
    ( ! [X52,X53] : k5_xboole_0(k5_xboole_0(X53,k5_xboole_0(k5_xboole_0(X52,X53),X52)),X53) = X53
    | ~ spl2_16
    | ~ spl2_23
    | ~ spl2_40 ),
    inference(forward_demodulation,[],[f2213,f221])).

fof(f2213,plain,
    ( ! [X52,X53] : k5_xboole_0(k5_xboole_0(k5_xboole_0(X52,X53),k5_xboole_0(X52,X53)),X53) = X53
    | ~ spl2_23
    | ~ spl2_40 ),
    inference(superposition,[],[f521,f2168])).

fof(f521,plain,
    ( ! [X10,X9] : k5_xboole_0(X10,X9) = k5_xboole_0(k5_xboole_0(X9,X9),k5_xboole_0(X10,X9))
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f520])).

fof(f2326,plain,
    ( spl2_42
    | ~ spl2_18
    | ~ spl2_26
    | ~ spl2_39
    | ~ spl2_40 ),
    inference(avatar_split_clause,[],[f2292,f2167,f1921,f533,f228,f2324])).

fof(f228,plain,
    ( spl2_18
  <=> ! [X2,X4] : k5_xboole_0(X2,X4) = k5_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X2,X4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f533,plain,
    ( spl2_26
  <=> ! [X9,X10] : k5_xboole_0(X10,X9) = k5_xboole_0(X9,k5_xboole_0(X9,k5_xboole_0(X9,X10))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f2292,plain,
    ( ! [X48,X49] : k5_xboole_0(k5_xboole_0(X48,X49),X48) = X49
    | ~ spl2_18
    | ~ spl2_26
    | ~ spl2_39
    | ~ spl2_40 ),
    inference(backward_demodulation,[],[f2163,f2181])).

fof(f2163,plain,
    ( ! [X48,X49] : k5_xboole_0(k5_xboole_0(k4_xboole_0(X48,X49),k4_xboole_0(X49,X48)),X48) = X49
    | ~ spl2_18
    | ~ spl2_26
    | ~ spl2_39 ),
    inference(forward_demodulation,[],[f2055,f2048])).

fof(f2048,plain,
    ( ! [X30,X29] : k5_xboole_0(X29,k5_xboole_0(X29,X30)) = X30
    | ~ spl2_18
    | ~ spl2_39 ),
    inference(superposition,[],[f229,f1922])).

fof(f229,plain,
    ( ! [X4,X2] : k5_xboole_0(X2,X4) = k5_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X2,X4)))
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f228])).

fof(f2055,plain,
    ( ! [X48,X49] : k5_xboole_0(X48,k5_xboole_0(X48,X49)) = k5_xboole_0(k5_xboole_0(k4_xboole_0(X48,X49),k4_xboole_0(X49,X48)),X48)
    | ~ spl2_26
    | ~ spl2_39 ),
    inference(superposition,[],[f534,f1922])).

fof(f534,plain,
    ( ! [X10,X9] : k5_xboole_0(X10,X9) = k5_xboole_0(X9,k5_xboole_0(X9,k5_xboole_0(X9,X10)))
    | ~ spl2_26 ),
    inference(avatar_component_clause,[],[f533])).

fof(f2322,plain,
    ( spl2_41
    | ~ spl2_1
    | ~ spl2_23
    | ~ spl2_40 ),
    inference(avatar_split_clause,[],[f2246,f2167,f520,f40,f2320])).

fof(f2246,plain,
    ( ! [X23,X22] : k5_xboole_0(X23,k5_xboole_0(X22,X22)) = X23
    | ~ spl2_1
    | ~ spl2_23
    | ~ spl2_40 ),
    inference(backward_demodulation,[],[f804,f2170])).

fof(f2170,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1
    | ~ spl2_1
    | ~ spl2_40 ),
    inference(superposition,[],[f2168,f41])).

fof(f804,plain,
    ( ! [X23,X22] : k5_xboole_0(X23,k5_xboole_0(X22,X22)) = k5_xboole_0(k5_xboole_0(X22,X22),k5_xboole_0(X23,k5_xboole_0(X22,X22)))
    | ~ spl2_23 ),
    inference(superposition,[],[f521,f521])).

fof(f2169,plain,
    ( spl2_40
    | ~ spl2_18
    | ~ spl2_39 ),
    inference(avatar_split_clause,[],[f2048,f1921,f228,f2167])).

fof(f1923,plain,
    ( spl2_39
    | ~ spl2_2
    | ~ spl2_35 ),
    inference(avatar_split_clause,[],[f1555,f1429,f44,f1921])).

fof(f1429,plain,
    ( spl2_35
  <=> ! [X1,X0] : k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_35])])).

fof(f1555,plain,
    ( ! [X8,X7] : k5_xboole_0(X7,k5_xboole_0(k4_xboole_0(X7,X8),k4_xboole_0(X8,X7))) = X8
    | ~ spl2_2
    | ~ spl2_35 ),
    inference(superposition,[],[f1430,f45])).

fof(f1430,plain,
    ( ! [X0,X1] : k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) = X0
    | ~ spl2_35 ),
    inference(avatar_component_clause,[],[f1429])).

fof(f1919,plain,
    ( spl2_38
    | ~ spl2_3
    | ~ spl2_28
    | ~ spl2_31 ),
    inference(avatar_split_clause,[],[f1312,f553,f541,f48,f1917])).

fof(f553,plain,
    ( spl2_31
  <=> ! [X3,X4] : k5_xboole_0(k4_xboole_0(X4,X3),k4_xboole_0(X3,k4_xboole_0(X3,X4))) = X4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).

fof(f1312,plain,
    ( ! [X4,X3] : k5_xboole_0(k4_xboole_0(X4,X3),k5_xboole_0(X3,k4_xboole_0(X3,X4))) = X4
    | ~ spl2_3
    | ~ spl2_28
    | ~ spl2_31 ),
    inference(backward_demodulation,[],[f554,f1251])).

fof(f554,plain,
    ( ! [X4,X3] : k5_xboole_0(k4_xboole_0(X4,X3),k4_xboole_0(X3,k4_xboole_0(X3,X4))) = X4
    | ~ spl2_31 ),
    inference(avatar_component_clause,[],[f553])).

fof(f1502,plain,
    ( spl2_37
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_16
    | ~ spl2_19
    | ~ spl2_28
    | ~ spl2_34 ),
    inference(avatar_split_clause,[],[f1469,f1425,f541,f232,f220,f52,f48,f1500])).

fof(f232,plain,
    ( spl2_19
  <=> ! [X1,X0] : k5_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f1469,plain,
    ( ! [X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X0) = k5_xboole_0(X0,X0)
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_16
    | ~ spl2_19
    | ~ spl2_28
    | ~ spl2_34 ),
    inference(forward_demodulation,[],[f1468,f1307])).

fof(f1307,plain,
    ( ! [X14,X15,X16] : k5_xboole_0(X16,X15) = k5_xboole_0(k4_xboole_0(X15,X14),k5_xboole_0(X16,k5_xboole_0(X14,k4_xboole_0(X14,X15))))
    | ~ spl2_3
    | ~ spl2_16
    | ~ spl2_19
    | ~ spl2_28 ),
    inference(backward_demodulation,[],[f459,f1251])).

fof(f459,plain,
    ( ! [X14,X15,X16] : k5_xboole_0(X16,X15) = k5_xboole_0(k4_xboole_0(X15,X14),k5_xboole_0(X16,k4_xboole_0(X14,k4_xboole_0(X14,X15))))
    | ~ spl2_16
    | ~ spl2_19 ),
    inference(superposition,[],[f221,f233])).

fof(f233,plain,
    ( ! [X0,X1] : k5_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) = X0
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f232])).

fof(f1468,plain,
    ( ! [X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X0) = k5_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,X0))))
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_28
    | ~ spl2_34 ),
    inference(forward_demodulation,[],[f1432,f1251])).

fof(f1432,plain,
    ( ! [X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X0) = k5_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))
    | ~ spl2_4
    | ~ spl2_34 ),
    inference(superposition,[],[f1426,f53])).

fof(f1498,plain,
    ( ~ spl2_36
    | ~ spl2_4
    | ~ spl2_17
    | spl2_24
    | ~ spl2_28 ),
    inference(avatar_split_clause,[],[f1277,f541,f524,f224,f52,f1495])).

fof(f524,plain,
    ( spl2_24
  <=> k5_xboole_0(sK0,sK1) = k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f1277,plain,
    ( k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(sK1,k4_xboole_0(sK1,sK0)))
    | ~ spl2_4
    | ~ spl2_17
    | spl2_24
    | ~ spl2_28 ),
    inference(backward_demodulation,[],[f526,f1276])).

fof(f1276,plain,
    ( ! [X0,X1] : k4_xboole_0(X1,k4_xboole_0(X1,X0)) = k5_xboole_0(X0,k4_xboole_0(X0,X1))
    | ~ spl2_4
    | ~ spl2_17
    | ~ spl2_28 ),
    inference(forward_demodulation,[],[f1244,f225])).

fof(f1244,plain,
    ( ! [X0,X1] : k4_xboole_0(X1,k4_xboole_0(X1,X0)) = k5_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))
    | ~ spl2_4
    | ~ spl2_28 ),
    inference(superposition,[],[f542,f53])).

fof(f526,plain,
    ( k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl2_24 ),
    inference(avatar_component_clause,[],[f524])).

fof(f1431,plain,
    ( spl2_35
    | ~ spl2_3
    | ~ spl2_19
    | ~ spl2_28 ),
    inference(avatar_split_clause,[],[f1290,f541,f232,f48,f1429])).

fof(f1290,plain,
    ( ! [X0,X1] : k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) = X0
    | ~ spl2_3
    | ~ spl2_19
    | ~ spl2_28 ),
    inference(backward_demodulation,[],[f233,f1251])).

fof(f1427,plain,
    ( spl2_34
    | ~ spl2_3
    | ~ spl2_17
    | ~ spl2_28 ),
    inference(avatar_split_clause,[],[f1289,f541,f224,f48,f1425])).

fof(f1289,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,X0)))
    | ~ spl2_3
    | ~ spl2_17
    | ~ spl2_28 ),
    inference(backward_demodulation,[],[f225,f1251])).

fof(f555,plain,
    ( spl2_31
    | ~ spl2_1
    | ~ spl2_19 ),
    inference(avatar_split_clause,[],[f452,f232,f40,f553])).

fof(f452,plain,
    ( ! [X4,X3] : k5_xboole_0(k4_xboole_0(X4,X3),k4_xboole_0(X3,k4_xboole_0(X3,X4))) = X4
    | ~ spl2_1
    | ~ spl2_19 ),
    inference(superposition,[],[f233,f41])).

fof(f543,plain,
    ( spl2_28
    | ~ spl2_3
    | ~ spl2_18 ),
    inference(avatar_split_clause,[],[f387,f228,f48,f541])).

fof(f387,plain,
    ( ! [X4,X5] : k4_xboole_0(X4,X5) = k5_xboole_0(X4,k5_xboole_0(X4,k4_xboole_0(X4,X5)))
    | ~ spl2_3
    | ~ spl2_18 ),
    inference(superposition,[],[f229,f49])).

fof(f535,plain,
    ( spl2_26
    | ~ spl2_2
    | ~ spl2_8
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f333,f220,f112,f44,f533])).

fof(f112,plain,
    ( spl2_8
  <=> ! [X0] : k5_xboole_0(X0,k5_xboole_0(X0,X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f333,plain,
    ( ! [X10,X9] : k5_xboole_0(X10,X9) = k5_xboole_0(X9,k5_xboole_0(X9,k5_xboole_0(X9,X10)))
    | ~ spl2_2
    | ~ spl2_8
    | ~ spl2_16 ),
    inference(forward_demodulation,[],[f293,f45])).

fof(f293,plain,
    ( ! [X10,X9] : k5_xboole_0(X10,X9) = k5_xboole_0(X9,k5_xboole_0(k5_xboole_0(X9,X9),X10))
    | ~ spl2_8
    | ~ spl2_16 ),
    inference(superposition,[],[f221,f113])).

fof(f113,plain,
    ( ! [X0] : k5_xboole_0(X0,k5_xboole_0(X0,X0)) = X0
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f112])).

fof(f527,plain,(
    ~ spl2_24 ),
    inference(avatar_split_clause,[],[f30,f524])).

fof(f30,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f17,f21,f23])).

fof(f17,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f15])).

fof(f15,plain,
    ( ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_xboole_1)).

fof(f522,plain,
    ( spl2_23
    | ~ spl2_8
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f277,f220,f112,f520])).

fof(f277,plain,
    ( ! [X10,X9] : k5_xboole_0(X10,X9) = k5_xboole_0(k5_xboole_0(X9,X9),k5_xboole_0(X10,X9))
    | ~ spl2_8
    | ~ spl2_16 ),
    inference(superposition,[],[f221,f113])).

fof(f518,plain,
    ( spl2_22
    | ~ spl2_1
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f249,f216,f40,f516])).

fof(f216,plain,
    ( spl2_15
  <=> ! [X1,X0,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X1,X0),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f249,plain,
    ( ! [X8,X7,X9] : k5_xboole_0(X9,k5_xboole_0(X7,X8)) = k5_xboole_0(X8,k5_xboole_0(X7,X9))
    | ~ spl2_1
    | ~ spl2_15 ),
    inference(superposition,[],[f217,f41])).

fof(f217,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X1,X0),X2)
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f216])).

fof(f514,plain,
    ( spl2_21
    | ~ spl2_2
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f247,f216,f44,f512])).

fof(f247,plain,
    ( ! [X4,X5,X3] : k5_xboole_0(X3,k5_xboole_0(X4,X5)) = k5_xboole_0(X4,k5_xboole_0(X3,X5))
    | ~ spl2_2
    | ~ spl2_15 ),
    inference(superposition,[],[f217,f45])).

fof(f234,plain,
    ( spl2_19
    | ~ spl2_4
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f182,f158,f52,f232])).

fof(f158,plain,
    ( spl2_12
  <=> ! [X1,X0] : k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f182,plain,
    ( ! [X0,X1] : k5_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) = X0
    | ~ spl2_4
    | ~ spl2_12 ),
    inference(superposition,[],[f159,f53])).

fof(f159,plain,
    ( ! [X0,X1] : k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f158])).

fof(f230,plain,
    ( spl2_18
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f107,f95,f56,f48,f44,f228])).

fof(f56,plain,
    ( spl2_5
  <=> ! [X1,X0] : k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f107,plain,
    ( ! [X4,X2] : k5_xboole_0(X2,X4) = k5_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X2,X4)))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_7 ),
    inference(forward_demodulation,[],[f105,f45])).

fof(f105,plain,
    ( ! [X4,X2] : k5_xboole_0(X2,X4) = k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X2),X4))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_7 ),
    inference(backward_demodulation,[],[f85,f101])).

fof(f101,plain,
    ( ! [X2] : k4_xboole_0(X2,X2) = k5_xboole_0(X2,X2)
    | ~ spl2_3
    | ~ spl2_7 ),
    inference(superposition,[],[f49,f96])).

fof(f85,plain,
    ( ! [X4,X2] : k5_xboole_0(X2,X4) = k5_xboole_0(X2,k5_xboole_0(k4_xboole_0(X2,X2),X4))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(forward_demodulation,[],[f80,f77])).

fof(f77,plain,
    ( ! [X2,X3] : k4_xboole_0(X2,k4_xboole_0(X3,X2)) = X2
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(superposition,[],[f57,f49])).

fof(f57,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = X0
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f56])).

fof(f80,plain,
    ( ! [X4,X2,X3] : k5_xboole_0(X2,k5_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,X2))),X4)) = k5_xboole_0(X2,X4)
    | ~ spl2_2
    | ~ spl2_5 ),
    inference(superposition,[],[f45,f57])).

fof(f226,plain,
    ( spl2_17
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f71,f52,f48,f224])).

fof(f71,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(superposition,[],[f49,f53])).

fof(f222,plain,
    ( spl2_16
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f62,f44,f40,f220])).

fof(f62,plain,
    ( ! [X4,X5,X3] : k5_xboole_0(X3,k5_xboole_0(X4,X5)) = k5_xboole_0(X5,k5_xboole_0(X3,X4))
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(superposition,[],[f45,f41])).

fof(f218,plain,
    ( spl2_15
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f59,f44,f40,f216])).

fof(f59,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X1,X0),X2)
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(superposition,[],[f45,f41])).

fof(f164,plain,
    ( spl2_13
    | ~ spl2_7
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f135,f131,f95,f162])).

fof(f135,plain,
    ( ! [X0] : k5_xboole_0(X0,X0) = k4_xboole_0(k5_xboole_0(X0,X0),X0)
    | ~ spl2_7
    | ~ spl2_10 ),
    inference(superposition,[],[f96,f132])).

fof(f160,plain,
    ( spl2_12
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f83,f56,f48,f158])).

fof(f83,plain,
    ( ! [X0,X1] : k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(backward_demodulation,[],[f33,f77])).

fof(f33,plain,(
    ! [X0,X1] : k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = X0 ),
    inference(definition_unfolding,[],[f24,f21,f23])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f141,plain,
    ( spl2_11
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f100,f95,f139])).

fof(f100,plain,
    ( ! [X4,X5] : k4_xboole_0(X5,X4) = k4_xboole_0(k4_xboole_0(X5,X4),X4)
    | ~ spl2_7 ),
    inference(superposition,[],[f96,f96])).

fof(f133,plain,
    ( spl2_10
    | ~ spl2_7
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f128,f125,f95,f131])).

fof(f125,plain,
    ( spl2_9
  <=> ! [X2] : k4_xboole_0(X2,X2) = k5_xboole_0(X2,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f128,plain,
    ( ! [X0] : k4_xboole_0(X0,k5_xboole_0(X0,X0)) = X0
    | ~ spl2_7
    | ~ spl2_9 ),
    inference(superposition,[],[f96,f126])).

fof(f126,plain,
    ( ! [X2] : k4_xboole_0(X2,X2) = k5_xboole_0(X2,X2)
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f125])).

fof(f127,plain,
    ( spl2_9
    | ~ spl2_3
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f101,f95,f48,f125])).

fof(f114,plain,
    ( spl2_8
    | ~ spl2_3
    | ~ spl2_6
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f104,f95,f88,f48,f112])).

fof(f88,plain,
    ( spl2_6
  <=> ! [X0] : k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f104,plain,
    ( ! [X0] : k5_xboole_0(X0,k5_xboole_0(X0,X0)) = X0
    | ~ spl2_3
    | ~ spl2_6
    | ~ spl2_7 ),
    inference(backward_demodulation,[],[f89,f101])).

fof(f89,plain,
    ( ! [X0] : k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f88])).

fof(f97,plain,
    ( spl2_7
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f77,f56,f48,f95])).

fof(f90,plain,
    ( spl2_6
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f82,f56,f48,f88])).

fof(f82,plain,
    ( ! [X0] : k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(backward_demodulation,[],[f57,f77])).

fof(f58,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f37,f56])).

fof(f37,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = X0 ),
    inference(backward_demodulation,[],[f32,f34])).

fof(f32,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = X0 ),
    inference(definition_unfolding,[],[f20,f21,f23])).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f54,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f31,f52])).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f19,f23,f23])).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f50,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f29,f48])).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f22,f23])).

fof(f22,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f46,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f25,f44])).

fof(f25,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f42,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f18,f40])).

fof(f18,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 09:47:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.44  % (4077)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.47  % (4078)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.48  % (4076)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.48  % (4080)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.48  % (4083)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.49  % (4087)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.49  % (4090)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.49  % (4079)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.49  % (4082)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.49  % (4091)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.50  % (4081)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.50  % (4085)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.50  % (4093)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.50  % (4086)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.50  % (4089)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.51  % (4088)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.51  % (4088)Refutation not found, incomplete strategy% (4088)------------------------------
% 0.22/0.51  % (4088)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (4094)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.52  % (4088)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (4088)Memory used [KB]: 10490
% 0.22/0.52  % (4088)Time elapsed: 0.099 s
% 0.22/0.52  % (4088)------------------------------
% 0.22/0.52  % (4088)------------------------------
% 0.22/0.52  % (4092)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 5.18/1.03  % (4080)Time limit reached!
% 5.18/1.03  % (4080)------------------------------
% 5.18/1.03  % (4080)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.18/1.03  % (4080)Termination reason: Time limit
% 5.18/1.03  % (4080)Termination phase: Saturation
% 5.18/1.03  
% 5.18/1.03  % (4080)Memory used [KB]: 16375
% 5.18/1.03  % (4080)Time elapsed: 0.600 s
% 5.18/1.03  % (4080)------------------------------
% 5.18/1.03  % (4080)------------------------------
% 12.43/1.92  % (4082)Time limit reached!
% 12.43/1.92  % (4082)------------------------------
% 12.43/1.92  % (4082)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.43/1.92  % (4082)Termination reason: Time limit
% 12.43/1.92  % (4082)Termination phase: Saturation
% 12.43/1.92  
% 12.43/1.92  % (4082)Memory used [KB]: 45415
% 12.43/1.92  % (4082)Time elapsed: 1.500 s
% 12.43/1.92  % (4082)------------------------------
% 12.43/1.92  % (4082)------------------------------
% 12.43/1.95  % (4081)Time limit reached!
% 12.43/1.95  % (4081)------------------------------
% 12.43/1.95  % (4081)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.43/1.95  % (4081)Termination reason: Time limit
% 12.43/1.95  % (4081)Termination phase: Saturation
% 12.43/1.95  
% 12.43/1.95  % (4081)Memory used [KB]: 43496
% 12.43/1.95  % (4081)Time elapsed: 1.500 s
% 12.43/1.95  % (4081)------------------------------
% 12.43/1.95  % (4081)------------------------------
% 14.83/2.23  % (4078)Time limit reached!
% 14.83/2.23  % (4078)------------------------------
% 14.83/2.23  % (4078)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.83/2.23  % (4078)Termination reason: Time limit
% 14.83/2.23  % (4078)Termination phase: Saturation
% 14.83/2.23  
% 14.83/2.23  % (4078)Memory used [KB]: 42856
% 14.83/2.23  % (4078)Time elapsed: 1.800 s
% 14.83/2.23  % (4078)------------------------------
% 14.83/2.23  % (4078)------------------------------
% 17.79/2.61  % (4089)Time limit reached!
% 17.79/2.61  % (4089)------------------------------
% 17.79/2.61  % (4089)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.79/2.61  % (4089)Termination reason: Time limit
% 17.79/2.61  % (4089)Termination phase: Saturation
% 17.79/2.61  
% 17.79/2.61  % (4089)Memory used [KB]: 66779
% 17.79/2.61  % (4089)Time elapsed: 2.200 s
% 17.79/2.61  % (4089)------------------------------
% 17.79/2.61  % (4089)------------------------------
% 34.64/4.74  % (4083)Refutation found. Thanks to Tanya!
% 34.64/4.74  % SZS status Theorem for theBenchmark
% 34.64/4.74  % SZS output start Proof for theBenchmark
% 34.64/4.74  fof(f67823,plain,(
% 34.64/4.74    $false),
% 34.64/4.74    inference(avatar_sat_refutation,[],[f42,f46,f50,f54,f58,f90,f97,f114,f127,f133,f141,f160,f164,f218,f222,f226,f230,f234,f514,f518,f522,f527,f535,f543,f555,f1427,f1431,f1498,f1502,f1919,f1923,f2169,f2322,f2326,f2498,f2502,f2511,f2926,f2987,f2991,f3055,f3619,f3780,f3820,f3844,f5942,f6091,f6722,f6730,f6742,f6770,f6774,f6838,f16709,f17356,f17360,f17372,f26830,f27273,f31522,f34115,f46987,f62433,f64735,f67768])).
% 34.64/4.74  fof(f67768,plain,(
% 34.64/4.74    ~spl2_2 | ~spl2_3 | ~spl2_17 | ~spl2_21 | ~spl2_28 | ~spl2_34 | spl2_47 | ~spl2_162 | ~spl2_222),
% 34.64/4.74    inference(avatar_contradiction_clause,[],[f67767])).
% 34.64/4.74  fof(f67767,plain,(
% 34.64/4.74    $false | (~spl2_2 | ~spl2_3 | ~spl2_17 | ~spl2_21 | ~spl2_28 | ~spl2_34 | spl2_47 | ~spl2_162 | ~spl2_222)),
% 34.64/4.74    inference(subsumption_resolution,[],[f2510,f67766])).
% 34.64/4.74  fof(f67766,plain,(
% 34.64/4.74    ( ! [X180,X179] : (k5_xboole_0(X179,X180) = k4_xboole_0(k5_xboole_0(X179,k4_xboole_0(X180,X179)),k5_xboole_0(X179,k4_xboole_0(X179,X180)))) ) | (~spl2_2 | ~spl2_3 | ~spl2_17 | ~spl2_21 | ~spl2_28 | ~spl2_34 | ~spl2_162 | ~spl2_222)),
% 34.64/4.74    inference(forward_demodulation,[],[f67356,f67572])).
% 34.64/4.74  fof(f67572,plain,(
% 34.64/4.74    ( ! [X52,X53] : (k5_xboole_0(X52,k4_xboole_0(X52,X53)) = k4_xboole_0(X52,k5_xboole_0(X52,X53))) ) | (~spl2_2 | ~spl2_3 | ~spl2_17 | ~spl2_21 | ~spl2_28 | ~spl2_34 | ~spl2_222)),
% 34.64/4.74    inference(forward_demodulation,[],[f67571,f1314])).
% 34.64/4.74  fof(f1314,plain,(
% 34.64/4.74    ( ! [X10,X11,X9] : (k5_xboole_0(X11,k4_xboole_0(X9,X10)) = k5_xboole_0(X9,k5_xboole_0(X11,k5_xboole_0(X10,k4_xboole_0(X10,X9))))) ) | (~spl2_3 | ~spl2_17 | ~spl2_21 | ~spl2_28)),
% 34.64/4.74    inference(backward_demodulation,[],[f563,f1251])).
% 34.64/4.74  fof(f1251,plain,(
% 34.64/4.74    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k5_xboole_0(X0,k4_xboole_0(X0,X1))) ) | (~spl2_3 | ~spl2_28)),
% 34.64/4.74    inference(superposition,[],[f542,f49])).
% 34.64/4.74  fof(f49,plain,(
% 34.64/4.74    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ) | ~spl2_3),
% 34.64/4.74    inference(avatar_component_clause,[],[f48])).
% 34.64/4.74  fof(f48,plain,(
% 34.64/4.74    spl2_3 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),
% 34.64/4.74    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 34.64/4.74  fof(f542,plain,(
% 34.64/4.74    ( ! [X4,X5] : (k4_xboole_0(X4,X5) = k5_xboole_0(X4,k5_xboole_0(X4,k4_xboole_0(X4,X5)))) ) | ~spl2_28),
% 34.64/4.74    inference(avatar_component_clause,[],[f541])).
% 34.64/4.74  fof(f541,plain,(
% 34.64/4.74    spl2_28 <=> ! [X5,X4] : k4_xboole_0(X4,X5) = k5_xboole_0(X4,k5_xboole_0(X4,k4_xboole_0(X4,X5)))),
% 34.64/4.74    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).
% 34.64/4.74  fof(f563,plain,(
% 34.64/4.74    ( ! [X10,X11,X9] : (k5_xboole_0(X9,k5_xboole_0(X11,k4_xboole_0(X10,k4_xboole_0(X10,X9)))) = k5_xboole_0(X11,k4_xboole_0(X9,X10))) ) | (~spl2_17 | ~spl2_21)),
% 34.64/4.74    inference(superposition,[],[f513,f225])).
% 34.64/4.74  fof(f225,plain,(
% 34.64/4.74    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ) | ~spl2_17),
% 34.64/4.74    inference(avatar_component_clause,[],[f224])).
% 34.64/4.74  fof(f224,plain,(
% 34.64/4.74    spl2_17 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))),
% 34.64/4.74    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 34.64/4.74  fof(f513,plain,(
% 34.64/4.74    ( ! [X4,X5,X3] : (k5_xboole_0(X3,k5_xboole_0(X4,X5)) = k5_xboole_0(X4,k5_xboole_0(X3,X5))) ) | ~spl2_21),
% 34.64/4.74    inference(avatar_component_clause,[],[f512])).
% 34.64/4.74  fof(f512,plain,(
% 34.64/4.74    spl2_21 <=> ! [X3,X5,X4] : k5_xboole_0(X3,k5_xboole_0(X4,X5)) = k5_xboole_0(X4,k5_xboole_0(X3,X5))),
% 34.64/4.74    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 34.64/4.74  fof(f67571,plain,(
% 34.64/4.74    ( ! [X52,X53] : (k4_xboole_0(X52,k5_xboole_0(X52,X53)) = k5_xboole_0(X52,k5_xboole_0(X52,k5_xboole_0(X53,k4_xboole_0(X53,X52))))) ) | (~spl2_2 | ~spl2_34 | ~spl2_222)),
% 34.64/4.74    inference(forward_demodulation,[],[f67305,f45])).
% 34.64/4.74  fof(f45,plain,(
% 34.64/4.74    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) ) | ~spl2_2),
% 34.64/4.74    inference(avatar_component_clause,[],[f44])).
% 34.64/4.74  fof(f44,plain,(
% 34.64/4.74    spl2_2 <=> ! [X1,X0,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 34.64/4.74    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 34.64/4.74  fof(f67305,plain,(
% 34.64/4.74    ( ! [X52,X53] : (k4_xboole_0(X52,k5_xboole_0(X52,X53)) = k5_xboole_0(X52,k5_xboole_0(k5_xboole_0(X52,X53),k4_xboole_0(X53,X52)))) ) | (~spl2_34 | ~spl2_222)),
% 34.64/4.74    inference(superposition,[],[f1426,f64734])).
% 34.64/4.74  fof(f64734,plain,(
% 34.64/4.74    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k5_xboole_0(X1,X0),X1)) ) | ~spl2_222),
% 34.64/4.74    inference(avatar_component_clause,[],[f64733])).
% 34.64/4.74  fof(f64733,plain,(
% 34.64/4.74    spl2_222 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(k5_xboole_0(X1,X0),X1)),
% 34.64/4.74    introduced(avatar_definition,[new_symbols(naming,[spl2_222])])).
% 34.64/4.74  fof(f1426,plain,(
% 34.64/4.74    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,X0)))) ) | ~spl2_34),
% 34.64/4.74    inference(avatar_component_clause,[],[f1425])).
% 34.64/4.74  fof(f1425,plain,(
% 34.64/4.74    spl2_34 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,X0)))),
% 34.64/4.74    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).
% 34.64/4.74  fof(f67356,plain,(
% 34.64/4.74    ( ! [X180,X179] : (k5_xboole_0(X179,X180) = k4_xboole_0(k5_xboole_0(X179,k4_xboole_0(X180,X179)),k4_xboole_0(X179,k5_xboole_0(X179,X180)))) ) | (~spl2_162 | ~spl2_222)),
% 34.64/4.74    inference(superposition,[],[f34114,f64734])).
% 34.64/4.74  fof(f34114,plain,(
% 34.64/4.74    ( ! [X6,X5] : (k4_xboole_0(k5_xboole_0(X5,k4_xboole_0(X6,X5)),k4_xboole_0(X5,X6)) = X6) ) | ~spl2_162),
% 34.64/4.74    inference(avatar_component_clause,[],[f34113])).
% 34.64/4.74  fof(f34113,plain,(
% 34.64/4.74    spl2_162 <=> ! [X5,X6] : k4_xboole_0(k5_xboole_0(X5,k4_xboole_0(X6,X5)),k4_xboole_0(X5,X6)) = X6),
% 34.64/4.74    introduced(avatar_definition,[new_symbols(naming,[spl2_162])])).
% 34.64/4.74  fof(f2510,plain,(
% 34.64/4.74    k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl2_47),
% 34.64/4.74    inference(avatar_component_clause,[],[f2508])).
% 34.64/4.74  fof(f2508,plain,(
% 34.64/4.74    spl2_47 <=> k5_xboole_0(sK0,sK1) = k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 34.64/4.74    introduced(avatar_definition,[new_symbols(naming,[spl2_47])])).
% 34.64/4.74  fof(f64735,plain,(
% 34.64/4.74    spl2_222 | ~spl2_135 | ~spl2_220),
% 34.64/4.74    inference(avatar_split_clause,[],[f63901,f62431,f16707,f64733])).
% 34.64/4.74  fof(f16707,plain,(
% 34.64/4.74    spl2_135 <=> ! [X38,X39] : k5_xboole_0(X39,X38) = k5_xboole_0(k4_xboole_0(X38,X39),k4_xboole_0(X39,X38))),
% 34.64/4.74    introduced(avatar_definition,[new_symbols(naming,[spl2_135])])).
% 34.64/4.74  fof(f62431,plain,(
% 34.64/4.74    spl2_220 <=> ! [X29,X28,X30] : k4_xboole_0(X30,X28) = k4_xboole_0(k5_xboole_0(k4_xboole_0(X30,X28),k4_xboole_0(X28,X29)),X28)),
% 34.64/4.74    introduced(avatar_definition,[new_symbols(naming,[spl2_220])])).
% 34.64/4.74  fof(f63901,plain,(
% 34.64/4.74    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k5_xboole_0(X1,X0),X1)) ) | (~spl2_135 | ~spl2_220)),
% 34.64/4.74    inference(superposition,[],[f62432,f16708])).
% 34.64/4.74  fof(f16708,plain,(
% 34.64/4.74    ( ! [X39,X38] : (k5_xboole_0(X39,X38) = k5_xboole_0(k4_xboole_0(X38,X39),k4_xboole_0(X39,X38))) ) | ~spl2_135),
% 34.64/4.74    inference(avatar_component_clause,[],[f16707])).
% 34.64/4.74  fof(f62432,plain,(
% 34.64/4.74    ( ! [X30,X28,X29] : (k4_xboole_0(X30,X28) = k4_xboole_0(k5_xboole_0(k4_xboole_0(X30,X28),k4_xboole_0(X28,X29)),X28)) ) | ~spl2_220),
% 34.64/4.74    inference(avatar_component_clause,[],[f62431])).
% 34.64/4.74  fof(f62433,plain,(
% 34.64/4.74    spl2_220 | ~spl2_11 | ~spl2_141 | ~spl2_185),
% 34.64/4.74    inference(avatar_split_clause,[],[f47772,f46985,f17370,f139,f62431])).
% 34.64/4.74  fof(f139,plain,(
% 34.64/4.74    spl2_11 <=> ! [X5,X4] : k4_xboole_0(X5,X4) = k4_xboole_0(k4_xboole_0(X5,X4),X4)),
% 34.64/4.74    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 34.64/4.74  fof(f17370,plain,(
% 34.64/4.74    spl2_141 <=> ! [X29,X28,X30] : k4_xboole_0(X29,X30) = k4_xboole_0(k4_xboole_0(X29,X30),k4_xboole_0(X28,X29))),
% 34.64/4.74    introduced(avatar_definition,[new_symbols(naming,[spl2_141])])).
% 34.64/4.74  fof(f46985,plain,(
% 34.64/4.74    spl2_185 <=> ! [X49,X51,X50] : k4_xboole_0(k5_xboole_0(X51,k4_xboole_0(k4_xboole_0(X49,X50),X51)),X49) = k4_xboole_0(X51,X49)),
% 34.64/4.74    introduced(avatar_definition,[new_symbols(naming,[spl2_185])])).
% 34.64/4.74  fof(f47772,plain,(
% 34.64/4.74    ( ! [X30,X28,X29] : (k4_xboole_0(X30,X28) = k4_xboole_0(k5_xboole_0(k4_xboole_0(X30,X28),k4_xboole_0(X28,X29)),X28)) ) | (~spl2_11 | ~spl2_141 | ~spl2_185)),
% 34.64/4.74    inference(forward_demodulation,[],[f47552,f140])).
% 34.64/4.74  fof(f140,plain,(
% 34.64/4.74    ( ! [X4,X5] : (k4_xboole_0(X5,X4) = k4_xboole_0(k4_xboole_0(X5,X4),X4)) ) | ~spl2_11),
% 34.64/4.74    inference(avatar_component_clause,[],[f139])).
% 34.64/4.74  fof(f47552,plain,(
% 34.64/4.74    ( ! [X30,X28,X29] : (k4_xboole_0(k4_xboole_0(X30,X28),X28) = k4_xboole_0(k5_xboole_0(k4_xboole_0(X30,X28),k4_xboole_0(X28,X29)),X28)) ) | (~spl2_141 | ~spl2_185)),
% 34.64/4.74    inference(superposition,[],[f46986,f17371])).
% 34.64/4.74  fof(f17371,plain,(
% 34.64/4.74    ( ! [X30,X28,X29] : (k4_xboole_0(X29,X30) = k4_xboole_0(k4_xboole_0(X29,X30),k4_xboole_0(X28,X29))) ) | ~spl2_141),
% 34.64/4.74    inference(avatar_component_clause,[],[f17370])).
% 34.64/4.74  fof(f46986,plain,(
% 34.64/4.74    ( ! [X50,X51,X49] : (k4_xboole_0(k5_xboole_0(X51,k4_xboole_0(k4_xboole_0(X49,X50),X51)),X49) = k4_xboole_0(X51,X49)) ) | ~spl2_185),
% 34.64/4.74    inference(avatar_component_clause,[],[f46985])).
% 34.64/4.74  fof(f46987,plain,(
% 34.64/4.74    spl2_185 | ~spl2_37 | ~spl2_41 | ~spl2_49 | ~spl2_103),
% 34.64/4.74    inference(avatar_split_clause,[],[f7827,f6772,f2985,f2320,f1500,f46985])).
% 34.64/4.74  fof(f1500,plain,(
% 34.64/4.74    spl2_37 <=> ! [X1,X0] : k4_xboole_0(k4_xboole_0(X0,X1),X0) = k5_xboole_0(X0,X0)),
% 34.64/4.74    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).
% 34.64/4.74  fof(f2320,plain,(
% 34.64/4.74    spl2_41 <=> ! [X22,X23] : k5_xboole_0(X23,k5_xboole_0(X22,X22)) = X23),
% 34.64/4.74    introduced(avatar_definition,[new_symbols(naming,[spl2_41])])).
% 34.64/4.74  fof(f2985,plain,(
% 34.64/4.74    spl2_49 <=> ! [X5,X4] : k5_xboole_0(X5,X5) = k4_xboole_0(k5_xboole_0(X5,X5),X4)),
% 34.64/4.74    introduced(avatar_definition,[new_symbols(naming,[spl2_49])])).
% 34.64/4.74  fof(f6772,plain,(
% 34.64/4.74    spl2_103 <=> ! [X1,X0,X2] : k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X2) = k5_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X0,X2)))),
% 34.64/4.74    introduced(avatar_definition,[new_symbols(naming,[spl2_103])])).
% 34.64/4.74  fof(f7827,plain,(
% 34.64/4.74    ( ! [X50,X51,X49] : (k4_xboole_0(k5_xboole_0(X51,k4_xboole_0(k4_xboole_0(X49,X50),X51)),X49) = k4_xboole_0(X51,X49)) ) | (~spl2_37 | ~spl2_41 | ~spl2_49 | ~spl2_103)),
% 34.64/4.74    inference(forward_demodulation,[],[f7826,f2321])).
% 34.64/4.74  fof(f2321,plain,(
% 34.64/4.74    ( ! [X23,X22] : (k5_xboole_0(X23,k5_xboole_0(X22,X22)) = X23) ) | ~spl2_41),
% 34.64/4.74    inference(avatar_component_clause,[],[f2320])).
% 34.64/4.74  fof(f7826,plain,(
% 34.64/4.74    ( ! [X50,X51,X49] : (k4_xboole_0(k5_xboole_0(X51,k4_xboole_0(k4_xboole_0(X49,X50),X51)),X49) = k5_xboole_0(k4_xboole_0(X51,X49),k5_xboole_0(X49,X49))) ) | (~spl2_37 | ~spl2_49 | ~spl2_103)),
% 34.64/4.74    inference(forward_demodulation,[],[f7721,f2986])).
% 34.64/4.74  fof(f2986,plain,(
% 34.64/4.74    ( ! [X4,X5] : (k5_xboole_0(X5,X5) = k4_xboole_0(k5_xboole_0(X5,X5),X4)) ) | ~spl2_49),
% 34.64/4.74    inference(avatar_component_clause,[],[f2985])).
% 34.64/4.74  fof(f7721,plain,(
% 34.64/4.74    ( ! [X50,X51,X49] : (k4_xboole_0(k5_xboole_0(X51,k4_xboole_0(k4_xboole_0(X49,X50),X51)),X49) = k5_xboole_0(k4_xboole_0(X51,X49),k4_xboole_0(k5_xboole_0(X49,X49),k4_xboole_0(X51,X49)))) ) | (~spl2_37 | ~spl2_103)),
% 34.64/4.74    inference(superposition,[],[f6773,f1501])).
% 34.64/4.74  fof(f1501,plain,(
% 34.64/4.74    ( ! [X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X0) = k5_xboole_0(X0,X0)) ) | ~spl2_37),
% 34.64/4.74    inference(avatar_component_clause,[],[f1500])).
% 34.64/4.74  fof(f6773,plain,(
% 34.64/4.74    ( ! [X2,X0,X1] : (k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X2) = k5_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X0,X2)))) ) | ~spl2_103),
% 34.64/4.74    inference(avatar_component_clause,[],[f6772])).
% 34.64/4.74  fof(f34115,plain,(
% 34.64/4.74    spl2_162 | ~spl2_1 | ~spl2_4 | ~spl2_48 | ~spl2_137 | ~spl2_153 | ~spl2_155),
% 34.64/4.74    inference(avatar_split_clause,[],[f31737,f31520,f27271,f17354,f2924,f52,f40,f34113])).
% 34.64/4.74  fof(f40,plain,(
% 34.64/4.74    spl2_1 <=> ! [X1,X0] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 34.64/4.74    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 34.64/4.74  fof(f52,plain,(
% 34.64/4.74    spl2_4 <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))),
% 34.64/4.74    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 34.64/4.74  fof(f2924,plain,(
% 34.64/4.74    spl2_48 <=> ! [X3,X2] : k4_xboole_0(X2,k5_xboole_0(X3,X3)) = X2),
% 34.64/4.74    introduced(avatar_definition,[new_symbols(naming,[spl2_48])])).
% 34.64/4.74  fof(f17354,plain,(
% 34.64/4.74    spl2_137 <=> ! [X117,X116] : k5_xboole_0(k4_xboole_0(X116,X117),X117) = k5_xboole_0(k4_xboole_0(X117,X116),X116)),
% 34.64/4.74    introduced(avatar_definition,[new_symbols(naming,[spl2_137])])).
% 34.64/4.74  fof(f27271,plain,(
% 34.64/4.74    spl2_153 <=> ! [X63,X64] : k5_xboole_0(X63,X63) = k4_xboole_0(k5_xboole_0(X64,X63),k5_xboole_0(X63,X64))),
% 34.64/4.74    introduced(avatar_definition,[new_symbols(naming,[spl2_153])])).
% 34.64/4.74  fof(f31520,plain,(
% 34.64/4.74    spl2_155 <=> ! [X22,X19] : k4_xboole_0(k5_xboole_0(X22,k4_xboole_0(X19,X22)),X19) = k4_xboole_0(X22,X19)),
% 34.64/4.74    introduced(avatar_definition,[new_symbols(naming,[spl2_155])])).
% 34.64/4.74  fof(f31737,plain,(
% 34.64/4.74    ( ! [X6,X5] : (k4_xboole_0(k5_xboole_0(X5,k4_xboole_0(X6,X5)),k4_xboole_0(X5,X6)) = X6) ) | (~spl2_1 | ~spl2_4 | ~spl2_48 | ~spl2_137 | ~spl2_153 | ~spl2_155)),
% 34.64/4.74    inference(forward_demodulation,[],[f31736,f2925])).
% 34.64/4.74  fof(f2925,plain,(
% 34.64/4.74    ( ! [X2,X3] : (k4_xboole_0(X2,k5_xboole_0(X3,X3)) = X2) ) | ~spl2_48),
% 34.64/4.74    inference(avatar_component_clause,[],[f2924])).
% 34.64/4.74  fof(f31736,plain,(
% 34.64/4.74    ( ! [X6,X5] : (k4_xboole_0(X6,k5_xboole_0(X5,X5)) = k4_xboole_0(k5_xboole_0(X5,k4_xboole_0(X6,X5)),k4_xboole_0(X5,X6))) ) | (~spl2_1 | ~spl2_4 | ~spl2_137 | ~spl2_153 | ~spl2_155)),
% 34.64/4.74    inference(forward_demodulation,[],[f31593,f31717])).
% 34.64/4.74  fof(f31717,plain,(
% 34.64/4.74    ( ! [X80,X79] : (k5_xboole_0(X79,X79) = k4_xboole_0(X80,k5_xboole_0(X79,k4_xboole_0(X80,X79)))) ) | (~spl2_1 | ~spl2_137 | ~spl2_153 | ~spl2_155)),
% 34.64/4.74    inference(forward_demodulation,[],[f31572,f31195])).
% 34.64/4.74  fof(f31195,plain,(
% 34.64/4.74    ( ! [X218,X219] : (k5_xboole_0(X219,X219) = k4_xboole_0(k5_xboole_0(X218,k4_xboole_0(X219,X218)),k5_xboole_0(X219,k4_xboole_0(X218,X219)))) ) | (~spl2_1 | ~spl2_137 | ~spl2_153)),
% 34.64/4.74    inference(forward_demodulation,[],[f30842,f41])).
% 34.64/4.74  fof(f41,plain,(
% 34.64/4.74    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) ) | ~spl2_1),
% 34.64/4.74    inference(avatar_component_clause,[],[f40])).
% 34.64/4.74  fof(f30842,plain,(
% 34.64/4.74    ( ! [X218,X219] : (k5_xboole_0(X219,X219) = k4_xboole_0(k5_xboole_0(k4_xboole_0(X219,X218),X218),k5_xboole_0(X219,k4_xboole_0(X218,X219)))) ) | (~spl2_137 | ~spl2_153)),
% 34.64/4.74    inference(superposition,[],[f27272,f17355])).
% 34.64/4.74  fof(f17355,plain,(
% 34.64/4.74    ( ! [X116,X117] : (k5_xboole_0(k4_xboole_0(X116,X117),X117) = k5_xboole_0(k4_xboole_0(X117,X116),X116)) ) | ~spl2_137),
% 34.64/4.74    inference(avatar_component_clause,[],[f17354])).
% 34.64/4.74  fof(f27272,plain,(
% 34.64/4.74    ( ! [X64,X63] : (k5_xboole_0(X63,X63) = k4_xboole_0(k5_xboole_0(X64,X63),k5_xboole_0(X63,X64))) ) | ~spl2_153),
% 34.64/4.74    inference(avatar_component_clause,[],[f27271])).
% 34.64/4.74  fof(f31572,plain,(
% 34.64/4.74    ( ! [X80,X79] : (k4_xboole_0(X80,k5_xboole_0(X79,k4_xboole_0(X80,X79))) = k4_xboole_0(k5_xboole_0(X80,k4_xboole_0(X79,X80)),k5_xboole_0(X79,k4_xboole_0(X80,X79)))) ) | ~spl2_155),
% 34.64/4.74    inference(superposition,[],[f31521,f31521])).
% 34.64/4.74  fof(f31521,plain,(
% 34.64/4.74    ( ! [X19,X22] : (k4_xboole_0(k5_xboole_0(X22,k4_xboole_0(X19,X22)),X19) = k4_xboole_0(X22,X19)) ) | ~spl2_155),
% 34.64/4.74    inference(avatar_component_clause,[],[f31520])).
% 34.64/4.74  fof(f31593,plain,(
% 34.64/4.74    ( ! [X6,X5] : (k4_xboole_0(X6,k4_xboole_0(X6,k5_xboole_0(X5,k4_xboole_0(X6,X5)))) = k4_xboole_0(k5_xboole_0(X5,k4_xboole_0(X6,X5)),k4_xboole_0(X5,X6))) ) | (~spl2_4 | ~spl2_155)),
% 34.64/4.74    inference(superposition,[],[f53,f31521])).
% 34.64/4.74  fof(f53,plain,(
% 34.64/4.74    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) ) | ~spl2_4),
% 34.64/4.74    inference(avatar_component_clause,[],[f52])).
% 34.64/4.74  fof(f31522,plain,(
% 34.64/4.74    spl2_155 | ~spl2_41 | ~spl2_49 | ~spl2_54 | ~spl2_103),
% 34.64/4.74    inference(avatar_split_clause,[],[f7812,f6772,f3617,f2985,f2320,f31520])).
% 34.64/4.74  fof(f3617,plain,(
% 34.64/4.74    spl2_54 <=> ! [X27,X29,X28] : k4_xboole_0(X28,X28) = k4_xboole_0(k5_xboole_0(X29,X29),X27)),
% 34.64/4.74    introduced(avatar_definition,[new_symbols(naming,[spl2_54])])).
% 34.64/4.74  fof(f7812,plain,(
% 34.64/4.74    ( ! [X19,X22] : (k4_xboole_0(k5_xboole_0(X22,k4_xboole_0(X19,X22)),X19) = k4_xboole_0(X22,X19)) ) | (~spl2_41 | ~spl2_49 | ~spl2_54 | ~spl2_103)),
% 34.64/4.74    inference(forward_demodulation,[],[f7811,f2321])).
% 34.64/4.74  fof(f7811,plain,(
% 34.64/4.74    ( ! [X19,X22,X20] : (k4_xboole_0(k5_xboole_0(X22,k4_xboole_0(X19,X22)),X19) = k5_xboole_0(k4_xboole_0(X22,X19),k5_xboole_0(X20,X20))) ) | (~spl2_49 | ~spl2_54 | ~spl2_103)),
% 34.64/4.74    inference(forward_demodulation,[],[f7810,f2986])).
% 34.64/4.74  fof(f7810,plain,(
% 34.64/4.74    ( ! [X19,X22,X20] : (k4_xboole_0(k5_xboole_0(X22,k4_xboole_0(X19,X22)),X19) = k5_xboole_0(k4_xboole_0(X22,X19),k4_xboole_0(k5_xboole_0(X20,X20),k4_xboole_0(X22,X19)))) ) | (~spl2_49 | ~spl2_54 | ~spl2_103)),
% 34.64/4.74    inference(forward_demodulation,[],[f7711,f2986])).
% 34.64/4.74  fof(f7711,plain,(
% 34.64/4.74    ( ! [X21,X19,X22,X20] : (k4_xboole_0(k5_xboole_0(X22,k4_xboole_0(X19,X22)),X19) = k5_xboole_0(k4_xboole_0(X22,X19),k4_xboole_0(k4_xboole_0(k5_xboole_0(X20,X20),X21),k4_xboole_0(X22,X19)))) ) | (~spl2_54 | ~spl2_103)),
% 34.64/4.74    inference(superposition,[],[f6773,f3618])).
% 34.64/4.74  fof(f3618,plain,(
% 34.64/4.74    ( ! [X28,X29,X27] : (k4_xboole_0(X28,X28) = k4_xboole_0(k5_xboole_0(X29,X29),X27)) ) | ~spl2_54),
% 34.64/4.74    inference(avatar_component_clause,[],[f3617])).
% 34.64/4.74  fof(f27273,plain,(
% 34.64/4.74    spl2_153 | ~spl2_16 | ~spl2_37 | ~spl2_61 | ~spl2_90 | ~spl2_148),
% 34.64/4.74    inference(avatar_split_clause,[],[f27168,f26828,f6720,f3778,f1500,f220,f27271])).
% 34.64/4.74  fof(f220,plain,(
% 34.64/4.74    spl2_16 <=> ! [X3,X5,X4] : k5_xboole_0(X3,k5_xboole_0(X4,X5)) = k5_xboole_0(X5,k5_xboole_0(X3,X4))),
% 34.64/4.74    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 34.64/4.74  fof(f3778,plain,(
% 34.64/4.74    spl2_61 <=> ! [X9,X11,X10] : k5_xboole_0(X10,k5_xboole_0(X11,X9)) = k5_xboole_0(X10,k5_xboole_0(X9,X11))),
% 34.64/4.74    introduced(avatar_definition,[new_symbols(naming,[spl2_61])])).
% 34.64/4.74  fof(f6720,plain,(
% 34.64/4.74    spl2_90 <=> ! [X13,X15,X14] : k5_xboole_0(X14,X15) = k5_xboole_0(X13,k5_xboole_0(X15,k5_xboole_0(X14,X13)))),
% 34.64/4.74    introduced(avatar_definition,[new_symbols(naming,[spl2_90])])).
% 34.64/4.74  fof(f26828,plain,(
% 34.64/4.74    spl2_148 <=> ! [X131,X130,X132] : k5_xboole_0(X132,X131) = k4_xboole_0(k5_xboole_0(X131,X132),k5_xboole_0(X130,X130))),
% 34.64/4.74    introduced(avatar_definition,[new_symbols(naming,[spl2_148])])).
% 34.64/4.74  fof(f27168,plain,(
% 34.64/4.74    ( ! [X64,X63] : (k5_xboole_0(X63,X63) = k4_xboole_0(k5_xboole_0(X64,X63),k5_xboole_0(X63,X64))) ) | (~spl2_16 | ~spl2_37 | ~spl2_61 | ~spl2_90 | ~spl2_148)),
% 34.64/4.74    inference(forward_demodulation,[],[f27167,f6721])).
% 34.64/4.74  fof(f6721,plain,(
% 34.64/4.74    ( ! [X14,X15,X13] : (k5_xboole_0(X14,X15) = k5_xboole_0(X13,k5_xboole_0(X15,k5_xboole_0(X14,X13)))) ) | ~spl2_90),
% 34.64/4.74    inference(avatar_component_clause,[],[f6720])).
% 34.64/4.74  fof(f27167,plain,(
% 34.64/4.74    ( ! [X64,X63] : (k5_xboole_0(X64,k5_xboole_0(X63,k5_xboole_0(X63,X64))) = k4_xboole_0(k5_xboole_0(X64,X63),k5_xboole_0(X63,X64))) ) | (~spl2_16 | ~spl2_37 | ~spl2_61 | ~spl2_148)),
% 34.64/4.74    inference(forward_demodulation,[],[f27166,f3779])).
% 34.64/4.74  fof(f3779,plain,(
% 34.64/4.74    ( ! [X10,X11,X9] : (k5_xboole_0(X10,k5_xboole_0(X11,X9)) = k5_xboole_0(X10,k5_xboole_0(X9,X11))) ) | ~spl2_61),
% 34.64/4.74    inference(avatar_component_clause,[],[f3778])).
% 34.64/4.74  fof(f27166,plain,(
% 34.64/4.74    ( ! [X64,X63] : (k5_xboole_0(X64,k5_xboole_0(k5_xboole_0(X63,X64),X63)) = k4_xboole_0(k5_xboole_0(X64,X63),k5_xboole_0(X63,X64))) ) | (~spl2_16 | ~spl2_37 | ~spl2_148)),
% 34.64/4.74    inference(forward_demodulation,[],[f26994,f221])).
% 34.64/4.74  fof(f221,plain,(
% 34.64/4.74    ( ! [X4,X5,X3] : (k5_xboole_0(X3,k5_xboole_0(X4,X5)) = k5_xboole_0(X5,k5_xboole_0(X3,X4))) ) | ~spl2_16),
% 34.64/4.74    inference(avatar_component_clause,[],[f220])).
% 34.64/4.74  fof(f26994,plain,(
% 34.64/4.74    ( ! [X64,X63] : (k5_xboole_0(k5_xboole_0(X63,X64),k5_xboole_0(X63,X64)) = k4_xboole_0(k5_xboole_0(X64,X63),k5_xboole_0(X63,X64))) ) | (~spl2_37 | ~spl2_148)),
% 34.64/4.74    inference(superposition,[],[f1501,f26829])).
% 34.64/4.74  fof(f26829,plain,(
% 34.64/4.74    ( ! [X132,X130,X131] : (k5_xboole_0(X132,X131) = k4_xboole_0(k5_xboole_0(X131,X132),k5_xboole_0(X130,X130))) ) | ~spl2_148),
% 34.64/4.74    inference(avatar_component_clause,[],[f26828])).
% 34.64/4.74  fof(f26830,plain,(
% 34.64/4.74    spl2_148 | ~spl2_41 | ~spl2_49 | ~spl2_102 | ~spl2_138),
% 34.64/4.74    inference(avatar_split_clause,[],[f25869,f17358,f6768,f2985,f2320,f26828])).
% 34.64/4.74  fof(f6768,plain,(
% 34.64/4.74    spl2_102 <=> ! [X42,X44,X43] : k5_xboole_0(X44,X42) = k5_xboole_0(k5_xboole_0(X43,X43),k5_xboole_0(X42,X44))),
% 34.64/4.74    introduced(avatar_definition,[new_symbols(naming,[spl2_102])])).
% 34.64/4.74  fof(f17358,plain,(
% 34.64/4.74    spl2_138 <=> ! [X69,X68] : k4_xboole_0(X69,X68) = k5_xboole_0(k5_xboole_0(X68,X69),k4_xboole_0(X68,X69))),
% 34.64/4.74    introduced(avatar_definition,[new_symbols(naming,[spl2_138])])).
% 34.64/4.74  fof(f25869,plain,(
% 34.64/4.74    ( ! [X132,X130,X131] : (k5_xboole_0(X132,X131) = k4_xboole_0(k5_xboole_0(X131,X132),k5_xboole_0(X130,X130))) ) | (~spl2_41 | ~spl2_49 | ~spl2_102 | ~spl2_138)),
% 34.64/4.74    inference(forward_demodulation,[],[f25868,f2321])).
% 34.64/4.74  fof(f25868,plain,(
% 34.64/4.74    ( ! [X132,X130,X131] : (k4_xboole_0(k5_xboole_0(X131,X132),k5_xboole_0(X130,X130)) = k5_xboole_0(k5_xboole_0(X132,X131),k5_xboole_0(X130,X130))) ) | (~spl2_49 | ~spl2_102 | ~spl2_138)),
% 34.64/4.74    inference(forward_demodulation,[],[f25684,f2986])).
% 34.64/4.74  fof(f25684,plain,(
% 34.64/4.74    ( ! [X132,X130,X131] : (k4_xboole_0(k5_xboole_0(X131,X132),k5_xboole_0(X130,X130)) = k5_xboole_0(k5_xboole_0(X132,X131),k4_xboole_0(k5_xboole_0(X130,X130),k5_xboole_0(X131,X132)))) ) | (~spl2_102 | ~spl2_138)),
% 34.64/4.74    inference(superposition,[],[f17359,f6769])).
% 34.64/4.74  fof(f6769,plain,(
% 34.64/4.74    ( ! [X43,X44,X42] : (k5_xboole_0(X44,X42) = k5_xboole_0(k5_xboole_0(X43,X43),k5_xboole_0(X42,X44))) ) | ~spl2_102),
% 34.64/4.74    inference(avatar_component_clause,[],[f6768])).
% 34.64/4.74  fof(f17359,plain,(
% 34.64/4.74    ( ! [X68,X69] : (k4_xboole_0(X69,X68) = k5_xboole_0(k5_xboole_0(X68,X69),k4_xboole_0(X68,X69))) ) | ~spl2_138),
% 34.64/4.74    inference(avatar_component_clause,[],[f17358])).
% 34.64/4.74  fof(f17372,plain,(
% 34.64/4.74    spl2_141 | ~spl2_7 | ~spl2_119),
% 34.64/4.74    inference(avatar_split_clause,[],[f16568,f6836,f95,f17370])).
% 34.64/4.74  fof(f95,plain,(
% 34.64/4.74    spl2_7 <=> ! [X3,X2] : k4_xboole_0(X2,k4_xboole_0(X3,X2)) = X2),
% 34.64/4.74    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 34.64/4.74  fof(f6836,plain,(
% 34.64/4.74    spl2_119 <=> ! [X13,X12,X14] : k4_xboole_0(X13,X12) = k4_xboole_0(k4_xboole_0(X13,X12),k4_xboole_0(X12,X14))),
% 34.64/4.74    introduced(avatar_definition,[new_symbols(naming,[spl2_119])])).
% 34.64/4.74  fof(f16568,plain,(
% 34.64/4.74    ( ! [X30,X28,X29] : (k4_xboole_0(X29,X30) = k4_xboole_0(k4_xboole_0(X29,X30),k4_xboole_0(X28,X29))) ) | (~spl2_7 | ~spl2_119)),
% 34.64/4.74    inference(superposition,[],[f96,f6837])).
% 34.64/4.74  fof(f6837,plain,(
% 34.64/4.74    ( ! [X14,X12,X13] : (k4_xboole_0(X13,X12) = k4_xboole_0(k4_xboole_0(X13,X12),k4_xboole_0(X12,X14))) ) | ~spl2_119),
% 34.64/4.74    inference(avatar_component_clause,[],[f6836])).
% 34.64/4.74  fof(f96,plain,(
% 34.64/4.74    ( ! [X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X3,X2)) = X2) ) | ~spl2_7),
% 34.64/4.74    inference(avatar_component_clause,[],[f95])).
% 34.64/4.74  fof(f17360,plain,(
% 34.64/4.74    spl2_138 | ~spl2_42 | ~spl2_95),
% 34.64/4.74    inference(avatar_split_clause,[],[f8215,f6740,f2324,f17358])).
% 34.64/4.74  fof(f2324,plain,(
% 34.64/4.74    spl2_42 <=> ! [X49,X48] : k5_xboole_0(k5_xboole_0(X48,X49),X48) = X49),
% 34.64/4.74    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).
% 34.64/4.74  fof(f6740,plain,(
% 34.64/4.74    spl2_95 <=> ! [X36,X35] : k5_xboole_0(X35,X36) = k5_xboole_0(k4_xboole_0(X35,X36),k4_xboole_0(X36,X35))),
% 34.64/4.74    introduced(avatar_definition,[new_symbols(naming,[spl2_95])])).
% 34.64/4.74  fof(f8215,plain,(
% 34.64/4.74    ( ! [X68,X69] : (k4_xboole_0(X69,X68) = k5_xboole_0(k5_xboole_0(X68,X69),k4_xboole_0(X68,X69))) ) | (~spl2_42 | ~spl2_95)),
% 34.64/4.74    inference(superposition,[],[f2325,f6741])).
% 34.64/4.74  fof(f6741,plain,(
% 34.64/4.74    ( ! [X35,X36] : (k5_xboole_0(X35,X36) = k5_xboole_0(k4_xboole_0(X35,X36),k4_xboole_0(X36,X35))) ) | ~spl2_95),
% 34.64/4.74    inference(avatar_component_clause,[],[f6740])).
% 34.64/4.74  fof(f2325,plain,(
% 34.64/4.74    ( ! [X48,X49] : (k5_xboole_0(k5_xboole_0(X48,X49),X48) = X49) ) | ~spl2_42),
% 34.64/4.74    inference(avatar_component_clause,[],[f2324])).
% 34.64/4.74  fof(f17356,plain,(
% 34.64/4.74    spl2_137 | ~spl2_38 | ~spl2_92),
% 34.64/4.74    inference(avatar_split_clause,[],[f7340,f6728,f1917,f17354])).
% 34.64/4.74  fof(f1917,plain,(
% 34.64/4.74    spl2_38 <=> ! [X3,X4] : k5_xboole_0(k4_xboole_0(X4,X3),k5_xboole_0(X3,k4_xboole_0(X3,X4))) = X4),
% 34.64/4.74    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).
% 34.64/4.74  fof(f6728,plain,(
% 34.64/4.74    spl2_92 <=> ! [X25,X27,X26] : k5_xboole_0(X26,X27) = k5_xboole_0(X25,k5_xboole_0(X26,k5_xboole_0(X27,X25)))),
% 34.64/4.74    introduced(avatar_definition,[new_symbols(naming,[spl2_92])])).
% 34.64/4.74  fof(f7340,plain,(
% 34.64/4.74    ( ! [X116,X117] : (k5_xboole_0(k4_xboole_0(X116,X117),X117) = k5_xboole_0(k4_xboole_0(X117,X116),X116)) ) | (~spl2_38 | ~spl2_92)),
% 34.64/4.74    inference(superposition,[],[f6729,f1918])).
% 34.64/4.74  fof(f1918,plain,(
% 34.64/4.74    ( ! [X4,X3] : (k5_xboole_0(k4_xboole_0(X4,X3),k5_xboole_0(X3,k4_xboole_0(X3,X4))) = X4) ) | ~spl2_38),
% 34.64/4.74    inference(avatar_component_clause,[],[f1917])).
% 34.64/4.74  fof(f6729,plain,(
% 34.64/4.74    ( ! [X26,X27,X25] : (k5_xboole_0(X26,X27) = k5_xboole_0(X25,k5_xboole_0(X26,k5_xboole_0(X27,X25)))) ) | ~spl2_92),
% 34.64/4.74    inference(avatar_component_clause,[],[f6728])).
% 34.64/4.74  fof(f16709,plain,(
% 34.64/4.74    spl2_135 | ~spl2_71 | ~spl2_90),
% 34.64/4.74    inference(avatar_split_clause,[],[f6895,f6720,f3818,f16707])).
% 34.64/4.74  fof(f3818,plain,(
% 34.64/4.74    spl2_71 <=> ! [X7,X8] : k4_xboole_0(X7,X8) = k5_xboole_0(X8,k5_xboole_0(X7,k4_xboole_0(X8,X7)))),
% 34.64/4.74    introduced(avatar_definition,[new_symbols(naming,[spl2_71])])).
% 34.64/4.74  fof(f6895,plain,(
% 34.64/4.74    ( ! [X39,X38] : (k5_xboole_0(X39,X38) = k5_xboole_0(k4_xboole_0(X38,X39),k4_xboole_0(X39,X38))) ) | (~spl2_71 | ~spl2_90)),
% 34.64/4.74    inference(superposition,[],[f6721,f3819])).
% 34.64/4.74  fof(f3819,plain,(
% 34.64/4.74    ( ! [X8,X7] : (k4_xboole_0(X7,X8) = k5_xboole_0(X8,k5_xboole_0(X7,k4_xboole_0(X8,X7)))) ) | ~spl2_71),
% 34.64/4.74    inference(avatar_component_clause,[],[f3818])).
% 34.64/4.74  fof(f6838,plain,(
% 34.64/4.74    spl2_119 | ~spl2_7 | ~spl2_88),
% 34.64/4.74    inference(avatar_split_clause,[],[f6096,f6089,f95,f6836])).
% 34.64/4.74  fof(f6089,plain,(
% 34.64/4.74    spl2_88 <=> ! [X29,X28,X30] : k4_xboole_0(X29,k4_xboole_0(k4_xboole_0(X28,X29),X30)) = X29),
% 34.64/4.74    introduced(avatar_definition,[new_symbols(naming,[spl2_88])])).
% 34.64/4.74  fof(f6096,plain,(
% 34.64/4.74    ( ! [X14,X12,X13] : (k4_xboole_0(X13,X12) = k4_xboole_0(k4_xboole_0(X13,X12),k4_xboole_0(X12,X14))) ) | (~spl2_7 | ~spl2_88)),
% 34.64/4.74    inference(superposition,[],[f6090,f96])).
% 34.64/4.74  fof(f6090,plain,(
% 34.64/4.74    ( ! [X30,X28,X29] : (k4_xboole_0(X29,k4_xboole_0(k4_xboole_0(X28,X29),X30)) = X29) ) | ~spl2_88),
% 34.64/4.74    inference(avatar_component_clause,[],[f6089])).
% 34.64/4.74  fof(f6774,plain,(
% 34.64/4.74    spl2_103),
% 34.64/4.74    inference(avatar_split_clause,[],[f36,f6772])).
% 34.64/4.74  fof(f36,plain,(
% 34.64/4.74    ( ! [X2,X0,X1] : (k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X2) = k5_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X0,X2)))) )),
% 34.64/4.74    inference(definition_unfolding,[],[f28,f21,f21])).
% 34.64/4.74  fof(f21,plain,(
% 34.64/4.74    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 34.64/4.74    inference(cnf_transformation,[],[f11])).
% 34.64/4.74  fof(f11,axiom,(
% 34.64/4.74    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 34.64/4.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 34.64/4.74  fof(f28,plain,(
% 34.64/4.74    ( ! [X2,X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))) )),
% 34.64/4.74    inference(cnf_transformation,[],[f6])).
% 34.64/4.74  fof(f6,axiom,(
% 34.64/4.74    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))),
% 34.64/4.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).
% 34.64/4.74  fof(f6770,plain,(
% 34.64/4.74    spl2_102 | ~spl2_22 | ~spl2_41),
% 34.64/4.74    inference(avatar_split_clause,[],[f2369,f2320,f516,f6768])).
% 34.64/4.74  fof(f516,plain,(
% 34.64/4.74    spl2_22 <=> ! [X9,X7,X8] : k5_xboole_0(X9,k5_xboole_0(X7,X8)) = k5_xboole_0(X8,k5_xboole_0(X7,X9))),
% 34.64/4.74    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 34.64/4.74  fof(f2369,plain,(
% 34.64/4.74    ( ! [X43,X44,X42] : (k5_xboole_0(X44,X42) = k5_xboole_0(k5_xboole_0(X43,X43),k5_xboole_0(X42,X44))) ) | (~spl2_22 | ~spl2_41)),
% 34.64/4.74    inference(superposition,[],[f517,f2321])).
% 34.64/4.74  fof(f517,plain,(
% 34.64/4.74    ( ! [X8,X7,X9] : (k5_xboole_0(X9,k5_xboole_0(X7,X8)) = k5_xboole_0(X8,k5_xboole_0(X7,X9))) ) | ~spl2_22),
% 34.64/4.74    inference(avatar_component_clause,[],[f516])).
% 34.64/4.74  fof(f6742,plain,(
% 34.64/4.74    spl2_95 | ~spl2_39 | ~spl2_40),
% 34.64/4.74    inference(avatar_split_clause,[],[f2181,f2167,f1921,f6740])).
% 34.64/4.74  fof(f1921,plain,(
% 34.64/4.74    spl2_39 <=> ! [X7,X8] : k5_xboole_0(X7,k5_xboole_0(k4_xboole_0(X7,X8),k4_xboole_0(X8,X7))) = X8),
% 34.64/4.74    introduced(avatar_definition,[new_symbols(naming,[spl2_39])])).
% 34.64/4.74  fof(f2167,plain,(
% 34.64/4.74    spl2_40 <=> ! [X29,X30] : k5_xboole_0(X29,k5_xboole_0(X29,X30)) = X30),
% 34.64/4.74    introduced(avatar_definition,[new_symbols(naming,[spl2_40])])).
% 34.64/4.74  fof(f2181,plain,(
% 34.64/4.74    ( ! [X35,X36] : (k5_xboole_0(X35,X36) = k5_xboole_0(k4_xboole_0(X35,X36),k4_xboole_0(X36,X35))) ) | (~spl2_39 | ~spl2_40)),
% 34.64/4.74    inference(superposition,[],[f2168,f1922])).
% 34.64/4.74  fof(f1922,plain,(
% 34.64/4.74    ( ! [X8,X7] : (k5_xboole_0(X7,k5_xboole_0(k4_xboole_0(X7,X8),k4_xboole_0(X8,X7))) = X8) ) | ~spl2_39),
% 34.64/4.74    inference(avatar_component_clause,[],[f1921])).
% 34.64/4.74  fof(f2168,plain,(
% 34.64/4.74    ( ! [X30,X29] : (k5_xboole_0(X29,k5_xboole_0(X29,X30)) = X30) ) | ~spl2_40),
% 34.64/4.74    inference(avatar_component_clause,[],[f2167])).
% 34.64/4.74  fof(f6730,plain,(
% 34.64/4.74    spl2_92 | ~spl2_16 | ~spl2_40),
% 34.64/4.74    inference(avatar_split_clause,[],[f2177,f2167,f220,f6728])).
% 34.64/4.74  fof(f2177,plain,(
% 34.64/4.74    ( ! [X26,X27,X25] : (k5_xboole_0(X26,X27) = k5_xboole_0(X25,k5_xboole_0(X26,k5_xboole_0(X27,X25)))) ) | (~spl2_16 | ~spl2_40)),
% 34.64/4.74    inference(superposition,[],[f2168,f221])).
% 34.64/4.74  fof(f6722,plain,(
% 34.64/4.74    spl2_90 | ~spl2_22 | ~spl2_40),
% 34.64/4.74    inference(avatar_split_clause,[],[f2173,f2167,f516,f6720])).
% 34.64/4.74  fof(f2173,plain,(
% 34.64/4.74    ( ! [X14,X15,X13] : (k5_xboole_0(X14,X15) = k5_xboole_0(X13,k5_xboole_0(X15,k5_xboole_0(X14,X13)))) ) | (~spl2_22 | ~spl2_40)),
% 34.64/4.74    inference(superposition,[],[f2168,f517])).
% 34.64/4.74  fof(f6091,plain,(
% 34.64/4.74    spl2_88 | ~spl2_16 | ~spl2_28 | ~spl2_37 | ~spl2_87),
% 34.64/4.74    inference(avatar_split_clause,[],[f6052,f5940,f1500,f541,f220,f6089])).
% 34.64/4.74  fof(f5940,plain,(
% 34.64/4.74    spl2_87 <=> ! [X25,X23,X24] : k4_xboole_0(X25,k5_xboole_0(X23,k4_xboole_0(X23,k4_xboole_0(X24,X25)))) = X25),
% 34.64/4.74    introduced(avatar_definition,[new_symbols(naming,[spl2_87])])).
% 34.64/4.74  fof(f6052,plain,(
% 34.64/4.74    ( ! [X30,X28,X29] : (k4_xboole_0(X29,k4_xboole_0(k4_xboole_0(X28,X29),X30)) = X29) ) | (~spl2_16 | ~spl2_28 | ~spl2_37 | ~spl2_87)),
% 34.64/4.74    inference(forward_demodulation,[],[f6051,f542])).
% 34.64/4.74  fof(f6051,plain,(
% 34.64/4.74    ( ! [X30,X28,X29] : (k4_xboole_0(X29,k5_xboole_0(k4_xboole_0(X28,X29),k5_xboole_0(k4_xboole_0(X28,X29),k4_xboole_0(k4_xboole_0(X28,X29),X30)))) = X29) ) | (~spl2_16 | ~spl2_37 | ~spl2_87)),
% 34.64/4.74    inference(forward_demodulation,[],[f6050,f221])).
% 34.64/4.74  fof(f6050,plain,(
% 34.64/4.74    ( ! [X30,X28,X29] : (k4_xboole_0(X29,k5_xboole_0(k4_xboole_0(X28,X29),k5_xboole_0(k4_xboole_0(k4_xboole_0(X28,X29),X30),k4_xboole_0(X28,X29)))) = X29) ) | (~spl2_16 | ~spl2_37 | ~spl2_87)),
% 34.64/4.74    inference(forward_demodulation,[],[f5977,f221])).
% 34.64/4.74  fof(f5977,plain,(
% 34.64/4.74    ( ! [X30,X28,X29] : (k4_xboole_0(X29,k5_xboole_0(k4_xboole_0(k4_xboole_0(X28,X29),X30),k5_xboole_0(k4_xboole_0(X28,X29),k4_xboole_0(X28,X29)))) = X29) ) | (~spl2_37 | ~spl2_87)),
% 34.64/4.74    inference(superposition,[],[f5941,f1501])).
% 34.64/4.74  fof(f5941,plain,(
% 34.64/4.74    ( ! [X24,X23,X25] : (k4_xboole_0(X25,k5_xboole_0(X23,k4_xboole_0(X23,k4_xboole_0(X24,X25)))) = X25) ) | ~spl2_87),
% 34.64/4.74    inference(avatar_component_clause,[],[f5940])).
% 34.64/4.74  fof(f5942,plain,(
% 34.64/4.74    spl2_87 | ~spl2_7 | ~spl2_77),
% 34.64/4.74    inference(avatar_split_clause,[],[f5752,f3842,f95,f5940])).
% 34.64/4.74  fof(f3842,plain,(
% 34.64/4.74    spl2_77 <=> ! [X1,X0,X2] : k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 34.64/4.74    introduced(avatar_definition,[new_symbols(naming,[spl2_77])])).
% 34.64/4.74  fof(f5752,plain,(
% 34.64/4.74    ( ! [X24,X23,X25] : (k4_xboole_0(X25,k5_xboole_0(X23,k4_xboole_0(X23,k4_xboole_0(X24,X25)))) = X25) ) | (~spl2_7 | ~spl2_77)),
% 34.64/4.74    inference(superposition,[],[f96,f3843])).
% 34.64/4.74  fof(f3843,plain,(
% 34.64/4.74    ( ! [X2,X0,X1] : (k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) ) | ~spl2_77),
% 34.64/4.74    inference(avatar_component_clause,[],[f3842])).
% 34.64/4.74  fof(f3844,plain,(
% 34.64/4.74    spl2_77 | ~spl2_3 | ~spl2_28),
% 34.64/4.74    inference(avatar_split_clause,[],[f1332,f541,f48,f3842])).
% 34.64/4.74  fof(f1332,plain,(
% 34.64/4.74    ( ! [X2,X0,X1] : (k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) ) | (~spl2_3 | ~spl2_28)),
% 34.64/4.74    inference(forward_demodulation,[],[f1279,f1251])).
% 34.64/4.74  fof(f1279,plain,(
% 34.64/4.74    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) ) | (~spl2_3 | ~spl2_28)),
% 34.64/4.74    inference(backward_demodulation,[],[f34,f1251])).
% 34.64/4.74  fof(f34,plain,(
% 34.64/4.74    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 34.64/4.74    inference(definition_unfolding,[],[f26,f23,f23])).
% 34.64/4.74  fof(f23,plain,(
% 34.64/4.74    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 34.64/4.74    inference(cnf_transformation,[],[f7])).
% 34.64/4.74  fof(f7,axiom,(
% 34.64/4.74    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 34.64/4.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 34.64/4.74  fof(f26,plain,(
% 34.64/4.74    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 34.64/4.74    inference(cnf_transformation,[],[f8])).
% 34.64/4.74  fof(f8,axiom,(
% 34.64/4.74    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 34.64/4.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 34.64/4.74  fof(f3820,plain,(
% 34.64/4.74    spl2_71 | ~spl2_21 | ~spl2_34),
% 34.64/4.74    inference(avatar_split_clause,[],[f1442,f1425,f512,f3818])).
% 34.64/4.74  fof(f1442,plain,(
% 34.64/4.74    ( ! [X8,X7] : (k4_xboole_0(X7,X8) = k5_xboole_0(X8,k5_xboole_0(X7,k4_xboole_0(X8,X7)))) ) | (~spl2_21 | ~spl2_34)),
% 34.64/4.74    inference(superposition,[],[f1426,f513])).
% 34.64/4.74  fof(f3780,plain,(
% 34.64/4.74    spl2_61 | ~spl2_16 | ~spl2_21),
% 34.64/4.74    inference(avatar_split_clause,[],[f576,f512,f220,f3778])).
% 34.64/4.74  fof(f576,plain,(
% 34.64/4.74    ( ! [X10,X11,X9] : (k5_xboole_0(X10,k5_xboole_0(X11,X9)) = k5_xboole_0(X10,k5_xboole_0(X9,X11))) ) | (~spl2_16 | ~spl2_21)),
% 34.64/4.74    inference(superposition,[],[f513,f221])).
% 34.64/4.74  fof(f3619,plain,(
% 34.64/4.74    spl2_54 | ~spl2_50 | ~spl2_51),
% 34.64/4.74    inference(avatar_split_clause,[],[f3243,f3053,f2989,f3617])).
% 34.64/4.74  fof(f2989,plain,(
% 34.64/4.74    spl2_50 <=> ! [X44,X43] : k5_xboole_0(X44,X44) = k4_xboole_0(k5_xboole_0(X43,X43),X44)),
% 34.64/4.74    introduced(avatar_definition,[new_symbols(naming,[spl2_50])])).
% 34.64/4.74  fof(f3053,plain,(
% 34.64/4.74    spl2_51 <=> ! [X3,X4] : k5_xboole_0(X3,X3) = k4_xboole_0(X4,X4)),
% 34.64/4.74    introduced(avatar_definition,[new_symbols(naming,[spl2_51])])).
% 34.64/4.74  fof(f3243,plain,(
% 34.64/4.74    ( ! [X28,X29,X27] : (k4_xboole_0(X28,X28) = k4_xboole_0(k5_xboole_0(X29,X29),X27)) ) | (~spl2_50 | ~spl2_51)),
% 34.64/4.74    inference(superposition,[],[f2990,f3054])).
% 34.64/4.74  fof(f3054,plain,(
% 34.64/4.74    ( ! [X4,X3] : (k5_xboole_0(X3,X3) = k4_xboole_0(X4,X4)) ) | ~spl2_51),
% 34.64/4.74    inference(avatar_component_clause,[],[f3053])).
% 34.64/4.74  fof(f2990,plain,(
% 34.64/4.74    ( ! [X43,X44] : (k5_xboole_0(X44,X44) = k4_xboole_0(k5_xboole_0(X43,X43),X44)) ) | ~spl2_50),
% 34.64/4.74    inference(avatar_component_clause,[],[f2989])).
% 34.64/4.74  fof(f3055,plain,(
% 34.64/4.74    spl2_51 | ~spl2_4 | ~spl2_48 | ~spl2_49),
% 34.64/4.74    inference(avatar_split_clause,[],[f3038,f2985,f2924,f52,f3053])).
% 34.64/4.74  fof(f3038,plain,(
% 34.64/4.74    ( ! [X4,X3] : (k5_xboole_0(X3,X3) = k4_xboole_0(X4,X4)) ) | (~spl2_4 | ~spl2_48 | ~spl2_49)),
% 34.64/4.74    inference(forward_demodulation,[],[f3006,f2925])).
% 34.64/4.74  fof(f3006,plain,(
% 34.64/4.74    ( ! [X4,X3] : (k5_xboole_0(X3,X3) = k4_xboole_0(X4,k4_xboole_0(X4,k5_xboole_0(X3,X3)))) ) | (~spl2_4 | ~spl2_49)),
% 34.64/4.74    inference(superposition,[],[f2986,f53])).
% 34.64/4.74  fof(f2991,plain,(
% 34.64/4.74    spl2_50 | ~spl2_10 | ~spl2_34 | ~spl2_44 | ~spl2_45),
% 34.64/4.74    inference(avatar_split_clause,[],[f2792,f2500,f2496,f1425,f131,f2989])).
% 34.64/4.74  fof(f131,plain,(
% 34.64/4.74    spl2_10 <=> ! [X0] : k4_xboole_0(X0,k5_xboole_0(X0,X0)) = X0),
% 34.64/4.74    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 34.64/4.74  fof(f2496,plain,(
% 34.64/4.74    spl2_44 <=> ! [X53,X52] : k5_xboole_0(k5_xboole_0(X52,X52),X53) = X53),
% 34.64/4.74    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).
% 34.64/4.74  fof(f2500,plain,(
% 34.64/4.74    spl2_45 <=> ! [X53,X54] : k5_xboole_0(X53,X53) = k5_xboole_0(X54,X54)),
% 34.64/4.74    introduced(avatar_definition,[new_symbols(naming,[spl2_45])])).
% 34.64/4.74  fof(f2792,plain,(
% 34.64/4.74    ( ! [X43,X44] : (k5_xboole_0(X44,X44) = k4_xboole_0(k5_xboole_0(X43,X43),X44)) ) | (~spl2_10 | ~spl2_34 | ~spl2_44 | ~spl2_45)),
% 34.64/4.74    inference(backward_demodulation,[],[f2597,f2700])).
% 34.64/4.74  fof(f2700,plain,(
% 34.64/4.74    ( ! [X2,X3] : (k4_xboole_0(X2,k5_xboole_0(X3,X3)) = X2) ) | (~spl2_10 | ~spl2_45)),
% 34.64/4.74    inference(superposition,[],[f132,f2501])).
% 34.64/4.74  fof(f2501,plain,(
% 34.64/4.74    ( ! [X54,X53] : (k5_xboole_0(X53,X53) = k5_xboole_0(X54,X54)) ) | ~spl2_45),
% 34.64/4.74    inference(avatar_component_clause,[],[f2500])).
% 34.64/4.74  fof(f132,plain,(
% 34.64/4.74    ( ! [X0] : (k4_xboole_0(X0,k5_xboole_0(X0,X0)) = X0) ) | ~spl2_10),
% 34.64/4.74    inference(avatar_component_clause,[],[f131])).
% 34.64/4.74  fof(f2597,plain,(
% 34.64/4.74    ( ! [X43,X44] : (k5_xboole_0(X44,k4_xboole_0(X44,k5_xboole_0(X43,X43))) = k4_xboole_0(k5_xboole_0(X43,X43),X44)) ) | (~spl2_34 | ~spl2_44)),
% 34.64/4.74    inference(superposition,[],[f2497,f1426])).
% 34.64/4.74  fof(f2497,plain,(
% 34.64/4.74    ( ! [X52,X53] : (k5_xboole_0(k5_xboole_0(X52,X52),X53) = X53) ) | ~spl2_44),
% 34.64/4.74    inference(avatar_component_clause,[],[f2496])).
% 34.64/4.74  fof(f2987,plain,(
% 34.64/4.74    spl2_49 | ~spl2_13 | ~spl2_45),
% 34.64/4.74    inference(avatar_split_clause,[],[f2701,f2500,f162,f2985])).
% 34.64/4.74  fof(f162,plain,(
% 34.64/4.74    spl2_13 <=> ! [X0] : k5_xboole_0(X0,X0) = k4_xboole_0(k5_xboole_0(X0,X0),X0)),
% 34.64/4.74    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 34.64/4.74  fof(f2701,plain,(
% 34.64/4.74    ( ! [X4,X5] : (k5_xboole_0(X5,X5) = k4_xboole_0(k5_xboole_0(X5,X5),X4)) ) | (~spl2_13 | ~spl2_45)),
% 34.64/4.74    inference(superposition,[],[f163,f2501])).
% 34.64/4.74  fof(f163,plain,(
% 34.64/4.74    ( ! [X0] : (k5_xboole_0(X0,X0) = k4_xboole_0(k5_xboole_0(X0,X0),X0)) ) | ~spl2_13),
% 34.64/4.74    inference(avatar_component_clause,[],[f162])).
% 34.64/4.74  fof(f2926,plain,(
% 34.64/4.74    spl2_48 | ~spl2_10 | ~spl2_45),
% 34.64/4.74    inference(avatar_split_clause,[],[f2700,f2500,f131,f2924])).
% 34.64/4.74  fof(f2511,plain,(
% 34.64/4.74    ~spl2_47 | ~spl2_34 | spl2_36 | ~spl2_40),
% 34.64/4.74    inference(avatar_split_clause,[],[f2284,f2167,f1495,f1425,f2508])).
% 34.64/4.74  fof(f1495,plain,(
% 34.64/4.74    spl2_36 <=> k5_xboole_0(sK0,sK1) = k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(sK1,k4_xboole_0(sK1,sK0)))),
% 34.64/4.74    introduced(avatar_definition,[new_symbols(naming,[spl2_36])])).
% 34.64/4.74  fof(f2284,plain,(
% 34.64/4.74    k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | (~spl2_34 | spl2_36 | ~spl2_40)),
% 34.64/4.74    inference(backward_demodulation,[],[f1497,f2179])).
% 34.64/4.74  fof(f2179,plain,(
% 34.64/4.74    ( ! [X31,X32] : (k5_xboole_0(X32,k4_xboole_0(X32,X31)) = k5_xboole_0(X31,k4_xboole_0(X31,X32))) ) | (~spl2_34 | ~spl2_40)),
% 34.64/4.74    inference(superposition,[],[f2168,f1426])).
% 34.64/4.74  fof(f1497,plain,(
% 34.64/4.74    k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(sK1,k4_xboole_0(sK1,sK0))) | spl2_36),
% 34.64/4.74    inference(avatar_component_clause,[],[f1495])).
% 34.64/4.74  fof(f2502,plain,(
% 34.64/4.74    spl2_45 | ~spl2_40 | ~spl2_41),
% 34.64/4.74    inference(avatar_split_clause,[],[f2373,f2320,f2167,f2500])).
% 34.64/4.74  fof(f2373,plain,(
% 34.64/4.74    ( ! [X54,X53] : (k5_xboole_0(X53,X53) = k5_xboole_0(X54,X54)) ) | (~spl2_40 | ~spl2_41)),
% 34.64/4.74    inference(superposition,[],[f2168,f2321])).
% 34.64/4.74  fof(f2498,plain,(
% 34.64/4.74    spl2_44 | ~spl2_16 | ~spl2_21 | ~spl2_22 | ~spl2_23 | ~spl2_40),
% 34.64/4.74    inference(avatar_split_clause,[],[f2310,f2167,f520,f516,f512,f220,f2496])).
% 34.64/4.74  fof(f520,plain,(
% 34.64/4.74    spl2_23 <=> ! [X9,X10] : k5_xboole_0(X10,X9) = k5_xboole_0(k5_xboole_0(X9,X9),k5_xboole_0(X10,X9))),
% 34.64/4.74    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 34.64/4.74  fof(f2310,plain,(
% 34.64/4.74    ( ! [X52,X53] : (k5_xboole_0(k5_xboole_0(X52,X52),X53) = X53) ) | (~spl2_16 | ~spl2_21 | ~spl2_22 | ~spl2_23 | ~spl2_40)),
% 34.64/4.74    inference(forward_demodulation,[],[f2309,f2173])).
% 34.64/4.74  fof(f2309,plain,(
% 34.64/4.74    ( ! [X52,X53] : (k5_xboole_0(k5_xboole_0(X53,k5_xboole_0(X52,k5_xboole_0(X52,X53))),X53) = X53) ) | (~spl2_16 | ~spl2_21 | ~spl2_23 | ~spl2_40)),
% 34.64/4.74    inference(forward_demodulation,[],[f2308,f576])).
% 34.64/4.74  fof(f2308,plain,(
% 34.64/4.74    ( ! [X52,X53] : (k5_xboole_0(k5_xboole_0(X53,k5_xboole_0(k5_xboole_0(X52,X53),X52)),X53) = X53) ) | (~spl2_16 | ~spl2_23 | ~spl2_40)),
% 34.64/4.74    inference(forward_demodulation,[],[f2213,f221])).
% 34.64/4.74  fof(f2213,plain,(
% 34.64/4.74    ( ! [X52,X53] : (k5_xboole_0(k5_xboole_0(k5_xboole_0(X52,X53),k5_xboole_0(X52,X53)),X53) = X53) ) | (~spl2_23 | ~spl2_40)),
% 34.64/4.74    inference(superposition,[],[f521,f2168])).
% 34.64/4.74  fof(f521,plain,(
% 34.64/4.74    ( ! [X10,X9] : (k5_xboole_0(X10,X9) = k5_xboole_0(k5_xboole_0(X9,X9),k5_xboole_0(X10,X9))) ) | ~spl2_23),
% 34.64/4.74    inference(avatar_component_clause,[],[f520])).
% 34.64/4.74  fof(f2326,plain,(
% 34.64/4.74    spl2_42 | ~spl2_18 | ~spl2_26 | ~spl2_39 | ~spl2_40),
% 34.64/4.74    inference(avatar_split_clause,[],[f2292,f2167,f1921,f533,f228,f2324])).
% 34.64/4.74  fof(f228,plain,(
% 34.64/4.74    spl2_18 <=> ! [X2,X4] : k5_xboole_0(X2,X4) = k5_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X2,X4)))),
% 34.64/4.74    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 34.64/4.74  fof(f533,plain,(
% 34.64/4.74    spl2_26 <=> ! [X9,X10] : k5_xboole_0(X10,X9) = k5_xboole_0(X9,k5_xboole_0(X9,k5_xboole_0(X9,X10)))),
% 34.64/4.74    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).
% 34.64/4.74  fof(f2292,plain,(
% 34.64/4.74    ( ! [X48,X49] : (k5_xboole_0(k5_xboole_0(X48,X49),X48) = X49) ) | (~spl2_18 | ~spl2_26 | ~spl2_39 | ~spl2_40)),
% 34.64/4.74    inference(backward_demodulation,[],[f2163,f2181])).
% 34.64/4.74  fof(f2163,plain,(
% 34.64/4.74    ( ! [X48,X49] : (k5_xboole_0(k5_xboole_0(k4_xboole_0(X48,X49),k4_xboole_0(X49,X48)),X48) = X49) ) | (~spl2_18 | ~spl2_26 | ~spl2_39)),
% 34.64/4.74    inference(forward_demodulation,[],[f2055,f2048])).
% 34.64/4.74  fof(f2048,plain,(
% 34.64/4.74    ( ! [X30,X29] : (k5_xboole_0(X29,k5_xboole_0(X29,X30)) = X30) ) | (~spl2_18 | ~spl2_39)),
% 34.64/4.74    inference(superposition,[],[f229,f1922])).
% 34.64/4.74  fof(f229,plain,(
% 34.64/4.74    ( ! [X4,X2] : (k5_xboole_0(X2,X4) = k5_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X2,X4)))) ) | ~spl2_18),
% 34.64/4.74    inference(avatar_component_clause,[],[f228])).
% 34.64/4.74  fof(f2055,plain,(
% 34.64/4.74    ( ! [X48,X49] : (k5_xboole_0(X48,k5_xboole_0(X48,X49)) = k5_xboole_0(k5_xboole_0(k4_xboole_0(X48,X49),k4_xboole_0(X49,X48)),X48)) ) | (~spl2_26 | ~spl2_39)),
% 34.64/4.74    inference(superposition,[],[f534,f1922])).
% 34.64/4.74  fof(f534,plain,(
% 34.64/4.74    ( ! [X10,X9] : (k5_xboole_0(X10,X9) = k5_xboole_0(X9,k5_xboole_0(X9,k5_xboole_0(X9,X10)))) ) | ~spl2_26),
% 34.64/4.74    inference(avatar_component_clause,[],[f533])).
% 34.64/4.74  fof(f2322,plain,(
% 34.64/4.74    spl2_41 | ~spl2_1 | ~spl2_23 | ~spl2_40),
% 34.64/4.74    inference(avatar_split_clause,[],[f2246,f2167,f520,f40,f2320])).
% 34.64/4.74  fof(f2246,plain,(
% 34.64/4.74    ( ! [X23,X22] : (k5_xboole_0(X23,k5_xboole_0(X22,X22)) = X23) ) | (~spl2_1 | ~spl2_23 | ~spl2_40)),
% 34.64/4.74    inference(backward_demodulation,[],[f804,f2170])).
% 34.64/4.74  fof(f2170,plain,(
% 34.64/4.74    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1) ) | (~spl2_1 | ~spl2_40)),
% 34.64/4.74    inference(superposition,[],[f2168,f41])).
% 34.64/4.74  fof(f804,plain,(
% 34.64/4.74    ( ! [X23,X22] : (k5_xboole_0(X23,k5_xboole_0(X22,X22)) = k5_xboole_0(k5_xboole_0(X22,X22),k5_xboole_0(X23,k5_xboole_0(X22,X22)))) ) | ~spl2_23),
% 34.64/4.74    inference(superposition,[],[f521,f521])).
% 34.64/4.74  fof(f2169,plain,(
% 34.64/4.74    spl2_40 | ~spl2_18 | ~spl2_39),
% 34.64/4.74    inference(avatar_split_clause,[],[f2048,f1921,f228,f2167])).
% 34.64/4.74  fof(f1923,plain,(
% 34.64/4.74    spl2_39 | ~spl2_2 | ~spl2_35),
% 34.64/4.74    inference(avatar_split_clause,[],[f1555,f1429,f44,f1921])).
% 34.64/4.74  fof(f1429,plain,(
% 34.64/4.74    spl2_35 <=> ! [X1,X0] : k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) = X0),
% 34.64/4.74    introduced(avatar_definition,[new_symbols(naming,[spl2_35])])).
% 34.64/4.74  fof(f1555,plain,(
% 34.64/4.74    ( ! [X8,X7] : (k5_xboole_0(X7,k5_xboole_0(k4_xboole_0(X7,X8),k4_xboole_0(X8,X7))) = X8) ) | (~spl2_2 | ~spl2_35)),
% 34.64/4.74    inference(superposition,[],[f1430,f45])).
% 34.64/4.74  fof(f1430,plain,(
% 34.64/4.74    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) = X0) ) | ~spl2_35),
% 34.64/4.74    inference(avatar_component_clause,[],[f1429])).
% 34.64/4.74  fof(f1919,plain,(
% 34.64/4.74    spl2_38 | ~spl2_3 | ~spl2_28 | ~spl2_31),
% 34.64/4.74    inference(avatar_split_clause,[],[f1312,f553,f541,f48,f1917])).
% 34.64/4.74  fof(f553,plain,(
% 34.64/4.74    spl2_31 <=> ! [X3,X4] : k5_xboole_0(k4_xboole_0(X4,X3),k4_xboole_0(X3,k4_xboole_0(X3,X4))) = X4),
% 34.64/4.74    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).
% 34.64/4.74  fof(f1312,plain,(
% 34.64/4.74    ( ! [X4,X3] : (k5_xboole_0(k4_xboole_0(X4,X3),k5_xboole_0(X3,k4_xboole_0(X3,X4))) = X4) ) | (~spl2_3 | ~spl2_28 | ~spl2_31)),
% 34.64/4.74    inference(backward_demodulation,[],[f554,f1251])).
% 34.64/4.74  fof(f554,plain,(
% 34.64/4.74    ( ! [X4,X3] : (k5_xboole_0(k4_xboole_0(X4,X3),k4_xboole_0(X3,k4_xboole_0(X3,X4))) = X4) ) | ~spl2_31),
% 34.64/4.74    inference(avatar_component_clause,[],[f553])).
% 34.64/4.74  fof(f1502,plain,(
% 34.64/4.74    spl2_37 | ~spl2_3 | ~spl2_4 | ~spl2_16 | ~spl2_19 | ~spl2_28 | ~spl2_34),
% 34.64/4.74    inference(avatar_split_clause,[],[f1469,f1425,f541,f232,f220,f52,f48,f1500])).
% 34.64/4.74  fof(f232,plain,(
% 34.64/4.74    spl2_19 <=> ! [X1,X0] : k5_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) = X0),
% 34.64/4.74    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 34.64/4.74  fof(f1469,plain,(
% 34.64/4.74    ( ! [X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X0) = k5_xboole_0(X0,X0)) ) | (~spl2_3 | ~spl2_4 | ~spl2_16 | ~spl2_19 | ~spl2_28 | ~spl2_34)),
% 34.64/4.74    inference(forward_demodulation,[],[f1468,f1307])).
% 34.64/4.74  fof(f1307,plain,(
% 34.64/4.74    ( ! [X14,X15,X16] : (k5_xboole_0(X16,X15) = k5_xboole_0(k4_xboole_0(X15,X14),k5_xboole_0(X16,k5_xboole_0(X14,k4_xboole_0(X14,X15))))) ) | (~spl2_3 | ~spl2_16 | ~spl2_19 | ~spl2_28)),
% 34.64/4.74    inference(backward_demodulation,[],[f459,f1251])).
% 34.64/4.74  fof(f459,plain,(
% 34.64/4.74    ( ! [X14,X15,X16] : (k5_xboole_0(X16,X15) = k5_xboole_0(k4_xboole_0(X15,X14),k5_xboole_0(X16,k4_xboole_0(X14,k4_xboole_0(X14,X15))))) ) | (~spl2_16 | ~spl2_19)),
% 34.64/4.74    inference(superposition,[],[f221,f233])).
% 34.64/4.74  fof(f233,plain,(
% 34.64/4.74    ( ! [X0,X1] : (k5_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) = X0) ) | ~spl2_19),
% 34.64/4.74    inference(avatar_component_clause,[],[f232])).
% 34.64/4.74  fof(f1468,plain,(
% 34.64/4.74    ( ! [X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X0) = k5_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,X0))))) ) | (~spl2_3 | ~spl2_4 | ~spl2_28 | ~spl2_34)),
% 34.64/4.74    inference(forward_demodulation,[],[f1432,f1251])).
% 34.64/4.74  fof(f1432,plain,(
% 34.64/4.74    ( ! [X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X0) = k5_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) ) | (~spl2_4 | ~spl2_34)),
% 34.64/4.74    inference(superposition,[],[f1426,f53])).
% 34.64/4.74  fof(f1498,plain,(
% 34.64/4.74    ~spl2_36 | ~spl2_4 | ~spl2_17 | spl2_24 | ~spl2_28),
% 34.64/4.74    inference(avatar_split_clause,[],[f1277,f541,f524,f224,f52,f1495])).
% 34.64/4.74  fof(f524,plain,(
% 34.64/4.74    spl2_24 <=> k5_xboole_0(sK0,sK1) = k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 34.64/4.74    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 34.64/4.74  fof(f1277,plain,(
% 34.64/4.74    k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(sK1,k4_xboole_0(sK1,sK0))) | (~spl2_4 | ~spl2_17 | spl2_24 | ~spl2_28)),
% 34.64/4.74    inference(backward_demodulation,[],[f526,f1276])).
% 34.64/4.74  fof(f1276,plain,(
% 34.64/4.74    ( ! [X0,X1] : (k4_xboole_0(X1,k4_xboole_0(X1,X0)) = k5_xboole_0(X0,k4_xboole_0(X0,X1))) ) | (~spl2_4 | ~spl2_17 | ~spl2_28)),
% 34.64/4.74    inference(forward_demodulation,[],[f1244,f225])).
% 34.64/4.74  fof(f1244,plain,(
% 34.64/4.74    ( ! [X0,X1] : (k4_xboole_0(X1,k4_xboole_0(X1,X0)) = k5_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) ) | (~spl2_4 | ~spl2_28)),
% 34.64/4.74    inference(superposition,[],[f542,f53])).
% 34.64/4.74  fof(f526,plain,(
% 34.64/4.74    k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl2_24),
% 34.64/4.74    inference(avatar_component_clause,[],[f524])).
% 34.64/4.74  fof(f1431,plain,(
% 34.64/4.74    spl2_35 | ~spl2_3 | ~spl2_19 | ~spl2_28),
% 34.64/4.74    inference(avatar_split_clause,[],[f1290,f541,f232,f48,f1429])).
% 34.64/4.74  fof(f1290,plain,(
% 34.64/4.74    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) = X0) ) | (~spl2_3 | ~spl2_19 | ~spl2_28)),
% 34.64/4.74    inference(backward_demodulation,[],[f233,f1251])).
% 34.64/4.74  fof(f1427,plain,(
% 34.64/4.74    spl2_34 | ~spl2_3 | ~spl2_17 | ~spl2_28),
% 34.64/4.74    inference(avatar_split_clause,[],[f1289,f541,f224,f48,f1425])).
% 34.64/4.74  fof(f1289,plain,(
% 34.64/4.74    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,X0)))) ) | (~spl2_3 | ~spl2_17 | ~spl2_28)),
% 34.64/4.74    inference(backward_demodulation,[],[f225,f1251])).
% 34.64/4.74  fof(f555,plain,(
% 34.64/4.74    spl2_31 | ~spl2_1 | ~spl2_19),
% 34.64/4.74    inference(avatar_split_clause,[],[f452,f232,f40,f553])).
% 34.64/4.74  fof(f452,plain,(
% 34.64/4.74    ( ! [X4,X3] : (k5_xboole_0(k4_xboole_0(X4,X3),k4_xboole_0(X3,k4_xboole_0(X3,X4))) = X4) ) | (~spl2_1 | ~spl2_19)),
% 34.64/4.74    inference(superposition,[],[f233,f41])).
% 34.64/4.74  fof(f543,plain,(
% 34.64/4.74    spl2_28 | ~spl2_3 | ~spl2_18),
% 34.64/4.74    inference(avatar_split_clause,[],[f387,f228,f48,f541])).
% 34.64/4.74  fof(f387,plain,(
% 34.64/4.74    ( ! [X4,X5] : (k4_xboole_0(X4,X5) = k5_xboole_0(X4,k5_xboole_0(X4,k4_xboole_0(X4,X5)))) ) | (~spl2_3 | ~spl2_18)),
% 34.64/4.74    inference(superposition,[],[f229,f49])).
% 34.64/4.74  fof(f535,plain,(
% 34.64/4.74    spl2_26 | ~spl2_2 | ~spl2_8 | ~spl2_16),
% 34.64/4.74    inference(avatar_split_clause,[],[f333,f220,f112,f44,f533])).
% 34.64/4.74  fof(f112,plain,(
% 34.64/4.74    spl2_8 <=> ! [X0] : k5_xboole_0(X0,k5_xboole_0(X0,X0)) = X0),
% 34.64/4.74    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 34.64/4.74  fof(f333,plain,(
% 34.64/4.74    ( ! [X10,X9] : (k5_xboole_0(X10,X9) = k5_xboole_0(X9,k5_xboole_0(X9,k5_xboole_0(X9,X10)))) ) | (~spl2_2 | ~spl2_8 | ~spl2_16)),
% 34.64/4.74    inference(forward_demodulation,[],[f293,f45])).
% 34.64/4.74  fof(f293,plain,(
% 34.64/4.74    ( ! [X10,X9] : (k5_xboole_0(X10,X9) = k5_xboole_0(X9,k5_xboole_0(k5_xboole_0(X9,X9),X10))) ) | (~spl2_8 | ~spl2_16)),
% 34.64/4.74    inference(superposition,[],[f221,f113])).
% 34.64/4.74  fof(f113,plain,(
% 34.64/4.74    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(X0,X0)) = X0) ) | ~spl2_8),
% 34.64/4.74    inference(avatar_component_clause,[],[f112])).
% 34.64/4.74  fof(f527,plain,(
% 34.64/4.74    ~spl2_24),
% 34.64/4.74    inference(avatar_split_clause,[],[f30,f524])).
% 34.64/4.74  fof(f30,plain,(
% 34.64/4.74    k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 34.64/4.74    inference(definition_unfolding,[],[f17,f21,f23])).
% 34.64/4.74  fof(f17,plain,(
% 34.64/4.74    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 34.64/4.74    inference(cnf_transformation,[],[f16])).
% 34.64/4.74  fof(f16,plain,(
% 34.64/4.74    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 34.64/4.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f15])).
% 34.64/4.74  fof(f15,plain,(
% 34.64/4.74    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 34.64/4.74    introduced(choice_axiom,[])).
% 34.64/4.74  fof(f14,plain,(
% 34.64/4.74    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 34.64/4.74    inference(ennf_transformation,[],[f13])).
% 34.64/4.74  fof(f13,negated_conjecture,(
% 34.64/4.74    ~! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 34.64/4.74    inference(negated_conjecture,[],[f12])).
% 34.64/4.74  fof(f12,conjecture,(
% 34.64/4.74    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 34.64/4.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_xboole_1)).
% 34.64/4.74  fof(f522,plain,(
% 34.64/4.74    spl2_23 | ~spl2_8 | ~spl2_16),
% 34.64/4.74    inference(avatar_split_clause,[],[f277,f220,f112,f520])).
% 34.64/4.74  fof(f277,plain,(
% 34.64/4.74    ( ! [X10,X9] : (k5_xboole_0(X10,X9) = k5_xboole_0(k5_xboole_0(X9,X9),k5_xboole_0(X10,X9))) ) | (~spl2_8 | ~spl2_16)),
% 34.64/4.74    inference(superposition,[],[f221,f113])).
% 34.64/4.74  fof(f518,plain,(
% 34.64/4.74    spl2_22 | ~spl2_1 | ~spl2_15),
% 34.64/4.74    inference(avatar_split_clause,[],[f249,f216,f40,f516])).
% 34.64/4.74  fof(f216,plain,(
% 34.64/4.74    spl2_15 <=> ! [X1,X0,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X1,X0),X2)),
% 34.64/4.74    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 34.64/4.74  fof(f249,plain,(
% 34.64/4.74    ( ! [X8,X7,X9] : (k5_xboole_0(X9,k5_xboole_0(X7,X8)) = k5_xboole_0(X8,k5_xboole_0(X7,X9))) ) | (~spl2_1 | ~spl2_15)),
% 34.64/4.74    inference(superposition,[],[f217,f41])).
% 34.64/4.74  fof(f217,plain,(
% 34.64/4.74    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X1,X0),X2)) ) | ~spl2_15),
% 34.64/4.74    inference(avatar_component_clause,[],[f216])).
% 34.64/4.74  fof(f514,plain,(
% 34.64/4.74    spl2_21 | ~spl2_2 | ~spl2_15),
% 34.64/4.74    inference(avatar_split_clause,[],[f247,f216,f44,f512])).
% 34.64/4.74  fof(f247,plain,(
% 34.64/4.74    ( ! [X4,X5,X3] : (k5_xboole_0(X3,k5_xboole_0(X4,X5)) = k5_xboole_0(X4,k5_xboole_0(X3,X5))) ) | (~spl2_2 | ~spl2_15)),
% 34.64/4.74    inference(superposition,[],[f217,f45])).
% 34.64/4.74  fof(f234,plain,(
% 34.64/4.74    spl2_19 | ~spl2_4 | ~spl2_12),
% 34.64/4.74    inference(avatar_split_clause,[],[f182,f158,f52,f232])).
% 34.64/4.74  fof(f158,plain,(
% 34.64/4.74    spl2_12 <=> ! [X1,X0] : k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0),
% 34.64/4.74    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 34.64/4.74  fof(f182,plain,(
% 34.64/4.74    ( ! [X0,X1] : (k5_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) = X0) ) | (~spl2_4 | ~spl2_12)),
% 34.64/4.74    inference(superposition,[],[f159,f53])).
% 34.64/4.74  fof(f159,plain,(
% 34.64/4.74    ( ! [X0,X1] : (k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) ) | ~spl2_12),
% 34.64/4.74    inference(avatar_component_clause,[],[f158])).
% 34.64/4.74  fof(f230,plain,(
% 34.64/4.74    spl2_18 | ~spl2_2 | ~spl2_3 | ~spl2_5 | ~spl2_7),
% 34.64/4.74    inference(avatar_split_clause,[],[f107,f95,f56,f48,f44,f228])).
% 34.64/4.74  fof(f56,plain,(
% 34.64/4.74    spl2_5 <=> ! [X1,X0] : k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = X0),
% 34.64/4.74    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 34.64/4.74  fof(f107,plain,(
% 34.64/4.74    ( ! [X4,X2] : (k5_xboole_0(X2,X4) = k5_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X2,X4)))) ) | (~spl2_2 | ~spl2_3 | ~spl2_5 | ~spl2_7)),
% 34.64/4.74    inference(forward_demodulation,[],[f105,f45])).
% 34.64/4.74  fof(f105,plain,(
% 34.64/4.74    ( ! [X4,X2] : (k5_xboole_0(X2,X4) = k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X2),X4))) ) | (~spl2_2 | ~spl2_3 | ~spl2_5 | ~spl2_7)),
% 34.64/4.74    inference(backward_demodulation,[],[f85,f101])).
% 34.64/4.74  fof(f101,plain,(
% 34.64/4.74    ( ! [X2] : (k4_xboole_0(X2,X2) = k5_xboole_0(X2,X2)) ) | (~spl2_3 | ~spl2_7)),
% 34.64/4.74    inference(superposition,[],[f49,f96])).
% 34.64/4.74  fof(f85,plain,(
% 34.64/4.74    ( ! [X4,X2] : (k5_xboole_0(X2,X4) = k5_xboole_0(X2,k5_xboole_0(k4_xboole_0(X2,X2),X4))) ) | (~spl2_2 | ~spl2_3 | ~spl2_5)),
% 34.64/4.74    inference(forward_demodulation,[],[f80,f77])).
% 34.64/4.74  fof(f77,plain,(
% 34.64/4.74    ( ! [X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X3,X2)) = X2) ) | (~spl2_3 | ~spl2_5)),
% 34.64/4.74    inference(superposition,[],[f57,f49])).
% 34.64/4.74  fof(f57,plain,(
% 34.64/4.74    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = X0) ) | ~spl2_5),
% 34.64/4.74    inference(avatar_component_clause,[],[f56])).
% 34.64/4.74  fof(f80,plain,(
% 34.64/4.74    ( ! [X4,X2,X3] : (k5_xboole_0(X2,k5_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,X2))),X4)) = k5_xboole_0(X2,X4)) ) | (~spl2_2 | ~spl2_5)),
% 34.64/4.74    inference(superposition,[],[f45,f57])).
% 34.64/4.74  fof(f226,plain,(
% 34.64/4.74    spl2_17 | ~spl2_3 | ~spl2_4),
% 34.64/4.74    inference(avatar_split_clause,[],[f71,f52,f48,f224])).
% 34.64/4.74  fof(f71,plain,(
% 34.64/4.74    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ) | (~spl2_3 | ~spl2_4)),
% 34.64/4.74    inference(superposition,[],[f49,f53])).
% 34.64/4.74  fof(f222,plain,(
% 34.64/4.74    spl2_16 | ~spl2_1 | ~spl2_2),
% 34.64/4.74    inference(avatar_split_clause,[],[f62,f44,f40,f220])).
% 34.64/4.74  fof(f62,plain,(
% 34.64/4.74    ( ! [X4,X5,X3] : (k5_xboole_0(X3,k5_xboole_0(X4,X5)) = k5_xboole_0(X5,k5_xboole_0(X3,X4))) ) | (~spl2_1 | ~spl2_2)),
% 34.64/4.74    inference(superposition,[],[f45,f41])).
% 34.64/4.74  fof(f218,plain,(
% 34.64/4.74    spl2_15 | ~spl2_1 | ~spl2_2),
% 34.64/4.74    inference(avatar_split_clause,[],[f59,f44,f40,f216])).
% 34.64/4.74  fof(f59,plain,(
% 34.64/4.74    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X1,X0),X2)) ) | (~spl2_1 | ~spl2_2)),
% 34.64/4.74    inference(superposition,[],[f45,f41])).
% 34.64/4.74  fof(f164,plain,(
% 34.64/4.74    spl2_13 | ~spl2_7 | ~spl2_10),
% 34.64/4.74    inference(avatar_split_clause,[],[f135,f131,f95,f162])).
% 34.64/4.74  fof(f135,plain,(
% 34.64/4.74    ( ! [X0] : (k5_xboole_0(X0,X0) = k4_xboole_0(k5_xboole_0(X0,X0),X0)) ) | (~spl2_7 | ~spl2_10)),
% 34.64/4.74    inference(superposition,[],[f96,f132])).
% 34.64/4.74  fof(f160,plain,(
% 34.64/4.74    spl2_12 | ~spl2_3 | ~spl2_5),
% 34.64/4.74    inference(avatar_split_clause,[],[f83,f56,f48,f158])).
% 34.64/4.74  fof(f83,plain,(
% 34.64/4.74    ( ! [X0,X1] : (k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) ) | (~spl2_3 | ~spl2_5)),
% 34.64/4.74    inference(backward_demodulation,[],[f33,f77])).
% 34.64/4.74  fof(f33,plain,(
% 34.64/4.74    ( ! [X0,X1] : (k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = X0) )),
% 34.64/4.74    inference(definition_unfolding,[],[f24,f21,f23])).
% 34.64/4.74  fof(f24,plain,(
% 34.64/4.74    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 34.64/4.74    inference(cnf_transformation,[],[f9])).
% 34.64/4.74  fof(f9,axiom,(
% 34.64/4.74    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 34.64/4.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 34.64/4.74  fof(f141,plain,(
% 34.64/4.74    spl2_11 | ~spl2_7),
% 34.64/4.74    inference(avatar_split_clause,[],[f100,f95,f139])).
% 34.64/4.74  fof(f100,plain,(
% 34.64/4.74    ( ! [X4,X5] : (k4_xboole_0(X5,X4) = k4_xboole_0(k4_xboole_0(X5,X4),X4)) ) | ~spl2_7),
% 34.64/4.74    inference(superposition,[],[f96,f96])).
% 34.64/4.74  fof(f133,plain,(
% 34.64/4.74    spl2_10 | ~spl2_7 | ~spl2_9),
% 34.64/4.74    inference(avatar_split_clause,[],[f128,f125,f95,f131])).
% 34.64/4.74  fof(f125,plain,(
% 34.64/4.74    spl2_9 <=> ! [X2] : k4_xboole_0(X2,X2) = k5_xboole_0(X2,X2)),
% 34.64/4.74    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 34.64/4.74  fof(f128,plain,(
% 34.64/4.74    ( ! [X0] : (k4_xboole_0(X0,k5_xboole_0(X0,X0)) = X0) ) | (~spl2_7 | ~spl2_9)),
% 34.64/4.74    inference(superposition,[],[f96,f126])).
% 34.64/4.74  fof(f126,plain,(
% 34.64/4.74    ( ! [X2] : (k4_xboole_0(X2,X2) = k5_xboole_0(X2,X2)) ) | ~spl2_9),
% 34.64/4.74    inference(avatar_component_clause,[],[f125])).
% 34.64/4.74  fof(f127,plain,(
% 34.64/4.74    spl2_9 | ~spl2_3 | ~spl2_7),
% 34.64/4.74    inference(avatar_split_clause,[],[f101,f95,f48,f125])).
% 34.64/4.74  fof(f114,plain,(
% 34.64/4.74    spl2_8 | ~spl2_3 | ~spl2_6 | ~spl2_7),
% 34.64/4.74    inference(avatar_split_clause,[],[f104,f95,f88,f48,f112])).
% 34.64/4.74  fof(f88,plain,(
% 34.64/4.74    spl2_6 <=> ! [X0] : k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0),
% 34.64/4.74    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 34.64/4.74  fof(f104,plain,(
% 34.64/4.74    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(X0,X0)) = X0) ) | (~spl2_3 | ~spl2_6 | ~spl2_7)),
% 34.64/4.74    inference(backward_demodulation,[],[f89,f101])).
% 34.64/4.74  fof(f89,plain,(
% 34.64/4.74    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) ) | ~spl2_6),
% 34.64/4.74    inference(avatar_component_clause,[],[f88])).
% 34.64/4.74  fof(f97,plain,(
% 34.64/4.74    spl2_7 | ~spl2_3 | ~spl2_5),
% 34.64/4.74    inference(avatar_split_clause,[],[f77,f56,f48,f95])).
% 34.64/4.74  fof(f90,plain,(
% 34.64/4.74    spl2_6 | ~spl2_3 | ~spl2_5),
% 34.64/4.74    inference(avatar_split_clause,[],[f82,f56,f48,f88])).
% 34.64/4.74  fof(f82,plain,(
% 34.64/4.74    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) ) | (~spl2_3 | ~spl2_5)),
% 34.64/4.74    inference(backward_demodulation,[],[f57,f77])).
% 34.64/4.74  fof(f58,plain,(
% 34.64/4.74    spl2_5),
% 34.64/4.74    inference(avatar_split_clause,[],[f37,f56])).
% 34.64/4.74  fof(f37,plain,(
% 34.64/4.74    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = X0) )),
% 34.64/4.74    inference(backward_demodulation,[],[f32,f34])).
% 34.64/4.74  fof(f32,plain,(
% 34.64/4.74    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = X0) )),
% 34.64/4.74    inference(definition_unfolding,[],[f20,f21,f23])).
% 34.64/4.74  fof(f20,plain,(
% 34.64/4.74    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 34.64/4.74    inference(cnf_transformation,[],[f5])).
% 34.64/4.74  fof(f5,axiom,(
% 34.64/4.74    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 34.64/4.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 34.64/4.74  fof(f54,plain,(
% 34.64/4.74    spl2_4),
% 34.64/4.74    inference(avatar_split_clause,[],[f31,f52])).
% 34.64/4.74  fof(f31,plain,(
% 34.64/4.74    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 34.64/4.74    inference(definition_unfolding,[],[f19,f23,f23])).
% 34.64/4.74  fof(f19,plain,(
% 34.64/4.74    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 34.64/4.74    inference(cnf_transformation,[],[f1])).
% 34.64/4.74  fof(f1,axiom,(
% 34.64/4.74    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 34.64/4.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 34.64/4.74  fof(f50,plain,(
% 34.64/4.74    spl2_3),
% 34.64/4.74    inference(avatar_split_clause,[],[f29,f48])).
% 34.64/4.74  fof(f29,plain,(
% 34.64/4.74    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 34.64/4.74    inference(definition_unfolding,[],[f22,f23])).
% 34.64/4.74  fof(f22,plain,(
% 34.64/4.74    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 34.64/4.74    inference(cnf_transformation,[],[f3])).
% 34.64/4.74  fof(f3,axiom,(
% 34.64/4.74    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 34.64/4.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 34.64/4.74  fof(f46,plain,(
% 34.64/4.74    spl2_2),
% 34.64/4.74    inference(avatar_split_clause,[],[f25,f44])).
% 34.64/4.74  fof(f25,plain,(
% 34.64/4.74    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 34.64/4.74    inference(cnf_transformation,[],[f10])).
% 34.64/4.74  fof(f10,axiom,(
% 34.64/4.74    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 34.64/4.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 34.64/4.74  fof(f42,plain,(
% 34.64/4.74    spl2_1),
% 34.64/4.74    inference(avatar_split_clause,[],[f18,f40])).
% 34.64/4.74  fof(f18,plain,(
% 34.64/4.74    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 34.64/4.74    inference(cnf_transformation,[],[f2])).
% 34.64/4.74  fof(f2,axiom,(
% 34.64/4.74    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 34.64/4.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 34.64/4.74  % SZS output end Proof for theBenchmark
% 34.64/4.74  % (4083)------------------------------
% 34.64/4.74  % (4083)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 34.64/4.74  % (4083)Termination reason: Refutation
% 34.64/4.74  
% 34.64/4.74  % (4083)Memory used [KB]: 140594
% 34.64/4.74  % (4083)Time elapsed: 4.318 s
% 34.64/4.74  % (4083)------------------------------
% 34.64/4.74  % (4083)------------------------------
% 34.64/4.75  % (4075)Success in time 4.387 s
%------------------------------------------------------------------------------
