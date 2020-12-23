%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:27 EST 2020

% Result     : Theorem 25.62s
% Output     : Refutation 25.62s
% Verified   : 
% Statistics : Number of formulae       :  343 ( 857 expanded)
%              Number of leaves         :   76 ( 437 expanded)
%              Depth                    :    9
%              Number of atoms          :  960 (2002 expanded)
%              Number of equality atoms :  276 ( 790 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    8 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f45176,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f33,f37,f41,f53,f57,f61,f87,f95,f111,f118,f150,f154,f179,f261,f288,f313,f317,f321,f386,f391,f427,f450,f490,f494,f572,f576,f580,f584,f588,f870,f982,f990,f1703,f1711,f1735,f1739,f1763,f1936,f2033,f2106,f2174,f2309,f2542,f11482,f16877,f17659,f17846,f18918,f18922,f20871,f21877,f25298,f25715,f26139,f26544,f26971,f26975,f28786,f28790,f28830,f29688,f39146,f41091,f44226,f44768,f45154])).

fof(f45154,plain,
    ( ~ spl2_23
    | spl2_24
    | ~ spl2_30
    | ~ spl2_139
    | ~ spl2_150
    | ~ spl2_158 ),
    inference(avatar_contradiction_clause,[],[f45153])).

fof(f45153,plain,
    ( $false
    | ~ spl2_23
    | spl2_24
    | ~ spl2_30
    | ~ spl2_139
    | ~ spl2_150
    | ~ spl2_158 ),
    inference(subsumption_resolution,[],[f390,f45152])).

fof(f45152,plain,
    ( ! [X244,X245] : k5_xboole_0(X244,X245) = k4_xboole_0(k5_xboole_0(X244,k4_xboole_0(X245,X244)),k4_xboole_0(X244,k4_xboole_0(X244,X245)))
    | ~ spl2_23
    | ~ spl2_30
    | ~ spl2_139
    | ~ spl2_150
    | ~ spl2_158 ),
    inference(forward_demodulation,[],[f44959,f45037])).

fof(f45037,plain,
    ( ! [X17,X18] : k4_xboole_0(X17,k4_xboole_0(X17,X18)) = k4_xboole_0(X17,k5_xboole_0(X17,X18))
    | ~ spl2_23
    | ~ spl2_30
    | ~ spl2_150
    | ~ spl2_158 ),
    inference(forward_demodulation,[],[f45036,f575])).

fof(f575,plain,
    ( ! [X4,X5] : k4_xboole_0(X4,k4_xboole_0(X4,X5)) = k5_xboole_0(X4,k4_xboole_0(X4,X5))
    | ~ spl2_30 ),
    inference(avatar_component_clause,[],[f574])).

fof(f574,plain,
    ( spl2_30
  <=> ! [X5,X4] : k4_xboole_0(X4,k4_xboole_0(X4,X5)) = k5_xboole_0(X4,k4_xboole_0(X4,X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).

fof(f45036,plain,
    ( ! [X17,X18] : k5_xboole_0(X17,k4_xboole_0(X17,X18)) = k4_xboole_0(X17,k5_xboole_0(X17,X18))
    | ~ spl2_23
    | ~ spl2_150
    | ~ spl2_158 ),
    inference(forward_demodulation,[],[f44871,f39145])).

fof(f39145,plain,
    ( ! [X109,X110] : k4_xboole_0(X109,X110) = k4_xboole_0(k5_xboole_0(X109,X110),k4_xboole_0(X110,X109))
    | ~ spl2_150 ),
    inference(avatar_component_clause,[],[f39144])).

fof(f39144,plain,
    ( spl2_150
  <=> ! [X110,X109] : k4_xboole_0(X109,X110) = k4_xboole_0(k5_xboole_0(X109,X110),k4_xboole_0(X110,X109)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_150])])).

fof(f44871,plain,
    ( ! [X17,X18] : k4_xboole_0(X17,k5_xboole_0(X17,X18)) = k5_xboole_0(X17,k4_xboole_0(k5_xboole_0(X17,X18),k4_xboole_0(X18,X17)))
    | ~ spl2_23
    | ~ spl2_158 ),
    inference(superposition,[],[f385,f44767])).

fof(f44767,plain,
    ( ! [X2,X1] : k4_xboole_0(X1,X2) = k4_xboole_0(k5_xboole_0(X2,X1),X2)
    | ~ spl2_158 ),
    inference(avatar_component_clause,[],[f44766])).

fof(f44766,plain,
    ( spl2_158
  <=> ! [X1,X2] : k4_xboole_0(X1,X2) = k4_xboole_0(k5_xboole_0(X2,X1),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_158])])).

fof(f385,plain,
    ( ! [X2,X1] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f384])).

fof(f384,plain,
    ( spl2_23
  <=> ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f44959,plain,
    ( ! [X244,X245] : k5_xboole_0(X244,X245) = k4_xboole_0(k5_xboole_0(X244,k4_xboole_0(X245,X244)),k4_xboole_0(X244,k5_xboole_0(X244,X245)))
    | ~ spl2_139
    | ~ spl2_158 ),
    inference(superposition,[],[f28829,f44767])).

fof(f28829,plain,
    ( ! [X8,X9] : k4_xboole_0(k5_xboole_0(X9,k4_xboole_0(X8,X9)),k4_xboole_0(X9,X8)) = X8
    | ~ spl2_139 ),
    inference(avatar_component_clause,[],[f28828])).

fof(f28828,plain,
    ( spl2_139
  <=> ! [X9,X8] : k4_xboole_0(k5_xboole_0(X9,k4_xboole_0(X8,X9)),k4_xboole_0(X9,X8)) = X8 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_139])])).

fof(f390,plain,
    ( k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl2_24 ),
    inference(avatar_component_clause,[],[f388])).

fof(f388,plain,
    ( spl2_24
  <=> k5_xboole_0(sK0,sK1) = k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f44768,plain,
    ( spl2_158
    | ~ spl2_22
    | ~ spl2_157 ),
    inference(avatar_split_clause,[],[f44228,f44224,f319,f44766])).

fof(f319,plain,
    ( spl2_22
  <=> ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f44224,plain,
    ( spl2_157
  <=> ! [X48,X47] : k4_xboole_0(X47,X48) = k4_xboole_0(k5_xboole_0(X47,X48),X48) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_157])])).

fof(f44228,plain,
    ( ! [X2,X1] : k4_xboole_0(X1,X2) = k4_xboole_0(k5_xboole_0(X2,X1),X2)
    | ~ spl2_22
    | ~ spl2_157 ),
    inference(superposition,[],[f44225,f320])).

fof(f320,plain,
    ( ! [X2,X1] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1)
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f319])).

fof(f44225,plain,
    ( ! [X47,X48] : k4_xboole_0(X47,X48) = k4_xboole_0(k5_xboole_0(X47,X48),X48)
    | ~ spl2_157 ),
    inference(avatar_component_clause,[],[f44224])).

fof(f44226,plain,
    ( spl2_157
    | ~ spl2_2
    | ~ spl2_7
    | ~ spl2_46
    | ~ spl2_69
    | ~ spl2_143
    | ~ spl2_156 ),
    inference(avatar_split_clause,[],[f43980,f41089,f29686,f2104,f1709,f59,f35,f44224])).

fof(f35,plain,
    ( spl2_2
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f59,plain,
    ( spl2_7
  <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f1709,plain,
    ( spl2_46
  <=> ! [X1,X0,X2] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_46])])).

fof(f2104,plain,
    ( spl2_69
  <=> ! [X7,X8] : k4_xboole_0(X8,X7) = k4_xboole_0(k4_xboole_0(X8,X7),X7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_69])])).

fof(f29686,plain,
    ( spl2_143
  <=> ! [X3,X2] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X3),k5_xboole_0(X2,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_143])])).

fof(f41089,plain,
    ( spl2_156
  <=> ! [X5,X4] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k5_xboole_0(X4,X5),X5),k4_xboole_0(X4,X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_156])])).

fof(f43980,plain,
    ( ! [X47,X48] : k4_xboole_0(X47,X48) = k4_xboole_0(k5_xboole_0(X47,X48),X48)
    | ~ spl2_2
    | ~ spl2_7
    | ~ spl2_46
    | ~ spl2_69
    | ~ spl2_143
    | ~ spl2_156 ),
    inference(forward_demodulation,[],[f43979,f2105])).

fof(f2105,plain,
    ( ! [X8,X7] : k4_xboole_0(X8,X7) = k4_xboole_0(k4_xboole_0(X8,X7),X7)
    | ~ spl2_69 ),
    inference(avatar_component_clause,[],[f2104])).

fof(f43979,plain,
    ( ! [X47,X48] : k4_xboole_0(k4_xboole_0(X47,X48),X48) = k4_xboole_0(k5_xboole_0(X47,X48),X48)
    | ~ spl2_2
    | ~ spl2_7
    | ~ spl2_46
    | ~ spl2_143
    | ~ spl2_156 ),
    inference(forward_demodulation,[],[f43978,f30385])).

fof(f30385,plain,
    ( ! [X80,X78,X79] : k4_xboole_0(k4_xboole_0(X78,X79),X80) = k4_xboole_0(k4_xboole_0(X78,X79),k4_xboole_0(k4_xboole_0(X78,X79),k4_xboole_0(k5_xboole_0(X78,X79),X80)))
    | ~ spl2_2
    | ~ spl2_46
    | ~ spl2_143 ),
    inference(forward_demodulation,[],[f30245,f36])).

fof(f36,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f35])).

fof(f30245,plain,
    ( ! [X80,X78,X79] : k4_xboole_0(k4_xboole_0(X78,X79),k4_xboole_0(k4_xboole_0(X78,X79),k4_xboole_0(k5_xboole_0(X78,X79),X80))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X78,X79),k1_xboole_0),X80)
    | ~ spl2_46
    | ~ spl2_143 ),
    inference(superposition,[],[f1710,f29687])).

fof(f29687,plain,
    ( ! [X2,X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X3),k5_xboole_0(X2,X3))
    | ~ spl2_143 ),
    inference(avatar_component_clause,[],[f29686])).

fof(f1710,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)
    | ~ spl2_46 ),
    inference(avatar_component_clause,[],[f1709])).

fof(f43978,plain,
    ( ! [X47,X48] : k4_xboole_0(k5_xboole_0(X47,X48),X48) = k4_xboole_0(k4_xboole_0(X47,X48),k4_xboole_0(k4_xboole_0(X47,X48),k4_xboole_0(k5_xboole_0(X47,X48),X48)))
    | ~ spl2_2
    | ~ spl2_7
    | ~ spl2_156 ),
    inference(forward_demodulation,[],[f43653,f36])).

fof(f43653,plain,
    ( ! [X47,X48] : k4_xboole_0(k4_xboole_0(X47,X48),k4_xboole_0(k4_xboole_0(X47,X48),k4_xboole_0(k5_xboole_0(X47,X48),X48))) = k4_xboole_0(k4_xboole_0(k5_xboole_0(X47,X48),X48),k1_xboole_0)
    | ~ spl2_7
    | ~ spl2_156 ),
    inference(superposition,[],[f60,f41090])).

fof(f41090,plain,
    ( ! [X4,X5] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k5_xboole_0(X4,X5),X5),k4_xboole_0(X4,X5))
    | ~ spl2_156 ),
    inference(avatar_component_clause,[],[f41089])).

fof(f60,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f59])).

fof(f41091,plain,
    ( spl2_156
    | ~ spl2_122
    | ~ spl2_150 ),
    inference(avatar_split_clause,[],[f40627,f39144,f26137,f41089])).

fof(f26137,plain,
    ( spl2_122
  <=> ! [X13,X12,X14] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X12,X13),k4_xboole_0(X12,k4_xboole_0(X13,X14))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_122])])).

fof(f40627,plain,
    ( ! [X4,X5] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k5_xboole_0(X4,X5),X5),k4_xboole_0(X4,X5))
    | ~ spl2_122
    | ~ spl2_150 ),
    inference(superposition,[],[f26138,f39145])).

fof(f26138,plain,
    ( ! [X14,X12,X13] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X12,X13),k4_xboole_0(X12,k4_xboole_0(X13,X14)))
    | ~ spl2_122 ),
    inference(avatar_component_clause,[],[f26137])).

fof(f39146,plain,
    ( spl2_150
    | ~ spl2_11
    | ~ spl2_105
    | ~ spl2_128
    | ~ spl2_129 ),
    inference(avatar_split_clause,[],[f29646,f28788,f28784,f18920,f109,f39144])).

fof(f109,plain,
    ( spl2_11
  <=> ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f18920,plain,
    ( spl2_105
  <=> ! [X53,X52,X54] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X52,X53),k5_xboole_0(k4_xboole_0(X53,X54),k4_xboole_0(X52,X53))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_105])])).

fof(f28784,plain,
    ( spl2_128
  <=> ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_128])])).

fof(f28788,plain,
    ( spl2_129
  <=> ! [X3,X4] : k5_xboole_0(X3,X4) = k5_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X4,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_129])])).

fof(f29646,plain,
    ( ! [X109,X110] : k4_xboole_0(X109,X110) = k4_xboole_0(k5_xboole_0(X109,X110),k4_xboole_0(X110,X109))
    | ~ spl2_11
    | ~ spl2_105
    | ~ spl2_128
    | ~ spl2_129 ),
    inference(forward_demodulation,[],[f29645,f110])).

fof(f110,plain,
    ( ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f109])).

fof(f29645,plain,
    ( ! [X109,X110] : k5_xboole_0(k4_xboole_0(X109,X110),k1_xboole_0) = k4_xboole_0(k5_xboole_0(X109,X110),k4_xboole_0(X110,X109))
    | ~ spl2_105
    | ~ spl2_128
    | ~ spl2_129 ),
    inference(backward_demodulation,[],[f28885,f29424])).

fof(f29424,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,X0),k5_xboole_0(X0,X1))
    | ~ spl2_105
    | ~ spl2_129 ),
    inference(superposition,[],[f18921,f28789])).

fof(f28789,plain,
    ( ! [X4,X3] : k5_xboole_0(X3,X4) = k5_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X4,X3))
    | ~ spl2_129 ),
    inference(avatar_component_clause,[],[f28788])).

fof(f18921,plain,
    ( ! [X54,X52,X53] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X52,X53),k5_xboole_0(k4_xboole_0(X53,X54),k4_xboole_0(X52,X53)))
    | ~ spl2_105 ),
    inference(avatar_component_clause,[],[f18920])).

fof(f28885,plain,
    ( ! [X109,X110] : k4_xboole_0(k5_xboole_0(X109,X110),k4_xboole_0(X110,X109)) = k5_xboole_0(k4_xboole_0(X109,X110),k4_xboole_0(k4_xboole_0(X110,X109),k5_xboole_0(X109,X110)))
    | ~ spl2_128 ),
    inference(superposition,[],[f28785,f28785])).

fof(f28785,plain,
    ( ! [X2,X1] : k4_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X2,X1))
    | ~ spl2_128 ),
    inference(avatar_component_clause,[],[f28784])).

fof(f29688,plain,
    ( spl2_143
    | ~ spl2_104
    | ~ spl2_129 ),
    inference(avatar_split_clause,[],[f29425,f28788,f18916,f29686])).

fof(f18916,plain,
    ( spl2_104
  <=> ! [X20,X19,X21] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X20,X21),k5_xboole_0(k4_xboole_0(X20,X21),k4_xboole_0(X19,X20))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_104])])).

fof(f29425,plain,
    ( ! [X2,X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X3),k5_xboole_0(X2,X3))
    | ~ spl2_104
    | ~ spl2_129 ),
    inference(superposition,[],[f18917,f28789])).

fof(f18917,plain,
    ( ! [X21,X19,X20] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X20,X21),k5_xboole_0(k4_xboole_0(X20,X21),k4_xboole_0(X19,X20)))
    | ~ spl2_104 ),
    inference(avatar_component_clause,[],[f18916])).

fof(f28830,plain,
    ( spl2_139
    | ~ spl2_22
    | ~ spl2_33
    | ~ spl2_125 ),
    inference(avatar_split_clause,[],[f27833,f26973,f586,f319,f28828])).

fof(f586,plain,
    ( spl2_33
  <=> ! [X5,X4] : k4_xboole_0(k5_xboole_0(X4,k4_xboole_0(X5,X4)),k4_xboole_0(X5,X4)) = X4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).

fof(f26973,plain,
    ( spl2_125
  <=> ! [X51,X50] : k5_xboole_0(X51,k4_xboole_0(X50,X51)) = k5_xboole_0(k4_xboole_0(X51,X50),X50) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_125])])).

fof(f27833,plain,
    ( ! [X8,X9] : k4_xboole_0(k5_xboole_0(X9,k4_xboole_0(X8,X9)),k4_xboole_0(X9,X8)) = X8
    | ~ spl2_22
    | ~ spl2_33
    | ~ spl2_125 ),
    inference(forward_demodulation,[],[f27542,f320])).

fof(f27542,plain,
    ( ! [X8,X9] : k4_xboole_0(k5_xboole_0(k4_xboole_0(X8,X9),X9),k4_xboole_0(X9,X8)) = X8
    | ~ spl2_33
    | ~ spl2_125 ),
    inference(superposition,[],[f587,f26974])).

fof(f26974,plain,
    ( ! [X50,X51] : k5_xboole_0(X51,k4_xboole_0(X50,X51)) = k5_xboole_0(k4_xboole_0(X51,X50),X50)
    | ~ spl2_125 ),
    inference(avatar_component_clause,[],[f26973])).

fof(f587,plain,
    ( ! [X4,X5] : k4_xboole_0(k5_xboole_0(X4,k4_xboole_0(X5,X4)),k4_xboole_0(X5,X4)) = X4
    | ~ spl2_33 ),
    inference(avatar_component_clause,[],[f586])).

fof(f28790,plain,
    ( spl2_129
    | ~ spl2_35
    | ~ spl2_124 ),
    inference(avatar_split_clause,[],[f27058,f26969,f980,f28788])).

fof(f980,plain,
    ( spl2_35
  <=> ! [X1,X0,X2] : k5_xboole_0(X0,X1) = k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,X2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_35])])).

fof(f26969,plain,
    ( spl2_124
  <=> ! [X58,X59] : k4_xboole_0(X59,X58) = k5_xboole_0(X58,k5_xboole_0(X59,k4_xboole_0(X58,X59))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_124])])).

fof(f27058,plain,
    ( ! [X4,X3] : k5_xboole_0(X3,X4) = k5_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X4,X3))
    | ~ spl2_35
    | ~ spl2_124 ),
    inference(superposition,[],[f981,f26970])).

fof(f26970,plain,
    ( ! [X59,X58] : k4_xboole_0(X59,X58) = k5_xboole_0(X58,k5_xboole_0(X59,k4_xboole_0(X58,X59)))
    | ~ spl2_124 ),
    inference(avatar_component_clause,[],[f26969])).

fof(f981,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,X2)))
    | ~ spl2_35 ),
    inference(avatar_component_clause,[],[f980])).

fof(f28786,plain,
    ( spl2_128
    | ~ spl2_29
    | ~ spl2_124 ),
    inference(avatar_split_clause,[],[f27057,f26969,f570,f28784])).

fof(f570,plain,
    ( spl2_29
  <=> ! [X1,X0,X2] : k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = X2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).

fof(f27057,plain,
    ( ! [X2,X1] : k4_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X2,X1))
    | ~ spl2_29
    | ~ spl2_124 ),
    inference(superposition,[],[f571,f26970])).

fof(f571,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = X2
    | ~ spl2_29 ),
    inference(avatar_component_clause,[],[f570])).

fof(f26975,plain,
    ( spl2_125
    | ~ spl2_2
    | ~ spl2_7
    | ~ spl2_28
    | ~ spl2_31
    | ~ spl2_52
    | ~ spl2_98
    | ~ spl2_101
    | ~ spl2_115
    | ~ spl2_123 ),
    inference(avatar_split_clause,[],[f26842,f26542,f21875,f17844,f17657,f1733,f578,f492,f59,f35,f26973])).

fof(f492,plain,
    ( spl2_28
  <=> ! [X3,X2] : k4_xboole_0(X2,X3) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).

fof(f578,plain,
    ( spl2_31
  <=> ! [X9,X10] : k4_xboole_0(X10,k4_xboole_0(X9,k4_xboole_0(X9,X10))) = k4_xboole_0(X10,X9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).

fof(f1733,plain,
    ( spl2_52
  <=> ! [X9,X8] : k5_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(X9,k4_xboole_0(X9,X8))) = X8 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_52])])).

fof(f17657,plain,
    ( spl2_98
  <=> ! [X18,X17,X19] : k4_xboole_0(X17,k4_xboole_0(X17,k4_xboole_0(k5_xboole_0(X17,k4_xboole_0(X18,X17)),X19))) = k4_xboole_0(X17,X19) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_98])])).

fof(f17844,plain,
    ( spl2_101
  <=> ! [X22,X21] : k4_xboole_0(X21,k4_xboole_0(X21,X22)) = k4_xboole_0(k4_xboole_0(X22,k4_xboole_0(X22,X21)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_101])])).

fof(f21875,plain,
    ( spl2_115
  <=> ! [X79,X78] : k1_xboole_0 = k4_xboole_0(X79,k5_xboole_0(X78,k4_xboole_0(X79,X78))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_115])])).

fof(f26542,plain,
    ( spl2_123
  <=> ! [X93,X94] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k5_xboole_0(X93,k4_xboole_0(X94,X93)),X94),X93) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_123])])).

fof(f26842,plain,
    ( ! [X50,X51] : k5_xboole_0(X51,k4_xboole_0(X50,X51)) = k5_xboole_0(k4_xboole_0(X51,X50),X50)
    | ~ spl2_2
    | ~ spl2_7
    | ~ spl2_28
    | ~ spl2_31
    | ~ spl2_52
    | ~ spl2_98
    | ~ spl2_101
    | ~ spl2_115
    | ~ spl2_123 ),
    inference(backward_demodulation,[],[f22076,f26839])).

fof(f26839,plain,
    ( ! [X37,X38] : k4_xboole_0(X37,X38) = k4_xboole_0(k5_xboole_0(X37,k4_xboole_0(X38,X37)),X38)
    | ~ spl2_2
    | ~ spl2_7
    | ~ spl2_28
    | ~ spl2_31
    | ~ spl2_98
    | ~ spl2_101
    | ~ spl2_123 ),
    inference(forward_demodulation,[],[f26838,f493])).

fof(f493,plain,
    ( ! [X2,X3] : k4_xboole_0(X2,X3) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X2,X3)))
    | ~ spl2_28 ),
    inference(avatar_component_clause,[],[f492])).

fof(f26838,plain,
    ( ! [X37,X38] : k4_xboole_0(X37,k4_xboole_0(X37,k4_xboole_0(X37,X38))) = k4_xboole_0(k5_xboole_0(X37,k4_xboole_0(X38,X37)),X38)
    | ~ spl2_2
    | ~ spl2_7
    | ~ spl2_31
    | ~ spl2_98
    | ~ spl2_101
    | ~ spl2_123 ),
    inference(forward_demodulation,[],[f26837,f25172])).

fof(f25172,plain,
    ( ! [X17,X15,X16] : k4_xboole_0(X15,k4_xboole_0(k5_xboole_0(X15,k4_xboole_0(X16,X15)),X17)) = k4_xboole_0(X15,k4_xboole_0(X15,X17))
    | ~ spl2_2
    | ~ spl2_31
    | ~ spl2_98
    | ~ spl2_101 ),
    inference(backward_demodulation,[],[f25164,f25171])).

fof(f25171,plain,
    ( ! [X39,X37,X38] : k4_xboole_0(X37,X39) = k4_xboole_0(X37,k4_xboole_0(X39,k4_xboole_0(X39,k5_xboole_0(X37,k4_xboole_0(X38,X37)))))
    | ~ spl2_31
    | ~ spl2_98 ),
    inference(forward_demodulation,[],[f24947,f17658])).

fof(f17658,plain,
    ( ! [X19,X17,X18] : k4_xboole_0(X17,k4_xboole_0(X17,k4_xboole_0(k5_xboole_0(X17,k4_xboole_0(X18,X17)),X19))) = k4_xboole_0(X17,X19)
    | ~ spl2_98 ),
    inference(avatar_component_clause,[],[f17657])).

fof(f24947,plain,
    ( ! [X39,X37,X38] : k4_xboole_0(X37,k4_xboole_0(X39,k4_xboole_0(X39,k5_xboole_0(X37,k4_xboole_0(X38,X37))))) = k4_xboole_0(X37,k4_xboole_0(X37,k4_xboole_0(k5_xboole_0(X37,k4_xboole_0(X38,X37)),X39)))
    | ~ spl2_31
    | ~ spl2_98 ),
    inference(superposition,[],[f17658,f579])).

fof(f579,plain,
    ( ! [X10,X9] : k4_xboole_0(X10,k4_xboole_0(X9,k4_xboole_0(X9,X10))) = k4_xboole_0(X10,X9)
    | ~ spl2_31 ),
    inference(avatar_component_clause,[],[f578])).

fof(f25164,plain,
    ( ! [X17,X15,X16] : k4_xboole_0(X15,k4_xboole_0(k5_xboole_0(X15,k4_xboole_0(X16,X15)),X17)) = k4_xboole_0(X15,k4_xboole_0(X15,k4_xboole_0(X17,k4_xboole_0(X17,k5_xboole_0(X15,k4_xboole_0(X16,X15))))))
    | ~ spl2_2
    | ~ spl2_98
    | ~ spl2_101 ),
    inference(forward_demodulation,[],[f24940,f36])).

fof(f24940,plain,
    ( ! [X17,X15,X16] : k4_xboole_0(X15,k4_xboole_0(k5_xboole_0(X15,k4_xboole_0(X16,X15)),X17)) = k4_xboole_0(X15,k4_xboole_0(X15,k4_xboole_0(k4_xboole_0(X17,k4_xboole_0(X17,k5_xboole_0(X15,k4_xboole_0(X16,X15)))),k1_xboole_0)))
    | ~ spl2_98
    | ~ spl2_101 ),
    inference(superposition,[],[f17658,f17845])).

fof(f17845,plain,
    ( ! [X21,X22] : k4_xboole_0(X21,k4_xboole_0(X21,X22)) = k4_xboole_0(k4_xboole_0(X22,k4_xboole_0(X22,X21)),k1_xboole_0)
    | ~ spl2_101 ),
    inference(avatar_component_clause,[],[f17844])).

fof(f26837,plain,
    ( ! [X37,X38] : k4_xboole_0(k5_xboole_0(X37,k4_xboole_0(X38,X37)),X38) = k4_xboole_0(X37,k4_xboole_0(X37,k4_xboole_0(k5_xboole_0(X37,k4_xboole_0(X38,X37)),X38)))
    | ~ spl2_2
    | ~ spl2_7
    | ~ spl2_123 ),
    inference(forward_demodulation,[],[f26630,f36])).

fof(f26630,plain,
    ( ! [X37,X38] : k4_xboole_0(X37,k4_xboole_0(X37,k4_xboole_0(k5_xboole_0(X37,k4_xboole_0(X38,X37)),X38))) = k4_xboole_0(k4_xboole_0(k5_xboole_0(X37,k4_xboole_0(X38,X37)),X38),k1_xboole_0)
    | ~ spl2_7
    | ~ spl2_123 ),
    inference(superposition,[],[f60,f26543])).

fof(f26543,plain,
    ( ! [X94,X93] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k5_xboole_0(X93,k4_xboole_0(X94,X93)),X94),X93)
    | ~ spl2_123 ),
    inference(avatar_component_clause,[],[f26542])).

fof(f22076,plain,
    ( ! [X50,X51] : k5_xboole_0(X51,k4_xboole_0(X50,X51)) = k5_xboole_0(k4_xboole_0(k5_xboole_0(X51,k4_xboole_0(X50,X51)),X50),X50)
    | ~ spl2_2
    | ~ spl2_52
    | ~ spl2_115 ),
    inference(forward_demodulation,[],[f21950,f36])).

fof(f21950,plain,
    ( ! [X50,X51] : k5_xboole_0(X51,k4_xboole_0(X50,X51)) = k5_xboole_0(k4_xboole_0(k5_xboole_0(X51,k4_xboole_0(X50,X51)),X50),k4_xboole_0(X50,k1_xboole_0))
    | ~ spl2_52
    | ~ spl2_115 ),
    inference(superposition,[],[f1734,f21876])).

fof(f21876,plain,
    ( ! [X78,X79] : k1_xboole_0 = k4_xboole_0(X79,k5_xboole_0(X78,k4_xboole_0(X79,X78)))
    | ~ spl2_115 ),
    inference(avatar_component_clause,[],[f21875])).

fof(f1734,plain,
    ( ! [X8,X9] : k5_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(X9,k4_xboole_0(X9,X8))) = X8
    | ~ spl2_52 ),
    inference(avatar_component_clause,[],[f1733])).

fof(f26971,plain,
    ( spl2_124
    | ~ spl2_2
    | ~ spl2_7
    | ~ spl2_28
    | ~ spl2_31
    | ~ spl2_59
    | ~ spl2_98
    | ~ spl2_101
    | ~ spl2_115
    | ~ spl2_123 ),
    inference(avatar_split_clause,[],[f26841,f26542,f21875,f17844,f17657,f1761,f578,f492,f59,f35,f26969])).

fof(f1761,plain,
    ( spl2_59
  <=> ! [X18,X19] : k4_xboole_0(X18,X19) = k5_xboole_0(k4_xboole_0(X19,k4_xboole_0(X19,X18)),X18) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_59])])).

fof(f26841,plain,
    ( ! [X59,X58] : k4_xboole_0(X59,X58) = k5_xboole_0(X58,k5_xboole_0(X59,k4_xboole_0(X58,X59)))
    | ~ spl2_2
    | ~ spl2_7
    | ~ spl2_28
    | ~ spl2_31
    | ~ spl2_59
    | ~ spl2_98
    | ~ spl2_101
    | ~ spl2_115
    | ~ spl2_123 ),
    inference(backward_demodulation,[],[f22078,f26839])).

fof(f22078,plain,
    ( ! [X59,X58] : k4_xboole_0(k5_xboole_0(X59,k4_xboole_0(X58,X59)),X58) = k5_xboole_0(X58,k5_xboole_0(X59,k4_xboole_0(X58,X59)))
    | ~ spl2_2
    | ~ spl2_59
    | ~ spl2_115 ),
    inference(forward_demodulation,[],[f21952,f36])).

fof(f21952,plain,
    ( ! [X59,X58] : k4_xboole_0(k5_xboole_0(X59,k4_xboole_0(X58,X59)),X58) = k5_xboole_0(k4_xboole_0(X58,k1_xboole_0),k5_xboole_0(X59,k4_xboole_0(X58,X59)))
    | ~ spl2_59
    | ~ spl2_115 ),
    inference(superposition,[],[f1762,f21876])).

fof(f1762,plain,
    ( ! [X19,X18] : k4_xboole_0(X18,X19) = k5_xboole_0(k4_xboole_0(X19,k4_xboole_0(X19,X18)),X18)
    | ~ spl2_59 ),
    inference(avatar_component_clause,[],[f1761])).

fof(f26544,plain,
    ( spl2_123
    | ~ spl2_33
    | ~ spl2_122 ),
    inference(avatar_split_clause,[],[f26273,f26137,f586,f26542])).

fof(f26273,plain,
    ( ! [X94,X93] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k5_xboole_0(X93,k4_xboole_0(X94,X93)),X94),X93)
    | ~ spl2_33
    | ~ spl2_122 ),
    inference(superposition,[],[f26138,f587])).

fof(f26139,plain,
    ( spl2_122
    | ~ spl2_73
    | ~ spl2_121 ),
    inference(avatar_split_clause,[],[f25771,f25713,f2540,f26137])).

fof(f2540,plain,
    ( spl2_73
  <=> ! [X18,X17,X19] : k4_xboole_0(X18,X17) = k4_xboole_0(k4_xboole_0(X18,X17),k4_xboole_0(X17,X19)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_73])])).

fof(f25713,plain,
    ( spl2_121
  <=> ! [X11,X10,X12] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X10,X11),X12),k4_xboole_0(X10,X12)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_121])])).

fof(f25771,plain,
    ( ! [X14,X12,X13] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X12,X13),k4_xboole_0(X12,k4_xboole_0(X13,X14)))
    | ~ spl2_73
    | ~ spl2_121 ),
    inference(superposition,[],[f25714,f2541])).

fof(f2541,plain,
    ( ! [X19,X17,X18] : k4_xboole_0(X18,X17) = k4_xboole_0(k4_xboole_0(X18,X17),k4_xboole_0(X17,X19))
    | ~ spl2_73 ),
    inference(avatar_component_clause,[],[f2540])).

fof(f25714,plain,
    ( ! [X12,X10,X11] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X10,X11),X12),k4_xboole_0(X10,X12))
    | ~ spl2_121 ),
    inference(avatar_component_clause,[],[f25713])).

fof(f25715,plain,
    ( spl2_121
    | ~ spl2_44
    | ~ spl2_120 ),
    inference(avatar_split_clause,[],[f25399,f25296,f1701,f25713])).

fof(f1701,plain,
    ( spl2_44
  <=> ! [X7,X6] : k5_xboole_0(k4_xboole_0(X6,X7),k4_xboole_0(X6,k4_xboole_0(X6,X7))) = X6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).

fof(f25296,plain,
    ( spl2_120
  <=> ! [X22,X21,X23] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X21,X23),k4_xboole_0(k5_xboole_0(X21,k4_xboole_0(X22,X21)),X23)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_120])])).

fof(f25399,plain,
    ( ! [X12,X10,X11] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X10,X11),X12),k4_xboole_0(X10,X12))
    | ~ spl2_44
    | ~ spl2_120 ),
    inference(superposition,[],[f25297,f1702])).

fof(f1702,plain,
    ( ! [X6,X7] : k5_xboole_0(k4_xboole_0(X6,X7),k4_xboole_0(X6,k4_xboole_0(X6,X7))) = X6
    | ~ spl2_44 ),
    inference(avatar_component_clause,[],[f1701])).

fof(f25297,plain,
    ( ! [X23,X21,X22] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X21,X23),k4_xboole_0(k5_xboole_0(X21,k4_xboole_0(X22,X21)),X23))
    | ~ spl2_120 ),
    inference(avatar_component_clause,[],[f25296])).

fof(f25298,plain,
    ( spl2_120
    | ~ spl2_26
    | ~ spl2_98 ),
    inference(avatar_split_clause,[],[f24976,f17657,f448,f25296])).

fof(f448,plain,
    ( spl2_26
  <=> ! [X3,X2] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X2)),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f24976,plain,
    ( ! [X23,X21,X22] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X21,X23),k4_xboole_0(k5_xboole_0(X21,k4_xboole_0(X22,X21)),X23))
    | ~ spl2_26
    | ~ spl2_98 ),
    inference(superposition,[],[f449,f17658])).

fof(f449,plain,
    ( ! [X2,X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X2)),X2)
    | ~ spl2_26 ),
    inference(avatar_component_clause,[],[f448])).

fof(f21877,plain,
    ( spl2_115
    | ~ spl2_21
    | ~ spl2_112 ),
    inference(avatar_split_clause,[],[f20905,f20869,f315,f21875])).

fof(f315,plain,
    ( spl2_21
  <=> ! [X9,X8] : k5_xboole_0(k5_xboole_0(X9,X8),X9) = X8 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f20869,plain,
    ( spl2_112
  <=> ! [X3,X2] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X3,X2),k5_xboole_0(X2,k4_xboole_0(k5_xboole_0(X3,X2),X2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_112])])).

fof(f20905,plain,
    ( ! [X78,X79] : k1_xboole_0 = k4_xboole_0(X79,k5_xboole_0(X78,k4_xboole_0(X79,X78)))
    | ~ spl2_21
    | ~ spl2_112 ),
    inference(superposition,[],[f20870,f316])).

fof(f316,plain,
    ( ! [X8,X9] : k5_xboole_0(k5_xboole_0(X9,X8),X9) = X8
    | ~ spl2_21 ),
    inference(avatar_component_clause,[],[f315])).

fof(f20870,plain,
    ( ! [X2,X3] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X3,X2),k5_xboole_0(X2,k4_xboole_0(k5_xboole_0(X3,X2),X2)))
    | ~ spl2_112 ),
    inference(avatar_component_clause,[],[f20869])).

fof(f20871,plain,
    ( spl2_112
    | ~ spl2_22
    | ~ spl2_30
    | ~ spl2_37
    | ~ spl2_53
    | ~ spl2_88 ),
    inference(avatar_split_clause,[],[f20142,f11480,f1737,f988,f574,f319,f20869])).

fof(f988,plain,
    ( spl2_37
  <=> ! [X3,X5,X4] : k5_xboole_0(X4,X5) = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).

fof(f1737,plain,
    ( spl2_53
  <=> ! [X11,X10] : k4_xboole_0(X11,k4_xboole_0(X11,X10)) = k5_xboole_0(k4_xboole_0(X10,X11),X10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_53])])).

fof(f11480,plain,
    ( spl2_88
  <=> ! [X1,X0,X2] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,k5_xboole_0(X0,X1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_88])])).

fof(f20142,plain,
    ( ! [X2,X3] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X3,X2),k5_xboole_0(X2,k4_xboole_0(k5_xboole_0(X3,X2),X2)))
    | ~ spl2_22
    | ~ spl2_30
    | ~ spl2_37
    | ~ spl2_53
    | ~ spl2_88 ),
    inference(forward_demodulation,[],[f20141,f320])).

fof(f20141,plain,
    ( ! [X2,X3] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X3,X2),k5_xboole_0(k4_xboole_0(k5_xboole_0(X3,X2),X2),X2))
    | ~ spl2_30
    | ~ spl2_37
    | ~ spl2_53
    | ~ spl2_88 ),
    inference(forward_demodulation,[],[f19896,f4748])).

fof(f4748,plain,
    ( ! [X80,X81,X79] : k5_xboole_0(k4_xboole_0(k5_xboole_0(X79,X80),X81),X80) = k5_xboole_0(X79,k4_xboole_0(X81,k4_xboole_0(X81,k5_xboole_0(X79,X80))))
    | ~ spl2_37
    | ~ spl2_53 ),
    inference(superposition,[],[f989,f1738])).

fof(f1738,plain,
    ( ! [X10,X11] : k4_xboole_0(X11,k4_xboole_0(X11,X10)) = k5_xboole_0(k4_xboole_0(X10,X11),X10)
    | ~ spl2_53 ),
    inference(avatar_component_clause,[],[f1737])).

fof(f989,plain,
    ( ! [X4,X5,X3] : k5_xboole_0(X4,X5) = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X5)))
    | ~ spl2_37 ),
    inference(avatar_component_clause,[],[f988])).

fof(f19896,plain,
    ( ! [X2,X3] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X3,X2),k5_xboole_0(X3,k4_xboole_0(X2,k4_xboole_0(X2,k5_xboole_0(X3,X2)))))
    | ~ spl2_30
    | ~ spl2_88 ),
    inference(superposition,[],[f11481,f575])).

fof(f11481,plain,
    ( ! [X2,X0,X1] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,k5_xboole_0(X0,X1)))))
    | ~ spl2_88 ),
    inference(avatar_component_clause,[],[f11480])).

fof(f18922,plain,
    ( spl2_105
    | ~ spl2_32
    | ~ spl2_73 ),
    inference(avatar_split_clause,[],[f2608,f2540,f582,f18920])).

fof(f582,plain,
    ( spl2_32
  <=> ! [X11,X10] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X11,X10),k5_xboole_0(X10,k4_xboole_0(X11,X10))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).

fof(f2608,plain,
    ( ! [X54,X52,X53] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X52,X53),k5_xboole_0(k4_xboole_0(X53,X54),k4_xboole_0(X52,X53)))
    | ~ spl2_32
    | ~ spl2_73 ),
    inference(superposition,[],[f583,f2541])).

fof(f583,plain,
    ( ! [X10,X11] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X11,X10),k5_xboole_0(X10,k4_xboole_0(X11,X10)))
    | ~ spl2_32 ),
    inference(avatar_component_clause,[],[f582])).

fof(f18918,plain,
    ( spl2_104
    | ~ spl2_3
    | ~ spl2_73 ),
    inference(avatar_split_clause,[],[f2597,f2540,f39,f18916])).

fof(f39,plain,
    ( spl2_3
  <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f2597,plain,
    ( ! [X21,X19,X20] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X20,X21),k5_xboole_0(k4_xboole_0(X20,X21),k4_xboole_0(X19,X20)))
    | ~ spl2_3
    | ~ spl2_73 ),
    inference(superposition,[],[f40,f2541])).

fof(f40,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f39])).

fof(f17846,plain,
    ( spl2_101
    | ~ spl2_2
    | ~ spl2_7
    | ~ spl2_95 ),
    inference(avatar_split_clause,[],[f17151,f16875,f59,f35,f17844])).

fof(f16875,plain,
    ( spl2_95
  <=> ! [X7,X8] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X7)),k4_xboole_0(X7,k4_xboole_0(X7,X8))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_95])])).

fof(f17151,plain,
    ( ! [X21,X22] : k4_xboole_0(X21,k4_xboole_0(X21,X22)) = k4_xboole_0(k4_xboole_0(X22,k4_xboole_0(X22,X21)),k1_xboole_0)
    | ~ spl2_2
    | ~ spl2_7
    | ~ spl2_95 ),
    inference(forward_demodulation,[],[f17150,f16876])).

fof(f16876,plain,
    ( ! [X8,X7] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X7)),k4_xboole_0(X7,k4_xboole_0(X7,X8)))
    | ~ spl2_95 ),
    inference(avatar_component_clause,[],[f16875])).

fof(f17150,plain,
    ( ! [X21,X22] : k4_xboole_0(X21,k4_xboole_0(X21,X22)) = k4_xboole_0(k4_xboole_0(X22,k4_xboole_0(X22,X21)),k4_xboole_0(k4_xboole_0(X22,k4_xboole_0(X22,X21)),k4_xboole_0(X21,k4_xboole_0(X21,X22))))
    | ~ spl2_2
    | ~ spl2_7
    | ~ spl2_95 ),
    inference(forward_demodulation,[],[f16974,f36])).

fof(f16974,plain,
    ( ! [X21,X22] : k4_xboole_0(k4_xboole_0(X22,k4_xboole_0(X22,X21)),k4_xboole_0(k4_xboole_0(X22,k4_xboole_0(X22,X21)),k4_xboole_0(X21,k4_xboole_0(X21,X22)))) = k4_xboole_0(k4_xboole_0(X21,k4_xboole_0(X21,X22)),k1_xboole_0)
    | ~ spl2_7
    | ~ spl2_95 ),
    inference(superposition,[],[f60,f16876])).

fof(f17659,plain,
    ( spl2_98
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_46 ),
    inference(avatar_split_clause,[],[f1868,f1709,f39,f35,f17657])).

fof(f1868,plain,
    ( ! [X19,X17,X18] : k4_xboole_0(X17,k4_xboole_0(X17,k4_xboole_0(k5_xboole_0(X17,k4_xboole_0(X18,X17)),X19))) = k4_xboole_0(X17,X19)
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_46 ),
    inference(forward_demodulation,[],[f1798,f36])).

fof(f1798,plain,
    ( ! [X19,X17,X18] : k4_xboole_0(X17,k4_xboole_0(X17,k4_xboole_0(k5_xboole_0(X17,k4_xboole_0(X18,X17)),X19))) = k4_xboole_0(k4_xboole_0(X17,k1_xboole_0),X19)
    | ~ spl2_3
    | ~ spl2_46 ),
    inference(superposition,[],[f1710,f40])).

fof(f16877,plain,
    ( spl2_95
    | ~ spl2_2
    | ~ spl2_12
    | ~ spl2_31 ),
    inference(avatar_split_clause,[],[f751,f578,f116,f35,f16875])).

fof(f116,plain,
    ( spl2_12
  <=> ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f751,plain,
    ( ! [X8,X7] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X7)),k4_xboole_0(X7,k4_xboole_0(X7,X8)))
    | ~ spl2_2
    | ~ spl2_12
    | ~ spl2_31 ),
    inference(forward_demodulation,[],[f750,f117])).

fof(f117,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f116])).

fof(f750,plain,
    ( ! [X8,X7] : k4_xboole_0(X8,X8) = k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X7)),k4_xboole_0(X7,k4_xboole_0(X7,X8)))
    | ~ spl2_2
    | ~ spl2_12
    | ~ spl2_31 ),
    inference(forward_demodulation,[],[f749,f36])).

fof(f749,plain,
    ( ! [X8,X7] : k4_xboole_0(X8,k4_xboole_0(X8,k1_xboole_0)) = k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X7)),k4_xboole_0(X7,k4_xboole_0(X7,X8)))
    | ~ spl2_12
    | ~ spl2_31 ),
    inference(forward_demodulation,[],[f748,f117])).

fof(f748,plain,
    ( ! [X8,X7] : k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X7)),k4_xboole_0(X7,k4_xboole_0(X7,X8))) = k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X7,X7)))
    | ~ spl2_31 ),
    inference(forward_demodulation,[],[f718,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f23,f21,f21])).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f23,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f718,plain,
    ( ! [X8,X7] : k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X7)),X7) = k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X7)),k4_xboole_0(X7,k4_xboole_0(X7,X8)))
    | ~ spl2_31 ),
    inference(superposition,[],[f579,f579])).

fof(f11482,plain,
    ( spl2_88
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f63,f51,f39,f11480])).

fof(f51,plain,
    ( spl2_5
  <=> ! [X1,X0,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f63,plain,
    ( ! [X2,X0,X1] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,k5_xboole_0(X0,X1)))))
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(superposition,[],[f40,f52])).

fof(f52,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f51])).

fof(f2542,plain,
    ( spl2_73
    | ~ spl2_68
    | ~ spl2_71 ),
    inference(avatar_split_clause,[],[f2316,f2307,f2031,f2540])).

fof(f2031,plain,
    ( spl2_68
  <=> ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X2,X1)) = X1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_68])])).

fof(f2307,plain,
    ( spl2_71
  <=> ! [X1,X0,X2] : k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X2)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_71])])).

fof(f2316,plain,
    ( ! [X19,X17,X18] : k4_xboole_0(X18,X17) = k4_xboole_0(k4_xboole_0(X18,X17),k4_xboole_0(X17,X19))
    | ~ spl2_68
    | ~ spl2_71 ),
    inference(superposition,[],[f2308,f2032])).

fof(f2032,plain,
    ( ! [X2,X1] : k4_xboole_0(X1,k4_xboole_0(X2,X1)) = X1
    | ~ spl2_68 ),
    inference(avatar_component_clause,[],[f2031])).

fof(f2308,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X2)) = X0
    | ~ spl2_71 ),
    inference(avatar_component_clause,[],[f2307])).

fof(f2309,plain,
    ( spl2_71
    | ~ spl2_6
    | ~ spl2_11
    | ~ spl2_70 ),
    inference(avatar_split_clause,[],[f2274,f2172,f109,f55,f2307])).

fof(f55,plain,
    ( spl2_6
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f2172,plain,
    ( spl2_70
  <=> ! [X22,X21,X23] : k1_xboole_0 = k4_xboole_0(X21,k4_xboole_0(X21,k4_xboole_0(k4_xboole_0(X22,X21),X23))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_70])])).

fof(f2274,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X2)) = X0
    | ~ spl2_6
    | ~ spl2_11
    | ~ spl2_70 ),
    inference(forward_demodulation,[],[f2213,f110])).

fof(f2213,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X2))
    | ~ spl2_6
    | ~ spl2_70 ),
    inference(superposition,[],[f56,f2173])).

fof(f2173,plain,
    ( ! [X23,X21,X22] : k1_xboole_0 = k4_xboole_0(X21,k4_xboole_0(X21,k4_xboole_0(k4_xboole_0(X22,X21),X23)))
    | ~ spl2_70 ),
    inference(avatar_component_clause,[],[f2172])).

fof(f56,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f55])).

fof(f2174,plain,
    ( spl2_70
    | ~ spl2_1
    | ~ spl2_46
    | ~ spl2_67 ),
    inference(avatar_split_clause,[],[f2005,f1934,f1709,f31,f2172])).

fof(f31,plain,
    ( spl2_1
  <=> ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f1934,plain,
    ( spl2_67
  <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_67])])).

fof(f2005,plain,
    ( ! [X23,X21,X22] : k1_xboole_0 = k4_xboole_0(X21,k4_xboole_0(X21,k4_xboole_0(k4_xboole_0(X22,X21),X23)))
    | ~ spl2_1
    | ~ spl2_46
    | ~ spl2_67 ),
    inference(forward_demodulation,[],[f1966,f32])).

fof(f32,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f31])).

fof(f1966,plain,
    ( ! [X23,X21,X22] : k4_xboole_0(X21,k4_xboole_0(X21,k4_xboole_0(k4_xboole_0(X22,X21),X23))) = k4_xboole_0(k1_xboole_0,X23)
    | ~ spl2_46
    | ~ spl2_67 ),
    inference(superposition,[],[f1710,f1935])).

fof(f1935,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))
    | ~ spl2_67 ),
    inference(avatar_component_clause,[],[f1934])).

fof(f2106,plain,
    ( spl2_69
    | ~ spl2_11
    | ~ spl2_23
    | ~ spl2_67 ),
    inference(avatar_split_clause,[],[f1999,f1934,f384,f109,f2104])).

fof(f1999,plain,
    ( ! [X8,X7] : k4_xboole_0(X8,X7) = k4_xboole_0(k4_xboole_0(X8,X7),X7)
    | ~ spl2_11
    | ~ spl2_23
    | ~ spl2_67 ),
    inference(forward_demodulation,[],[f1960,f110])).

fof(f1960,plain,
    ( ! [X8,X7] : k4_xboole_0(k4_xboole_0(X8,X7),X7) = k5_xboole_0(k4_xboole_0(X8,X7),k1_xboole_0)
    | ~ spl2_23
    | ~ spl2_67 ),
    inference(superposition,[],[f385,f1935])).

fof(f2033,plain,
    ( spl2_68
    | ~ spl2_6
    | ~ spl2_11
    | ~ spl2_67 ),
    inference(avatar_split_clause,[],[f1996,f1934,f109,f55,f2031])).

fof(f1996,plain,
    ( ! [X2,X1] : k4_xboole_0(X1,k4_xboole_0(X2,X1)) = X1
    | ~ spl2_6
    | ~ spl2_11
    | ~ spl2_67 ),
    inference(forward_demodulation,[],[f1959,f110])).

fof(f1959,plain,
    ( ! [X2,X1] : k5_xboole_0(X1,k1_xboole_0) = k4_xboole_0(X1,k4_xboole_0(X2,X1))
    | ~ spl2_6
    | ~ spl2_67 ),
    inference(superposition,[],[f56,f1935])).

fof(f1936,plain,
    ( spl2_67
    | ~ spl2_25
    | ~ spl2_46 ),
    inference(avatar_split_clause,[],[f1814,f1709,f425,f1934])).

fof(f425,plain,
    ( spl2_25
  <=> ! [X5,X6] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X5,X6),X5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).

fof(f1814,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))
    | ~ spl2_25
    | ~ spl2_46 ),
    inference(superposition,[],[f1710,f426])).

fof(f426,plain,
    ( ! [X6,X5] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X5,X6),X5)
    | ~ spl2_25 ),
    inference(avatar_component_clause,[],[f425])).

fof(f1763,plain,
    ( spl2_59
    | ~ spl2_21
    | ~ spl2_34 ),
    inference(avatar_split_clause,[],[f916,f868,f315,f1761])).

fof(f868,plain,
    ( spl2_34
  <=> ! [X5,X4] : k4_xboole_0(X5,k4_xboole_0(X5,X4)) = k5_xboole_0(X4,k4_xboole_0(X4,X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).

fof(f916,plain,
    ( ! [X19,X18] : k4_xboole_0(X18,X19) = k5_xboole_0(k4_xboole_0(X19,k4_xboole_0(X19,X18)),X18)
    | ~ spl2_21
    | ~ spl2_34 ),
    inference(superposition,[],[f316,f869])).

fof(f869,plain,
    ( ! [X4,X5] : k4_xboole_0(X5,k4_xboole_0(X5,X4)) = k5_xboole_0(X4,k4_xboole_0(X4,X5))
    | ~ spl2_34 ),
    inference(avatar_component_clause,[],[f868])).

fof(f1739,plain,
    ( spl2_53
    | ~ spl2_21
    | ~ spl2_23 ),
    inference(avatar_split_clause,[],[f407,f384,f315,f1737])).

fof(f407,plain,
    ( ! [X10,X11] : k4_xboole_0(X11,k4_xboole_0(X11,X10)) = k5_xboole_0(k4_xboole_0(X10,X11),X10)
    | ~ spl2_21
    | ~ spl2_23 ),
    inference(superposition,[],[f316,f385])).

fof(f1735,plain,
    ( spl2_52
    | ~ spl2_20
    | ~ spl2_23 ),
    inference(avatar_split_clause,[],[f406,f384,f311,f1733])).

fof(f311,plain,
    ( spl2_20
  <=> ! [X7,X6] : k5_xboole_0(k5_xboole_0(X6,X7),X7) = X6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f406,plain,
    ( ! [X8,X9] : k5_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(X9,k4_xboole_0(X9,X8))) = X8
    | ~ spl2_20
    | ~ spl2_23 ),
    inference(superposition,[],[f312,f385])).

fof(f312,plain,
    ( ! [X6,X7] : k5_xboole_0(k5_xboole_0(X6,X7),X7) = X6
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f311])).

fof(f1711,plain,(
    spl2_46 ),
    inference(avatar_split_clause,[],[f29,f1709])).

fof(f1703,plain,
    ( spl2_44
    | ~ spl2_6
    | ~ spl2_20 ),
    inference(avatar_split_clause,[],[f324,f311,f55,f1701])).

fof(f324,plain,
    ( ! [X6,X7] : k5_xboole_0(k4_xboole_0(X6,X7),k4_xboole_0(X6,k4_xboole_0(X6,X7))) = X6
    | ~ spl2_6
    | ~ spl2_20 ),
    inference(superposition,[],[f312,f56])).

fof(f990,plain,
    ( spl2_37
    | ~ spl2_5
    | ~ spl2_19 ),
    inference(avatar_split_clause,[],[f307,f286,f51,f988])).

fof(f286,plain,
    ( spl2_19
  <=> ! [X7,X6] : k5_xboole_0(X7,k5_xboole_0(X6,X7)) = X6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f307,plain,
    ( ! [X4,X5,X3] : k5_xboole_0(X4,X5) = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X5)))
    | ~ spl2_5
    | ~ spl2_19 ),
    inference(forward_demodulation,[],[f299,f52])).

fof(f299,plain,
    ( ! [X4,X5,X3] : k5_xboole_0(X4,X5) = k5_xboole_0(X3,k5_xboole_0(k5_xboole_0(X4,X3),X5))
    | ~ spl2_5
    | ~ spl2_19 ),
    inference(superposition,[],[f52,f287])).

fof(f287,plain,
    ( ! [X6,X7] : k5_xboole_0(X7,k5_xboole_0(X6,X7)) = X6
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f286])).

fof(f982,plain,
    ( spl2_35
    | ~ spl2_5
    | ~ spl2_19 ),
    inference(avatar_split_clause,[],[f289,f286,f51,f980])).

fof(f289,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,X2)))
    | ~ spl2_5
    | ~ spl2_19 ),
    inference(superposition,[],[f287,f52])).

fof(f870,plain,
    ( spl2_34
    | ~ spl2_18
    | ~ spl2_23 ),
    inference(avatar_split_clause,[],[f404,f384,f259,f868])).

fof(f259,plain,
    ( spl2_18
  <=> ! [X3,X2] : k5_xboole_0(X2,k5_xboole_0(X2,X3)) = X3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f404,plain,
    ( ! [X4,X5] : k4_xboole_0(X5,k4_xboole_0(X5,X4)) = k5_xboole_0(X4,k4_xboole_0(X4,X5))
    | ~ spl2_18
    | ~ spl2_23 ),
    inference(superposition,[],[f260,f385])).

fof(f260,plain,
    ( ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(X2,X3)) = X3
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f259])).

fof(f588,plain,
    ( spl2_33
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_7
    | ~ spl2_27 ),
    inference(avatar_split_clause,[],[f525,f488,f59,f39,f35,f586])).

fof(f488,plain,
    ( spl2_27
  <=> ! [X7,X6] : k4_xboole_0(X7,X6) = k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(X7,X6)),X6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).

fof(f525,plain,
    ( ! [X4,X5] : k4_xboole_0(k5_xboole_0(X4,k4_xboole_0(X5,X4)),k4_xboole_0(X5,X4)) = X4
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_7
    | ~ spl2_27 ),
    inference(forward_demodulation,[],[f524,f36])).

fof(f524,plain,
    ( ! [X4,X5] : k4_xboole_0(X4,k1_xboole_0) = k4_xboole_0(k5_xboole_0(X4,k4_xboole_0(X5,X4)),k4_xboole_0(X5,X4))
    | ~ spl2_3
    | ~ spl2_7
    | ~ spl2_27 ),
    inference(forward_demodulation,[],[f509,f40])).

fof(f509,plain,
    ( ! [X4,X5] : k4_xboole_0(X4,k4_xboole_0(X4,k5_xboole_0(X4,k4_xboole_0(X5,X4)))) = k4_xboole_0(k5_xboole_0(X4,k4_xboole_0(X5,X4)),k4_xboole_0(X5,X4))
    | ~ spl2_7
    | ~ spl2_27 ),
    inference(superposition,[],[f60,f489])).

fof(f489,plain,
    ( ! [X6,X7] : k4_xboole_0(X7,X6) = k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(X7,X6)),X6)
    | ~ spl2_27 ),
    inference(avatar_component_clause,[],[f488])).

fof(f584,plain,
    ( spl2_32
    | ~ spl2_25
    | ~ spl2_27 ),
    inference(avatar_split_clause,[],[f512,f488,f425,f582])).

fof(f512,plain,
    ( ! [X10,X11] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X11,X10),k5_xboole_0(X10,k4_xboole_0(X11,X10)))
    | ~ spl2_25
    | ~ spl2_27 ),
    inference(superposition,[],[f426,f489])).

fof(f580,plain,
    ( spl2_31
    | ~ spl2_2
    | ~ spl2_23
    | ~ spl2_26 ),
    inference(avatar_split_clause,[],[f481,f448,f384,f35,f578])).

fof(f481,plain,
    ( ! [X10,X9] : k4_xboole_0(X10,k4_xboole_0(X9,k4_xboole_0(X9,X10))) = k4_xboole_0(X10,X9)
    | ~ spl2_2
    | ~ spl2_23
    | ~ spl2_26 ),
    inference(forward_demodulation,[],[f480,f385])).

fof(f480,plain,
    ( ! [X10,X9] : k4_xboole_0(X10,k4_xboole_0(X9,k4_xboole_0(X9,X10))) = k5_xboole_0(X10,k4_xboole_0(X9,k4_xboole_0(X9,X10)))
    | ~ spl2_2
    | ~ spl2_23
    | ~ spl2_26 ),
    inference(forward_demodulation,[],[f467,f36])).

fof(f467,plain,
    ( ! [X10,X9] : k4_xboole_0(X10,k4_xboole_0(X9,k4_xboole_0(X9,X10))) = k5_xboole_0(X10,k4_xboole_0(k4_xboole_0(X9,k4_xboole_0(X9,X10)),k1_xboole_0))
    | ~ spl2_23
    | ~ spl2_26 ),
    inference(superposition,[],[f385,f449])).

fof(f576,plain,
    ( spl2_30
    | ~ spl2_6
    | ~ spl2_9
    | ~ spl2_11
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f223,f152,f109,f85,f55,f574])).

fof(f85,plain,
    ( spl2_9
  <=> ! [X2] : k1_xboole_0 = k5_xboole_0(X2,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f152,plain,
    ( spl2_14
  <=> ! [X1,X0] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f223,plain,
    ( ! [X4,X5] : k4_xboole_0(X4,k4_xboole_0(X4,X5)) = k5_xboole_0(X4,k4_xboole_0(X4,X5))
    | ~ spl2_6
    | ~ spl2_9
    | ~ spl2_11
    | ~ spl2_14 ),
    inference(forward_demodulation,[],[f201,f216])).

fof(f216,plain,
    ( ! [X3] : k5_xboole_0(k1_xboole_0,X3) = X3
    | ~ spl2_9
    | ~ spl2_11
    | ~ spl2_14 ),
    inference(forward_demodulation,[],[f200,f110])).

fof(f200,plain,
    ( ! [X3] : k5_xboole_0(X3,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X3)
    | ~ spl2_9
    | ~ spl2_14 ),
    inference(superposition,[],[f153,f86])).

fof(f86,plain,
    ( ! [X2] : k1_xboole_0 = k5_xboole_0(X2,X2)
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f85])).

fof(f153,plain,
    ( ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f152])).

fof(f201,plain,
    ( ! [X4,X5] : k5_xboole_0(k1_xboole_0,k4_xboole_0(X4,k4_xboole_0(X4,X5))) = k5_xboole_0(X4,k4_xboole_0(X4,X5))
    | ~ spl2_6
    | ~ spl2_14 ),
    inference(superposition,[],[f153,f56])).

fof(f572,plain,
    ( spl2_29
    | ~ spl2_5
    | ~ spl2_9
    | ~ spl2_11
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f217,f152,f109,f85,f51,f570])).

fof(f217,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = X2
    | ~ spl2_5
    | ~ spl2_9
    | ~ spl2_11
    | ~ spl2_14 ),
    inference(backward_demodulation,[],[f199,f216])).

fof(f199,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(k1_xboole_0,X2) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2)))
    | ~ spl2_5
    | ~ spl2_14 ),
    inference(superposition,[],[f153,f52])).

fof(f494,plain,
    ( spl2_28
    | ~ spl2_2
    | ~ spl2_7
    | ~ spl2_25 ),
    inference(avatar_split_clause,[],[f443,f425,f59,f35,f492])).

fof(f443,plain,
    ( ! [X2,X3] : k4_xboole_0(X2,X3) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X2,X3)))
    | ~ spl2_2
    | ~ spl2_7
    | ~ spl2_25 ),
    inference(forward_demodulation,[],[f437,f36])).

fof(f437,plain,
    ( ! [X2,X3] : k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k4_xboole_0(k4_xboole_0(X2,X3),k1_xboole_0)
    | ~ spl2_7
    | ~ spl2_25 ),
    inference(superposition,[],[f60,f426])).

fof(f490,plain,
    ( spl2_27
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_21
    | ~ spl2_23 ),
    inference(avatar_split_clause,[],[f414,f384,f315,f39,f35,f488])).

fof(f414,plain,
    ( ! [X6,X7] : k4_xboole_0(X7,X6) = k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(X7,X6)),X6)
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_21
    | ~ spl2_23 ),
    inference(forward_demodulation,[],[f413,f316])).

fof(f413,plain,
    ( ! [X6,X7] : k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(X7,X6)),X6) = k5_xboole_0(k5_xboole_0(X6,k4_xboole_0(X7,X6)),X6)
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_23 ),
    inference(forward_demodulation,[],[f396,f36])).

fof(f396,plain,
    ( ! [X6,X7] : k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(X7,X6)),X6) = k5_xboole_0(k5_xboole_0(X6,k4_xboole_0(X7,X6)),k4_xboole_0(X6,k1_xboole_0))
    | ~ spl2_3
    | ~ spl2_23 ),
    inference(superposition,[],[f385,f40])).

fof(f450,plain,
    ( spl2_26
    | ~ spl2_7
    | ~ spl2_25 ),
    inference(avatar_split_clause,[],[f430,f425,f59,f448])).

fof(f430,plain,
    ( ! [X2,X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X2)),X2)
    | ~ spl2_7
    | ~ spl2_25 ),
    inference(superposition,[],[f426,f60])).

fof(f427,plain,
    ( spl2_25
    | ~ spl2_3
    | ~ spl2_7
    | ~ spl2_20
    | ~ spl2_23 ),
    inference(avatar_split_clause,[],[f420,f384,f311,f59,f39,f425])).

fof(f420,plain,
    ( ! [X6,X5] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X5,X6),X5)
    | ~ spl2_3
    | ~ spl2_7
    | ~ spl2_20
    | ~ spl2_23 ),
    inference(backward_demodulation,[],[f132,f406])).

fof(f132,plain,
    ( ! [X6,X5] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X5,X6),k5_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X6,k4_xboole_0(X6,X5))))
    | ~ spl2_3
    | ~ spl2_7 ),
    inference(superposition,[],[f40,f60])).

fof(f391,plain,(
    ~ spl2_24 ),
    inference(avatar_split_clause,[],[f26,f388])).

fof(f26,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f15,f20,f21])).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f15,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f13])).

fof(f13,plain,
    ( ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_xboole_1)).

fof(f386,plain,
    ( spl2_23
    | ~ spl2_6
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f130,f59,f55,f384])).

fof(f130,plain,
    ( ! [X2,X1] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))
    | ~ spl2_6
    | ~ spl2_7 ),
    inference(superposition,[],[f56,f60])).

fof(f321,plain,
    ( spl2_22
    | ~ spl2_18
    | ~ spl2_19 ),
    inference(avatar_split_clause,[],[f298,f286,f259,f319])).

fof(f298,plain,
    ( ! [X2,X1] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1)
    | ~ spl2_18
    | ~ spl2_19 ),
    inference(superposition,[],[f260,f287])).

fof(f317,plain,
    ( spl2_21
    | ~ spl2_19 ),
    inference(avatar_split_clause,[],[f293,f286,f315])).

fof(f293,plain,
    ( ! [X8,X9] : k5_xboole_0(k5_xboole_0(X9,X8),X9) = X8
    | ~ spl2_19 ),
    inference(superposition,[],[f287,f287])).

fof(f313,plain,
    ( spl2_20
    | ~ spl2_18
    | ~ spl2_19 ),
    inference(avatar_split_clause,[],[f292,f286,f259,f311])).

fof(f292,plain,
    ( ! [X6,X7] : k5_xboole_0(k5_xboole_0(X6,X7),X7) = X6
    | ~ spl2_18
    | ~ spl2_19 ),
    inference(superposition,[],[f287,f260])).

fof(f288,plain,
    ( spl2_19
    | ~ spl2_11
    | ~ spl2_13
    | ~ spl2_18 ),
    inference(avatar_split_clause,[],[f277,f259,f148,f109,f286])).

fof(f148,plain,
    ( spl2_13
  <=> ! [X1,X0] : k1_xboole_0 = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f277,plain,
    ( ! [X6,X7] : k5_xboole_0(X7,k5_xboole_0(X6,X7)) = X6
    | ~ spl2_11
    | ~ spl2_13
    | ~ spl2_18 ),
    inference(forward_demodulation,[],[f265,f110])).

fof(f265,plain,
    ( ! [X6,X7] : k5_xboole_0(X7,k5_xboole_0(X6,X7)) = k5_xboole_0(X6,k1_xboole_0)
    | ~ spl2_13
    | ~ spl2_18 ),
    inference(superposition,[],[f260,f149])).

fof(f149,plain,
    ( ! [X0,X1] : k1_xboole_0 = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1)))
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f148])).

fof(f261,plain,
    ( spl2_18
    | ~ spl2_5
    | ~ spl2_9
    | ~ spl2_11
    | ~ spl2_14
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f222,f177,f152,f109,f85,f51,f259])).

fof(f177,plain,
    ( spl2_16
  <=> ! [X8] : k1_xboole_0 = k5_xboole_0(X8,k5_xboole_0(k1_xboole_0,X8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f222,plain,
    ( ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(X2,X3)) = X3
    | ~ spl2_5
    | ~ spl2_9
    | ~ spl2_11
    | ~ spl2_14
    | ~ spl2_16 ),
    inference(forward_demodulation,[],[f218,f216])).

fof(f218,plain,
    ( ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(k1_xboole_0,k5_xboole_0(X2,X3))) = X3
    | ~ spl2_5
    | ~ spl2_9
    | ~ spl2_11
    | ~ spl2_14
    | ~ spl2_16 ),
    inference(backward_demodulation,[],[f197,f216])).

fof(f197,plain,
    ( ! [X2,X3] : k5_xboole_0(k1_xboole_0,X3) = k5_xboole_0(X2,k5_xboole_0(k1_xboole_0,k5_xboole_0(X2,X3)))
    | ~ spl2_5
    | ~ spl2_16 ),
    inference(forward_demodulation,[],[f188,f52])).

fof(f188,plain,
    ( ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(k1_xboole_0,X2),X3)) = k5_xboole_0(k1_xboole_0,X3)
    | ~ spl2_5
    | ~ spl2_16 ),
    inference(superposition,[],[f52,f178])).

fof(f178,plain,
    ( ! [X8] : k1_xboole_0 = k5_xboole_0(X8,k5_xboole_0(k1_xboole_0,X8))
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f177])).

fof(f179,plain,
    ( spl2_16
    | ~ spl2_11
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f163,f148,f109,f177])).

fof(f163,plain,
    ( ! [X8] : k1_xboole_0 = k5_xboole_0(X8,k5_xboole_0(k1_xboole_0,X8))
    | ~ spl2_11
    | ~ spl2_13 ),
    inference(superposition,[],[f149,f110])).

fof(f154,plain,
    ( spl2_14
    | ~ spl2_5
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f89,f85,f51,f152])).

fof(f89,plain,
    ( ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))
    | ~ spl2_5
    | ~ spl2_9 ),
    inference(superposition,[],[f52,f86])).

fof(f150,plain,
    ( spl2_13
    | ~ spl2_5
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f88,f85,f51,f148])).

fof(f88,plain,
    ( ! [X0,X1] : k1_xboole_0 = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1)))
    | ~ spl2_5
    | ~ spl2_9 ),
    inference(superposition,[],[f86,f52])).

fof(f118,plain,
    ( spl2_12
    | ~ spl2_3
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f99,f93,f39,f116])).

fof(f93,plain,
    ( spl2_10
  <=> ! [X1] : k5_xboole_0(X1,k4_xboole_0(X1,X1)) = X1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f99,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)
    | ~ spl2_3
    | ~ spl2_10 ),
    inference(superposition,[],[f40,f94])).

fof(f94,plain,
    ( ! [X1] : k5_xboole_0(X1,k4_xboole_0(X1,X1)) = X1
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f93])).

fof(f111,plain,
    ( spl2_11
    | ~ spl2_3
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f102,f93,f39,f109])).

fof(f102,plain,
    ( ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1
    | ~ spl2_3
    | ~ spl2_10 ),
    inference(backward_demodulation,[],[f94,f99])).

fof(f95,plain,
    ( spl2_10
    | ~ spl2_2
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f68,f55,f35,f93])).

fof(f68,plain,
    ( ! [X1] : k5_xboole_0(X1,k4_xboole_0(X1,X1)) = X1
    | ~ spl2_2
    | ~ spl2_6 ),
    inference(superposition,[],[f56,f36])).

fof(f87,plain,
    ( spl2_9
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f76,f55,f39,f35,f85])).

fof(f76,plain,
    ( ! [X2] : k1_xboole_0 = k5_xboole_0(X2,X2)
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f69,f36])).

fof(f69,plain,
    ( ! [X2] : k1_xboole_0 = k5_xboole_0(X2,k4_xboole_0(X2,k1_xboole_0))
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(superposition,[],[f56,f40])).

fof(f61,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f28,f59])).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f19,f21,f21])).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f57,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f25,f55])).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f22,f21])).

fof(f22,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f53,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f24,f51])).

fof(f24,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f41,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f27,f39])).

fof(f27,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f18,f20])).

fof(f18,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f37,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f17,f35])).

fof(f17,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f33,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f16,f31])).

fof(f16,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:59:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.45  % (26236)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.47  % (26225)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.48  % (26232)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.52  % (26230)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.52  % (26227)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.52  % (26228)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.53  % (26240)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.53  % (26229)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (26238)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.53  % (26231)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.53  % (26234)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.53  % (26241)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.53  % (26234)Refutation not found, incomplete strategy% (26234)------------------------------
% 0.21/0.53  % (26234)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (26234)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (26234)Memory used [KB]: 10490
% 0.21/0.53  % (26234)Time elapsed: 0.090 s
% 0.21/0.53  % (26234)------------------------------
% 0.21/0.53  % (26234)------------------------------
% 0.21/0.55  % (26239)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.55  % (26237)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.55  % (26224)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.57  % (26226)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.58  % (26223)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 1.76/0.59  % (26233)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 5.13/1.04  % (26227)Time limit reached!
% 5.13/1.04  % (26227)------------------------------
% 5.13/1.04  % (26227)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.13/1.04  % (26227)Termination reason: Time limit
% 5.13/1.04  % (26227)Termination phase: Saturation
% 5.13/1.04  
% 5.13/1.04  % (26227)Memory used [KB]: 21364
% 5.13/1.04  % (26227)Time elapsed: 0.600 s
% 5.13/1.04  % (26227)------------------------------
% 5.13/1.04  % (26227)------------------------------
% 12.46/1.95  % (26229)Time limit reached!
% 12.46/1.95  % (26229)------------------------------
% 12.46/1.95  % (26229)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.46/1.95  % (26229)Termination reason: Time limit
% 12.46/1.95  
% 12.46/1.95  % (26229)Memory used [KB]: 39146
% 12.46/1.95  % (26229)Time elapsed: 1.511 s
% 12.46/1.95  % (26229)------------------------------
% 12.46/1.95  % (26229)------------------------------
% 12.46/1.96  % (26228)Time limit reached!
% 12.46/1.96  % (26228)------------------------------
% 12.46/1.96  % (26228)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.46/1.96  % (26228)Termination reason: Time limit
% 12.46/1.96  
% 12.46/1.96  % (26228)Memory used [KB]: 45031
% 12.46/1.96  % (26228)Time elapsed: 1.523 s
% 12.46/1.96  % (26228)------------------------------
% 12.46/1.96  % (26228)------------------------------
% 14.96/2.23  % (26225)Time limit reached!
% 14.96/2.23  % (26225)------------------------------
% 14.96/2.23  % (26225)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.96/2.25  % (26225)Termination reason: Time limit
% 14.96/2.25  
% 14.96/2.25  % (26225)Memory used [KB]: 40937
% 14.96/2.25  % (26225)Time elapsed: 1.821 s
% 14.96/2.25  % (26225)------------------------------
% 14.96/2.25  % (26225)------------------------------
% 18.51/2.68  % (26236)Time limit reached!
% 18.51/2.68  % (26236)------------------------------
% 18.51/2.68  % (26236)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 18.51/2.68  % (26236)Termination reason: Time limit
% 18.51/2.68  
% 18.51/2.68  % (26236)Memory used [KB]: 68698
% 18.51/2.68  % (26236)Time elapsed: 2.240 s
% 18.51/2.68  % (26236)------------------------------
% 18.51/2.68  % (26236)------------------------------
% 25.62/3.65  % (26230)Refutation found. Thanks to Tanya!
% 25.62/3.65  % SZS status Theorem for theBenchmark
% 25.62/3.65  % SZS output start Proof for theBenchmark
% 25.62/3.65  fof(f45176,plain,(
% 25.62/3.65    $false),
% 25.62/3.65    inference(avatar_sat_refutation,[],[f33,f37,f41,f53,f57,f61,f87,f95,f111,f118,f150,f154,f179,f261,f288,f313,f317,f321,f386,f391,f427,f450,f490,f494,f572,f576,f580,f584,f588,f870,f982,f990,f1703,f1711,f1735,f1739,f1763,f1936,f2033,f2106,f2174,f2309,f2542,f11482,f16877,f17659,f17846,f18918,f18922,f20871,f21877,f25298,f25715,f26139,f26544,f26971,f26975,f28786,f28790,f28830,f29688,f39146,f41091,f44226,f44768,f45154])).
% 25.62/3.65  fof(f45154,plain,(
% 25.62/3.65    ~spl2_23 | spl2_24 | ~spl2_30 | ~spl2_139 | ~spl2_150 | ~spl2_158),
% 25.62/3.65    inference(avatar_contradiction_clause,[],[f45153])).
% 25.62/3.65  fof(f45153,plain,(
% 25.62/3.65    $false | (~spl2_23 | spl2_24 | ~spl2_30 | ~spl2_139 | ~spl2_150 | ~spl2_158)),
% 25.62/3.65    inference(subsumption_resolution,[],[f390,f45152])).
% 25.62/3.65  fof(f45152,plain,(
% 25.62/3.65    ( ! [X244,X245] : (k5_xboole_0(X244,X245) = k4_xboole_0(k5_xboole_0(X244,k4_xboole_0(X245,X244)),k4_xboole_0(X244,k4_xboole_0(X244,X245)))) ) | (~spl2_23 | ~spl2_30 | ~spl2_139 | ~spl2_150 | ~spl2_158)),
% 25.62/3.65    inference(forward_demodulation,[],[f44959,f45037])).
% 25.62/3.65  fof(f45037,plain,(
% 25.62/3.65    ( ! [X17,X18] : (k4_xboole_0(X17,k4_xboole_0(X17,X18)) = k4_xboole_0(X17,k5_xboole_0(X17,X18))) ) | (~spl2_23 | ~spl2_30 | ~spl2_150 | ~spl2_158)),
% 25.62/3.65    inference(forward_demodulation,[],[f45036,f575])).
% 25.62/3.65  fof(f575,plain,(
% 25.62/3.65    ( ! [X4,X5] : (k4_xboole_0(X4,k4_xboole_0(X4,X5)) = k5_xboole_0(X4,k4_xboole_0(X4,X5))) ) | ~spl2_30),
% 25.62/3.65    inference(avatar_component_clause,[],[f574])).
% 25.62/3.65  fof(f574,plain,(
% 25.62/3.65    spl2_30 <=> ! [X5,X4] : k4_xboole_0(X4,k4_xboole_0(X4,X5)) = k5_xboole_0(X4,k4_xboole_0(X4,X5))),
% 25.62/3.65    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).
% 25.62/3.65  fof(f45036,plain,(
% 25.62/3.65    ( ! [X17,X18] : (k5_xboole_0(X17,k4_xboole_0(X17,X18)) = k4_xboole_0(X17,k5_xboole_0(X17,X18))) ) | (~spl2_23 | ~spl2_150 | ~spl2_158)),
% 25.62/3.65    inference(forward_demodulation,[],[f44871,f39145])).
% 25.62/3.65  fof(f39145,plain,(
% 25.62/3.65    ( ! [X109,X110] : (k4_xboole_0(X109,X110) = k4_xboole_0(k5_xboole_0(X109,X110),k4_xboole_0(X110,X109))) ) | ~spl2_150),
% 25.62/3.65    inference(avatar_component_clause,[],[f39144])).
% 25.62/3.65  fof(f39144,plain,(
% 25.62/3.65    spl2_150 <=> ! [X110,X109] : k4_xboole_0(X109,X110) = k4_xboole_0(k5_xboole_0(X109,X110),k4_xboole_0(X110,X109))),
% 25.62/3.65    introduced(avatar_definition,[new_symbols(naming,[spl2_150])])).
% 25.62/3.65  fof(f44871,plain,(
% 25.62/3.65    ( ! [X17,X18] : (k4_xboole_0(X17,k5_xboole_0(X17,X18)) = k5_xboole_0(X17,k4_xboole_0(k5_xboole_0(X17,X18),k4_xboole_0(X18,X17)))) ) | (~spl2_23 | ~spl2_158)),
% 25.62/3.65    inference(superposition,[],[f385,f44767])).
% 25.62/3.65  fof(f44767,plain,(
% 25.62/3.65    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k4_xboole_0(k5_xboole_0(X2,X1),X2)) ) | ~spl2_158),
% 25.62/3.65    inference(avatar_component_clause,[],[f44766])).
% 25.62/3.65  fof(f44766,plain,(
% 25.62/3.65    spl2_158 <=> ! [X1,X2] : k4_xboole_0(X1,X2) = k4_xboole_0(k5_xboole_0(X2,X1),X2)),
% 25.62/3.65    introduced(avatar_definition,[new_symbols(naming,[spl2_158])])).
% 25.62/3.65  fof(f385,plain,(
% 25.62/3.65    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))) ) | ~spl2_23),
% 25.62/3.65    inference(avatar_component_clause,[],[f384])).
% 25.62/3.65  fof(f384,plain,(
% 25.62/3.65    spl2_23 <=> ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))),
% 25.62/3.65    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 25.62/3.65  fof(f44959,plain,(
% 25.62/3.65    ( ! [X244,X245] : (k5_xboole_0(X244,X245) = k4_xboole_0(k5_xboole_0(X244,k4_xboole_0(X245,X244)),k4_xboole_0(X244,k5_xboole_0(X244,X245)))) ) | (~spl2_139 | ~spl2_158)),
% 25.62/3.65    inference(superposition,[],[f28829,f44767])).
% 25.62/3.65  fof(f28829,plain,(
% 25.62/3.65    ( ! [X8,X9] : (k4_xboole_0(k5_xboole_0(X9,k4_xboole_0(X8,X9)),k4_xboole_0(X9,X8)) = X8) ) | ~spl2_139),
% 25.62/3.65    inference(avatar_component_clause,[],[f28828])).
% 25.62/3.65  fof(f28828,plain,(
% 25.62/3.65    spl2_139 <=> ! [X9,X8] : k4_xboole_0(k5_xboole_0(X9,k4_xboole_0(X8,X9)),k4_xboole_0(X9,X8)) = X8),
% 25.62/3.65    introduced(avatar_definition,[new_symbols(naming,[spl2_139])])).
% 25.62/3.65  fof(f390,plain,(
% 25.62/3.65    k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl2_24),
% 25.62/3.65    inference(avatar_component_clause,[],[f388])).
% 25.62/3.65  fof(f388,plain,(
% 25.62/3.65    spl2_24 <=> k5_xboole_0(sK0,sK1) = k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 25.62/3.65    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 25.62/3.65  fof(f44768,plain,(
% 25.62/3.65    spl2_158 | ~spl2_22 | ~spl2_157),
% 25.62/3.65    inference(avatar_split_clause,[],[f44228,f44224,f319,f44766])).
% 25.62/3.65  fof(f319,plain,(
% 25.62/3.65    spl2_22 <=> ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1)),
% 25.62/3.65    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 25.62/3.65  fof(f44224,plain,(
% 25.62/3.65    spl2_157 <=> ! [X48,X47] : k4_xboole_0(X47,X48) = k4_xboole_0(k5_xboole_0(X47,X48),X48)),
% 25.62/3.65    introduced(avatar_definition,[new_symbols(naming,[spl2_157])])).
% 25.62/3.65  fof(f44228,plain,(
% 25.62/3.65    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k4_xboole_0(k5_xboole_0(X2,X1),X2)) ) | (~spl2_22 | ~spl2_157)),
% 25.62/3.65    inference(superposition,[],[f44225,f320])).
% 25.62/3.65  fof(f320,plain,(
% 25.62/3.65    ( ! [X2,X1] : (k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1)) ) | ~spl2_22),
% 25.62/3.65    inference(avatar_component_clause,[],[f319])).
% 25.62/3.65  fof(f44225,plain,(
% 25.62/3.65    ( ! [X47,X48] : (k4_xboole_0(X47,X48) = k4_xboole_0(k5_xboole_0(X47,X48),X48)) ) | ~spl2_157),
% 25.62/3.65    inference(avatar_component_clause,[],[f44224])).
% 25.62/3.65  fof(f44226,plain,(
% 25.62/3.65    spl2_157 | ~spl2_2 | ~spl2_7 | ~spl2_46 | ~spl2_69 | ~spl2_143 | ~spl2_156),
% 25.62/3.65    inference(avatar_split_clause,[],[f43980,f41089,f29686,f2104,f1709,f59,f35,f44224])).
% 25.62/3.65  fof(f35,plain,(
% 25.62/3.65    spl2_2 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 25.62/3.65    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 25.62/3.65  fof(f59,plain,(
% 25.62/3.65    spl2_7 <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))),
% 25.62/3.65    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 25.62/3.65  fof(f1709,plain,(
% 25.62/3.65    spl2_46 <=> ! [X1,X0,X2] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)),
% 25.62/3.65    introduced(avatar_definition,[new_symbols(naming,[spl2_46])])).
% 25.62/3.65  fof(f2104,plain,(
% 25.62/3.65    spl2_69 <=> ! [X7,X8] : k4_xboole_0(X8,X7) = k4_xboole_0(k4_xboole_0(X8,X7),X7)),
% 25.62/3.65    introduced(avatar_definition,[new_symbols(naming,[spl2_69])])).
% 25.62/3.65  fof(f29686,plain,(
% 25.62/3.65    spl2_143 <=> ! [X3,X2] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X3),k5_xboole_0(X2,X3))),
% 25.62/3.65    introduced(avatar_definition,[new_symbols(naming,[spl2_143])])).
% 25.62/3.65  fof(f41089,plain,(
% 25.62/3.65    spl2_156 <=> ! [X5,X4] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k5_xboole_0(X4,X5),X5),k4_xboole_0(X4,X5))),
% 25.62/3.65    introduced(avatar_definition,[new_symbols(naming,[spl2_156])])).
% 25.62/3.65  fof(f43980,plain,(
% 25.62/3.65    ( ! [X47,X48] : (k4_xboole_0(X47,X48) = k4_xboole_0(k5_xboole_0(X47,X48),X48)) ) | (~spl2_2 | ~spl2_7 | ~spl2_46 | ~spl2_69 | ~spl2_143 | ~spl2_156)),
% 25.62/3.65    inference(forward_demodulation,[],[f43979,f2105])).
% 25.62/3.65  fof(f2105,plain,(
% 25.62/3.65    ( ! [X8,X7] : (k4_xboole_0(X8,X7) = k4_xboole_0(k4_xboole_0(X8,X7),X7)) ) | ~spl2_69),
% 25.62/3.65    inference(avatar_component_clause,[],[f2104])).
% 25.62/3.65  fof(f43979,plain,(
% 25.62/3.65    ( ! [X47,X48] : (k4_xboole_0(k4_xboole_0(X47,X48),X48) = k4_xboole_0(k5_xboole_0(X47,X48),X48)) ) | (~spl2_2 | ~spl2_7 | ~spl2_46 | ~spl2_143 | ~spl2_156)),
% 25.62/3.65    inference(forward_demodulation,[],[f43978,f30385])).
% 25.62/3.65  fof(f30385,plain,(
% 25.62/3.65    ( ! [X80,X78,X79] : (k4_xboole_0(k4_xboole_0(X78,X79),X80) = k4_xboole_0(k4_xboole_0(X78,X79),k4_xboole_0(k4_xboole_0(X78,X79),k4_xboole_0(k5_xboole_0(X78,X79),X80)))) ) | (~spl2_2 | ~spl2_46 | ~spl2_143)),
% 25.62/3.65    inference(forward_demodulation,[],[f30245,f36])).
% 25.62/3.65  fof(f36,plain,(
% 25.62/3.65    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl2_2),
% 25.62/3.65    inference(avatar_component_clause,[],[f35])).
% 25.62/3.65  fof(f30245,plain,(
% 25.62/3.65    ( ! [X80,X78,X79] : (k4_xboole_0(k4_xboole_0(X78,X79),k4_xboole_0(k4_xboole_0(X78,X79),k4_xboole_0(k5_xboole_0(X78,X79),X80))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X78,X79),k1_xboole_0),X80)) ) | (~spl2_46 | ~spl2_143)),
% 25.62/3.65    inference(superposition,[],[f1710,f29687])).
% 25.62/3.65  fof(f29687,plain,(
% 25.62/3.65    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X3),k5_xboole_0(X2,X3))) ) | ~spl2_143),
% 25.62/3.65    inference(avatar_component_clause,[],[f29686])).
% 25.62/3.65  fof(f1710,plain,(
% 25.62/3.65    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) ) | ~spl2_46),
% 25.62/3.65    inference(avatar_component_clause,[],[f1709])).
% 25.62/3.65  fof(f43978,plain,(
% 25.62/3.65    ( ! [X47,X48] : (k4_xboole_0(k5_xboole_0(X47,X48),X48) = k4_xboole_0(k4_xboole_0(X47,X48),k4_xboole_0(k4_xboole_0(X47,X48),k4_xboole_0(k5_xboole_0(X47,X48),X48)))) ) | (~spl2_2 | ~spl2_7 | ~spl2_156)),
% 25.62/3.65    inference(forward_demodulation,[],[f43653,f36])).
% 25.62/3.65  fof(f43653,plain,(
% 25.62/3.65    ( ! [X47,X48] : (k4_xboole_0(k4_xboole_0(X47,X48),k4_xboole_0(k4_xboole_0(X47,X48),k4_xboole_0(k5_xboole_0(X47,X48),X48))) = k4_xboole_0(k4_xboole_0(k5_xboole_0(X47,X48),X48),k1_xboole_0)) ) | (~spl2_7 | ~spl2_156)),
% 25.62/3.65    inference(superposition,[],[f60,f41090])).
% 25.62/3.65  fof(f41090,plain,(
% 25.62/3.65    ( ! [X4,X5] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k5_xboole_0(X4,X5),X5),k4_xboole_0(X4,X5))) ) | ~spl2_156),
% 25.62/3.65    inference(avatar_component_clause,[],[f41089])).
% 25.62/3.65  fof(f60,plain,(
% 25.62/3.65    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) ) | ~spl2_7),
% 25.62/3.65    inference(avatar_component_clause,[],[f59])).
% 25.62/3.65  fof(f41091,plain,(
% 25.62/3.65    spl2_156 | ~spl2_122 | ~spl2_150),
% 25.62/3.65    inference(avatar_split_clause,[],[f40627,f39144,f26137,f41089])).
% 25.62/3.65  fof(f26137,plain,(
% 25.62/3.65    spl2_122 <=> ! [X13,X12,X14] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X12,X13),k4_xboole_0(X12,k4_xboole_0(X13,X14)))),
% 25.62/3.65    introduced(avatar_definition,[new_symbols(naming,[spl2_122])])).
% 25.62/3.65  fof(f40627,plain,(
% 25.62/3.65    ( ! [X4,X5] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k5_xboole_0(X4,X5),X5),k4_xboole_0(X4,X5))) ) | (~spl2_122 | ~spl2_150)),
% 25.62/3.65    inference(superposition,[],[f26138,f39145])).
% 25.62/3.65  fof(f26138,plain,(
% 25.62/3.65    ( ! [X14,X12,X13] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X12,X13),k4_xboole_0(X12,k4_xboole_0(X13,X14)))) ) | ~spl2_122),
% 25.62/3.65    inference(avatar_component_clause,[],[f26137])).
% 25.62/3.65  fof(f39146,plain,(
% 25.62/3.65    spl2_150 | ~spl2_11 | ~spl2_105 | ~spl2_128 | ~spl2_129),
% 25.62/3.65    inference(avatar_split_clause,[],[f29646,f28788,f28784,f18920,f109,f39144])).
% 25.62/3.65  fof(f109,plain,(
% 25.62/3.65    spl2_11 <=> ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1),
% 25.62/3.65    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 25.62/3.65  fof(f18920,plain,(
% 25.62/3.65    spl2_105 <=> ! [X53,X52,X54] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X52,X53),k5_xboole_0(k4_xboole_0(X53,X54),k4_xboole_0(X52,X53)))),
% 25.62/3.65    introduced(avatar_definition,[new_symbols(naming,[spl2_105])])).
% 25.62/3.65  fof(f28784,plain,(
% 25.62/3.65    spl2_128 <=> ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X2,X1))),
% 25.62/3.65    introduced(avatar_definition,[new_symbols(naming,[spl2_128])])).
% 25.62/3.65  fof(f28788,plain,(
% 25.62/3.65    spl2_129 <=> ! [X3,X4] : k5_xboole_0(X3,X4) = k5_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X4,X3))),
% 25.62/3.65    introduced(avatar_definition,[new_symbols(naming,[spl2_129])])).
% 25.62/3.65  fof(f29646,plain,(
% 25.62/3.65    ( ! [X109,X110] : (k4_xboole_0(X109,X110) = k4_xboole_0(k5_xboole_0(X109,X110),k4_xboole_0(X110,X109))) ) | (~spl2_11 | ~spl2_105 | ~spl2_128 | ~spl2_129)),
% 25.62/3.65    inference(forward_demodulation,[],[f29645,f110])).
% 25.62/3.65  fof(f110,plain,(
% 25.62/3.65    ( ! [X1] : (k5_xboole_0(X1,k1_xboole_0) = X1) ) | ~spl2_11),
% 25.62/3.65    inference(avatar_component_clause,[],[f109])).
% 25.62/3.65  fof(f29645,plain,(
% 25.62/3.65    ( ! [X109,X110] : (k5_xboole_0(k4_xboole_0(X109,X110),k1_xboole_0) = k4_xboole_0(k5_xboole_0(X109,X110),k4_xboole_0(X110,X109))) ) | (~spl2_105 | ~spl2_128 | ~spl2_129)),
% 25.62/3.65    inference(backward_demodulation,[],[f28885,f29424])).
% 25.62/3.65  fof(f29424,plain,(
% 25.62/3.65    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,X0),k5_xboole_0(X0,X1))) ) | (~spl2_105 | ~spl2_129)),
% 25.62/3.65    inference(superposition,[],[f18921,f28789])).
% 25.62/3.65  fof(f28789,plain,(
% 25.62/3.65    ( ! [X4,X3] : (k5_xboole_0(X3,X4) = k5_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X4,X3))) ) | ~spl2_129),
% 25.62/3.65    inference(avatar_component_clause,[],[f28788])).
% 25.62/3.65  fof(f18921,plain,(
% 25.62/3.65    ( ! [X54,X52,X53] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X52,X53),k5_xboole_0(k4_xboole_0(X53,X54),k4_xboole_0(X52,X53)))) ) | ~spl2_105),
% 25.62/3.65    inference(avatar_component_clause,[],[f18920])).
% 25.62/3.65  fof(f28885,plain,(
% 25.62/3.65    ( ! [X109,X110] : (k4_xboole_0(k5_xboole_0(X109,X110),k4_xboole_0(X110,X109)) = k5_xboole_0(k4_xboole_0(X109,X110),k4_xboole_0(k4_xboole_0(X110,X109),k5_xboole_0(X109,X110)))) ) | ~spl2_128),
% 25.62/3.65    inference(superposition,[],[f28785,f28785])).
% 25.62/3.65  fof(f28785,plain,(
% 25.62/3.65    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X2,X1))) ) | ~spl2_128),
% 25.62/3.65    inference(avatar_component_clause,[],[f28784])).
% 25.62/3.65  fof(f29688,plain,(
% 25.62/3.65    spl2_143 | ~spl2_104 | ~spl2_129),
% 25.62/3.65    inference(avatar_split_clause,[],[f29425,f28788,f18916,f29686])).
% 25.62/3.65  fof(f18916,plain,(
% 25.62/3.65    spl2_104 <=> ! [X20,X19,X21] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X20,X21),k5_xboole_0(k4_xboole_0(X20,X21),k4_xboole_0(X19,X20)))),
% 25.62/3.65    introduced(avatar_definition,[new_symbols(naming,[spl2_104])])).
% 25.62/3.65  fof(f29425,plain,(
% 25.62/3.65    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X3),k5_xboole_0(X2,X3))) ) | (~spl2_104 | ~spl2_129)),
% 25.62/3.65    inference(superposition,[],[f18917,f28789])).
% 25.62/3.65  fof(f18917,plain,(
% 25.62/3.65    ( ! [X21,X19,X20] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X20,X21),k5_xboole_0(k4_xboole_0(X20,X21),k4_xboole_0(X19,X20)))) ) | ~spl2_104),
% 25.62/3.65    inference(avatar_component_clause,[],[f18916])).
% 25.62/3.65  fof(f28830,plain,(
% 25.62/3.65    spl2_139 | ~spl2_22 | ~spl2_33 | ~spl2_125),
% 25.62/3.65    inference(avatar_split_clause,[],[f27833,f26973,f586,f319,f28828])).
% 25.62/3.65  fof(f586,plain,(
% 25.62/3.65    spl2_33 <=> ! [X5,X4] : k4_xboole_0(k5_xboole_0(X4,k4_xboole_0(X5,X4)),k4_xboole_0(X5,X4)) = X4),
% 25.62/3.65    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).
% 25.62/3.65  fof(f26973,plain,(
% 25.62/3.65    spl2_125 <=> ! [X51,X50] : k5_xboole_0(X51,k4_xboole_0(X50,X51)) = k5_xboole_0(k4_xboole_0(X51,X50),X50)),
% 25.62/3.65    introduced(avatar_definition,[new_symbols(naming,[spl2_125])])).
% 25.62/3.65  fof(f27833,plain,(
% 25.62/3.65    ( ! [X8,X9] : (k4_xboole_0(k5_xboole_0(X9,k4_xboole_0(X8,X9)),k4_xboole_0(X9,X8)) = X8) ) | (~spl2_22 | ~spl2_33 | ~spl2_125)),
% 25.62/3.65    inference(forward_demodulation,[],[f27542,f320])).
% 25.62/3.65  fof(f27542,plain,(
% 25.62/3.65    ( ! [X8,X9] : (k4_xboole_0(k5_xboole_0(k4_xboole_0(X8,X9),X9),k4_xboole_0(X9,X8)) = X8) ) | (~spl2_33 | ~spl2_125)),
% 25.62/3.65    inference(superposition,[],[f587,f26974])).
% 25.62/3.65  fof(f26974,plain,(
% 25.62/3.65    ( ! [X50,X51] : (k5_xboole_0(X51,k4_xboole_0(X50,X51)) = k5_xboole_0(k4_xboole_0(X51,X50),X50)) ) | ~spl2_125),
% 25.62/3.65    inference(avatar_component_clause,[],[f26973])).
% 25.62/3.65  fof(f587,plain,(
% 25.62/3.65    ( ! [X4,X5] : (k4_xboole_0(k5_xboole_0(X4,k4_xboole_0(X5,X4)),k4_xboole_0(X5,X4)) = X4) ) | ~spl2_33),
% 25.62/3.65    inference(avatar_component_clause,[],[f586])).
% 25.62/3.65  fof(f28790,plain,(
% 25.62/3.65    spl2_129 | ~spl2_35 | ~spl2_124),
% 25.62/3.65    inference(avatar_split_clause,[],[f27058,f26969,f980,f28788])).
% 25.62/3.65  fof(f980,plain,(
% 25.62/3.65    spl2_35 <=> ! [X1,X0,X2] : k5_xboole_0(X0,X1) = k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,X2)))),
% 25.62/3.65    introduced(avatar_definition,[new_symbols(naming,[spl2_35])])).
% 25.62/3.65  fof(f26969,plain,(
% 25.62/3.65    spl2_124 <=> ! [X58,X59] : k4_xboole_0(X59,X58) = k5_xboole_0(X58,k5_xboole_0(X59,k4_xboole_0(X58,X59)))),
% 25.62/3.65    introduced(avatar_definition,[new_symbols(naming,[spl2_124])])).
% 25.62/3.65  fof(f27058,plain,(
% 25.62/3.65    ( ! [X4,X3] : (k5_xboole_0(X3,X4) = k5_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X4,X3))) ) | (~spl2_35 | ~spl2_124)),
% 25.62/3.65    inference(superposition,[],[f981,f26970])).
% 25.62/3.65  fof(f26970,plain,(
% 25.62/3.65    ( ! [X59,X58] : (k4_xboole_0(X59,X58) = k5_xboole_0(X58,k5_xboole_0(X59,k4_xboole_0(X58,X59)))) ) | ~spl2_124),
% 25.62/3.65    inference(avatar_component_clause,[],[f26969])).
% 25.62/3.65  fof(f981,plain,(
% 25.62/3.65    ( ! [X2,X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,X2)))) ) | ~spl2_35),
% 25.62/3.65    inference(avatar_component_clause,[],[f980])).
% 25.62/3.65  fof(f28786,plain,(
% 25.62/3.65    spl2_128 | ~spl2_29 | ~spl2_124),
% 25.62/3.65    inference(avatar_split_clause,[],[f27057,f26969,f570,f28784])).
% 25.62/3.65  fof(f570,plain,(
% 25.62/3.65    spl2_29 <=> ! [X1,X0,X2] : k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = X2),
% 25.62/3.65    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).
% 25.62/3.65  fof(f27057,plain,(
% 25.62/3.65    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X2,X1))) ) | (~spl2_29 | ~spl2_124)),
% 25.62/3.65    inference(superposition,[],[f571,f26970])).
% 25.62/3.65  fof(f571,plain,(
% 25.62/3.65    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = X2) ) | ~spl2_29),
% 25.62/3.65    inference(avatar_component_clause,[],[f570])).
% 25.62/3.65  fof(f26975,plain,(
% 25.62/3.65    spl2_125 | ~spl2_2 | ~spl2_7 | ~spl2_28 | ~spl2_31 | ~spl2_52 | ~spl2_98 | ~spl2_101 | ~spl2_115 | ~spl2_123),
% 25.62/3.65    inference(avatar_split_clause,[],[f26842,f26542,f21875,f17844,f17657,f1733,f578,f492,f59,f35,f26973])).
% 25.62/3.65  fof(f492,plain,(
% 25.62/3.65    spl2_28 <=> ! [X3,X2] : k4_xboole_0(X2,X3) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X2,X3)))),
% 25.62/3.65    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).
% 25.62/3.65  fof(f578,plain,(
% 25.62/3.65    spl2_31 <=> ! [X9,X10] : k4_xboole_0(X10,k4_xboole_0(X9,k4_xboole_0(X9,X10))) = k4_xboole_0(X10,X9)),
% 25.62/3.65    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).
% 25.62/3.65  fof(f1733,plain,(
% 25.62/3.65    spl2_52 <=> ! [X9,X8] : k5_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(X9,k4_xboole_0(X9,X8))) = X8),
% 25.62/3.65    introduced(avatar_definition,[new_symbols(naming,[spl2_52])])).
% 25.62/3.65  fof(f17657,plain,(
% 25.62/3.65    spl2_98 <=> ! [X18,X17,X19] : k4_xboole_0(X17,k4_xboole_0(X17,k4_xboole_0(k5_xboole_0(X17,k4_xboole_0(X18,X17)),X19))) = k4_xboole_0(X17,X19)),
% 25.62/3.65    introduced(avatar_definition,[new_symbols(naming,[spl2_98])])).
% 25.62/3.65  fof(f17844,plain,(
% 25.62/3.65    spl2_101 <=> ! [X22,X21] : k4_xboole_0(X21,k4_xboole_0(X21,X22)) = k4_xboole_0(k4_xboole_0(X22,k4_xboole_0(X22,X21)),k1_xboole_0)),
% 25.62/3.65    introduced(avatar_definition,[new_symbols(naming,[spl2_101])])).
% 25.62/3.65  fof(f21875,plain,(
% 25.62/3.65    spl2_115 <=> ! [X79,X78] : k1_xboole_0 = k4_xboole_0(X79,k5_xboole_0(X78,k4_xboole_0(X79,X78)))),
% 25.62/3.65    introduced(avatar_definition,[new_symbols(naming,[spl2_115])])).
% 25.62/3.65  fof(f26542,plain,(
% 25.62/3.65    spl2_123 <=> ! [X93,X94] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k5_xboole_0(X93,k4_xboole_0(X94,X93)),X94),X93)),
% 25.62/3.65    introduced(avatar_definition,[new_symbols(naming,[spl2_123])])).
% 25.62/3.65  fof(f26842,plain,(
% 25.62/3.65    ( ! [X50,X51] : (k5_xboole_0(X51,k4_xboole_0(X50,X51)) = k5_xboole_0(k4_xboole_0(X51,X50),X50)) ) | (~spl2_2 | ~spl2_7 | ~spl2_28 | ~spl2_31 | ~spl2_52 | ~spl2_98 | ~spl2_101 | ~spl2_115 | ~spl2_123)),
% 25.62/3.65    inference(backward_demodulation,[],[f22076,f26839])).
% 25.62/3.65  fof(f26839,plain,(
% 25.62/3.65    ( ! [X37,X38] : (k4_xboole_0(X37,X38) = k4_xboole_0(k5_xboole_0(X37,k4_xboole_0(X38,X37)),X38)) ) | (~spl2_2 | ~spl2_7 | ~spl2_28 | ~spl2_31 | ~spl2_98 | ~spl2_101 | ~spl2_123)),
% 25.62/3.65    inference(forward_demodulation,[],[f26838,f493])).
% 25.62/3.65  fof(f493,plain,(
% 25.62/3.65    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X2,X3)))) ) | ~spl2_28),
% 25.62/3.65    inference(avatar_component_clause,[],[f492])).
% 25.62/3.65  fof(f26838,plain,(
% 25.62/3.65    ( ! [X37,X38] : (k4_xboole_0(X37,k4_xboole_0(X37,k4_xboole_0(X37,X38))) = k4_xboole_0(k5_xboole_0(X37,k4_xboole_0(X38,X37)),X38)) ) | (~spl2_2 | ~spl2_7 | ~spl2_31 | ~spl2_98 | ~spl2_101 | ~spl2_123)),
% 25.62/3.65    inference(forward_demodulation,[],[f26837,f25172])).
% 25.62/3.65  fof(f25172,plain,(
% 25.62/3.65    ( ! [X17,X15,X16] : (k4_xboole_0(X15,k4_xboole_0(k5_xboole_0(X15,k4_xboole_0(X16,X15)),X17)) = k4_xboole_0(X15,k4_xboole_0(X15,X17))) ) | (~spl2_2 | ~spl2_31 | ~spl2_98 | ~spl2_101)),
% 25.62/3.65    inference(backward_demodulation,[],[f25164,f25171])).
% 25.62/3.65  fof(f25171,plain,(
% 25.62/3.65    ( ! [X39,X37,X38] : (k4_xboole_0(X37,X39) = k4_xboole_0(X37,k4_xboole_0(X39,k4_xboole_0(X39,k5_xboole_0(X37,k4_xboole_0(X38,X37)))))) ) | (~spl2_31 | ~spl2_98)),
% 25.62/3.65    inference(forward_demodulation,[],[f24947,f17658])).
% 25.62/3.65  fof(f17658,plain,(
% 25.62/3.65    ( ! [X19,X17,X18] : (k4_xboole_0(X17,k4_xboole_0(X17,k4_xboole_0(k5_xboole_0(X17,k4_xboole_0(X18,X17)),X19))) = k4_xboole_0(X17,X19)) ) | ~spl2_98),
% 25.62/3.65    inference(avatar_component_clause,[],[f17657])).
% 25.62/3.65  fof(f24947,plain,(
% 25.62/3.65    ( ! [X39,X37,X38] : (k4_xboole_0(X37,k4_xboole_0(X39,k4_xboole_0(X39,k5_xboole_0(X37,k4_xboole_0(X38,X37))))) = k4_xboole_0(X37,k4_xboole_0(X37,k4_xboole_0(k5_xboole_0(X37,k4_xboole_0(X38,X37)),X39)))) ) | (~spl2_31 | ~spl2_98)),
% 25.62/3.65    inference(superposition,[],[f17658,f579])).
% 25.62/3.65  fof(f579,plain,(
% 25.62/3.65    ( ! [X10,X9] : (k4_xboole_0(X10,k4_xboole_0(X9,k4_xboole_0(X9,X10))) = k4_xboole_0(X10,X9)) ) | ~spl2_31),
% 25.62/3.65    inference(avatar_component_clause,[],[f578])).
% 25.62/3.65  fof(f25164,plain,(
% 25.62/3.65    ( ! [X17,X15,X16] : (k4_xboole_0(X15,k4_xboole_0(k5_xboole_0(X15,k4_xboole_0(X16,X15)),X17)) = k4_xboole_0(X15,k4_xboole_0(X15,k4_xboole_0(X17,k4_xboole_0(X17,k5_xboole_0(X15,k4_xboole_0(X16,X15))))))) ) | (~spl2_2 | ~spl2_98 | ~spl2_101)),
% 25.62/3.65    inference(forward_demodulation,[],[f24940,f36])).
% 25.62/3.65  fof(f24940,plain,(
% 25.62/3.65    ( ! [X17,X15,X16] : (k4_xboole_0(X15,k4_xboole_0(k5_xboole_0(X15,k4_xboole_0(X16,X15)),X17)) = k4_xboole_0(X15,k4_xboole_0(X15,k4_xboole_0(k4_xboole_0(X17,k4_xboole_0(X17,k5_xboole_0(X15,k4_xboole_0(X16,X15)))),k1_xboole_0)))) ) | (~spl2_98 | ~spl2_101)),
% 25.62/3.65    inference(superposition,[],[f17658,f17845])).
% 25.62/3.65  fof(f17845,plain,(
% 25.62/3.65    ( ! [X21,X22] : (k4_xboole_0(X21,k4_xboole_0(X21,X22)) = k4_xboole_0(k4_xboole_0(X22,k4_xboole_0(X22,X21)),k1_xboole_0)) ) | ~spl2_101),
% 25.62/3.65    inference(avatar_component_clause,[],[f17844])).
% 25.62/3.65  fof(f26837,plain,(
% 25.62/3.65    ( ! [X37,X38] : (k4_xboole_0(k5_xboole_0(X37,k4_xboole_0(X38,X37)),X38) = k4_xboole_0(X37,k4_xboole_0(X37,k4_xboole_0(k5_xboole_0(X37,k4_xboole_0(X38,X37)),X38)))) ) | (~spl2_2 | ~spl2_7 | ~spl2_123)),
% 25.62/3.65    inference(forward_demodulation,[],[f26630,f36])).
% 25.62/3.65  fof(f26630,plain,(
% 25.62/3.65    ( ! [X37,X38] : (k4_xboole_0(X37,k4_xboole_0(X37,k4_xboole_0(k5_xboole_0(X37,k4_xboole_0(X38,X37)),X38))) = k4_xboole_0(k4_xboole_0(k5_xboole_0(X37,k4_xboole_0(X38,X37)),X38),k1_xboole_0)) ) | (~spl2_7 | ~spl2_123)),
% 25.62/3.65    inference(superposition,[],[f60,f26543])).
% 25.62/3.65  fof(f26543,plain,(
% 25.62/3.65    ( ! [X94,X93] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k5_xboole_0(X93,k4_xboole_0(X94,X93)),X94),X93)) ) | ~spl2_123),
% 25.62/3.65    inference(avatar_component_clause,[],[f26542])).
% 25.62/3.65  fof(f22076,plain,(
% 25.62/3.65    ( ! [X50,X51] : (k5_xboole_0(X51,k4_xboole_0(X50,X51)) = k5_xboole_0(k4_xboole_0(k5_xboole_0(X51,k4_xboole_0(X50,X51)),X50),X50)) ) | (~spl2_2 | ~spl2_52 | ~spl2_115)),
% 25.62/3.65    inference(forward_demodulation,[],[f21950,f36])).
% 25.62/3.65  fof(f21950,plain,(
% 25.62/3.65    ( ! [X50,X51] : (k5_xboole_0(X51,k4_xboole_0(X50,X51)) = k5_xboole_0(k4_xboole_0(k5_xboole_0(X51,k4_xboole_0(X50,X51)),X50),k4_xboole_0(X50,k1_xboole_0))) ) | (~spl2_52 | ~spl2_115)),
% 25.62/3.65    inference(superposition,[],[f1734,f21876])).
% 25.62/3.65  fof(f21876,plain,(
% 25.62/3.65    ( ! [X78,X79] : (k1_xboole_0 = k4_xboole_0(X79,k5_xboole_0(X78,k4_xboole_0(X79,X78)))) ) | ~spl2_115),
% 25.62/3.65    inference(avatar_component_clause,[],[f21875])).
% 25.62/3.65  fof(f1734,plain,(
% 25.62/3.65    ( ! [X8,X9] : (k5_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(X9,k4_xboole_0(X9,X8))) = X8) ) | ~spl2_52),
% 25.62/3.65    inference(avatar_component_clause,[],[f1733])).
% 25.62/3.65  fof(f26971,plain,(
% 25.62/3.65    spl2_124 | ~spl2_2 | ~spl2_7 | ~spl2_28 | ~spl2_31 | ~spl2_59 | ~spl2_98 | ~spl2_101 | ~spl2_115 | ~spl2_123),
% 25.62/3.65    inference(avatar_split_clause,[],[f26841,f26542,f21875,f17844,f17657,f1761,f578,f492,f59,f35,f26969])).
% 25.62/3.65  fof(f1761,plain,(
% 25.62/3.65    spl2_59 <=> ! [X18,X19] : k4_xboole_0(X18,X19) = k5_xboole_0(k4_xboole_0(X19,k4_xboole_0(X19,X18)),X18)),
% 25.62/3.65    introduced(avatar_definition,[new_symbols(naming,[spl2_59])])).
% 25.62/3.65  fof(f26841,plain,(
% 25.62/3.65    ( ! [X59,X58] : (k4_xboole_0(X59,X58) = k5_xboole_0(X58,k5_xboole_0(X59,k4_xboole_0(X58,X59)))) ) | (~spl2_2 | ~spl2_7 | ~spl2_28 | ~spl2_31 | ~spl2_59 | ~spl2_98 | ~spl2_101 | ~spl2_115 | ~spl2_123)),
% 25.62/3.65    inference(backward_demodulation,[],[f22078,f26839])).
% 25.62/3.65  fof(f22078,plain,(
% 25.62/3.65    ( ! [X59,X58] : (k4_xboole_0(k5_xboole_0(X59,k4_xboole_0(X58,X59)),X58) = k5_xboole_0(X58,k5_xboole_0(X59,k4_xboole_0(X58,X59)))) ) | (~spl2_2 | ~spl2_59 | ~spl2_115)),
% 25.62/3.65    inference(forward_demodulation,[],[f21952,f36])).
% 25.62/3.65  fof(f21952,plain,(
% 25.62/3.65    ( ! [X59,X58] : (k4_xboole_0(k5_xboole_0(X59,k4_xboole_0(X58,X59)),X58) = k5_xboole_0(k4_xboole_0(X58,k1_xboole_0),k5_xboole_0(X59,k4_xboole_0(X58,X59)))) ) | (~spl2_59 | ~spl2_115)),
% 25.62/3.65    inference(superposition,[],[f1762,f21876])).
% 25.62/3.65  fof(f1762,plain,(
% 25.62/3.65    ( ! [X19,X18] : (k4_xboole_0(X18,X19) = k5_xboole_0(k4_xboole_0(X19,k4_xboole_0(X19,X18)),X18)) ) | ~spl2_59),
% 25.62/3.65    inference(avatar_component_clause,[],[f1761])).
% 25.62/3.65  fof(f26544,plain,(
% 25.62/3.65    spl2_123 | ~spl2_33 | ~spl2_122),
% 25.62/3.65    inference(avatar_split_clause,[],[f26273,f26137,f586,f26542])).
% 25.62/3.65  fof(f26273,plain,(
% 25.62/3.65    ( ! [X94,X93] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k5_xboole_0(X93,k4_xboole_0(X94,X93)),X94),X93)) ) | (~spl2_33 | ~spl2_122)),
% 25.62/3.65    inference(superposition,[],[f26138,f587])).
% 25.62/3.65  fof(f26139,plain,(
% 25.62/3.65    spl2_122 | ~spl2_73 | ~spl2_121),
% 25.62/3.65    inference(avatar_split_clause,[],[f25771,f25713,f2540,f26137])).
% 25.62/3.65  fof(f2540,plain,(
% 25.62/3.65    spl2_73 <=> ! [X18,X17,X19] : k4_xboole_0(X18,X17) = k4_xboole_0(k4_xboole_0(X18,X17),k4_xboole_0(X17,X19))),
% 25.62/3.65    introduced(avatar_definition,[new_symbols(naming,[spl2_73])])).
% 25.62/3.65  fof(f25713,plain,(
% 25.62/3.65    spl2_121 <=> ! [X11,X10,X12] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X10,X11),X12),k4_xboole_0(X10,X12))),
% 25.62/3.65    introduced(avatar_definition,[new_symbols(naming,[spl2_121])])).
% 25.62/3.65  fof(f25771,plain,(
% 25.62/3.65    ( ! [X14,X12,X13] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X12,X13),k4_xboole_0(X12,k4_xboole_0(X13,X14)))) ) | (~spl2_73 | ~spl2_121)),
% 25.62/3.65    inference(superposition,[],[f25714,f2541])).
% 25.62/3.65  fof(f2541,plain,(
% 25.62/3.65    ( ! [X19,X17,X18] : (k4_xboole_0(X18,X17) = k4_xboole_0(k4_xboole_0(X18,X17),k4_xboole_0(X17,X19))) ) | ~spl2_73),
% 25.62/3.65    inference(avatar_component_clause,[],[f2540])).
% 25.62/3.65  fof(f25714,plain,(
% 25.62/3.65    ( ! [X12,X10,X11] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X10,X11),X12),k4_xboole_0(X10,X12))) ) | ~spl2_121),
% 25.62/3.65    inference(avatar_component_clause,[],[f25713])).
% 25.62/3.65  fof(f25715,plain,(
% 25.62/3.65    spl2_121 | ~spl2_44 | ~spl2_120),
% 25.62/3.65    inference(avatar_split_clause,[],[f25399,f25296,f1701,f25713])).
% 25.62/3.65  fof(f1701,plain,(
% 25.62/3.65    spl2_44 <=> ! [X7,X6] : k5_xboole_0(k4_xboole_0(X6,X7),k4_xboole_0(X6,k4_xboole_0(X6,X7))) = X6),
% 25.62/3.65    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).
% 25.62/3.65  fof(f25296,plain,(
% 25.62/3.65    spl2_120 <=> ! [X22,X21,X23] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X21,X23),k4_xboole_0(k5_xboole_0(X21,k4_xboole_0(X22,X21)),X23))),
% 25.62/3.65    introduced(avatar_definition,[new_symbols(naming,[spl2_120])])).
% 25.62/3.65  fof(f25399,plain,(
% 25.62/3.65    ( ! [X12,X10,X11] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X10,X11),X12),k4_xboole_0(X10,X12))) ) | (~spl2_44 | ~spl2_120)),
% 25.62/3.65    inference(superposition,[],[f25297,f1702])).
% 25.62/3.65  fof(f1702,plain,(
% 25.62/3.65    ( ! [X6,X7] : (k5_xboole_0(k4_xboole_0(X6,X7),k4_xboole_0(X6,k4_xboole_0(X6,X7))) = X6) ) | ~spl2_44),
% 25.62/3.65    inference(avatar_component_clause,[],[f1701])).
% 25.62/3.65  fof(f25297,plain,(
% 25.62/3.65    ( ! [X23,X21,X22] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X21,X23),k4_xboole_0(k5_xboole_0(X21,k4_xboole_0(X22,X21)),X23))) ) | ~spl2_120),
% 25.62/3.65    inference(avatar_component_clause,[],[f25296])).
% 25.62/3.65  fof(f25298,plain,(
% 25.62/3.65    spl2_120 | ~spl2_26 | ~spl2_98),
% 25.62/3.65    inference(avatar_split_clause,[],[f24976,f17657,f448,f25296])).
% 25.62/3.65  fof(f448,plain,(
% 25.62/3.65    spl2_26 <=> ! [X3,X2] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X2)),X2)),
% 25.62/3.65    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).
% 25.62/3.65  fof(f24976,plain,(
% 25.62/3.65    ( ! [X23,X21,X22] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X21,X23),k4_xboole_0(k5_xboole_0(X21,k4_xboole_0(X22,X21)),X23))) ) | (~spl2_26 | ~spl2_98)),
% 25.62/3.65    inference(superposition,[],[f449,f17658])).
% 25.62/3.65  fof(f449,plain,(
% 25.62/3.65    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X2)),X2)) ) | ~spl2_26),
% 25.62/3.65    inference(avatar_component_clause,[],[f448])).
% 25.62/3.65  fof(f21877,plain,(
% 25.62/3.65    spl2_115 | ~spl2_21 | ~spl2_112),
% 25.62/3.65    inference(avatar_split_clause,[],[f20905,f20869,f315,f21875])).
% 25.62/3.65  fof(f315,plain,(
% 25.62/3.65    spl2_21 <=> ! [X9,X8] : k5_xboole_0(k5_xboole_0(X9,X8),X9) = X8),
% 25.62/3.65    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 25.62/3.65  fof(f20869,plain,(
% 25.62/3.65    spl2_112 <=> ! [X3,X2] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X3,X2),k5_xboole_0(X2,k4_xboole_0(k5_xboole_0(X3,X2),X2)))),
% 25.62/3.65    introduced(avatar_definition,[new_symbols(naming,[spl2_112])])).
% 25.62/3.65  fof(f20905,plain,(
% 25.62/3.65    ( ! [X78,X79] : (k1_xboole_0 = k4_xboole_0(X79,k5_xboole_0(X78,k4_xboole_0(X79,X78)))) ) | (~spl2_21 | ~spl2_112)),
% 25.62/3.65    inference(superposition,[],[f20870,f316])).
% 25.62/3.65  fof(f316,plain,(
% 25.62/3.65    ( ! [X8,X9] : (k5_xboole_0(k5_xboole_0(X9,X8),X9) = X8) ) | ~spl2_21),
% 25.62/3.65    inference(avatar_component_clause,[],[f315])).
% 25.62/3.65  fof(f20870,plain,(
% 25.62/3.65    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(X3,X2),k5_xboole_0(X2,k4_xboole_0(k5_xboole_0(X3,X2),X2)))) ) | ~spl2_112),
% 25.62/3.65    inference(avatar_component_clause,[],[f20869])).
% 25.62/3.65  fof(f20871,plain,(
% 25.62/3.65    spl2_112 | ~spl2_22 | ~spl2_30 | ~spl2_37 | ~spl2_53 | ~spl2_88),
% 25.62/3.65    inference(avatar_split_clause,[],[f20142,f11480,f1737,f988,f574,f319,f20869])).
% 25.62/3.65  fof(f988,plain,(
% 25.62/3.65    spl2_37 <=> ! [X3,X5,X4] : k5_xboole_0(X4,X5) = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X5)))),
% 25.62/3.65    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).
% 25.62/3.65  fof(f1737,plain,(
% 25.62/3.65    spl2_53 <=> ! [X11,X10] : k4_xboole_0(X11,k4_xboole_0(X11,X10)) = k5_xboole_0(k4_xboole_0(X10,X11),X10)),
% 25.62/3.65    introduced(avatar_definition,[new_symbols(naming,[spl2_53])])).
% 25.62/3.65  fof(f11480,plain,(
% 25.62/3.65    spl2_88 <=> ! [X1,X0,X2] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,k5_xboole_0(X0,X1)))))),
% 25.62/3.65    introduced(avatar_definition,[new_symbols(naming,[spl2_88])])).
% 25.62/3.65  fof(f20142,plain,(
% 25.62/3.65    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(X3,X2),k5_xboole_0(X2,k4_xboole_0(k5_xboole_0(X3,X2),X2)))) ) | (~spl2_22 | ~spl2_30 | ~spl2_37 | ~spl2_53 | ~spl2_88)),
% 25.62/3.65    inference(forward_demodulation,[],[f20141,f320])).
% 25.62/3.65  fof(f20141,plain,(
% 25.62/3.65    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(X3,X2),k5_xboole_0(k4_xboole_0(k5_xboole_0(X3,X2),X2),X2))) ) | (~spl2_30 | ~spl2_37 | ~spl2_53 | ~spl2_88)),
% 25.62/3.65    inference(forward_demodulation,[],[f19896,f4748])).
% 25.62/3.65  fof(f4748,plain,(
% 25.62/3.65    ( ! [X80,X81,X79] : (k5_xboole_0(k4_xboole_0(k5_xboole_0(X79,X80),X81),X80) = k5_xboole_0(X79,k4_xboole_0(X81,k4_xboole_0(X81,k5_xboole_0(X79,X80))))) ) | (~spl2_37 | ~spl2_53)),
% 25.62/3.65    inference(superposition,[],[f989,f1738])).
% 25.62/3.65  fof(f1738,plain,(
% 25.62/3.65    ( ! [X10,X11] : (k4_xboole_0(X11,k4_xboole_0(X11,X10)) = k5_xboole_0(k4_xboole_0(X10,X11),X10)) ) | ~spl2_53),
% 25.62/3.65    inference(avatar_component_clause,[],[f1737])).
% 25.62/3.65  fof(f989,plain,(
% 25.62/3.65    ( ! [X4,X5,X3] : (k5_xboole_0(X4,X5) = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X5)))) ) | ~spl2_37),
% 25.62/3.65    inference(avatar_component_clause,[],[f988])).
% 25.62/3.65  fof(f19896,plain,(
% 25.62/3.65    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(X3,X2),k5_xboole_0(X3,k4_xboole_0(X2,k4_xboole_0(X2,k5_xboole_0(X3,X2)))))) ) | (~spl2_30 | ~spl2_88)),
% 25.62/3.65    inference(superposition,[],[f11481,f575])).
% 25.62/3.65  fof(f11481,plain,(
% 25.62/3.65    ( ! [X2,X0,X1] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,k5_xboole_0(X0,X1)))))) ) | ~spl2_88),
% 25.62/3.65    inference(avatar_component_clause,[],[f11480])).
% 25.62/3.65  fof(f18922,plain,(
% 25.62/3.65    spl2_105 | ~spl2_32 | ~spl2_73),
% 25.62/3.65    inference(avatar_split_clause,[],[f2608,f2540,f582,f18920])).
% 25.62/3.65  fof(f582,plain,(
% 25.62/3.65    spl2_32 <=> ! [X11,X10] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X11,X10),k5_xboole_0(X10,k4_xboole_0(X11,X10)))),
% 25.62/3.65    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).
% 25.62/3.65  fof(f2608,plain,(
% 25.62/3.65    ( ! [X54,X52,X53] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X52,X53),k5_xboole_0(k4_xboole_0(X53,X54),k4_xboole_0(X52,X53)))) ) | (~spl2_32 | ~spl2_73)),
% 25.62/3.65    inference(superposition,[],[f583,f2541])).
% 25.62/3.65  fof(f583,plain,(
% 25.62/3.65    ( ! [X10,X11] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X11,X10),k5_xboole_0(X10,k4_xboole_0(X11,X10)))) ) | ~spl2_32),
% 25.62/3.65    inference(avatar_component_clause,[],[f582])).
% 25.62/3.65  fof(f18918,plain,(
% 25.62/3.65    spl2_104 | ~spl2_3 | ~spl2_73),
% 25.62/3.65    inference(avatar_split_clause,[],[f2597,f2540,f39,f18916])).
% 25.62/3.65  fof(f39,plain,(
% 25.62/3.65    spl2_3 <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))),
% 25.62/3.65    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 25.62/3.65  fof(f2597,plain,(
% 25.62/3.65    ( ! [X21,X19,X20] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X20,X21),k5_xboole_0(k4_xboole_0(X20,X21),k4_xboole_0(X19,X20)))) ) | (~spl2_3 | ~spl2_73)),
% 25.62/3.65    inference(superposition,[],[f40,f2541])).
% 25.62/3.65  fof(f40,plain,(
% 25.62/3.65    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) ) | ~spl2_3),
% 25.62/3.65    inference(avatar_component_clause,[],[f39])).
% 25.62/3.65  fof(f17846,plain,(
% 25.62/3.65    spl2_101 | ~spl2_2 | ~spl2_7 | ~spl2_95),
% 25.62/3.65    inference(avatar_split_clause,[],[f17151,f16875,f59,f35,f17844])).
% 25.62/3.65  fof(f16875,plain,(
% 25.62/3.65    spl2_95 <=> ! [X7,X8] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X7)),k4_xboole_0(X7,k4_xboole_0(X7,X8)))),
% 25.62/3.65    introduced(avatar_definition,[new_symbols(naming,[spl2_95])])).
% 25.62/3.65  fof(f17151,plain,(
% 25.62/3.65    ( ! [X21,X22] : (k4_xboole_0(X21,k4_xboole_0(X21,X22)) = k4_xboole_0(k4_xboole_0(X22,k4_xboole_0(X22,X21)),k1_xboole_0)) ) | (~spl2_2 | ~spl2_7 | ~spl2_95)),
% 25.62/3.65    inference(forward_demodulation,[],[f17150,f16876])).
% 25.62/3.65  fof(f16876,plain,(
% 25.62/3.65    ( ! [X8,X7] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X7)),k4_xboole_0(X7,k4_xboole_0(X7,X8)))) ) | ~spl2_95),
% 25.62/3.65    inference(avatar_component_clause,[],[f16875])).
% 25.62/3.65  fof(f17150,plain,(
% 25.62/3.65    ( ! [X21,X22] : (k4_xboole_0(X21,k4_xboole_0(X21,X22)) = k4_xboole_0(k4_xboole_0(X22,k4_xboole_0(X22,X21)),k4_xboole_0(k4_xboole_0(X22,k4_xboole_0(X22,X21)),k4_xboole_0(X21,k4_xboole_0(X21,X22))))) ) | (~spl2_2 | ~spl2_7 | ~spl2_95)),
% 25.62/3.65    inference(forward_demodulation,[],[f16974,f36])).
% 25.62/3.65  fof(f16974,plain,(
% 25.62/3.65    ( ! [X21,X22] : (k4_xboole_0(k4_xboole_0(X22,k4_xboole_0(X22,X21)),k4_xboole_0(k4_xboole_0(X22,k4_xboole_0(X22,X21)),k4_xboole_0(X21,k4_xboole_0(X21,X22)))) = k4_xboole_0(k4_xboole_0(X21,k4_xboole_0(X21,X22)),k1_xboole_0)) ) | (~spl2_7 | ~spl2_95)),
% 25.62/3.65    inference(superposition,[],[f60,f16876])).
% 25.62/3.65  fof(f17659,plain,(
% 25.62/3.65    spl2_98 | ~spl2_2 | ~spl2_3 | ~spl2_46),
% 25.62/3.65    inference(avatar_split_clause,[],[f1868,f1709,f39,f35,f17657])).
% 25.62/3.65  fof(f1868,plain,(
% 25.62/3.65    ( ! [X19,X17,X18] : (k4_xboole_0(X17,k4_xboole_0(X17,k4_xboole_0(k5_xboole_0(X17,k4_xboole_0(X18,X17)),X19))) = k4_xboole_0(X17,X19)) ) | (~spl2_2 | ~spl2_3 | ~spl2_46)),
% 25.62/3.65    inference(forward_demodulation,[],[f1798,f36])).
% 25.62/3.65  fof(f1798,plain,(
% 25.62/3.65    ( ! [X19,X17,X18] : (k4_xboole_0(X17,k4_xboole_0(X17,k4_xboole_0(k5_xboole_0(X17,k4_xboole_0(X18,X17)),X19))) = k4_xboole_0(k4_xboole_0(X17,k1_xboole_0),X19)) ) | (~spl2_3 | ~spl2_46)),
% 25.62/3.65    inference(superposition,[],[f1710,f40])).
% 25.62/3.65  fof(f16877,plain,(
% 25.62/3.65    spl2_95 | ~spl2_2 | ~spl2_12 | ~spl2_31),
% 25.62/3.65    inference(avatar_split_clause,[],[f751,f578,f116,f35,f16875])).
% 25.62/3.65  fof(f116,plain,(
% 25.62/3.65    spl2_12 <=> ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)),
% 25.62/3.65    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 25.62/3.65  fof(f751,plain,(
% 25.62/3.65    ( ! [X8,X7] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X7)),k4_xboole_0(X7,k4_xboole_0(X7,X8)))) ) | (~spl2_2 | ~spl2_12 | ~spl2_31)),
% 25.62/3.65    inference(forward_demodulation,[],[f750,f117])).
% 25.62/3.65  fof(f117,plain,(
% 25.62/3.65    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) ) | ~spl2_12),
% 25.62/3.65    inference(avatar_component_clause,[],[f116])).
% 25.62/3.65  fof(f750,plain,(
% 25.62/3.65    ( ! [X8,X7] : (k4_xboole_0(X8,X8) = k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X7)),k4_xboole_0(X7,k4_xboole_0(X7,X8)))) ) | (~spl2_2 | ~spl2_12 | ~spl2_31)),
% 25.62/3.65    inference(forward_demodulation,[],[f749,f36])).
% 25.62/3.65  fof(f749,plain,(
% 25.62/3.65    ( ! [X8,X7] : (k4_xboole_0(X8,k4_xboole_0(X8,k1_xboole_0)) = k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X7)),k4_xboole_0(X7,k4_xboole_0(X7,X8)))) ) | (~spl2_12 | ~spl2_31)),
% 25.62/3.65    inference(forward_demodulation,[],[f748,f117])).
% 25.62/3.65  fof(f748,plain,(
% 25.62/3.65    ( ! [X8,X7] : (k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X7)),k4_xboole_0(X7,k4_xboole_0(X7,X8))) = k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X7,X7)))) ) | ~spl2_31),
% 25.62/3.65    inference(forward_demodulation,[],[f718,f29])).
% 25.62/3.65  fof(f29,plain,(
% 25.62/3.65    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 25.62/3.65    inference(definition_unfolding,[],[f23,f21,f21])).
% 25.62/3.65  fof(f21,plain,(
% 25.62/3.65    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 25.62/3.65    inference(cnf_transformation,[],[f5])).
% 25.62/3.65  fof(f5,axiom,(
% 25.62/3.65    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 25.62/3.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 25.62/3.65  fof(f23,plain,(
% 25.62/3.65    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 25.62/3.65    inference(cnf_transformation,[],[f6])).
% 25.62/3.65  fof(f6,axiom,(
% 25.62/3.65    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 25.62/3.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 25.62/3.65  fof(f718,plain,(
% 25.62/3.65    ( ! [X8,X7] : (k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X7)),X7) = k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X7)),k4_xboole_0(X7,k4_xboole_0(X7,X8)))) ) | ~spl2_31),
% 25.62/3.65    inference(superposition,[],[f579,f579])).
% 25.62/3.65  fof(f11482,plain,(
% 25.62/3.65    spl2_88 | ~spl2_3 | ~spl2_5),
% 25.62/3.65    inference(avatar_split_clause,[],[f63,f51,f39,f11480])).
% 25.62/3.65  fof(f51,plain,(
% 25.62/3.65    spl2_5 <=> ! [X1,X0,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 25.62/3.65    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 25.62/3.65  fof(f63,plain,(
% 25.62/3.65    ( ! [X2,X0,X1] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,k5_xboole_0(X0,X1)))))) ) | (~spl2_3 | ~spl2_5)),
% 25.62/3.65    inference(superposition,[],[f40,f52])).
% 25.62/3.65  fof(f52,plain,(
% 25.62/3.65    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) ) | ~spl2_5),
% 25.62/3.65    inference(avatar_component_clause,[],[f51])).
% 25.62/3.65  fof(f2542,plain,(
% 25.62/3.65    spl2_73 | ~spl2_68 | ~spl2_71),
% 25.62/3.65    inference(avatar_split_clause,[],[f2316,f2307,f2031,f2540])).
% 25.62/3.65  fof(f2031,plain,(
% 25.62/3.65    spl2_68 <=> ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X2,X1)) = X1),
% 25.62/3.65    introduced(avatar_definition,[new_symbols(naming,[spl2_68])])).
% 25.62/3.65  fof(f2307,plain,(
% 25.62/3.65    spl2_71 <=> ! [X1,X0,X2] : k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X2)) = X0),
% 25.62/3.65    introduced(avatar_definition,[new_symbols(naming,[spl2_71])])).
% 25.62/3.65  fof(f2316,plain,(
% 25.62/3.65    ( ! [X19,X17,X18] : (k4_xboole_0(X18,X17) = k4_xboole_0(k4_xboole_0(X18,X17),k4_xboole_0(X17,X19))) ) | (~spl2_68 | ~spl2_71)),
% 25.62/3.65    inference(superposition,[],[f2308,f2032])).
% 25.62/3.65  fof(f2032,plain,(
% 25.62/3.65    ( ! [X2,X1] : (k4_xboole_0(X1,k4_xboole_0(X2,X1)) = X1) ) | ~spl2_68),
% 25.62/3.65    inference(avatar_component_clause,[],[f2031])).
% 25.62/3.65  fof(f2308,plain,(
% 25.62/3.65    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X2)) = X0) ) | ~spl2_71),
% 25.62/3.65    inference(avatar_component_clause,[],[f2307])).
% 25.62/3.65  fof(f2309,plain,(
% 25.62/3.65    spl2_71 | ~spl2_6 | ~spl2_11 | ~spl2_70),
% 25.62/3.65    inference(avatar_split_clause,[],[f2274,f2172,f109,f55,f2307])).
% 25.62/3.65  fof(f55,plain,(
% 25.62/3.65    spl2_6 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),
% 25.62/3.65    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 25.62/3.65  fof(f2172,plain,(
% 25.62/3.65    spl2_70 <=> ! [X22,X21,X23] : k1_xboole_0 = k4_xboole_0(X21,k4_xboole_0(X21,k4_xboole_0(k4_xboole_0(X22,X21),X23)))),
% 25.62/3.65    introduced(avatar_definition,[new_symbols(naming,[spl2_70])])).
% 25.62/3.65  fof(f2274,plain,(
% 25.62/3.65    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X2)) = X0) ) | (~spl2_6 | ~spl2_11 | ~spl2_70)),
% 25.62/3.65    inference(forward_demodulation,[],[f2213,f110])).
% 25.62/3.65  fof(f2213,plain,(
% 25.62/3.65    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X2))) ) | (~spl2_6 | ~spl2_70)),
% 25.62/3.65    inference(superposition,[],[f56,f2173])).
% 25.62/3.65  fof(f2173,plain,(
% 25.62/3.65    ( ! [X23,X21,X22] : (k1_xboole_0 = k4_xboole_0(X21,k4_xboole_0(X21,k4_xboole_0(k4_xboole_0(X22,X21),X23)))) ) | ~spl2_70),
% 25.62/3.65    inference(avatar_component_clause,[],[f2172])).
% 25.62/3.65  fof(f56,plain,(
% 25.62/3.65    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ) | ~spl2_6),
% 25.62/3.65    inference(avatar_component_clause,[],[f55])).
% 25.62/3.65  fof(f2174,plain,(
% 25.62/3.65    spl2_70 | ~spl2_1 | ~spl2_46 | ~spl2_67),
% 25.62/3.65    inference(avatar_split_clause,[],[f2005,f1934,f1709,f31,f2172])).
% 25.62/3.65  fof(f31,plain,(
% 25.62/3.65    spl2_1 <=> ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 25.62/3.65    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 25.62/3.65  fof(f1934,plain,(
% 25.62/3.65    spl2_67 <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))),
% 25.62/3.65    introduced(avatar_definition,[new_symbols(naming,[spl2_67])])).
% 25.62/3.65  fof(f2005,plain,(
% 25.62/3.65    ( ! [X23,X21,X22] : (k1_xboole_0 = k4_xboole_0(X21,k4_xboole_0(X21,k4_xboole_0(k4_xboole_0(X22,X21),X23)))) ) | (~spl2_1 | ~spl2_46 | ~spl2_67)),
% 25.62/3.65    inference(forward_demodulation,[],[f1966,f32])).
% 25.62/3.65  fof(f32,plain,(
% 25.62/3.65    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) ) | ~spl2_1),
% 25.62/3.65    inference(avatar_component_clause,[],[f31])).
% 25.62/3.65  fof(f1966,plain,(
% 25.62/3.65    ( ! [X23,X21,X22] : (k4_xboole_0(X21,k4_xboole_0(X21,k4_xboole_0(k4_xboole_0(X22,X21),X23))) = k4_xboole_0(k1_xboole_0,X23)) ) | (~spl2_46 | ~spl2_67)),
% 25.62/3.65    inference(superposition,[],[f1710,f1935])).
% 25.62/3.65  fof(f1935,plain,(
% 25.62/3.65    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) ) | ~spl2_67),
% 25.62/3.65    inference(avatar_component_clause,[],[f1934])).
% 25.62/3.65  fof(f2106,plain,(
% 25.62/3.65    spl2_69 | ~spl2_11 | ~spl2_23 | ~spl2_67),
% 25.62/3.65    inference(avatar_split_clause,[],[f1999,f1934,f384,f109,f2104])).
% 25.62/3.65  fof(f1999,plain,(
% 25.62/3.65    ( ! [X8,X7] : (k4_xboole_0(X8,X7) = k4_xboole_0(k4_xboole_0(X8,X7),X7)) ) | (~spl2_11 | ~spl2_23 | ~spl2_67)),
% 25.62/3.65    inference(forward_demodulation,[],[f1960,f110])).
% 25.62/3.65  fof(f1960,plain,(
% 25.62/3.65    ( ! [X8,X7] : (k4_xboole_0(k4_xboole_0(X8,X7),X7) = k5_xboole_0(k4_xboole_0(X8,X7),k1_xboole_0)) ) | (~spl2_23 | ~spl2_67)),
% 25.62/3.65    inference(superposition,[],[f385,f1935])).
% 25.62/3.65  fof(f2033,plain,(
% 25.62/3.65    spl2_68 | ~spl2_6 | ~spl2_11 | ~spl2_67),
% 25.62/3.65    inference(avatar_split_clause,[],[f1996,f1934,f109,f55,f2031])).
% 25.62/3.65  fof(f1996,plain,(
% 25.62/3.65    ( ! [X2,X1] : (k4_xboole_0(X1,k4_xboole_0(X2,X1)) = X1) ) | (~spl2_6 | ~spl2_11 | ~spl2_67)),
% 25.62/3.65    inference(forward_demodulation,[],[f1959,f110])).
% 25.62/3.65  fof(f1959,plain,(
% 25.62/3.65    ( ! [X2,X1] : (k5_xboole_0(X1,k1_xboole_0) = k4_xboole_0(X1,k4_xboole_0(X2,X1))) ) | (~spl2_6 | ~spl2_67)),
% 25.62/3.65    inference(superposition,[],[f56,f1935])).
% 25.62/3.65  fof(f1936,plain,(
% 25.62/3.65    spl2_67 | ~spl2_25 | ~spl2_46),
% 25.62/3.65    inference(avatar_split_clause,[],[f1814,f1709,f425,f1934])).
% 25.62/3.65  fof(f425,plain,(
% 25.62/3.65    spl2_25 <=> ! [X5,X6] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X5,X6),X5)),
% 25.62/3.65    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).
% 25.62/3.65  fof(f1814,plain,(
% 25.62/3.65    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) ) | (~spl2_25 | ~spl2_46)),
% 25.62/3.65    inference(superposition,[],[f1710,f426])).
% 25.62/3.65  fof(f426,plain,(
% 25.62/3.65    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X5,X6),X5)) ) | ~spl2_25),
% 25.62/3.65    inference(avatar_component_clause,[],[f425])).
% 25.62/3.65  fof(f1763,plain,(
% 25.62/3.65    spl2_59 | ~spl2_21 | ~spl2_34),
% 25.62/3.65    inference(avatar_split_clause,[],[f916,f868,f315,f1761])).
% 25.62/3.65  fof(f868,plain,(
% 25.62/3.65    spl2_34 <=> ! [X5,X4] : k4_xboole_0(X5,k4_xboole_0(X5,X4)) = k5_xboole_0(X4,k4_xboole_0(X4,X5))),
% 25.62/3.65    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).
% 25.62/3.65  fof(f916,plain,(
% 25.62/3.65    ( ! [X19,X18] : (k4_xboole_0(X18,X19) = k5_xboole_0(k4_xboole_0(X19,k4_xboole_0(X19,X18)),X18)) ) | (~spl2_21 | ~spl2_34)),
% 25.62/3.65    inference(superposition,[],[f316,f869])).
% 25.62/3.65  fof(f869,plain,(
% 25.62/3.65    ( ! [X4,X5] : (k4_xboole_0(X5,k4_xboole_0(X5,X4)) = k5_xboole_0(X4,k4_xboole_0(X4,X5))) ) | ~spl2_34),
% 25.62/3.65    inference(avatar_component_clause,[],[f868])).
% 25.62/3.65  fof(f1739,plain,(
% 25.62/3.65    spl2_53 | ~spl2_21 | ~spl2_23),
% 25.62/3.65    inference(avatar_split_clause,[],[f407,f384,f315,f1737])).
% 25.62/3.65  fof(f407,plain,(
% 25.62/3.65    ( ! [X10,X11] : (k4_xboole_0(X11,k4_xboole_0(X11,X10)) = k5_xboole_0(k4_xboole_0(X10,X11),X10)) ) | (~spl2_21 | ~spl2_23)),
% 25.62/3.65    inference(superposition,[],[f316,f385])).
% 25.62/3.65  fof(f1735,plain,(
% 25.62/3.65    spl2_52 | ~spl2_20 | ~spl2_23),
% 25.62/3.65    inference(avatar_split_clause,[],[f406,f384,f311,f1733])).
% 25.62/3.65  fof(f311,plain,(
% 25.62/3.65    spl2_20 <=> ! [X7,X6] : k5_xboole_0(k5_xboole_0(X6,X7),X7) = X6),
% 25.62/3.65    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 25.62/3.65  fof(f406,plain,(
% 25.62/3.65    ( ! [X8,X9] : (k5_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(X9,k4_xboole_0(X9,X8))) = X8) ) | (~spl2_20 | ~spl2_23)),
% 25.62/3.65    inference(superposition,[],[f312,f385])).
% 25.62/3.65  fof(f312,plain,(
% 25.62/3.65    ( ! [X6,X7] : (k5_xboole_0(k5_xboole_0(X6,X7),X7) = X6) ) | ~spl2_20),
% 25.62/3.65    inference(avatar_component_clause,[],[f311])).
% 25.62/3.65  fof(f1711,plain,(
% 25.62/3.65    spl2_46),
% 25.62/3.65    inference(avatar_split_clause,[],[f29,f1709])).
% 25.62/3.65  fof(f1703,plain,(
% 25.62/3.65    spl2_44 | ~spl2_6 | ~spl2_20),
% 25.62/3.65    inference(avatar_split_clause,[],[f324,f311,f55,f1701])).
% 25.62/3.65  fof(f324,plain,(
% 25.62/3.65    ( ! [X6,X7] : (k5_xboole_0(k4_xboole_0(X6,X7),k4_xboole_0(X6,k4_xboole_0(X6,X7))) = X6) ) | (~spl2_6 | ~spl2_20)),
% 25.62/3.65    inference(superposition,[],[f312,f56])).
% 25.62/3.65  fof(f990,plain,(
% 25.62/3.65    spl2_37 | ~spl2_5 | ~spl2_19),
% 25.62/3.65    inference(avatar_split_clause,[],[f307,f286,f51,f988])).
% 25.62/3.65  fof(f286,plain,(
% 25.62/3.65    spl2_19 <=> ! [X7,X6] : k5_xboole_0(X7,k5_xboole_0(X6,X7)) = X6),
% 25.62/3.65    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 25.62/3.65  fof(f307,plain,(
% 25.62/3.65    ( ! [X4,X5,X3] : (k5_xboole_0(X4,X5) = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X5)))) ) | (~spl2_5 | ~spl2_19)),
% 25.62/3.65    inference(forward_demodulation,[],[f299,f52])).
% 25.62/3.65  fof(f299,plain,(
% 25.62/3.65    ( ! [X4,X5,X3] : (k5_xboole_0(X4,X5) = k5_xboole_0(X3,k5_xboole_0(k5_xboole_0(X4,X3),X5))) ) | (~spl2_5 | ~spl2_19)),
% 25.62/3.65    inference(superposition,[],[f52,f287])).
% 25.62/3.65  fof(f287,plain,(
% 25.62/3.65    ( ! [X6,X7] : (k5_xboole_0(X7,k5_xboole_0(X6,X7)) = X6) ) | ~spl2_19),
% 25.62/3.65    inference(avatar_component_clause,[],[f286])).
% 25.62/3.65  fof(f982,plain,(
% 25.62/3.65    spl2_35 | ~spl2_5 | ~spl2_19),
% 25.62/3.65    inference(avatar_split_clause,[],[f289,f286,f51,f980])).
% 25.62/3.65  fof(f289,plain,(
% 25.62/3.65    ( ! [X2,X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,X2)))) ) | (~spl2_5 | ~spl2_19)),
% 25.62/3.65    inference(superposition,[],[f287,f52])).
% 25.62/3.65  fof(f870,plain,(
% 25.62/3.65    spl2_34 | ~spl2_18 | ~spl2_23),
% 25.62/3.65    inference(avatar_split_clause,[],[f404,f384,f259,f868])).
% 25.62/3.65  fof(f259,plain,(
% 25.62/3.65    spl2_18 <=> ! [X3,X2] : k5_xboole_0(X2,k5_xboole_0(X2,X3)) = X3),
% 25.62/3.65    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 25.62/3.65  fof(f404,plain,(
% 25.62/3.65    ( ! [X4,X5] : (k4_xboole_0(X5,k4_xboole_0(X5,X4)) = k5_xboole_0(X4,k4_xboole_0(X4,X5))) ) | (~spl2_18 | ~spl2_23)),
% 25.62/3.65    inference(superposition,[],[f260,f385])).
% 25.62/3.65  fof(f260,plain,(
% 25.62/3.65    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X2,X3)) = X3) ) | ~spl2_18),
% 25.62/3.65    inference(avatar_component_clause,[],[f259])).
% 25.62/3.65  fof(f588,plain,(
% 25.62/3.65    spl2_33 | ~spl2_2 | ~spl2_3 | ~spl2_7 | ~spl2_27),
% 25.62/3.65    inference(avatar_split_clause,[],[f525,f488,f59,f39,f35,f586])).
% 25.62/3.65  fof(f488,plain,(
% 25.62/3.65    spl2_27 <=> ! [X7,X6] : k4_xboole_0(X7,X6) = k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(X7,X6)),X6)),
% 25.62/3.65    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).
% 25.62/3.65  fof(f525,plain,(
% 25.62/3.65    ( ! [X4,X5] : (k4_xboole_0(k5_xboole_0(X4,k4_xboole_0(X5,X4)),k4_xboole_0(X5,X4)) = X4) ) | (~spl2_2 | ~spl2_3 | ~spl2_7 | ~spl2_27)),
% 25.62/3.65    inference(forward_demodulation,[],[f524,f36])).
% 25.62/3.65  fof(f524,plain,(
% 25.62/3.65    ( ! [X4,X5] : (k4_xboole_0(X4,k1_xboole_0) = k4_xboole_0(k5_xboole_0(X4,k4_xboole_0(X5,X4)),k4_xboole_0(X5,X4))) ) | (~spl2_3 | ~spl2_7 | ~spl2_27)),
% 25.62/3.65    inference(forward_demodulation,[],[f509,f40])).
% 25.62/3.65  fof(f509,plain,(
% 25.62/3.65    ( ! [X4,X5] : (k4_xboole_0(X4,k4_xboole_0(X4,k5_xboole_0(X4,k4_xboole_0(X5,X4)))) = k4_xboole_0(k5_xboole_0(X4,k4_xboole_0(X5,X4)),k4_xboole_0(X5,X4))) ) | (~spl2_7 | ~spl2_27)),
% 25.62/3.65    inference(superposition,[],[f60,f489])).
% 25.62/3.65  fof(f489,plain,(
% 25.62/3.65    ( ! [X6,X7] : (k4_xboole_0(X7,X6) = k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(X7,X6)),X6)) ) | ~spl2_27),
% 25.62/3.65    inference(avatar_component_clause,[],[f488])).
% 25.62/3.65  fof(f584,plain,(
% 25.62/3.65    spl2_32 | ~spl2_25 | ~spl2_27),
% 25.62/3.65    inference(avatar_split_clause,[],[f512,f488,f425,f582])).
% 25.62/3.65  fof(f512,plain,(
% 25.62/3.65    ( ! [X10,X11] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X11,X10),k5_xboole_0(X10,k4_xboole_0(X11,X10)))) ) | (~spl2_25 | ~spl2_27)),
% 25.62/3.65    inference(superposition,[],[f426,f489])).
% 25.62/3.65  fof(f580,plain,(
% 25.62/3.65    spl2_31 | ~spl2_2 | ~spl2_23 | ~spl2_26),
% 25.62/3.65    inference(avatar_split_clause,[],[f481,f448,f384,f35,f578])).
% 25.62/3.65  fof(f481,plain,(
% 25.62/3.65    ( ! [X10,X9] : (k4_xboole_0(X10,k4_xboole_0(X9,k4_xboole_0(X9,X10))) = k4_xboole_0(X10,X9)) ) | (~spl2_2 | ~spl2_23 | ~spl2_26)),
% 25.62/3.65    inference(forward_demodulation,[],[f480,f385])).
% 25.62/3.65  fof(f480,plain,(
% 25.62/3.65    ( ! [X10,X9] : (k4_xboole_0(X10,k4_xboole_0(X9,k4_xboole_0(X9,X10))) = k5_xboole_0(X10,k4_xboole_0(X9,k4_xboole_0(X9,X10)))) ) | (~spl2_2 | ~spl2_23 | ~spl2_26)),
% 25.62/3.65    inference(forward_demodulation,[],[f467,f36])).
% 25.62/3.65  fof(f467,plain,(
% 25.62/3.65    ( ! [X10,X9] : (k4_xboole_0(X10,k4_xboole_0(X9,k4_xboole_0(X9,X10))) = k5_xboole_0(X10,k4_xboole_0(k4_xboole_0(X9,k4_xboole_0(X9,X10)),k1_xboole_0))) ) | (~spl2_23 | ~spl2_26)),
% 25.62/3.65    inference(superposition,[],[f385,f449])).
% 25.62/3.65  fof(f576,plain,(
% 25.62/3.65    spl2_30 | ~spl2_6 | ~spl2_9 | ~spl2_11 | ~spl2_14),
% 25.62/3.65    inference(avatar_split_clause,[],[f223,f152,f109,f85,f55,f574])).
% 25.62/3.65  fof(f85,plain,(
% 25.62/3.65    spl2_9 <=> ! [X2] : k1_xboole_0 = k5_xboole_0(X2,X2)),
% 25.62/3.65    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 25.62/3.65  fof(f152,plain,(
% 25.62/3.65    spl2_14 <=> ! [X1,X0] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))),
% 25.62/3.65    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 25.62/3.65  fof(f223,plain,(
% 25.62/3.65    ( ! [X4,X5] : (k4_xboole_0(X4,k4_xboole_0(X4,X5)) = k5_xboole_0(X4,k4_xboole_0(X4,X5))) ) | (~spl2_6 | ~spl2_9 | ~spl2_11 | ~spl2_14)),
% 25.62/3.65    inference(forward_demodulation,[],[f201,f216])).
% 25.62/3.65  fof(f216,plain,(
% 25.62/3.65    ( ! [X3] : (k5_xboole_0(k1_xboole_0,X3) = X3) ) | (~spl2_9 | ~spl2_11 | ~spl2_14)),
% 25.62/3.65    inference(forward_demodulation,[],[f200,f110])).
% 25.62/3.65  fof(f200,plain,(
% 25.62/3.65    ( ! [X3] : (k5_xboole_0(X3,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X3)) ) | (~spl2_9 | ~spl2_14)),
% 25.62/3.65    inference(superposition,[],[f153,f86])).
% 25.62/3.65  fof(f86,plain,(
% 25.62/3.65    ( ! [X2] : (k1_xboole_0 = k5_xboole_0(X2,X2)) ) | ~spl2_9),
% 25.62/3.65    inference(avatar_component_clause,[],[f85])).
% 25.62/3.65  fof(f153,plain,(
% 25.62/3.65    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) ) | ~spl2_14),
% 25.62/3.65    inference(avatar_component_clause,[],[f152])).
% 25.62/3.65  fof(f201,plain,(
% 25.62/3.65    ( ! [X4,X5] : (k5_xboole_0(k1_xboole_0,k4_xboole_0(X4,k4_xboole_0(X4,X5))) = k5_xboole_0(X4,k4_xboole_0(X4,X5))) ) | (~spl2_6 | ~spl2_14)),
% 25.62/3.65    inference(superposition,[],[f153,f56])).
% 25.62/3.65  fof(f572,plain,(
% 25.62/3.65    spl2_29 | ~spl2_5 | ~spl2_9 | ~spl2_11 | ~spl2_14),
% 25.62/3.65    inference(avatar_split_clause,[],[f217,f152,f109,f85,f51,f570])).
% 25.62/3.65  fof(f217,plain,(
% 25.62/3.65    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = X2) ) | (~spl2_5 | ~spl2_9 | ~spl2_11 | ~spl2_14)),
% 25.62/3.65    inference(backward_demodulation,[],[f199,f216])).
% 25.62/3.65  fof(f199,plain,(
% 25.62/3.65    ( ! [X2,X0,X1] : (k5_xboole_0(k1_xboole_0,X2) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2)))) ) | (~spl2_5 | ~spl2_14)),
% 25.62/3.65    inference(superposition,[],[f153,f52])).
% 25.62/3.65  fof(f494,plain,(
% 25.62/3.65    spl2_28 | ~spl2_2 | ~spl2_7 | ~spl2_25),
% 25.62/3.65    inference(avatar_split_clause,[],[f443,f425,f59,f35,f492])).
% 25.62/3.65  fof(f443,plain,(
% 25.62/3.65    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X2,X3)))) ) | (~spl2_2 | ~spl2_7 | ~spl2_25)),
% 25.62/3.65    inference(forward_demodulation,[],[f437,f36])).
% 25.62/3.65  fof(f437,plain,(
% 25.62/3.65    ( ! [X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k4_xboole_0(k4_xboole_0(X2,X3),k1_xboole_0)) ) | (~spl2_7 | ~spl2_25)),
% 25.62/3.65    inference(superposition,[],[f60,f426])).
% 25.62/3.65  fof(f490,plain,(
% 25.62/3.65    spl2_27 | ~spl2_2 | ~spl2_3 | ~spl2_21 | ~spl2_23),
% 25.62/3.65    inference(avatar_split_clause,[],[f414,f384,f315,f39,f35,f488])).
% 25.62/3.65  fof(f414,plain,(
% 25.62/3.65    ( ! [X6,X7] : (k4_xboole_0(X7,X6) = k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(X7,X6)),X6)) ) | (~spl2_2 | ~spl2_3 | ~spl2_21 | ~spl2_23)),
% 25.62/3.65    inference(forward_demodulation,[],[f413,f316])).
% 25.62/3.65  fof(f413,plain,(
% 25.62/3.65    ( ! [X6,X7] : (k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(X7,X6)),X6) = k5_xboole_0(k5_xboole_0(X6,k4_xboole_0(X7,X6)),X6)) ) | (~spl2_2 | ~spl2_3 | ~spl2_23)),
% 25.62/3.65    inference(forward_demodulation,[],[f396,f36])).
% 25.62/3.65  fof(f396,plain,(
% 25.62/3.65    ( ! [X6,X7] : (k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(X7,X6)),X6) = k5_xboole_0(k5_xboole_0(X6,k4_xboole_0(X7,X6)),k4_xboole_0(X6,k1_xboole_0))) ) | (~spl2_3 | ~spl2_23)),
% 25.62/3.65    inference(superposition,[],[f385,f40])).
% 25.62/3.65  fof(f450,plain,(
% 25.62/3.65    spl2_26 | ~spl2_7 | ~spl2_25),
% 25.62/3.65    inference(avatar_split_clause,[],[f430,f425,f59,f448])).
% 25.62/3.65  fof(f430,plain,(
% 25.62/3.65    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X2)),X2)) ) | (~spl2_7 | ~spl2_25)),
% 25.62/3.65    inference(superposition,[],[f426,f60])).
% 25.62/3.65  fof(f427,plain,(
% 25.62/3.65    spl2_25 | ~spl2_3 | ~spl2_7 | ~spl2_20 | ~spl2_23),
% 25.62/3.65    inference(avatar_split_clause,[],[f420,f384,f311,f59,f39,f425])).
% 25.62/3.65  fof(f420,plain,(
% 25.62/3.65    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X5,X6),X5)) ) | (~spl2_3 | ~spl2_7 | ~spl2_20 | ~spl2_23)),
% 25.62/3.65    inference(backward_demodulation,[],[f132,f406])).
% 25.62/3.65  fof(f132,plain,(
% 25.62/3.65    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X5,X6),k5_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X6,k4_xboole_0(X6,X5))))) ) | (~spl2_3 | ~spl2_7)),
% 25.62/3.65    inference(superposition,[],[f40,f60])).
% 25.62/3.65  fof(f391,plain,(
% 25.62/3.65    ~spl2_24),
% 25.62/3.65    inference(avatar_split_clause,[],[f26,f388])).
% 25.62/3.65  fof(f26,plain,(
% 25.62/3.65    k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 25.62/3.65    inference(definition_unfolding,[],[f15,f20,f21])).
% 25.62/3.65  fof(f20,plain,(
% 25.62/3.65    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 25.62/3.65    inference(cnf_transformation,[],[f9])).
% 25.62/3.65  fof(f9,axiom,(
% 25.62/3.65    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 25.62/3.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 25.62/3.65  fof(f15,plain,(
% 25.62/3.65    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 25.62/3.65    inference(cnf_transformation,[],[f14])).
% 25.62/3.65  fof(f14,plain,(
% 25.62/3.65    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 25.62/3.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f13])).
% 25.62/3.65  fof(f13,plain,(
% 25.62/3.65    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 25.62/3.65    introduced(choice_axiom,[])).
% 25.62/3.65  fof(f12,plain,(
% 25.62/3.65    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 25.62/3.65    inference(ennf_transformation,[],[f11])).
% 25.62/3.65  fof(f11,negated_conjecture,(
% 25.62/3.65    ~! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 25.62/3.65    inference(negated_conjecture,[],[f10])).
% 25.62/3.65  fof(f10,conjecture,(
% 25.62/3.65    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 25.62/3.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_xboole_1)).
% 25.62/3.65  fof(f386,plain,(
% 25.62/3.65    spl2_23 | ~spl2_6 | ~spl2_7),
% 25.62/3.65    inference(avatar_split_clause,[],[f130,f59,f55,f384])).
% 25.62/3.65  fof(f130,plain,(
% 25.62/3.65    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))) ) | (~spl2_6 | ~spl2_7)),
% 25.62/3.65    inference(superposition,[],[f56,f60])).
% 25.62/3.65  fof(f321,plain,(
% 25.62/3.65    spl2_22 | ~spl2_18 | ~spl2_19),
% 25.62/3.65    inference(avatar_split_clause,[],[f298,f286,f259,f319])).
% 25.62/3.65  fof(f298,plain,(
% 25.62/3.65    ( ! [X2,X1] : (k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1)) ) | (~spl2_18 | ~spl2_19)),
% 25.62/3.65    inference(superposition,[],[f260,f287])).
% 25.62/3.65  fof(f317,plain,(
% 25.62/3.65    spl2_21 | ~spl2_19),
% 25.62/3.65    inference(avatar_split_clause,[],[f293,f286,f315])).
% 25.62/3.65  fof(f293,plain,(
% 25.62/3.65    ( ! [X8,X9] : (k5_xboole_0(k5_xboole_0(X9,X8),X9) = X8) ) | ~spl2_19),
% 25.62/3.65    inference(superposition,[],[f287,f287])).
% 25.62/3.65  fof(f313,plain,(
% 25.62/3.65    spl2_20 | ~spl2_18 | ~spl2_19),
% 25.62/3.65    inference(avatar_split_clause,[],[f292,f286,f259,f311])).
% 25.62/3.65  fof(f292,plain,(
% 25.62/3.65    ( ! [X6,X7] : (k5_xboole_0(k5_xboole_0(X6,X7),X7) = X6) ) | (~spl2_18 | ~spl2_19)),
% 25.62/3.65    inference(superposition,[],[f287,f260])).
% 25.62/3.65  fof(f288,plain,(
% 25.62/3.65    spl2_19 | ~spl2_11 | ~spl2_13 | ~spl2_18),
% 25.62/3.65    inference(avatar_split_clause,[],[f277,f259,f148,f109,f286])).
% 25.62/3.65  fof(f148,plain,(
% 25.62/3.65    spl2_13 <=> ! [X1,X0] : k1_xboole_0 = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1)))),
% 25.62/3.65    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 25.62/3.65  fof(f277,plain,(
% 25.62/3.65    ( ! [X6,X7] : (k5_xboole_0(X7,k5_xboole_0(X6,X7)) = X6) ) | (~spl2_11 | ~spl2_13 | ~spl2_18)),
% 25.62/3.65    inference(forward_demodulation,[],[f265,f110])).
% 25.62/3.65  fof(f265,plain,(
% 25.62/3.65    ( ! [X6,X7] : (k5_xboole_0(X7,k5_xboole_0(X6,X7)) = k5_xboole_0(X6,k1_xboole_0)) ) | (~spl2_13 | ~spl2_18)),
% 25.62/3.65    inference(superposition,[],[f260,f149])).
% 25.62/3.65  fof(f149,plain,(
% 25.62/3.65    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1)))) ) | ~spl2_13),
% 25.62/3.65    inference(avatar_component_clause,[],[f148])).
% 25.62/3.65  fof(f261,plain,(
% 25.62/3.65    spl2_18 | ~spl2_5 | ~spl2_9 | ~spl2_11 | ~spl2_14 | ~spl2_16),
% 25.62/3.65    inference(avatar_split_clause,[],[f222,f177,f152,f109,f85,f51,f259])).
% 25.62/3.65  fof(f177,plain,(
% 25.62/3.65    spl2_16 <=> ! [X8] : k1_xboole_0 = k5_xboole_0(X8,k5_xboole_0(k1_xboole_0,X8))),
% 25.62/3.65    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 25.62/3.65  fof(f222,plain,(
% 25.62/3.65    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X2,X3)) = X3) ) | (~spl2_5 | ~spl2_9 | ~spl2_11 | ~spl2_14 | ~spl2_16)),
% 25.62/3.65    inference(forward_demodulation,[],[f218,f216])).
% 25.62/3.65  fof(f218,plain,(
% 25.62/3.65    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(k1_xboole_0,k5_xboole_0(X2,X3))) = X3) ) | (~spl2_5 | ~spl2_9 | ~spl2_11 | ~spl2_14 | ~spl2_16)),
% 25.62/3.65    inference(backward_demodulation,[],[f197,f216])).
% 25.62/3.65  fof(f197,plain,(
% 25.62/3.65    ( ! [X2,X3] : (k5_xboole_0(k1_xboole_0,X3) = k5_xboole_0(X2,k5_xboole_0(k1_xboole_0,k5_xboole_0(X2,X3)))) ) | (~spl2_5 | ~spl2_16)),
% 25.62/3.65    inference(forward_demodulation,[],[f188,f52])).
% 25.62/3.65  fof(f188,plain,(
% 25.62/3.65    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(k1_xboole_0,X2),X3)) = k5_xboole_0(k1_xboole_0,X3)) ) | (~spl2_5 | ~spl2_16)),
% 25.62/3.65    inference(superposition,[],[f52,f178])).
% 25.62/3.65  fof(f178,plain,(
% 25.62/3.65    ( ! [X8] : (k1_xboole_0 = k5_xboole_0(X8,k5_xboole_0(k1_xboole_0,X8))) ) | ~spl2_16),
% 25.62/3.65    inference(avatar_component_clause,[],[f177])).
% 25.62/3.65  fof(f179,plain,(
% 25.62/3.65    spl2_16 | ~spl2_11 | ~spl2_13),
% 25.62/3.65    inference(avatar_split_clause,[],[f163,f148,f109,f177])).
% 25.62/3.65  fof(f163,plain,(
% 25.62/3.65    ( ! [X8] : (k1_xboole_0 = k5_xboole_0(X8,k5_xboole_0(k1_xboole_0,X8))) ) | (~spl2_11 | ~spl2_13)),
% 25.62/3.65    inference(superposition,[],[f149,f110])).
% 25.62/3.65  fof(f154,plain,(
% 25.62/3.65    spl2_14 | ~spl2_5 | ~spl2_9),
% 25.62/3.65    inference(avatar_split_clause,[],[f89,f85,f51,f152])).
% 25.62/3.65  fof(f89,plain,(
% 25.62/3.65    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) ) | (~spl2_5 | ~spl2_9)),
% 25.62/3.65    inference(superposition,[],[f52,f86])).
% 25.62/3.65  fof(f150,plain,(
% 25.62/3.65    spl2_13 | ~spl2_5 | ~spl2_9),
% 25.62/3.65    inference(avatar_split_clause,[],[f88,f85,f51,f148])).
% 25.62/3.65  fof(f88,plain,(
% 25.62/3.65    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1)))) ) | (~spl2_5 | ~spl2_9)),
% 25.62/3.65    inference(superposition,[],[f86,f52])).
% 25.62/3.65  fof(f118,plain,(
% 25.62/3.65    spl2_12 | ~spl2_3 | ~spl2_10),
% 25.62/3.65    inference(avatar_split_clause,[],[f99,f93,f39,f116])).
% 25.62/3.65  fof(f93,plain,(
% 25.62/3.65    spl2_10 <=> ! [X1] : k5_xboole_0(X1,k4_xboole_0(X1,X1)) = X1),
% 25.62/3.65    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 25.62/3.65  fof(f99,plain,(
% 25.62/3.65    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) ) | (~spl2_3 | ~spl2_10)),
% 25.62/3.65    inference(superposition,[],[f40,f94])).
% 25.62/3.65  fof(f94,plain,(
% 25.62/3.65    ( ! [X1] : (k5_xboole_0(X1,k4_xboole_0(X1,X1)) = X1) ) | ~spl2_10),
% 25.62/3.65    inference(avatar_component_clause,[],[f93])).
% 25.62/3.65  fof(f111,plain,(
% 25.62/3.65    spl2_11 | ~spl2_3 | ~spl2_10),
% 25.62/3.65    inference(avatar_split_clause,[],[f102,f93,f39,f109])).
% 25.62/3.65  fof(f102,plain,(
% 25.62/3.65    ( ! [X1] : (k5_xboole_0(X1,k1_xboole_0) = X1) ) | (~spl2_3 | ~spl2_10)),
% 25.62/3.65    inference(backward_demodulation,[],[f94,f99])).
% 25.62/3.65  fof(f95,plain,(
% 25.62/3.65    spl2_10 | ~spl2_2 | ~spl2_6),
% 25.62/3.65    inference(avatar_split_clause,[],[f68,f55,f35,f93])).
% 25.62/3.65  fof(f68,plain,(
% 25.62/3.65    ( ! [X1] : (k5_xboole_0(X1,k4_xboole_0(X1,X1)) = X1) ) | (~spl2_2 | ~spl2_6)),
% 25.62/3.65    inference(superposition,[],[f56,f36])).
% 25.62/3.65  fof(f87,plain,(
% 25.62/3.65    spl2_9 | ~spl2_2 | ~spl2_3 | ~spl2_6),
% 25.62/3.65    inference(avatar_split_clause,[],[f76,f55,f39,f35,f85])).
% 25.62/3.65  fof(f76,plain,(
% 25.62/3.65    ( ! [X2] : (k1_xboole_0 = k5_xboole_0(X2,X2)) ) | (~spl2_2 | ~spl2_3 | ~spl2_6)),
% 25.62/3.65    inference(forward_demodulation,[],[f69,f36])).
% 25.62/3.65  fof(f69,plain,(
% 25.62/3.65    ( ! [X2] : (k1_xboole_0 = k5_xboole_0(X2,k4_xboole_0(X2,k1_xboole_0))) ) | (~spl2_3 | ~spl2_6)),
% 25.62/3.65    inference(superposition,[],[f56,f40])).
% 25.62/3.65  fof(f61,plain,(
% 25.62/3.65    spl2_7),
% 25.62/3.65    inference(avatar_split_clause,[],[f28,f59])).
% 25.62/3.65  fof(f28,plain,(
% 25.62/3.65    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 25.62/3.65    inference(definition_unfolding,[],[f19,f21,f21])).
% 25.62/3.65  fof(f19,plain,(
% 25.62/3.65    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 25.62/3.65    inference(cnf_transformation,[],[f1])).
% 25.62/3.65  fof(f1,axiom,(
% 25.62/3.65    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 25.62/3.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 25.62/3.65  fof(f57,plain,(
% 25.62/3.65    spl2_6),
% 25.62/3.65    inference(avatar_split_clause,[],[f25,f55])).
% 25.62/3.65  fof(f25,plain,(
% 25.62/3.65    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 25.62/3.65    inference(definition_unfolding,[],[f22,f21])).
% 25.62/3.65  fof(f22,plain,(
% 25.62/3.65    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 25.62/3.65    inference(cnf_transformation,[],[f2])).
% 25.62/3.65  fof(f2,axiom,(
% 25.62/3.65    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 25.62/3.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 25.62/3.65  fof(f53,plain,(
% 25.62/3.65    spl2_5),
% 25.62/3.65    inference(avatar_split_clause,[],[f24,f51])).
% 25.62/3.65  fof(f24,plain,(
% 25.62/3.65    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 25.62/3.65    inference(cnf_transformation,[],[f8])).
% 25.62/3.65  fof(f8,axiom,(
% 25.62/3.65    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 25.62/3.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 25.62/3.65  fof(f41,plain,(
% 25.62/3.65    spl2_3),
% 25.62/3.65    inference(avatar_split_clause,[],[f27,f39])).
% 25.62/3.65  fof(f27,plain,(
% 25.62/3.65    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 25.62/3.65    inference(definition_unfolding,[],[f18,f20])).
% 25.62/3.65  fof(f18,plain,(
% 25.62/3.65    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 25.62/3.65    inference(cnf_transformation,[],[f4])).
% 25.62/3.65  fof(f4,axiom,(
% 25.62/3.65    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 25.62/3.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 25.62/3.65  fof(f37,plain,(
% 25.62/3.65    spl2_2),
% 25.62/3.65    inference(avatar_split_clause,[],[f17,f35])).
% 25.62/3.65  fof(f17,plain,(
% 25.62/3.65    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 25.62/3.65    inference(cnf_transformation,[],[f3])).
% 25.62/3.65  fof(f3,axiom,(
% 25.62/3.65    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 25.62/3.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 25.62/3.65  fof(f33,plain,(
% 25.62/3.65    spl2_1),
% 25.62/3.65    inference(avatar_split_clause,[],[f16,f31])).
% 25.62/3.65  fof(f16,plain,(
% 25.62/3.65    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 25.62/3.65    inference(cnf_transformation,[],[f7])).
% 25.62/3.65  fof(f7,axiom,(
% 25.62/3.65    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 25.62/3.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 25.62/3.65  % SZS output end Proof for theBenchmark
% 25.62/3.65  % (26230)------------------------------
% 25.62/3.65  % (26230)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 25.62/3.65  % (26230)Termination reason: Refutation
% 25.62/3.65  
% 25.62/3.65  % (26230)Memory used [KB]: 84049
% 25.62/3.65  % (26230)Time elapsed: 3.197 s
% 25.62/3.65  % (26230)------------------------------
% 25.62/3.65  % (26230)------------------------------
% 26.33/3.66  % (26216)Success in time 3.311 s
%------------------------------------------------------------------------------
