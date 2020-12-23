%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:00 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  169 ( 381 expanded)
%              Number of leaves         :   43 ( 184 expanded)
%              Depth                    :   10
%              Number of atoms          :  428 ( 908 expanded)
%              Number of equality atoms :  105 ( 289 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2000,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f38,f43,f48,f52,f56,f60,f75,f97,f107,f120,f130,f142,f190,f197,f201,f216,f319,f419,f431,f468,f989,f1001,f1030,f1039,f1071,f1141,f1455,f1687,f1758,f1899,f1928,f1974,f1993])).

fof(f1993,plain,
    ( spl3_2
    | ~ spl3_4
    | ~ spl3_63
    | ~ spl3_96 ),
    inference(avatar_contradiction_clause,[],[f1992])).

fof(f1992,plain,
    ( $false
    | spl3_2
    | ~ spl3_4
    | ~ spl3_63
    | ~ spl3_96 ),
    inference(subsumption_resolution,[],[f1991,f42])).

fof(f42,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl3_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f1991,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_4
    | ~ spl3_63
    | ~ spl3_96 ),
    inference(forward_demodulation,[],[f1979,f51])).

fof(f51,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl3_4
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f1979,plain,
    ( r1_tarski(k4_xboole_0(sK0,k1_xboole_0),sK1)
    | ~ spl3_63
    | ~ spl3_96 ),
    inference(superposition,[],[f1000,f1973])).

fof(f1973,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_96 ),
    inference(avatar_component_clause,[],[f1971])).

fof(f1971,plain,
    ( spl3_96
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_96])])).

fof(f1000,plain,
    ( ! [X4,X5] : r1_tarski(k4_xboole_0(X5,k4_xboole_0(X5,X4)),X4)
    | ~ spl3_63 ),
    inference(avatar_component_clause,[],[f999])).

fof(f999,plain,
    ( spl3_63
  <=> ! [X5,X4] : r1_tarski(k4_xboole_0(X5,k4_xboole_0(X5,X4)),X4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_63])])).

fof(f1974,plain,
    ( spl3_96
    | ~ spl3_62
    | ~ spl3_92 ),
    inference(avatar_split_clause,[],[f1947,f1926,f986,f1971])).

fof(f986,plain,
    ( spl3_62
  <=> k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_62])])).

fof(f1926,plain,
    ( spl3_92
  <=> ! [X0] : k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k2_xboole_0(X0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_92])])).

fof(f1947,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_62
    | ~ spl3_92 ),
    inference(superposition,[],[f1927,f988])).

fof(f988,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl3_62 ),
    inference(avatar_component_clause,[],[f986])).

fof(f1927,plain,
    ( ! [X0] : k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k2_xboole_0(X0,sK2))
    | ~ spl3_92 ),
    inference(avatar_component_clause,[],[f1926])).

fof(f1928,plain,
    ( spl3_92
    | ~ spl3_5
    | ~ spl3_91 ),
    inference(avatar_split_clause,[],[f1900,f1897,f54,f1926])).

fof(f54,plain,
    ( spl3_5
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f1897,plain,
    ( spl3_91
  <=> ! [X0] : k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k2_xboole_0(sK2,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_91])])).

fof(f1900,plain,
    ( ! [X0] : k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k2_xboole_0(X0,sK2))
    | ~ spl3_5
    | ~ spl3_91 ),
    inference(superposition,[],[f1898,f55])).

fof(f55,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f54])).

fof(f1898,plain,
    ( ! [X0] : k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k2_xboole_0(sK2,X0))
    | ~ spl3_91 ),
    inference(avatar_component_clause,[],[f1897])).

fof(f1899,plain,
    ( spl3_91
    | ~ spl3_44
    | ~ spl3_86 ),
    inference(avatar_split_clause,[],[f1766,f1755,f429,f1897])).

fof(f429,plain,
    ( spl3_44
  <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).

fof(f1755,plain,
    ( spl3_86
  <=> sK0 = k4_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_86])])).

fof(f1766,plain,
    ( ! [X0] : k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k2_xboole_0(sK2,X0))
    | ~ spl3_44
    | ~ spl3_86 ),
    inference(superposition,[],[f430,f1757])).

fof(f1757,plain,
    ( sK0 = k4_xboole_0(sK0,sK2)
    | ~ spl3_86 ),
    inference(avatar_component_clause,[],[f1755])).

fof(f430,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))
    | ~ spl3_44 ),
    inference(avatar_component_clause,[],[f429])).

fof(f1758,plain,
    ( spl3_86
    | ~ spl3_5
    | ~ spl3_16
    | ~ spl3_44
    | ~ spl3_85 ),
    inference(avatar_split_clause,[],[f1707,f1684,f429,f128,f54,f1755])).

fof(f128,plain,
    ( spl3_16
  <=> ! [X1] : k2_xboole_0(k1_xboole_0,X1) = X1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f1684,plain,
    ( spl3_85
  <=> sK0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_85])])).

fof(f1707,plain,
    ( sK0 = k4_xboole_0(sK0,sK2)
    | ~ spl3_5
    | ~ spl3_16
    | ~ spl3_44
    | ~ spl3_85 ),
    inference(forward_demodulation,[],[f1706,f129])).

fof(f129,plain,
    ( ! [X1] : k2_xboole_0(k1_xboole_0,X1) = X1
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f128])).

fof(f1706,plain,
    ( sK0 = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,sK2))
    | ~ spl3_5
    | ~ spl3_44
    | ~ spl3_85 ),
    inference(forward_demodulation,[],[f1688,f55])).

fof(f1688,plain,
    ( sK0 = k4_xboole_0(sK0,k2_xboole_0(sK2,k1_xboole_0))
    | ~ spl3_44
    | ~ spl3_85 ),
    inference(superposition,[],[f1686,f430])).

fof(f1686,plain,
    ( sK0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k1_xboole_0)
    | ~ spl3_85 ),
    inference(avatar_component_clause,[],[f1684])).

fof(f1687,plain,
    ( spl3_85
    | ~ spl3_44
    | ~ spl3_67
    | ~ spl3_72
    | ~ spl3_83 ),
    inference(avatar_split_clause,[],[f1641,f1453,f1138,f1069,f429,f1684])).

fof(f1069,plain,
    ( spl3_67
  <=> ! [X1,X2] : k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_67])])).

fof(f1138,plain,
    ( spl3_72
  <=> k4_xboole_0(sK0,sK2) = k2_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_72])])).

fof(f1453,plain,
    ( spl3_83
  <=> ! [X9,X10] : k4_xboole_0(k2_xboole_0(X9,X10),k4_xboole_0(X10,X9)) = X9 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_83])])).

fof(f1641,plain,
    ( sK0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k1_xboole_0)
    | ~ spl3_44
    | ~ spl3_67
    | ~ spl3_72
    | ~ spl3_83 ),
    inference(forward_demodulation,[],[f1640,f1070])).

fof(f1070,plain,
    ( ! [X2,X1] : k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1))
    | ~ spl3_67 ),
    inference(avatar_component_clause,[],[f1069])).

fof(f1640,plain,
    ( sK0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,k2_xboole_0(sK2,sK0)))
    | ~ spl3_44
    | ~ spl3_72
    | ~ spl3_83 ),
    inference(forward_demodulation,[],[f1603,f430])).

fof(f1603,plain,
    ( sK0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),sK0))
    | ~ spl3_72
    | ~ spl3_83 ),
    inference(superposition,[],[f1454,f1140])).

fof(f1140,plain,
    ( k4_xboole_0(sK0,sK2) = k2_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl3_72 ),
    inference(avatar_component_clause,[],[f1138])).

fof(f1454,plain,
    ( ! [X10,X9] : k4_xboole_0(k2_xboole_0(X9,X10),k4_xboole_0(X10,X9)) = X9
    | ~ spl3_83 ),
    inference(avatar_component_clause,[],[f1453])).

fof(f1455,plain,
    ( spl3_83
    | ~ spl3_4
    | ~ spl3_17
    | ~ spl3_25
    | ~ spl3_26
    | ~ spl3_44
    | ~ spl3_48 ),
    inference(avatar_split_clause,[],[f825,f466,f429,f214,f199,f140,f50,f1453])).

fof(f140,plain,
    ( spl3_17
  <=> ! [X0] : k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f199,plain,
    ( spl3_25
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f214,plain,
    ( spl3_26
  <=> ! [X6] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f466,plain,
    ( spl3_48
  <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).

fof(f825,plain,
    ( ! [X10,X9] : k4_xboole_0(k2_xboole_0(X9,X10),k4_xboole_0(X10,X9)) = X9
    | ~ spl3_4
    | ~ spl3_17
    | ~ spl3_25
    | ~ spl3_26
    | ~ spl3_44
    | ~ spl3_48 ),
    inference(forward_demodulation,[],[f824,f51])).

fof(f824,plain,
    ( ! [X10,X9] : k4_xboole_0(k2_xboole_0(X9,X10),k4_xboole_0(X10,X9)) = k4_xboole_0(X9,k1_xboole_0)
    | ~ spl3_4
    | ~ spl3_17
    | ~ spl3_25
    | ~ spl3_26
    | ~ spl3_44
    | ~ spl3_48 ),
    inference(forward_demodulation,[],[f656,f786])).

fof(f786,plain,
    ( ! [X2,X3] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X3))
    | ~ spl3_4
    | ~ spl3_17
    | ~ spl3_26
    | ~ spl3_44
    | ~ spl3_48 ),
    inference(forward_demodulation,[],[f753,f722])).

fof(f722,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)
    | ~ spl3_4
    | ~ spl3_17
    | ~ spl3_26
    | ~ spl3_48 ),
    inference(backward_demodulation,[],[f141,f718])).

fof(f718,plain,
    ( ! [X2] : k1_xboole_0 = k4_xboole_0(X2,X2)
    | ~ spl3_4
    | ~ spl3_26
    | ~ spl3_48 ),
    inference(forward_demodulation,[],[f654,f215])).

fof(f215,plain,
    ( ! [X6] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X6))
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f214])).

fof(f654,plain,
    ( ! [X2] : k4_xboole_0(X2,X2) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X2))
    | ~ spl3_4
    | ~ spl3_48 ),
    inference(superposition,[],[f467,f51])).

fof(f467,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))
    | ~ spl3_48 ),
    inference(avatar_component_clause,[],[f466])).

fof(f141,plain,
    ( ! [X0] : k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X0)
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f140])).

fof(f753,plain,
    ( ! [X2,X3] : k4_xboole_0(k1_xboole_0,X3) = k4_xboole_0(X2,k2_xboole_0(X2,X3))
    | ~ spl3_4
    | ~ spl3_17
    | ~ spl3_26
    | ~ spl3_44
    | ~ spl3_48 ),
    inference(backward_demodulation,[],[f470,f722])).

fof(f470,plain,
    ( ! [X2,X3] : k4_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X2),X3)
    | ~ spl3_17
    | ~ spl3_44 ),
    inference(superposition,[],[f430,f141])).

fof(f656,plain,
    ( ! [X10,X9] : k4_xboole_0(X9,k4_xboole_0(X9,k2_xboole_0(X9,X10))) = k4_xboole_0(k2_xboole_0(X9,X10),k4_xboole_0(X10,X9))
    | ~ spl3_25
    | ~ spl3_48 ),
    inference(superposition,[],[f467,f200])).

fof(f200,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1)
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f199])).

fof(f1141,plain,
    ( spl3_72
    | ~ spl3_9
    | ~ spl3_64 ),
    inference(avatar_split_clause,[],[f1031,f1027,f73,f1138])).

fof(f73,plain,
    ( spl3_9
  <=> ! [X1,X0] :
        ( k2_xboole_0(X0,X1) = X1
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f1027,plain,
    ( spl3_64
  <=> r1_tarski(sK0,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_64])])).

fof(f1031,plain,
    ( k4_xboole_0(sK0,sK2) = k2_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl3_9
    | ~ spl3_64 ),
    inference(resolution,[],[f1029,f74])).

fof(f74,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k2_xboole_0(X0,X1) = X1 )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f73])).

fof(f1029,plain,
    ( r1_tarski(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl3_64 ),
    inference(avatar_component_clause,[],[f1027])).

fof(f1071,plain,
    ( spl3_67
    | ~ spl3_5
    | ~ spl3_66 ),
    inference(avatar_split_clause,[],[f1041,f1037,f54,f1069])).

fof(f1037,plain,
    ( spl3_66
  <=> ! [X3,X2] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_66])])).

fof(f1041,plain,
    ( ! [X2,X1] : k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1))
    | ~ spl3_5
    | ~ spl3_66 ),
    inference(superposition,[],[f1038,f55])).

fof(f1038,plain,
    ( ! [X2,X3] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X3))
    | ~ spl3_66 ),
    inference(avatar_component_clause,[],[f1037])).

fof(f1039,plain,
    ( spl3_66
    | ~ spl3_4
    | ~ spl3_17
    | ~ spl3_26
    | ~ spl3_44
    | ~ spl3_48 ),
    inference(avatar_split_clause,[],[f786,f466,f429,f214,f140,f50,f1037])).

fof(f1030,plain,
    ( spl3_64
    | ~ spl3_4
    | ~ spl3_34
    | ~ spl3_63 ),
    inference(avatar_split_clause,[],[f1023,f999,f316,f50,f1027])).

fof(f316,plain,
    ( spl3_34
  <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f1023,plain,
    ( r1_tarski(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl3_4
    | ~ spl3_34
    | ~ spl3_63 ),
    inference(forward_demodulation,[],[f1011,f51])).

fof(f1011,plain,
    ( r1_tarski(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK0,sK2))
    | ~ spl3_34
    | ~ spl3_63 ),
    inference(superposition,[],[f1000,f318])).

fof(f318,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl3_34 ),
    inference(avatar_component_clause,[],[f316])).

fof(f1001,plain,
    ( spl3_63
    | ~ spl3_6
    | ~ spl3_48 ),
    inference(avatar_split_clause,[],[f678,f466,f58,f999])).

fof(f58,plain,
    ( spl3_6
  <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f678,plain,
    ( ! [X4,X5] : r1_tarski(k4_xboole_0(X5,k4_xboole_0(X5,X4)),X4)
    | ~ spl3_6
    | ~ spl3_48 ),
    inference(superposition,[],[f59,f467])).

fof(f59,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f58])).

fof(f989,plain,
    ( spl3_62
    | ~ spl3_4
    | ~ spl3_17
    | ~ spl3_26
    | ~ spl3_42
    | ~ spl3_48 ),
    inference(avatar_split_clause,[],[f768,f466,f416,f214,f140,f50,f986])).

fof(f416,plain,
    ( spl3_42
  <=> k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(k1_xboole_0,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).

fof(f768,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl3_4
    | ~ spl3_17
    | ~ spl3_26
    | ~ spl3_42
    | ~ spl3_48 ),
    inference(backward_demodulation,[],[f418,f722])).

fof(f418,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(k1_xboole_0,k2_xboole_0(sK1,sK2))
    | ~ spl3_42 ),
    inference(avatar_component_clause,[],[f416])).

fof(f468,plain,(
    spl3_48 ),
    inference(avatar_split_clause,[],[f32,f466])).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f24,f26,f26])).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f431,plain,(
    spl3_44 ),
    inference(avatar_split_clause,[],[f30,f429])).

fof(f30,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f419,plain,
    ( spl3_42
    | ~ spl3_12
    | ~ spl3_14
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f138,f128,f104,f95,f416])).

fof(f95,plain,
    ( spl3_12
  <=> ! [X1,X0] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f104,plain,
    ( spl3_14
  <=> k2_xboole_0(sK1,sK2) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f138,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(k1_xboole_0,k2_xboole_0(sK1,sK2))
    | ~ spl3_12
    | ~ spl3_14
    | ~ spl3_16 ),
    inference(backward_demodulation,[],[f111,f134])).

fof(f134,plain,
    ( ! [X0] : k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X0)
    | ~ spl3_12
    | ~ spl3_16 ),
    inference(superposition,[],[f96,f129])).

fof(f96,plain,
    ( ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f95])).

fof(f111,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(k2_xboole_0(sK1,sK2),k2_xboole_0(sK1,sK2))
    | ~ spl3_12
    | ~ spl3_14 ),
    inference(superposition,[],[f96,f106])).

fof(f106,plain,
    ( k2_xboole_0(sK1,sK2) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f104])).

fof(f319,plain,
    ( spl3_34
    | ~ spl3_1
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f314,f188,f35,f316])).

fof(f35,plain,
    ( spl3_1
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f188,plain,
    ( spl3_23
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f314,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl3_1
    | ~ spl3_23 ),
    inference(resolution,[],[f189,f37])).

fof(f37,plain,
    ( r1_xboole_0(sK0,sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f189,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) )
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f188])).

fof(f216,plain,
    ( spl3_26
    | ~ spl3_15
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f208,f195,f118,f214])).

fof(f118,plain,
    ( spl3_15
  <=> ! [X2] : k2_xboole_0(X2,k1_xboole_0) = X2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f195,plain,
    ( spl3_24
  <=> ! [X1,X0] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f208,plain,
    ( ! [X6] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X6))
    | ~ spl3_15
    | ~ spl3_24 ),
    inference(superposition,[],[f196,f119])).

fof(f119,plain,
    ( ! [X2] : k2_xboole_0(X2,k1_xboole_0) = X2
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f118])).

fof(f196,plain,
    ( ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = X0
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f195])).

fof(f201,plain,
    ( spl3_25
    | ~ spl3_5
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f108,f95,f54,f199])).

fof(f108,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1)
    | ~ spl3_5
    | ~ spl3_12 ),
    inference(superposition,[],[f96,f55])).

fof(f197,plain,
    ( spl3_24
    | ~ spl3_6
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f77,f73,f58,f195])).

fof(f77,plain,
    ( ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = X0
    | ~ spl3_6
    | ~ spl3_9 ),
    inference(resolution,[],[f74,f59])).

fof(f190,plain,(
    spl3_23 ),
    inference(avatar_split_clause,[],[f33,f188])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f29,f26])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f142,plain,
    ( spl3_17
    | ~ spl3_12
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f134,f128,f95,f140])).

fof(f130,plain,
    ( spl3_16
    | ~ spl3_5
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f121,f118,f54,f128])).

fof(f121,plain,
    ( ! [X1] : k2_xboole_0(k1_xboole_0,X1) = X1
    | ~ spl3_5
    | ~ spl3_15 ),
    inference(superposition,[],[f119,f55])).

fof(f120,plain,
    ( spl3_15
    | ~ spl3_4
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f115,f95,f50,f118])).

fof(f115,plain,
    ( ! [X2] : k2_xboole_0(X2,k1_xboole_0) = X2
    | ~ spl3_4
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f112,f51])).

fof(f112,plain,
    ( ! [X2] : k2_xboole_0(X2,k1_xboole_0) = k4_xboole_0(X2,k1_xboole_0)
    | ~ spl3_4
    | ~ spl3_12 ),
    inference(superposition,[],[f96,f51])).

fof(f107,plain,
    ( spl3_14
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f76,f73,f45,f104])).

fof(f45,plain,
    ( spl3_3
  <=> r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f76,plain,
    ( k2_xboole_0(sK1,sK2) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(resolution,[],[f74,f47])).

fof(f47,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f45])).

fof(f97,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f27,f95])).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f75,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f28,f73])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f60,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f31,f58])).

fof(f31,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f23,f26])).

fof(f23,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f56,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f25,f54])).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f52,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f22,f50])).

fof(f22,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f48,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f19,f45])).

fof(f19,plain,(
    r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ~ r1_tarski(sK0,sK1)
    & r1_xboole_0(sK0,sK2)
    & r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
   => ( ~ r1_tarski(sK0,sK1)
      & r1_xboole_0(sK0,sK2)
      & r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
       => r1_tarski(X0,X1) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

fof(f43,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f21,f40])).

fof(f21,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f38,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f20,f35])).

fof(f20,plain,(
    r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:13:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.42  % (31761)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.45  % (31761)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f2000,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(avatar_sat_refutation,[],[f38,f43,f48,f52,f56,f60,f75,f97,f107,f120,f130,f142,f190,f197,f201,f216,f319,f419,f431,f468,f989,f1001,f1030,f1039,f1071,f1141,f1455,f1687,f1758,f1899,f1928,f1974,f1993])).
% 0.21/0.45  fof(f1993,plain,(
% 0.21/0.45    spl3_2 | ~spl3_4 | ~spl3_63 | ~spl3_96),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f1992])).
% 0.21/0.45  fof(f1992,plain,(
% 0.21/0.45    $false | (spl3_2 | ~spl3_4 | ~spl3_63 | ~spl3_96)),
% 0.21/0.45    inference(subsumption_resolution,[],[f1991,f42])).
% 0.21/0.45  fof(f42,plain,(
% 0.21/0.45    ~r1_tarski(sK0,sK1) | spl3_2),
% 0.21/0.45    inference(avatar_component_clause,[],[f40])).
% 0.21/0.45  fof(f40,plain,(
% 0.21/0.45    spl3_2 <=> r1_tarski(sK0,sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.45  fof(f1991,plain,(
% 0.21/0.45    r1_tarski(sK0,sK1) | (~spl3_4 | ~spl3_63 | ~spl3_96)),
% 0.21/0.45    inference(forward_demodulation,[],[f1979,f51])).
% 0.21/0.45  fof(f51,plain,(
% 0.21/0.45    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl3_4),
% 0.21/0.45    inference(avatar_component_clause,[],[f50])).
% 0.21/0.45  fof(f50,plain,(
% 0.21/0.45    spl3_4 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.45  fof(f1979,plain,(
% 0.21/0.45    r1_tarski(k4_xboole_0(sK0,k1_xboole_0),sK1) | (~spl3_63 | ~spl3_96)),
% 0.21/0.45    inference(superposition,[],[f1000,f1973])).
% 0.21/0.45  fof(f1973,plain,(
% 0.21/0.45    k1_xboole_0 = k4_xboole_0(sK0,sK1) | ~spl3_96),
% 0.21/0.45    inference(avatar_component_clause,[],[f1971])).
% 0.21/0.45  fof(f1971,plain,(
% 0.21/0.45    spl3_96 <=> k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_96])])).
% 0.21/0.45  fof(f1000,plain,(
% 0.21/0.45    ( ! [X4,X5] : (r1_tarski(k4_xboole_0(X5,k4_xboole_0(X5,X4)),X4)) ) | ~spl3_63),
% 0.21/0.45    inference(avatar_component_clause,[],[f999])).
% 0.21/0.45  fof(f999,plain,(
% 0.21/0.45    spl3_63 <=> ! [X5,X4] : r1_tarski(k4_xboole_0(X5,k4_xboole_0(X5,X4)),X4)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_63])])).
% 0.21/0.45  fof(f1974,plain,(
% 0.21/0.45    spl3_96 | ~spl3_62 | ~spl3_92),
% 0.21/0.45    inference(avatar_split_clause,[],[f1947,f1926,f986,f1971])).
% 0.21/0.45  fof(f986,plain,(
% 0.21/0.45    spl3_62 <=> k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_62])])).
% 0.21/0.45  fof(f1926,plain,(
% 0.21/0.45    spl3_92 <=> ! [X0] : k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k2_xboole_0(X0,sK2))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_92])])).
% 0.21/0.45  fof(f1947,plain,(
% 0.21/0.45    k1_xboole_0 = k4_xboole_0(sK0,sK1) | (~spl3_62 | ~spl3_92)),
% 0.21/0.45    inference(superposition,[],[f1927,f988])).
% 0.21/0.45  fof(f988,plain,(
% 0.21/0.45    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | ~spl3_62),
% 0.21/0.45    inference(avatar_component_clause,[],[f986])).
% 0.21/0.45  fof(f1927,plain,(
% 0.21/0.45    ( ! [X0] : (k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k2_xboole_0(X0,sK2))) ) | ~spl3_92),
% 0.21/0.45    inference(avatar_component_clause,[],[f1926])).
% 0.21/0.45  fof(f1928,plain,(
% 0.21/0.45    spl3_92 | ~spl3_5 | ~spl3_91),
% 0.21/0.45    inference(avatar_split_clause,[],[f1900,f1897,f54,f1926])).
% 0.21/0.45  fof(f54,plain,(
% 0.21/0.45    spl3_5 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.45  fof(f1897,plain,(
% 0.21/0.45    spl3_91 <=> ! [X0] : k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k2_xboole_0(sK2,X0))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_91])])).
% 0.21/0.45  fof(f1900,plain,(
% 0.21/0.45    ( ! [X0] : (k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k2_xboole_0(X0,sK2))) ) | (~spl3_5 | ~spl3_91)),
% 0.21/0.45    inference(superposition,[],[f1898,f55])).
% 0.21/0.45  fof(f55,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl3_5),
% 0.21/0.45    inference(avatar_component_clause,[],[f54])).
% 0.21/0.45  fof(f1898,plain,(
% 0.21/0.45    ( ! [X0] : (k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k2_xboole_0(sK2,X0))) ) | ~spl3_91),
% 0.21/0.45    inference(avatar_component_clause,[],[f1897])).
% 0.21/0.45  fof(f1899,plain,(
% 0.21/0.45    spl3_91 | ~spl3_44 | ~spl3_86),
% 0.21/0.45    inference(avatar_split_clause,[],[f1766,f1755,f429,f1897])).
% 0.21/0.45  fof(f429,plain,(
% 0.21/0.45    spl3_44 <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).
% 0.21/0.45  fof(f1755,plain,(
% 0.21/0.45    spl3_86 <=> sK0 = k4_xboole_0(sK0,sK2)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_86])])).
% 0.21/0.45  fof(f1766,plain,(
% 0.21/0.45    ( ! [X0] : (k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k2_xboole_0(sK2,X0))) ) | (~spl3_44 | ~spl3_86)),
% 0.21/0.45    inference(superposition,[],[f430,f1757])).
% 0.21/0.45  fof(f1757,plain,(
% 0.21/0.45    sK0 = k4_xboole_0(sK0,sK2) | ~spl3_86),
% 0.21/0.45    inference(avatar_component_clause,[],[f1755])).
% 0.21/0.45  fof(f430,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) ) | ~spl3_44),
% 0.21/0.45    inference(avatar_component_clause,[],[f429])).
% 0.21/0.45  fof(f1758,plain,(
% 0.21/0.45    spl3_86 | ~spl3_5 | ~spl3_16 | ~spl3_44 | ~spl3_85),
% 0.21/0.45    inference(avatar_split_clause,[],[f1707,f1684,f429,f128,f54,f1755])).
% 0.21/0.45  fof(f128,plain,(
% 0.21/0.45    spl3_16 <=> ! [X1] : k2_xboole_0(k1_xboole_0,X1) = X1),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.45  fof(f1684,plain,(
% 0.21/0.45    spl3_85 <=> sK0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k1_xboole_0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_85])])).
% 0.21/0.45  fof(f1707,plain,(
% 0.21/0.45    sK0 = k4_xboole_0(sK0,sK2) | (~spl3_5 | ~spl3_16 | ~spl3_44 | ~spl3_85)),
% 0.21/0.45    inference(forward_demodulation,[],[f1706,f129])).
% 0.21/0.45  fof(f129,plain,(
% 0.21/0.45    ( ! [X1] : (k2_xboole_0(k1_xboole_0,X1) = X1) ) | ~spl3_16),
% 0.21/0.45    inference(avatar_component_clause,[],[f128])).
% 0.21/0.45  fof(f1706,plain,(
% 0.21/0.45    sK0 = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,sK2)) | (~spl3_5 | ~spl3_44 | ~spl3_85)),
% 0.21/0.45    inference(forward_demodulation,[],[f1688,f55])).
% 0.21/0.45  fof(f1688,plain,(
% 0.21/0.45    sK0 = k4_xboole_0(sK0,k2_xboole_0(sK2,k1_xboole_0)) | (~spl3_44 | ~spl3_85)),
% 0.21/0.45    inference(superposition,[],[f1686,f430])).
% 0.21/0.45  fof(f1686,plain,(
% 0.21/0.45    sK0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k1_xboole_0) | ~spl3_85),
% 0.21/0.45    inference(avatar_component_clause,[],[f1684])).
% 0.21/0.45  fof(f1687,plain,(
% 0.21/0.45    spl3_85 | ~spl3_44 | ~spl3_67 | ~spl3_72 | ~spl3_83),
% 0.21/0.45    inference(avatar_split_clause,[],[f1641,f1453,f1138,f1069,f429,f1684])).
% 0.21/0.45  fof(f1069,plain,(
% 0.21/0.45    spl3_67 <=> ! [X1,X2] : k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_67])])).
% 0.21/0.45  fof(f1138,plain,(
% 0.21/0.45    spl3_72 <=> k4_xboole_0(sK0,sK2) = k2_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_72])])).
% 0.21/0.45  fof(f1453,plain,(
% 0.21/0.45    spl3_83 <=> ! [X9,X10] : k4_xboole_0(k2_xboole_0(X9,X10),k4_xboole_0(X10,X9)) = X9),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_83])])).
% 0.21/0.45  fof(f1641,plain,(
% 0.21/0.45    sK0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k1_xboole_0) | (~spl3_44 | ~spl3_67 | ~spl3_72 | ~spl3_83)),
% 0.21/0.45    inference(forward_demodulation,[],[f1640,f1070])).
% 0.21/0.45  fof(f1070,plain,(
% 0.21/0.45    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1))) ) | ~spl3_67),
% 0.21/0.45    inference(avatar_component_clause,[],[f1069])).
% 0.21/0.45  fof(f1640,plain,(
% 0.21/0.45    sK0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,k2_xboole_0(sK2,sK0))) | (~spl3_44 | ~spl3_72 | ~spl3_83)),
% 0.21/0.45    inference(forward_demodulation,[],[f1603,f430])).
% 0.21/0.45  fof(f1603,plain,(
% 0.21/0.45    sK0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),sK0)) | (~spl3_72 | ~spl3_83)),
% 0.21/0.45    inference(superposition,[],[f1454,f1140])).
% 0.21/0.45  fof(f1140,plain,(
% 0.21/0.45    k4_xboole_0(sK0,sK2) = k2_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | ~spl3_72),
% 0.21/0.45    inference(avatar_component_clause,[],[f1138])).
% 0.21/0.45  fof(f1454,plain,(
% 0.21/0.45    ( ! [X10,X9] : (k4_xboole_0(k2_xboole_0(X9,X10),k4_xboole_0(X10,X9)) = X9) ) | ~spl3_83),
% 0.21/0.45    inference(avatar_component_clause,[],[f1453])).
% 0.21/0.45  fof(f1455,plain,(
% 0.21/0.45    spl3_83 | ~spl3_4 | ~spl3_17 | ~spl3_25 | ~spl3_26 | ~spl3_44 | ~spl3_48),
% 0.21/0.45    inference(avatar_split_clause,[],[f825,f466,f429,f214,f199,f140,f50,f1453])).
% 0.21/0.45  fof(f140,plain,(
% 0.21/0.45    spl3_17 <=> ! [X0] : k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.45  fof(f199,plain,(
% 0.21/0.45    spl3_25 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.21/0.45  fof(f214,plain,(
% 0.21/0.45    spl3_26 <=> ! [X6] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X6))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.21/0.45  fof(f466,plain,(
% 0.21/0.45    spl3_48 <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).
% 0.21/0.45  fof(f825,plain,(
% 0.21/0.45    ( ! [X10,X9] : (k4_xboole_0(k2_xboole_0(X9,X10),k4_xboole_0(X10,X9)) = X9) ) | (~spl3_4 | ~spl3_17 | ~spl3_25 | ~spl3_26 | ~spl3_44 | ~spl3_48)),
% 0.21/0.45    inference(forward_demodulation,[],[f824,f51])).
% 0.21/0.45  fof(f824,plain,(
% 0.21/0.45    ( ! [X10,X9] : (k4_xboole_0(k2_xboole_0(X9,X10),k4_xboole_0(X10,X9)) = k4_xboole_0(X9,k1_xboole_0)) ) | (~spl3_4 | ~spl3_17 | ~spl3_25 | ~spl3_26 | ~spl3_44 | ~spl3_48)),
% 0.21/0.45    inference(forward_demodulation,[],[f656,f786])).
% 0.21/0.45  fof(f786,plain,(
% 0.21/0.45    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X3))) ) | (~spl3_4 | ~spl3_17 | ~spl3_26 | ~spl3_44 | ~spl3_48)),
% 0.21/0.45    inference(forward_demodulation,[],[f753,f722])).
% 0.21/0.45  fof(f722,plain,(
% 0.21/0.45    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) ) | (~spl3_4 | ~spl3_17 | ~spl3_26 | ~spl3_48)),
% 0.21/0.45    inference(backward_demodulation,[],[f141,f718])).
% 0.21/0.45  fof(f718,plain,(
% 0.21/0.45    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(X2,X2)) ) | (~spl3_4 | ~spl3_26 | ~spl3_48)),
% 0.21/0.45    inference(forward_demodulation,[],[f654,f215])).
% 0.21/0.45  fof(f215,plain,(
% 0.21/0.45    ( ! [X6] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X6))) ) | ~spl3_26),
% 0.21/0.45    inference(avatar_component_clause,[],[f214])).
% 0.21/0.45  fof(f654,plain,(
% 0.21/0.45    ( ! [X2] : (k4_xboole_0(X2,X2) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X2))) ) | (~spl3_4 | ~spl3_48)),
% 0.21/0.45    inference(superposition,[],[f467,f51])).
% 0.21/0.45  fof(f467,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) ) | ~spl3_48),
% 0.21/0.45    inference(avatar_component_clause,[],[f466])).
% 0.21/0.45  fof(f141,plain,(
% 0.21/0.45    ( ! [X0] : (k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X0)) ) | ~spl3_17),
% 0.21/0.45    inference(avatar_component_clause,[],[f140])).
% 0.21/0.45  fof(f753,plain,(
% 0.21/0.45    ( ! [X2,X3] : (k4_xboole_0(k1_xboole_0,X3) = k4_xboole_0(X2,k2_xboole_0(X2,X3))) ) | (~spl3_4 | ~spl3_17 | ~spl3_26 | ~spl3_44 | ~spl3_48)),
% 0.21/0.45    inference(backward_demodulation,[],[f470,f722])).
% 0.21/0.45  fof(f470,plain,(
% 0.21/0.45    ( ! [X2,X3] : (k4_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X2),X3)) ) | (~spl3_17 | ~spl3_44)),
% 0.21/0.45    inference(superposition,[],[f430,f141])).
% 0.21/0.45  fof(f656,plain,(
% 0.21/0.45    ( ! [X10,X9] : (k4_xboole_0(X9,k4_xboole_0(X9,k2_xboole_0(X9,X10))) = k4_xboole_0(k2_xboole_0(X9,X10),k4_xboole_0(X10,X9))) ) | (~spl3_25 | ~spl3_48)),
% 0.21/0.45    inference(superposition,[],[f467,f200])).
% 0.21/0.45  fof(f200,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1)) ) | ~spl3_25),
% 0.21/0.45    inference(avatar_component_clause,[],[f199])).
% 0.21/0.45  fof(f1141,plain,(
% 0.21/0.45    spl3_72 | ~spl3_9 | ~spl3_64),
% 0.21/0.45    inference(avatar_split_clause,[],[f1031,f1027,f73,f1138])).
% 0.21/0.45  fof(f73,plain,(
% 0.21/0.45    spl3_9 <=> ! [X1,X0] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.45  fof(f1027,plain,(
% 0.21/0.45    spl3_64 <=> r1_tarski(sK0,k4_xboole_0(sK0,sK2))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_64])])).
% 0.21/0.45  fof(f1031,plain,(
% 0.21/0.45    k4_xboole_0(sK0,sK2) = k2_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | (~spl3_9 | ~spl3_64)),
% 0.21/0.45    inference(resolution,[],[f1029,f74])).
% 0.21/0.45  fof(f74,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) ) | ~spl3_9),
% 0.21/0.45    inference(avatar_component_clause,[],[f73])).
% 0.21/0.45  fof(f1029,plain,(
% 0.21/0.45    r1_tarski(sK0,k4_xboole_0(sK0,sK2)) | ~spl3_64),
% 0.21/0.45    inference(avatar_component_clause,[],[f1027])).
% 0.21/0.45  fof(f1071,plain,(
% 0.21/0.45    spl3_67 | ~spl3_5 | ~spl3_66),
% 0.21/0.45    inference(avatar_split_clause,[],[f1041,f1037,f54,f1069])).
% 0.21/0.45  fof(f1037,plain,(
% 0.21/0.45    spl3_66 <=> ! [X3,X2] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X3))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_66])])).
% 0.21/0.45  fof(f1041,plain,(
% 0.21/0.45    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1))) ) | (~spl3_5 | ~spl3_66)),
% 0.21/0.45    inference(superposition,[],[f1038,f55])).
% 0.21/0.45  fof(f1038,plain,(
% 0.21/0.45    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X3))) ) | ~spl3_66),
% 0.21/0.45    inference(avatar_component_clause,[],[f1037])).
% 0.21/0.45  fof(f1039,plain,(
% 0.21/0.45    spl3_66 | ~spl3_4 | ~spl3_17 | ~spl3_26 | ~spl3_44 | ~spl3_48),
% 0.21/0.45    inference(avatar_split_clause,[],[f786,f466,f429,f214,f140,f50,f1037])).
% 0.21/0.45  fof(f1030,plain,(
% 0.21/0.45    spl3_64 | ~spl3_4 | ~spl3_34 | ~spl3_63),
% 0.21/0.45    inference(avatar_split_clause,[],[f1023,f999,f316,f50,f1027])).
% 0.21/0.45  fof(f316,plain,(
% 0.21/0.45    spl3_34 <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 0.21/0.45  fof(f1023,plain,(
% 0.21/0.45    r1_tarski(sK0,k4_xboole_0(sK0,sK2)) | (~spl3_4 | ~spl3_34 | ~spl3_63)),
% 0.21/0.45    inference(forward_demodulation,[],[f1011,f51])).
% 0.21/0.45  fof(f1011,plain,(
% 0.21/0.45    r1_tarski(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK0,sK2)) | (~spl3_34 | ~spl3_63)),
% 0.21/0.45    inference(superposition,[],[f1000,f318])).
% 0.21/0.45  fof(f318,plain,(
% 0.21/0.45    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | ~spl3_34),
% 0.21/0.45    inference(avatar_component_clause,[],[f316])).
% 0.21/0.45  fof(f1001,plain,(
% 0.21/0.45    spl3_63 | ~spl3_6 | ~spl3_48),
% 0.21/0.45    inference(avatar_split_clause,[],[f678,f466,f58,f999])).
% 0.21/0.45  fof(f58,plain,(
% 0.21/0.45    spl3_6 <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.45  fof(f678,plain,(
% 0.21/0.45    ( ! [X4,X5] : (r1_tarski(k4_xboole_0(X5,k4_xboole_0(X5,X4)),X4)) ) | (~spl3_6 | ~spl3_48)),
% 0.21/0.45    inference(superposition,[],[f59,f467])).
% 0.21/0.45  fof(f59,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) ) | ~spl3_6),
% 0.21/0.45    inference(avatar_component_clause,[],[f58])).
% 0.21/0.46  fof(f989,plain,(
% 0.21/0.46    spl3_62 | ~spl3_4 | ~spl3_17 | ~spl3_26 | ~spl3_42 | ~spl3_48),
% 0.21/0.46    inference(avatar_split_clause,[],[f768,f466,f416,f214,f140,f50,f986])).
% 0.21/0.46  fof(f416,plain,(
% 0.21/0.46    spl3_42 <=> k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(k1_xboole_0,k2_xboole_0(sK1,sK2))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).
% 0.21/0.46  fof(f768,plain,(
% 0.21/0.46    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | (~spl3_4 | ~spl3_17 | ~spl3_26 | ~spl3_42 | ~spl3_48)),
% 0.21/0.46    inference(backward_demodulation,[],[f418,f722])).
% 0.21/0.46  fof(f418,plain,(
% 0.21/0.46    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(k1_xboole_0,k2_xboole_0(sK1,sK2)) | ~spl3_42),
% 0.21/0.46    inference(avatar_component_clause,[],[f416])).
% 0.21/0.46  fof(f468,plain,(
% 0.21/0.46    spl3_48),
% 0.21/0.46    inference(avatar_split_clause,[],[f32,f466])).
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.21/0.46    inference(definition_unfolding,[],[f24,f26,f26])).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f9])).
% 0.21/0.46  fof(f9,axiom,(
% 0.21/0.46    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.46  fof(f431,plain,(
% 0.21/0.46    spl3_44),
% 0.21/0.46    inference(avatar_split_clause,[],[f30,f429])).
% 0.21/0.46  fof(f30,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f8])).
% 0.21/0.46  fof(f8,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.21/0.46  fof(f419,plain,(
% 0.21/0.46    spl3_42 | ~spl3_12 | ~spl3_14 | ~spl3_16),
% 0.21/0.46    inference(avatar_split_clause,[],[f138,f128,f104,f95,f416])).
% 0.21/0.46  fof(f95,plain,(
% 0.21/0.46    spl3_12 <=> ! [X1,X0] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.46  fof(f104,plain,(
% 0.21/0.46    spl3_14 <=> k2_xboole_0(sK1,sK2) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.46  fof(f138,plain,(
% 0.21/0.46    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(k1_xboole_0,k2_xboole_0(sK1,sK2)) | (~spl3_12 | ~spl3_14 | ~spl3_16)),
% 0.21/0.46    inference(backward_demodulation,[],[f111,f134])).
% 0.21/0.46  fof(f134,plain,(
% 0.21/0.46    ( ! [X0] : (k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X0)) ) | (~spl3_12 | ~spl3_16)),
% 0.21/0.46    inference(superposition,[],[f96,f129])).
% 0.21/0.46  fof(f96,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)) ) | ~spl3_12),
% 0.21/0.46    inference(avatar_component_clause,[],[f95])).
% 0.21/0.46  fof(f111,plain,(
% 0.21/0.46    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(k2_xboole_0(sK1,sK2),k2_xboole_0(sK1,sK2)) | (~spl3_12 | ~spl3_14)),
% 0.21/0.46    inference(superposition,[],[f96,f106])).
% 0.21/0.46  fof(f106,plain,(
% 0.21/0.46    k2_xboole_0(sK1,sK2) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | ~spl3_14),
% 0.21/0.46    inference(avatar_component_clause,[],[f104])).
% 0.21/0.46  fof(f319,plain,(
% 0.21/0.46    spl3_34 | ~spl3_1 | ~spl3_23),
% 0.21/0.46    inference(avatar_split_clause,[],[f314,f188,f35,f316])).
% 0.21/0.46  fof(f35,plain,(
% 0.21/0.46    spl3_1 <=> r1_xboole_0(sK0,sK2)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.46  fof(f188,plain,(
% 0.21/0.46    spl3_23 <=> ! [X1,X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.21/0.46  fof(f314,plain,(
% 0.21/0.46    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | (~spl3_1 | ~spl3_23)),
% 0.21/0.46    inference(resolution,[],[f189,f37])).
% 0.21/0.46  fof(f37,plain,(
% 0.21/0.46    r1_xboole_0(sK0,sK2) | ~spl3_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f35])).
% 0.21/0.46  fof(f189,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) | ~spl3_23),
% 0.21/0.46    inference(avatar_component_clause,[],[f188])).
% 0.21/0.46  fof(f216,plain,(
% 0.21/0.46    spl3_26 | ~spl3_15 | ~spl3_24),
% 0.21/0.46    inference(avatar_split_clause,[],[f208,f195,f118,f214])).
% 0.21/0.46  fof(f118,plain,(
% 0.21/0.46    spl3_15 <=> ! [X2] : k2_xboole_0(X2,k1_xboole_0) = X2),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.46  fof(f195,plain,(
% 0.21/0.46    spl3_24 <=> ! [X1,X0] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = X0),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.21/0.46  fof(f208,plain,(
% 0.21/0.46    ( ! [X6] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X6))) ) | (~spl3_15 | ~spl3_24)),
% 0.21/0.46    inference(superposition,[],[f196,f119])).
% 0.21/0.46  fof(f119,plain,(
% 0.21/0.46    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = X2) ) | ~spl3_15),
% 0.21/0.46    inference(avatar_component_clause,[],[f118])).
% 0.21/0.46  fof(f196,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = X0) ) | ~spl3_24),
% 0.21/0.46    inference(avatar_component_clause,[],[f195])).
% 0.21/0.46  fof(f201,plain,(
% 0.21/0.46    spl3_25 | ~spl3_5 | ~spl3_12),
% 0.21/0.46    inference(avatar_split_clause,[],[f108,f95,f54,f199])).
% 0.21/0.46  fof(f108,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1)) ) | (~spl3_5 | ~spl3_12)),
% 0.21/0.46    inference(superposition,[],[f96,f55])).
% 0.21/0.46  fof(f197,plain,(
% 0.21/0.46    spl3_24 | ~spl3_6 | ~spl3_9),
% 0.21/0.46    inference(avatar_split_clause,[],[f77,f73,f58,f195])).
% 0.21/0.46  fof(f77,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = X0) ) | (~spl3_6 | ~spl3_9)),
% 0.21/0.46    inference(resolution,[],[f74,f59])).
% 0.21/0.46  fof(f190,plain,(
% 0.21/0.46    spl3_23),
% 0.21/0.46    inference(avatar_split_clause,[],[f33,f188])).
% 0.21/0.46  fof(f33,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.46    inference(definition_unfolding,[],[f29,f26])).
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f16])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f12])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ! [X0,X1] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.46    inference(unused_predicate_definition_removal,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.46  fof(f142,plain,(
% 0.21/0.46    spl3_17 | ~spl3_12 | ~spl3_16),
% 0.21/0.46    inference(avatar_split_clause,[],[f134,f128,f95,f140])).
% 0.21/0.46  fof(f130,plain,(
% 0.21/0.46    spl3_16 | ~spl3_5 | ~spl3_15),
% 0.21/0.46    inference(avatar_split_clause,[],[f121,f118,f54,f128])).
% 0.21/0.46  fof(f121,plain,(
% 0.21/0.46    ( ! [X1] : (k2_xboole_0(k1_xboole_0,X1) = X1) ) | (~spl3_5 | ~spl3_15)),
% 0.21/0.46    inference(superposition,[],[f119,f55])).
% 0.21/0.46  fof(f120,plain,(
% 0.21/0.46    spl3_15 | ~spl3_4 | ~spl3_12),
% 0.21/0.46    inference(avatar_split_clause,[],[f115,f95,f50,f118])).
% 0.21/0.46  fof(f115,plain,(
% 0.21/0.46    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = X2) ) | (~spl3_4 | ~spl3_12)),
% 0.21/0.46    inference(forward_demodulation,[],[f112,f51])).
% 0.21/0.46  fof(f112,plain,(
% 0.21/0.46    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = k4_xboole_0(X2,k1_xboole_0)) ) | (~spl3_4 | ~spl3_12)),
% 0.21/0.46    inference(superposition,[],[f96,f51])).
% 0.21/0.46  fof(f107,plain,(
% 0.21/0.46    spl3_14 | ~spl3_3 | ~spl3_9),
% 0.21/0.46    inference(avatar_split_clause,[],[f76,f73,f45,f104])).
% 0.21/0.46  fof(f45,plain,(
% 0.21/0.46    spl3_3 <=> r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.46  fof(f76,plain,(
% 0.21/0.46    k2_xboole_0(sK1,sK2) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | (~spl3_3 | ~spl3_9)),
% 0.21/0.46    inference(resolution,[],[f74,f47])).
% 0.21/0.46  fof(f47,plain,(
% 0.21/0.46    r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | ~spl3_3),
% 0.21/0.46    inference(avatar_component_clause,[],[f45])).
% 0.21/0.46  fof(f97,plain,(
% 0.21/0.46    spl3_12),
% 0.21/0.46    inference(avatar_split_clause,[],[f27,f95])).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f7])).
% 0.21/0.46  fof(f7,axiom,(
% 0.21/0.46    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 0.21/0.46  fof(f75,plain,(
% 0.21/0.46    spl3_9),
% 0.21/0.46    inference(avatar_split_clause,[],[f28,f73])).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f15])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.46  fof(f60,plain,(
% 0.21/0.46    spl3_6),
% 0.21/0.46    inference(avatar_split_clause,[],[f31,f58])).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 0.21/0.46    inference(definition_unfolding,[],[f23,f26])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,axiom,(
% 0.21/0.46    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.21/0.46  fof(f56,plain,(
% 0.21/0.46    spl3_5),
% 0.21/0.46    inference(avatar_split_clause,[],[f25,f54])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.46  fof(f52,plain,(
% 0.21/0.46    spl3_4),
% 0.21/0.46    inference(avatar_split_clause,[],[f22,f50])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.46    inference(cnf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,axiom,(
% 0.21/0.46    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.46  fof(f48,plain,(
% 0.21/0.46    spl3_3),
% 0.21/0.46    inference(avatar_split_clause,[],[f19,f45])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 0.21/0.46    inference(cnf_transformation,[],[f18])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    ~r1_tarski(sK0,sK1) & r1_xboole_0(sK0,sK2) & r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f17])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => (~r1_tarski(sK0,sK1) & r1_xboole_0(sK0,sK2) & r1_tarski(sK0,k2_xboole_0(sK1,sK2)))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.21/0.46    inference(flattening,[],[f13])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & (r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 0.21/0.46    inference(ennf_transformation,[],[f11])).
% 0.21/0.46  fof(f11,negated_conjecture,(
% 0.21/0.46    ~! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 0.21/0.46    inference(negated_conjecture,[],[f10])).
% 0.21/0.46  fof(f10,conjecture,(
% 0.21/0.46    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).
% 0.21/0.46  fof(f43,plain,(
% 0.21/0.46    ~spl3_2),
% 0.21/0.46    inference(avatar_split_clause,[],[f21,f40])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    ~r1_tarski(sK0,sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f18])).
% 0.21/0.46  fof(f38,plain,(
% 0.21/0.46    spl3_1),
% 0.21/0.46    inference(avatar_split_clause,[],[f20,f35])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    r1_xboole_0(sK0,sK2)),
% 0.21/0.46    inference(cnf_transformation,[],[f18])).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (31761)------------------------------
% 0.21/0.46  % (31761)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (31761)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (31761)Memory used [KB]: 7291
% 0.21/0.46  % (31761)Time elapsed: 0.063 s
% 0.21/0.46  % (31761)------------------------------
% 0.21/0.46  % (31761)------------------------------
% 0.21/0.46  % (31753)Success in time 0.106 s
%------------------------------------------------------------------------------
