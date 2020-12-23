%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:44 EST 2020

% Result     : Theorem 2.75s
% Output     : Refutation 2.75s
% Verified   : 
% Statistics : Number of formulae       :  176 ( 312 expanded)
%              Number of leaves         :   47 ( 156 expanded)
%              Depth                    :    7
%              Number of atoms          :  455 ( 801 expanded)
%              Number of equality atoms :   74 ( 156 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12392,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f40,f45,f50,f54,f58,f62,f66,f74,f78,f82,f86,f90,f94,f99,f131,f147,f151,f155,f185,f201,f472,f505,f521,f793,f824,f869,f1446,f1473,f5558,f6099,f6145,f6842,f7766,f7845,f7948,f12327,f12391])).

fof(f12391,plain,
    ( ~ spl3_23
    | spl3_27
    | ~ spl3_830
    | ~ spl3_1251 ),
    inference(avatar_contradiction_clause,[],[f12390])).

fof(f12390,plain,
    ( $false
    | ~ spl3_23
    | spl3_27
    | ~ spl3_830
    | ~ spl3_1251 ),
    inference(subsumption_resolution,[],[f12389,f184])).

fof(f184,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | spl3_27 ),
    inference(avatar_component_clause,[],[f182])).

fof(f182,plain,
    ( spl3_27
  <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f12389,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl3_23
    | ~ spl3_830
    | ~ spl3_1251 ),
    inference(forward_demodulation,[],[f12340,f150])).

fof(f150,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl3_23
  <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f12340,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)),sK0)
    | ~ spl3_830
    | ~ spl3_1251 ),
    inference(resolution,[],[f12326,f7947])).

fof(f7947,plain,
    ( ! [X2] :
        ( ~ r1_xboole_0(sK1,X2)
        | k4_xboole_0(X2,sK0) = X2 )
    | ~ spl3_830 ),
    inference(avatar_component_clause,[],[f7946])).

fof(f7946,plain,
    ( spl3_830
  <=> ! [X2] :
        ( k4_xboole_0(X2,sK0) = X2
        | ~ r1_xboole_0(sK1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_830])])).

fof(f12326,plain,
    ( ! [X57] : r1_xboole_0(X57,k4_xboole_0(sK0,k4_xboole_0(X57,sK2)))
    | ~ spl3_1251 ),
    inference(avatar_component_clause,[],[f12325])).

fof(f12325,plain,
    ( spl3_1251
  <=> ! [X57] : r1_xboole_0(X57,k4_xboole_0(sK0,k4_xboole_0(X57,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1251])])).

fof(f12327,plain,
    ( spl3_1251
    | ~ spl3_99
    | ~ spl3_759 ),
    inference(avatar_split_clause,[],[f12228,f6840,f822,f12325])).

fof(f822,plain,
    ( spl3_99
  <=> ! [X17] : k4_xboole_0(sK0,X17) = k4_xboole_0(sK0,k2_xboole_0(sK2,X17)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_99])])).

fof(f6840,plain,
    ( spl3_759
  <=> ! [X20,X19,X21] : r1_xboole_0(X19,k4_xboole_0(X21,k2_xboole_0(X20,k4_xboole_0(X19,X20)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_759])])).

fof(f12228,plain,
    ( ! [X57] : r1_xboole_0(X57,k4_xboole_0(sK0,k4_xboole_0(X57,sK2)))
    | ~ spl3_99
    | ~ spl3_759 ),
    inference(superposition,[],[f6841,f823])).

fof(f823,plain,
    ( ! [X17] : k4_xboole_0(sK0,X17) = k4_xboole_0(sK0,k2_xboole_0(sK2,X17))
    | ~ spl3_99 ),
    inference(avatar_component_clause,[],[f822])).

fof(f6841,plain,
    ( ! [X21,X19,X20] : r1_xboole_0(X19,k4_xboole_0(X21,k2_xboole_0(X20,k4_xboole_0(X19,X20))))
    | ~ spl3_759 ),
    inference(avatar_component_clause,[],[f6840])).

fof(f7948,plain,
    ( spl3_830
    | ~ spl3_93
    | ~ spl3_714
    | ~ spl3_823 ),
    inference(avatar_split_clause,[],[f7944,f7843,f6143,f791,f7946])).

fof(f791,plain,
    ( spl3_93
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_93])])).

fof(f6143,plain,
    ( spl3_714
  <=> ! [X3,X4] :
        ( k4_xboole_0(X4,X3) = X4
        | ~ r1_xboole_0(X3,X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_714])])).

fof(f7843,plain,
    ( spl3_823
  <=> ! [X7] :
        ( r1_xboole_0(k2_xboole_0(k1_xboole_0,sK0),X7)
        | ~ r1_xboole_0(sK1,X7) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_823])])).

fof(f7944,plain,
    ( ! [X2] :
        ( k4_xboole_0(X2,sK0) = X2
        | ~ r1_xboole_0(sK1,X2) )
    | ~ spl3_93
    | ~ spl3_714
    | ~ spl3_823 ),
    inference(forward_demodulation,[],[f7937,f792])).

fof(f792,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1))
    | ~ spl3_93 ),
    inference(avatar_component_clause,[],[f791])).

fof(f7937,plain,
    ( ! [X2] :
        ( ~ r1_xboole_0(sK1,X2)
        | k4_xboole_0(X2,k2_xboole_0(k1_xboole_0,sK0)) = X2 )
    | ~ spl3_714
    | ~ spl3_823 ),
    inference(resolution,[],[f7844,f6144])).

fof(f6144,plain,
    ( ! [X4,X3] :
        ( ~ r1_xboole_0(X3,X4)
        | k4_xboole_0(X4,X3) = X4 )
    | ~ spl3_714 ),
    inference(avatar_component_clause,[],[f6143])).

fof(f7844,plain,
    ( ! [X7] :
        ( r1_xboole_0(k2_xboole_0(k1_xboole_0,sK0),X7)
        | ~ r1_xboole_0(sK1,X7) )
    | ~ spl3_823 ),
    inference(avatar_component_clause,[],[f7843])).

fof(f7845,plain,
    ( spl3_823
    | ~ spl3_29
    | ~ spl3_816 ),
    inference(avatar_split_clause,[],[f7832,f7753,f199,f7843])).

fof(f199,plain,
    ( spl3_29
  <=> ! [X3,X2,X4] :
        ( ~ r1_xboole_0(X2,X3)
        | r1_xboole_0(X4,X3)
        | k1_xboole_0 != k4_xboole_0(X4,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f7753,plain,
    ( spl3_816
  <=> k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_xboole_0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_816])])).

fof(f7832,plain,
    ( ! [X7] :
        ( r1_xboole_0(k2_xboole_0(k1_xboole_0,sK0),X7)
        | ~ r1_xboole_0(sK1,X7) )
    | ~ spl3_29
    | ~ spl3_816 ),
    inference(trivial_inequality_removal,[],[f7809])).

fof(f7809,plain,
    ( ! [X7] :
        ( k1_xboole_0 != k1_xboole_0
        | r1_xboole_0(k2_xboole_0(k1_xboole_0,sK0),X7)
        | ~ r1_xboole_0(sK1,X7) )
    | ~ spl3_29
    | ~ spl3_816 ),
    inference(superposition,[],[f200,f7755])).

fof(f7755,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_xboole_0,sK0),sK1)
    | ~ spl3_816 ),
    inference(avatar_component_clause,[],[f7753])).

fof(f200,plain,
    ( ! [X4,X2,X3] :
        ( k1_xboole_0 != k4_xboole_0(X4,X2)
        | r1_xboole_0(X4,X3)
        | ~ r1_xboole_0(X2,X3) )
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f199])).

fof(f7766,plain,
    ( spl3_816
    | ~ spl3_71
    | ~ spl3_166 ),
    inference(avatar_split_clause,[],[f7719,f1436,f519,f7753])).

fof(f519,plain,
    ( spl3_71
  <=> ! [X2] : k4_xboole_0(X2,sK1) = k4_xboole_0(k4_xboole_0(X2,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_71])])).

fof(f1436,plain,
    ( spl3_166
  <=> ! [X5,X6] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k2_xboole_0(k1_xboole_0,X5),X6),X5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_166])])).

fof(f7719,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_xboole_0,sK0),sK1)
    | ~ spl3_71
    | ~ spl3_166 ),
    inference(superposition,[],[f1437,f520])).

fof(f520,plain,
    ( ! [X2] : k4_xboole_0(X2,sK1) = k4_xboole_0(k4_xboole_0(X2,sK1),sK0)
    | ~ spl3_71 ),
    inference(avatar_component_clause,[],[f519])).

fof(f1437,plain,
    ( ! [X6,X5] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k2_xboole_0(k1_xboole_0,X5),X6),X5)
    | ~ spl3_166 ),
    inference(avatar_component_clause,[],[f1436])).

fof(f6842,plain,
    ( spl3_759
    | ~ spl3_4
    | ~ spl3_13
    | ~ spl3_109 ),
    inference(avatar_split_clause,[],[f6838,f863,f88,f52,f6840])).

fof(f52,plain,
    ( spl3_4
  <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f88,plain,
    ( spl3_13
  <=> ! [X1,X0,X2] :
        ( r1_xboole_0(X1,k4_xboole_0(X0,X2))
        | ~ r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f863,plain,
    ( spl3_109
  <=> ! [X9,X10] : k1_xboole_0 = k4_xboole_0(X9,k2_xboole_0(X10,k4_xboole_0(X9,X10))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_109])])).

fof(f6838,plain,
    ( ! [X21,X19,X20] : r1_xboole_0(X19,k4_xboole_0(X21,k2_xboole_0(X20,k4_xboole_0(X19,X20))))
    | ~ spl3_4
    | ~ spl3_13
    | ~ spl3_109 ),
    inference(subsumption_resolution,[],[f6717,f53])).

fof(f53,plain,
    ( ! [X0] : r1_xboole_0(X0,k1_xboole_0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f52])).

fof(f6717,plain,
    ( ! [X21,X19,X20] :
        ( ~ r1_xboole_0(X21,k1_xboole_0)
        | r1_xboole_0(X19,k4_xboole_0(X21,k2_xboole_0(X20,k4_xboole_0(X19,X20)))) )
    | ~ spl3_13
    | ~ spl3_109 ),
    inference(superposition,[],[f89,f864])).

fof(f864,plain,
    ( ! [X10,X9] : k1_xboole_0 = k4_xboole_0(X9,k2_xboole_0(X10,k4_xboole_0(X9,X10)))
    | ~ spl3_109 ),
    inference(avatar_component_clause,[],[f863])).

fof(f89,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(X0,k4_xboole_0(X1,X2))
        | r1_xboole_0(X1,k4_xboole_0(X0,X2)) )
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f88])).

fof(f6145,plain,
    ( spl3_714
    | ~ spl3_9
    | ~ spl3_93
    | ~ spl3_708 ),
    inference(avatar_split_clause,[],[f6141,f6097,f791,f72,f6143])).

fof(f72,plain,
    ( spl3_9
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f6097,plain,
    ( spl3_708
  <=> ! [X9,X10] :
        ( ~ r1_xboole_0(X9,X10)
        | r1_xboole_0(X10,k2_xboole_0(k1_xboole_0,X9)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_708])])).

fof(f6141,plain,
    ( ! [X4,X3] :
        ( k4_xboole_0(X4,X3) = X4
        | ~ r1_xboole_0(X3,X4) )
    | ~ spl3_9
    | ~ spl3_93
    | ~ spl3_708 ),
    inference(forward_demodulation,[],[f6130,f792])).

fof(f6130,plain,
    ( ! [X4,X3] :
        ( ~ r1_xboole_0(X3,X4)
        | k4_xboole_0(X4,k2_xboole_0(k1_xboole_0,X3)) = X4 )
    | ~ spl3_9
    | ~ spl3_708 ),
    inference(resolution,[],[f6098,f73])).

fof(f73,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) = X0 )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f72])).

fof(f6098,plain,
    ( ! [X10,X9] :
        ( r1_xboole_0(X10,k2_xboole_0(k1_xboole_0,X9))
        | ~ r1_xboole_0(X9,X10) )
    | ~ spl3_708 ),
    inference(avatar_component_clause,[],[f6097])).

fof(f6099,plain,
    ( spl3_708
    | ~ spl3_7
    | ~ spl3_647 ),
    inference(avatar_split_clause,[],[f6089,f5556,f64,f6097])).

fof(f64,plain,
    ( spl3_7
  <=> ! [X1,X0] :
        ( r1_xboole_0(X1,X0)
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f5556,plain,
    ( spl3_647
  <=> ! [X42,X43] :
        ( r1_xboole_0(k2_xboole_0(k1_xboole_0,X42),X43)
        | ~ r1_xboole_0(X42,X43) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_647])])).

fof(f6089,plain,
    ( ! [X10,X9] :
        ( ~ r1_xboole_0(X9,X10)
        | r1_xboole_0(X10,k2_xboole_0(k1_xboole_0,X9)) )
    | ~ spl3_7
    | ~ spl3_647 ),
    inference(resolution,[],[f5557,f65])).

fof(f65,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X1,X0) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f64])).

fof(f5557,plain,
    ( ! [X43,X42] :
        ( r1_xboole_0(k2_xboole_0(k1_xboole_0,X42),X43)
        | ~ r1_xboole_0(X42,X43) )
    | ~ spl3_647 ),
    inference(avatar_component_clause,[],[f5556])).

fof(f5558,plain,
    ( spl3_647
    | ~ spl3_29
    | ~ spl3_165 ),
    inference(avatar_split_clause,[],[f5504,f1432,f199,f5556])).

fof(f1432,plain,
    ( spl3_165
  <=> ! [X4] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_xboole_0,X4),X4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_165])])).

fof(f5504,plain,
    ( ! [X43,X42] :
        ( r1_xboole_0(k2_xboole_0(k1_xboole_0,X42),X43)
        | ~ r1_xboole_0(X42,X43) )
    | ~ spl3_29
    | ~ spl3_165 ),
    inference(trivial_inequality_removal,[],[f5484])).

fof(f5484,plain,
    ( ! [X43,X42] :
        ( k1_xboole_0 != k1_xboole_0
        | r1_xboole_0(k2_xboole_0(k1_xboole_0,X42),X43)
        | ~ r1_xboole_0(X42,X43) )
    | ~ spl3_29
    | ~ spl3_165 ),
    inference(superposition,[],[f200,f1433])).

fof(f1433,plain,
    ( ! [X4] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_xboole_0,X4),X4)
    | ~ spl3_165 ),
    inference(avatar_component_clause,[],[f1432])).

fof(f1473,plain,
    ( spl3_166
    | ~ spl3_23
    | ~ spl3_93 ),
    inference(avatar_split_clause,[],[f1411,f791,f149,f1436])).

fof(f1411,plain,
    ( ! [X45,X46] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k2_xboole_0(k1_xboole_0,X45),X46),X45)
    | ~ spl3_23
    | ~ spl3_93 ),
    inference(superposition,[],[f150,f792])).

fof(f1446,plain,
    ( spl3_165
    | ~ spl3_24
    | ~ spl3_93 ),
    inference(avatar_split_clause,[],[f1399,f791,f153,f1432])).

fof(f153,plain,
    ( spl3_24
  <=> ! [X2] : k1_xboole_0 = k4_xboole_0(X2,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f1399,plain,
    ( ! [X16] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_xboole_0,X16),X16)
    | ~ spl3_24
    | ~ spl3_93 ),
    inference(superposition,[],[f154,f792])).

fof(f154,plain,
    ( ! [X2] : k1_xboole_0 = k4_xboole_0(X2,X2)
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f153])).

fof(f869,plain,
    ( spl3_109
    | ~ spl3_12
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f773,f153,f84,f863])).

fof(f84,plain,
    ( spl3_12
  <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f773,plain,
    ( ! [X4,X5] : k1_xboole_0 = k4_xboole_0(X4,k2_xboole_0(X5,k4_xboole_0(X4,X5)))
    | ~ spl3_12
    | ~ spl3_24 ),
    inference(superposition,[],[f154,f85])).

fof(f85,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f84])).

fof(f824,plain,
    ( spl3_99
    | ~ spl3_12
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f759,f128,f84,f822])).

fof(f128,plain,
    ( spl3_20
  <=> sK0 = k4_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f759,plain,
    ( ! [X17] : k4_xboole_0(sK0,X17) = k4_xboole_0(sK0,k2_xboole_0(sK2,X17))
    | ~ spl3_12
    | ~ spl3_20 ),
    inference(superposition,[],[f85,f130])).

fof(f130,plain,
    ( sK0 = k4_xboole_0(sK0,sK2)
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f128])).

fof(f793,plain,
    ( spl3_93
    | ~ spl3_5
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f752,f84,f56,f791])).

fof(f56,plain,
    ( spl3_5
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f752,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1))
    | ~ spl3_5
    | ~ spl3_12 ),
    inference(superposition,[],[f85,f57])).

fof(f57,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f56])).

fof(f521,plain,
    ( spl3_71
    | ~ spl3_9
    | ~ spl3_69 ),
    inference(avatar_split_clause,[],[f507,f503,f72,f519])).

fof(f503,plain,
    ( spl3_69
  <=> ! [X4] : r1_xboole_0(k4_xboole_0(X4,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_69])])).

fof(f507,plain,
    ( ! [X2] : k4_xboole_0(X2,sK1) = k4_xboole_0(k4_xboole_0(X2,sK1),sK0)
    | ~ spl3_9
    | ~ spl3_69 ),
    inference(resolution,[],[f504,f73])).

fof(f504,plain,
    ( ! [X4] : r1_xboole_0(k4_xboole_0(X4,sK1),sK0)
    | ~ spl3_69 ),
    inference(avatar_component_clause,[],[f503])).

fof(f505,plain,
    ( spl3_69
    | ~ spl3_7
    | ~ spl3_63 ),
    inference(avatar_split_clause,[],[f488,f470,f64,f503])).

fof(f470,plain,
    ( spl3_63
  <=> ! [X14] : r1_xboole_0(sK0,k4_xboole_0(X14,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_63])])).

fof(f488,plain,
    ( ! [X4] : r1_xboole_0(k4_xboole_0(X4,sK1),sK0)
    | ~ spl3_7
    | ~ spl3_63 ),
    inference(resolution,[],[f471,f65])).

fof(f471,plain,
    ( ! [X14] : r1_xboole_0(sK0,k4_xboole_0(X14,sK1))
    | ~ spl3_63 ),
    inference(avatar_component_clause,[],[f470])).

fof(f472,plain,
    ( spl3_63
    | ~ spl3_4
    | ~ spl3_13
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f468,f144,f88,f52,f470])).

fof(f144,plain,
    ( spl3_22
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f468,plain,
    ( ! [X14] : r1_xboole_0(sK0,k4_xboole_0(X14,sK1))
    | ~ spl3_4
    | ~ spl3_13
    | ~ spl3_22 ),
    inference(subsumption_resolution,[],[f424,f53])).

fof(f424,plain,
    ( ! [X14] :
        ( ~ r1_xboole_0(X14,k1_xboole_0)
        | r1_xboole_0(sK0,k4_xboole_0(X14,sK1)) )
    | ~ spl3_13
    | ~ spl3_22 ),
    inference(superposition,[],[f89,f146])).

fof(f146,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f144])).

fof(f201,plain,
    ( spl3_29
    | ~ spl3_11
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f193,f92,f80,f199])).

fof(f80,plain,
    ( spl3_11
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f92,plain,
    ( spl3_14
  <=> ! [X1,X0,X2] :
        ( r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X1,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f193,plain,
    ( ! [X4,X2,X3] :
        ( ~ r1_xboole_0(X2,X3)
        | r1_xboole_0(X4,X3)
        | k1_xboole_0 != k4_xboole_0(X4,X2) )
    | ~ spl3_11
    | ~ spl3_14 ),
    inference(resolution,[],[f93,f81])).

fof(f81,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f80])).

fof(f93,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ r1_xboole_0(X1,X2)
        | r1_xboole_0(X0,X2) )
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f92])).

fof(f185,plain,
    ( ~ spl3_27
    | spl3_1
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f179,f80,f37,f182])).

fof(f37,plain,
    ( spl3_1
  <=> r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f179,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | spl3_1
    | ~ spl3_11 ),
    inference(resolution,[],[f81,f39])).

fof(f39,plain,
    ( ~ r1_tarski(sK0,k4_xboole_0(sK1,sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f37])).

fof(f155,plain,
    ( spl3_24
    | ~ spl3_10
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f142,f97,f76,f153])).

fof(f76,plain,
    ( spl3_10
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f97,plain,
    ( spl3_15
  <=> ! [X0] : r1_tarski(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f142,plain,
    ( ! [X2] : k1_xboole_0 = k4_xboole_0(X2,X2)
    | ~ spl3_10
    | ~ spl3_15 ),
    inference(resolution,[],[f77,f98])).

fof(f98,plain,
    ( ! [X0] : r1_tarski(X0,X0)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f97])).

fof(f77,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) = k1_xboole_0 )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f76])).

fof(f151,plain,
    ( spl3_23
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f141,f76,f60,f149])).

fof(f60,plain,
    ( spl3_6
  <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f141,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(resolution,[],[f77,f61])).

fof(f61,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f60])).

fof(f147,plain,
    ( spl3_22
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f140,f76,f47,f144])).

fof(f47,plain,
    ( spl3_3
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f140,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(resolution,[],[f77,f49])).

fof(f49,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f47])).

fof(f131,plain,
    ( spl3_20
    | ~ spl3_2
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f121,f72,f42,f128])).

fof(f42,plain,
    ( spl3_2
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f121,plain,
    ( sK0 = k4_xboole_0(sK0,sK2)
    | ~ spl3_2
    | ~ spl3_9 ),
    inference(resolution,[],[f73,f44])).

fof(f44,plain,
    ( r1_xboole_0(sK0,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f42])).

fof(f99,plain,
    ( spl3_15
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f95,f60,f56,f97])).

fof(f95,plain,
    ( ! [X0] : r1_tarski(X0,X0)
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(superposition,[],[f61,f57])).

fof(f94,plain,(
    spl3_14 ),
    inference(avatar_split_clause,[],[f35,f92])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f90,plain,(
    spl3_13 ),
    inference(avatar_split_clause,[],[f34,f88])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X1,k4_xboole_0(X0,X2))
      | ~ r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X1,k4_xboole_0(X0,X2))
      | ~ r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
     => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_xboole_1)).

fof(f86,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f33,f84])).

fof(f33,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f82,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f31,f80])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f78,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f32,f76])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f74,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f29,f72])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f66,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f28,f64])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f62,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f27,f60])).

fof(f27,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f58,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f26,f56])).

fof(f26,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f54,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f25,f52])).

fof(f25,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f50,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f22,f47])).

fof(f22,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ~ r1_tarski(sK0,k4_xboole_0(sK1,sK2))
    & r1_xboole_0(sK0,sK2)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
        & r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(sK0,k4_xboole_0(sK1,sK2))
      & r1_xboole_0(sK0,sK2)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) )
       => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

fof(f45,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f23,f42])).

fof(f23,plain,(
    r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f40,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f24,f37])).

fof(f24,plain,(
    ~ r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:49:52 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.21/0.43  % (13995)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.21/0.45  % (13991)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.21/0.45  % (13989)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.21/0.45  % (13997)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.21/0.45  % (13999)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.21/0.46  % (13996)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.21/0.46  % (13992)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.21/0.47  % (13993)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.47  % (13994)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.47  % (13988)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.21/0.48  % (13990)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.21/0.49  % (13998)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 2.75/0.72  % (13993)Refutation found. Thanks to Tanya!
% 2.75/0.72  % SZS status Theorem for theBenchmark
% 2.75/0.72  % SZS output start Proof for theBenchmark
% 2.75/0.72  fof(f12392,plain,(
% 2.75/0.72    $false),
% 2.75/0.72    inference(avatar_sat_refutation,[],[f40,f45,f50,f54,f58,f62,f66,f74,f78,f82,f86,f90,f94,f99,f131,f147,f151,f155,f185,f201,f472,f505,f521,f793,f824,f869,f1446,f1473,f5558,f6099,f6145,f6842,f7766,f7845,f7948,f12327,f12391])).
% 2.75/0.72  fof(f12391,plain,(
% 2.75/0.72    ~spl3_23 | spl3_27 | ~spl3_830 | ~spl3_1251),
% 2.75/0.72    inference(avatar_contradiction_clause,[],[f12390])).
% 2.75/0.72  fof(f12390,plain,(
% 2.75/0.72    $false | (~spl3_23 | spl3_27 | ~spl3_830 | ~spl3_1251)),
% 2.75/0.72    inference(subsumption_resolution,[],[f12389,f184])).
% 2.75/0.72  fof(f184,plain,(
% 2.75/0.72    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | spl3_27),
% 2.75/0.72    inference(avatar_component_clause,[],[f182])).
% 2.75/0.72  fof(f182,plain,(
% 2.75/0.72    spl3_27 <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 2.75/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 2.75/0.72  fof(f12389,plain,(
% 2.75/0.72    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | (~spl3_23 | ~spl3_830 | ~spl3_1251)),
% 2.75/0.72    inference(forward_demodulation,[],[f12340,f150])).
% 2.75/0.72  fof(f150,plain,(
% 2.75/0.72    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)) ) | ~spl3_23),
% 2.75/0.72    inference(avatar_component_clause,[],[f149])).
% 2.75/0.72  fof(f149,plain,(
% 2.75/0.72    spl3_23 <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)),
% 2.75/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 2.75/0.72  fof(f12340,plain,(
% 2.75/0.72    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)),sK0) | (~spl3_830 | ~spl3_1251)),
% 2.75/0.72    inference(resolution,[],[f12326,f7947])).
% 2.75/0.72  fof(f7947,plain,(
% 2.75/0.72    ( ! [X2] : (~r1_xboole_0(sK1,X2) | k4_xboole_0(X2,sK0) = X2) ) | ~spl3_830),
% 2.75/0.72    inference(avatar_component_clause,[],[f7946])).
% 2.75/0.72  fof(f7946,plain,(
% 2.75/0.72    spl3_830 <=> ! [X2] : (k4_xboole_0(X2,sK0) = X2 | ~r1_xboole_0(sK1,X2))),
% 2.75/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_830])])).
% 2.75/0.72  fof(f12326,plain,(
% 2.75/0.72    ( ! [X57] : (r1_xboole_0(X57,k4_xboole_0(sK0,k4_xboole_0(X57,sK2)))) ) | ~spl3_1251),
% 2.75/0.72    inference(avatar_component_clause,[],[f12325])).
% 2.75/0.72  fof(f12325,plain,(
% 2.75/0.72    spl3_1251 <=> ! [X57] : r1_xboole_0(X57,k4_xboole_0(sK0,k4_xboole_0(X57,sK2)))),
% 2.75/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_1251])])).
% 2.75/0.72  fof(f12327,plain,(
% 2.75/0.72    spl3_1251 | ~spl3_99 | ~spl3_759),
% 2.75/0.72    inference(avatar_split_clause,[],[f12228,f6840,f822,f12325])).
% 2.75/0.72  fof(f822,plain,(
% 2.75/0.72    spl3_99 <=> ! [X17] : k4_xboole_0(sK0,X17) = k4_xboole_0(sK0,k2_xboole_0(sK2,X17))),
% 2.75/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_99])])).
% 2.75/0.72  fof(f6840,plain,(
% 2.75/0.72    spl3_759 <=> ! [X20,X19,X21] : r1_xboole_0(X19,k4_xboole_0(X21,k2_xboole_0(X20,k4_xboole_0(X19,X20))))),
% 2.75/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_759])])).
% 2.75/0.72  fof(f12228,plain,(
% 2.75/0.72    ( ! [X57] : (r1_xboole_0(X57,k4_xboole_0(sK0,k4_xboole_0(X57,sK2)))) ) | (~spl3_99 | ~spl3_759)),
% 2.75/0.72    inference(superposition,[],[f6841,f823])).
% 2.75/0.72  fof(f823,plain,(
% 2.75/0.72    ( ! [X17] : (k4_xboole_0(sK0,X17) = k4_xboole_0(sK0,k2_xboole_0(sK2,X17))) ) | ~spl3_99),
% 2.75/0.72    inference(avatar_component_clause,[],[f822])).
% 2.75/0.72  fof(f6841,plain,(
% 2.75/0.72    ( ! [X21,X19,X20] : (r1_xboole_0(X19,k4_xboole_0(X21,k2_xboole_0(X20,k4_xboole_0(X19,X20))))) ) | ~spl3_759),
% 2.75/0.72    inference(avatar_component_clause,[],[f6840])).
% 2.75/0.72  fof(f7948,plain,(
% 2.75/0.72    spl3_830 | ~spl3_93 | ~spl3_714 | ~spl3_823),
% 2.75/0.72    inference(avatar_split_clause,[],[f7944,f7843,f6143,f791,f7946])).
% 2.75/0.72  fof(f791,plain,(
% 2.75/0.72    spl3_93 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1))),
% 2.75/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_93])])).
% 2.75/0.72  fof(f6143,plain,(
% 2.75/0.72    spl3_714 <=> ! [X3,X4] : (k4_xboole_0(X4,X3) = X4 | ~r1_xboole_0(X3,X4))),
% 2.75/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_714])])).
% 2.75/0.72  fof(f7843,plain,(
% 2.75/0.72    spl3_823 <=> ! [X7] : (r1_xboole_0(k2_xboole_0(k1_xboole_0,sK0),X7) | ~r1_xboole_0(sK1,X7))),
% 2.75/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_823])])).
% 2.75/0.72  fof(f7944,plain,(
% 2.75/0.72    ( ! [X2] : (k4_xboole_0(X2,sK0) = X2 | ~r1_xboole_0(sK1,X2)) ) | (~spl3_93 | ~spl3_714 | ~spl3_823)),
% 2.75/0.72    inference(forward_demodulation,[],[f7937,f792])).
% 2.75/0.72  fof(f792,plain,(
% 2.75/0.72    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1))) ) | ~spl3_93),
% 2.75/0.72    inference(avatar_component_clause,[],[f791])).
% 2.75/0.72  fof(f7937,plain,(
% 2.75/0.72    ( ! [X2] : (~r1_xboole_0(sK1,X2) | k4_xboole_0(X2,k2_xboole_0(k1_xboole_0,sK0)) = X2) ) | (~spl3_714 | ~spl3_823)),
% 2.75/0.72    inference(resolution,[],[f7844,f6144])).
% 2.75/0.72  fof(f6144,plain,(
% 2.75/0.72    ( ! [X4,X3] : (~r1_xboole_0(X3,X4) | k4_xboole_0(X4,X3) = X4) ) | ~spl3_714),
% 2.75/0.72    inference(avatar_component_clause,[],[f6143])).
% 2.75/0.72  fof(f7844,plain,(
% 2.75/0.72    ( ! [X7] : (r1_xboole_0(k2_xboole_0(k1_xboole_0,sK0),X7) | ~r1_xboole_0(sK1,X7)) ) | ~spl3_823),
% 2.75/0.72    inference(avatar_component_clause,[],[f7843])).
% 2.75/0.72  fof(f7845,plain,(
% 2.75/0.72    spl3_823 | ~spl3_29 | ~spl3_816),
% 2.75/0.72    inference(avatar_split_clause,[],[f7832,f7753,f199,f7843])).
% 2.75/0.72  fof(f199,plain,(
% 2.75/0.72    spl3_29 <=> ! [X3,X2,X4] : (~r1_xboole_0(X2,X3) | r1_xboole_0(X4,X3) | k1_xboole_0 != k4_xboole_0(X4,X2))),
% 2.75/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 2.75/0.72  fof(f7753,plain,(
% 2.75/0.72    spl3_816 <=> k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_xboole_0,sK0),sK1)),
% 2.75/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_816])])).
% 2.75/0.72  fof(f7832,plain,(
% 2.75/0.72    ( ! [X7] : (r1_xboole_0(k2_xboole_0(k1_xboole_0,sK0),X7) | ~r1_xboole_0(sK1,X7)) ) | (~spl3_29 | ~spl3_816)),
% 2.75/0.72    inference(trivial_inequality_removal,[],[f7809])).
% 2.75/0.72  fof(f7809,plain,(
% 2.75/0.72    ( ! [X7] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k2_xboole_0(k1_xboole_0,sK0),X7) | ~r1_xboole_0(sK1,X7)) ) | (~spl3_29 | ~spl3_816)),
% 2.75/0.72    inference(superposition,[],[f200,f7755])).
% 2.75/0.72  fof(f7755,plain,(
% 2.75/0.72    k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_xboole_0,sK0),sK1) | ~spl3_816),
% 2.75/0.72    inference(avatar_component_clause,[],[f7753])).
% 2.75/0.72  fof(f200,plain,(
% 2.75/0.72    ( ! [X4,X2,X3] : (k1_xboole_0 != k4_xboole_0(X4,X2) | r1_xboole_0(X4,X3) | ~r1_xboole_0(X2,X3)) ) | ~spl3_29),
% 2.75/0.72    inference(avatar_component_clause,[],[f199])).
% 2.75/0.72  fof(f7766,plain,(
% 2.75/0.72    spl3_816 | ~spl3_71 | ~spl3_166),
% 2.75/0.72    inference(avatar_split_clause,[],[f7719,f1436,f519,f7753])).
% 2.75/0.72  fof(f519,plain,(
% 2.75/0.72    spl3_71 <=> ! [X2] : k4_xboole_0(X2,sK1) = k4_xboole_0(k4_xboole_0(X2,sK1),sK0)),
% 2.75/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_71])])).
% 2.75/0.72  fof(f1436,plain,(
% 2.75/0.72    spl3_166 <=> ! [X5,X6] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k2_xboole_0(k1_xboole_0,X5),X6),X5)),
% 2.75/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_166])])).
% 2.75/0.72  fof(f7719,plain,(
% 2.75/0.72    k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_xboole_0,sK0),sK1) | (~spl3_71 | ~spl3_166)),
% 2.75/0.72    inference(superposition,[],[f1437,f520])).
% 2.75/0.72  fof(f520,plain,(
% 2.75/0.72    ( ! [X2] : (k4_xboole_0(X2,sK1) = k4_xboole_0(k4_xboole_0(X2,sK1),sK0)) ) | ~spl3_71),
% 2.75/0.72    inference(avatar_component_clause,[],[f519])).
% 2.75/0.72  fof(f1437,plain,(
% 2.75/0.72    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k2_xboole_0(k1_xboole_0,X5),X6),X5)) ) | ~spl3_166),
% 2.75/0.72    inference(avatar_component_clause,[],[f1436])).
% 2.75/0.72  fof(f6842,plain,(
% 2.75/0.72    spl3_759 | ~spl3_4 | ~spl3_13 | ~spl3_109),
% 2.75/0.72    inference(avatar_split_clause,[],[f6838,f863,f88,f52,f6840])).
% 2.75/0.72  fof(f52,plain,(
% 2.75/0.72    spl3_4 <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 2.75/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 2.75/0.72  fof(f88,plain,(
% 2.75/0.72    spl3_13 <=> ! [X1,X0,X2] : (r1_xboole_0(X1,k4_xboole_0(X0,X2)) | ~r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 2.75/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 2.75/0.72  fof(f863,plain,(
% 2.75/0.72    spl3_109 <=> ! [X9,X10] : k1_xboole_0 = k4_xboole_0(X9,k2_xboole_0(X10,k4_xboole_0(X9,X10)))),
% 2.75/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_109])])).
% 2.75/0.72  fof(f6838,plain,(
% 2.75/0.72    ( ! [X21,X19,X20] : (r1_xboole_0(X19,k4_xboole_0(X21,k2_xboole_0(X20,k4_xboole_0(X19,X20))))) ) | (~spl3_4 | ~spl3_13 | ~spl3_109)),
% 2.75/0.72    inference(subsumption_resolution,[],[f6717,f53])).
% 2.75/0.72  fof(f53,plain,(
% 2.75/0.72    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) ) | ~spl3_4),
% 2.75/0.72    inference(avatar_component_clause,[],[f52])).
% 2.75/0.72  fof(f6717,plain,(
% 2.75/0.72    ( ! [X21,X19,X20] : (~r1_xboole_0(X21,k1_xboole_0) | r1_xboole_0(X19,k4_xboole_0(X21,k2_xboole_0(X20,k4_xboole_0(X19,X20))))) ) | (~spl3_13 | ~spl3_109)),
% 2.75/0.72    inference(superposition,[],[f89,f864])).
% 2.75/0.72  fof(f864,plain,(
% 2.75/0.72    ( ! [X10,X9] : (k1_xboole_0 = k4_xboole_0(X9,k2_xboole_0(X10,k4_xboole_0(X9,X10)))) ) | ~spl3_109),
% 2.75/0.72    inference(avatar_component_clause,[],[f863])).
% 2.75/0.72  fof(f89,plain,(
% 2.75/0.72    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X1,k4_xboole_0(X0,X2))) ) | ~spl3_13),
% 2.75/0.72    inference(avatar_component_clause,[],[f88])).
% 2.75/0.72  fof(f6145,plain,(
% 2.75/0.72    spl3_714 | ~spl3_9 | ~spl3_93 | ~spl3_708),
% 2.75/0.72    inference(avatar_split_clause,[],[f6141,f6097,f791,f72,f6143])).
% 2.75/0.72  fof(f72,plain,(
% 2.75/0.72    spl3_9 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 2.75/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 2.75/0.72  fof(f6097,plain,(
% 2.75/0.72    spl3_708 <=> ! [X9,X10] : (~r1_xboole_0(X9,X10) | r1_xboole_0(X10,k2_xboole_0(k1_xboole_0,X9)))),
% 2.75/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_708])])).
% 2.75/0.72  fof(f6141,plain,(
% 2.75/0.72    ( ! [X4,X3] : (k4_xboole_0(X4,X3) = X4 | ~r1_xboole_0(X3,X4)) ) | (~spl3_9 | ~spl3_93 | ~spl3_708)),
% 2.75/0.72    inference(forward_demodulation,[],[f6130,f792])).
% 2.75/0.72  fof(f6130,plain,(
% 2.75/0.72    ( ! [X4,X3] : (~r1_xboole_0(X3,X4) | k4_xboole_0(X4,k2_xboole_0(k1_xboole_0,X3)) = X4) ) | (~spl3_9 | ~spl3_708)),
% 2.75/0.72    inference(resolution,[],[f6098,f73])).
% 2.75/0.72  fof(f73,plain,(
% 2.75/0.72    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) ) | ~spl3_9),
% 2.75/0.72    inference(avatar_component_clause,[],[f72])).
% 2.75/0.72  fof(f6098,plain,(
% 2.75/0.72    ( ! [X10,X9] : (r1_xboole_0(X10,k2_xboole_0(k1_xboole_0,X9)) | ~r1_xboole_0(X9,X10)) ) | ~spl3_708),
% 2.75/0.72    inference(avatar_component_clause,[],[f6097])).
% 2.75/0.72  fof(f6099,plain,(
% 2.75/0.72    spl3_708 | ~spl3_7 | ~spl3_647),
% 2.75/0.72    inference(avatar_split_clause,[],[f6089,f5556,f64,f6097])).
% 2.75/0.72  fof(f64,plain,(
% 2.75/0.72    spl3_7 <=> ! [X1,X0] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 2.75/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 2.75/0.72  fof(f5556,plain,(
% 2.75/0.72    spl3_647 <=> ! [X42,X43] : (r1_xboole_0(k2_xboole_0(k1_xboole_0,X42),X43) | ~r1_xboole_0(X42,X43))),
% 2.75/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_647])])).
% 2.75/0.72  fof(f6089,plain,(
% 2.75/0.72    ( ! [X10,X9] : (~r1_xboole_0(X9,X10) | r1_xboole_0(X10,k2_xboole_0(k1_xboole_0,X9))) ) | (~spl3_7 | ~spl3_647)),
% 2.75/0.72    inference(resolution,[],[f5557,f65])).
% 2.75/0.72  fof(f65,plain,(
% 2.75/0.72    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) ) | ~spl3_7),
% 2.75/0.72    inference(avatar_component_clause,[],[f64])).
% 2.75/0.72  fof(f5557,plain,(
% 2.75/0.72    ( ! [X43,X42] : (r1_xboole_0(k2_xboole_0(k1_xboole_0,X42),X43) | ~r1_xboole_0(X42,X43)) ) | ~spl3_647),
% 2.75/0.72    inference(avatar_component_clause,[],[f5556])).
% 2.75/0.72  fof(f5558,plain,(
% 2.75/0.72    spl3_647 | ~spl3_29 | ~spl3_165),
% 2.75/0.72    inference(avatar_split_clause,[],[f5504,f1432,f199,f5556])).
% 2.75/0.72  fof(f1432,plain,(
% 2.75/0.72    spl3_165 <=> ! [X4] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_xboole_0,X4),X4)),
% 2.75/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_165])])).
% 2.75/0.72  fof(f5504,plain,(
% 2.75/0.72    ( ! [X43,X42] : (r1_xboole_0(k2_xboole_0(k1_xboole_0,X42),X43) | ~r1_xboole_0(X42,X43)) ) | (~spl3_29 | ~spl3_165)),
% 2.75/0.72    inference(trivial_inequality_removal,[],[f5484])).
% 2.75/0.72  fof(f5484,plain,(
% 2.75/0.72    ( ! [X43,X42] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k2_xboole_0(k1_xboole_0,X42),X43) | ~r1_xboole_0(X42,X43)) ) | (~spl3_29 | ~spl3_165)),
% 2.75/0.72    inference(superposition,[],[f200,f1433])).
% 2.75/0.72  fof(f1433,plain,(
% 2.75/0.72    ( ! [X4] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_xboole_0,X4),X4)) ) | ~spl3_165),
% 2.75/0.72    inference(avatar_component_clause,[],[f1432])).
% 2.75/0.72  fof(f1473,plain,(
% 2.75/0.72    spl3_166 | ~spl3_23 | ~spl3_93),
% 2.75/0.72    inference(avatar_split_clause,[],[f1411,f791,f149,f1436])).
% 2.75/0.72  fof(f1411,plain,(
% 2.75/0.72    ( ! [X45,X46] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k2_xboole_0(k1_xboole_0,X45),X46),X45)) ) | (~spl3_23 | ~spl3_93)),
% 2.75/0.72    inference(superposition,[],[f150,f792])).
% 2.75/0.72  fof(f1446,plain,(
% 2.75/0.72    spl3_165 | ~spl3_24 | ~spl3_93),
% 2.75/0.72    inference(avatar_split_clause,[],[f1399,f791,f153,f1432])).
% 2.75/0.72  fof(f153,plain,(
% 2.75/0.72    spl3_24 <=> ! [X2] : k1_xboole_0 = k4_xboole_0(X2,X2)),
% 2.75/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 2.75/0.72  fof(f1399,plain,(
% 2.75/0.72    ( ! [X16] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_xboole_0,X16),X16)) ) | (~spl3_24 | ~spl3_93)),
% 2.75/0.72    inference(superposition,[],[f154,f792])).
% 2.75/0.72  fof(f154,plain,(
% 2.75/0.72    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(X2,X2)) ) | ~spl3_24),
% 2.75/0.72    inference(avatar_component_clause,[],[f153])).
% 2.75/0.72  fof(f869,plain,(
% 2.75/0.72    spl3_109 | ~spl3_12 | ~spl3_24),
% 2.75/0.72    inference(avatar_split_clause,[],[f773,f153,f84,f863])).
% 2.75/0.72  fof(f84,plain,(
% 2.75/0.72    spl3_12 <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.75/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 2.75/0.72  fof(f773,plain,(
% 2.75/0.72    ( ! [X4,X5] : (k1_xboole_0 = k4_xboole_0(X4,k2_xboole_0(X5,k4_xboole_0(X4,X5)))) ) | (~spl3_12 | ~spl3_24)),
% 2.75/0.72    inference(superposition,[],[f154,f85])).
% 2.75/0.72  fof(f85,plain,(
% 2.75/0.72    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) ) | ~spl3_12),
% 2.75/0.72    inference(avatar_component_clause,[],[f84])).
% 2.75/0.72  fof(f824,plain,(
% 2.75/0.72    spl3_99 | ~spl3_12 | ~spl3_20),
% 2.75/0.72    inference(avatar_split_clause,[],[f759,f128,f84,f822])).
% 2.75/0.72  fof(f128,plain,(
% 2.75/0.72    spl3_20 <=> sK0 = k4_xboole_0(sK0,sK2)),
% 2.75/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 2.75/0.72  fof(f759,plain,(
% 2.75/0.72    ( ! [X17] : (k4_xboole_0(sK0,X17) = k4_xboole_0(sK0,k2_xboole_0(sK2,X17))) ) | (~spl3_12 | ~spl3_20)),
% 2.75/0.72    inference(superposition,[],[f85,f130])).
% 2.75/0.72  fof(f130,plain,(
% 2.75/0.72    sK0 = k4_xboole_0(sK0,sK2) | ~spl3_20),
% 2.75/0.72    inference(avatar_component_clause,[],[f128])).
% 2.75/0.72  fof(f793,plain,(
% 2.75/0.72    spl3_93 | ~spl3_5 | ~spl3_12),
% 2.75/0.72    inference(avatar_split_clause,[],[f752,f84,f56,f791])).
% 2.75/0.72  fof(f56,plain,(
% 2.75/0.72    spl3_5 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.75/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 2.75/0.72  fof(f752,plain,(
% 2.75/0.72    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1))) ) | (~spl3_5 | ~spl3_12)),
% 2.75/0.72    inference(superposition,[],[f85,f57])).
% 2.75/0.72  fof(f57,plain,(
% 2.75/0.72    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl3_5),
% 2.75/0.72    inference(avatar_component_clause,[],[f56])).
% 2.75/0.72  fof(f521,plain,(
% 2.75/0.72    spl3_71 | ~spl3_9 | ~spl3_69),
% 2.75/0.72    inference(avatar_split_clause,[],[f507,f503,f72,f519])).
% 2.75/0.72  fof(f503,plain,(
% 2.75/0.72    spl3_69 <=> ! [X4] : r1_xboole_0(k4_xboole_0(X4,sK1),sK0)),
% 2.75/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_69])])).
% 2.75/0.72  fof(f507,plain,(
% 2.75/0.72    ( ! [X2] : (k4_xboole_0(X2,sK1) = k4_xboole_0(k4_xboole_0(X2,sK1),sK0)) ) | (~spl3_9 | ~spl3_69)),
% 2.75/0.72    inference(resolution,[],[f504,f73])).
% 2.75/0.72  fof(f504,plain,(
% 2.75/0.72    ( ! [X4] : (r1_xboole_0(k4_xboole_0(X4,sK1),sK0)) ) | ~spl3_69),
% 2.75/0.72    inference(avatar_component_clause,[],[f503])).
% 2.75/0.72  fof(f505,plain,(
% 2.75/0.72    spl3_69 | ~spl3_7 | ~spl3_63),
% 2.75/0.72    inference(avatar_split_clause,[],[f488,f470,f64,f503])).
% 2.75/0.72  fof(f470,plain,(
% 2.75/0.72    spl3_63 <=> ! [X14] : r1_xboole_0(sK0,k4_xboole_0(X14,sK1))),
% 2.75/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_63])])).
% 2.75/0.72  fof(f488,plain,(
% 2.75/0.72    ( ! [X4] : (r1_xboole_0(k4_xboole_0(X4,sK1),sK0)) ) | (~spl3_7 | ~spl3_63)),
% 2.75/0.72    inference(resolution,[],[f471,f65])).
% 2.75/0.72  fof(f471,plain,(
% 2.75/0.72    ( ! [X14] : (r1_xboole_0(sK0,k4_xboole_0(X14,sK1))) ) | ~spl3_63),
% 2.75/0.72    inference(avatar_component_clause,[],[f470])).
% 2.75/0.72  fof(f472,plain,(
% 2.75/0.72    spl3_63 | ~spl3_4 | ~spl3_13 | ~spl3_22),
% 2.75/0.72    inference(avatar_split_clause,[],[f468,f144,f88,f52,f470])).
% 2.75/0.72  fof(f144,plain,(
% 2.75/0.72    spl3_22 <=> k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 2.75/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 2.75/0.72  fof(f468,plain,(
% 2.75/0.72    ( ! [X14] : (r1_xboole_0(sK0,k4_xboole_0(X14,sK1))) ) | (~spl3_4 | ~spl3_13 | ~spl3_22)),
% 2.75/0.72    inference(subsumption_resolution,[],[f424,f53])).
% 2.75/0.72  fof(f424,plain,(
% 2.75/0.72    ( ! [X14] : (~r1_xboole_0(X14,k1_xboole_0) | r1_xboole_0(sK0,k4_xboole_0(X14,sK1))) ) | (~spl3_13 | ~spl3_22)),
% 2.75/0.72    inference(superposition,[],[f89,f146])).
% 2.75/0.72  fof(f146,plain,(
% 2.75/0.72    k1_xboole_0 = k4_xboole_0(sK0,sK1) | ~spl3_22),
% 2.75/0.72    inference(avatar_component_clause,[],[f144])).
% 2.75/0.72  fof(f201,plain,(
% 2.75/0.72    spl3_29 | ~spl3_11 | ~spl3_14),
% 2.75/0.72    inference(avatar_split_clause,[],[f193,f92,f80,f199])).
% 2.75/0.72  fof(f80,plain,(
% 2.75/0.72    spl3_11 <=> ! [X1,X0] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0)),
% 2.75/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 2.75/0.72  fof(f92,plain,(
% 2.75/0.72    spl3_14 <=> ! [X1,X0,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 2.75/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 2.75/0.72  fof(f193,plain,(
% 2.75/0.72    ( ! [X4,X2,X3] : (~r1_xboole_0(X2,X3) | r1_xboole_0(X4,X3) | k1_xboole_0 != k4_xboole_0(X4,X2)) ) | (~spl3_11 | ~spl3_14)),
% 2.75/0.72    inference(resolution,[],[f93,f81])).
% 2.75/0.72  fof(f81,plain,(
% 2.75/0.72    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) ) | ~spl3_11),
% 2.75/0.72    inference(avatar_component_clause,[],[f80])).
% 2.75/0.72  fof(f93,plain,(
% 2.75/0.72    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2)) ) | ~spl3_14),
% 2.75/0.72    inference(avatar_component_clause,[],[f92])).
% 2.75/0.72  fof(f185,plain,(
% 2.75/0.72    ~spl3_27 | spl3_1 | ~spl3_11),
% 2.75/0.72    inference(avatar_split_clause,[],[f179,f80,f37,f182])).
% 2.75/0.72  fof(f37,plain,(
% 2.75/0.72    spl3_1 <=> r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 2.75/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 2.75/0.72  fof(f179,plain,(
% 2.75/0.72    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | (spl3_1 | ~spl3_11)),
% 2.75/0.72    inference(resolution,[],[f81,f39])).
% 2.75/0.72  fof(f39,plain,(
% 2.75/0.72    ~r1_tarski(sK0,k4_xboole_0(sK1,sK2)) | spl3_1),
% 2.75/0.72    inference(avatar_component_clause,[],[f37])).
% 2.75/0.72  fof(f155,plain,(
% 2.75/0.72    spl3_24 | ~spl3_10 | ~spl3_15),
% 2.75/0.72    inference(avatar_split_clause,[],[f142,f97,f76,f153])).
% 2.75/0.72  fof(f76,plain,(
% 2.75/0.72    spl3_10 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 2.75/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 2.75/0.72  fof(f97,plain,(
% 2.75/0.72    spl3_15 <=> ! [X0] : r1_tarski(X0,X0)),
% 2.75/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 2.75/0.72  fof(f142,plain,(
% 2.75/0.72    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(X2,X2)) ) | (~spl3_10 | ~spl3_15)),
% 2.75/0.72    inference(resolution,[],[f77,f98])).
% 2.75/0.72  fof(f98,plain,(
% 2.75/0.72    ( ! [X0] : (r1_tarski(X0,X0)) ) | ~spl3_15),
% 2.75/0.72    inference(avatar_component_clause,[],[f97])).
% 2.75/0.72  fof(f77,plain,(
% 2.75/0.72    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) ) | ~spl3_10),
% 2.75/0.72    inference(avatar_component_clause,[],[f76])).
% 2.75/0.72  fof(f151,plain,(
% 2.75/0.72    spl3_23 | ~spl3_6 | ~spl3_10),
% 2.75/0.72    inference(avatar_split_clause,[],[f141,f76,f60,f149])).
% 2.75/0.72  fof(f60,plain,(
% 2.75/0.72    spl3_6 <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.75/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 2.75/0.72  fof(f141,plain,(
% 2.75/0.72    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)) ) | (~spl3_6 | ~spl3_10)),
% 2.75/0.72    inference(resolution,[],[f77,f61])).
% 2.75/0.72  fof(f61,plain,(
% 2.75/0.72    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) ) | ~spl3_6),
% 2.75/0.72    inference(avatar_component_clause,[],[f60])).
% 2.75/0.72  fof(f147,plain,(
% 2.75/0.72    spl3_22 | ~spl3_3 | ~spl3_10),
% 2.75/0.72    inference(avatar_split_clause,[],[f140,f76,f47,f144])).
% 2.75/0.72  fof(f47,plain,(
% 2.75/0.72    spl3_3 <=> r1_tarski(sK0,sK1)),
% 2.75/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 2.75/0.72  fof(f140,plain,(
% 2.75/0.72    k1_xboole_0 = k4_xboole_0(sK0,sK1) | (~spl3_3 | ~spl3_10)),
% 2.75/0.72    inference(resolution,[],[f77,f49])).
% 2.75/0.72  fof(f49,plain,(
% 2.75/0.72    r1_tarski(sK0,sK1) | ~spl3_3),
% 2.75/0.72    inference(avatar_component_clause,[],[f47])).
% 2.75/0.72  fof(f131,plain,(
% 2.75/0.72    spl3_20 | ~spl3_2 | ~spl3_9),
% 2.75/0.72    inference(avatar_split_clause,[],[f121,f72,f42,f128])).
% 2.75/0.72  fof(f42,plain,(
% 2.75/0.72    spl3_2 <=> r1_xboole_0(sK0,sK2)),
% 2.75/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 2.75/0.72  fof(f121,plain,(
% 2.75/0.72    sK0 = k4_xboole_0(sK0,sK2) | (~spl3_2 | ~spl3_9)),
% 2.75/0.72    inference(resolution,[],[f73,f44])).
% 2.75/0.72  fof(f44,plain,(
% 2.75/0.72    r1_xboole_0(sK0,sK2) | ~spl3_2),
% 2.75/0.72    inference(avatar_component_clause,[],[f42])).
% 2.75/0.72  fof(f99,plain,(
% 2.75/0.72    spl3_15 | ~spl3_5 | ~spl3_6),
% 2.75/0.72    inference(avatar_split_clause,[],[f95,f60,f56,f97])).
% 2.75/0.72  fof(f95,plain,(
% 2.75/0.72    ( ! [X0] : (r1_tarski(X0,X0)) ) | (~spl3_5 | ~spl3_6)),
% 2.75/0.72    inference(superposition,[],[f61,f57])).
% 2.75/0.72  fof(f94,plain,(
% 2.75/0.72    spl3_14),
% 2.75/0.72    inference(avatar_split_clause,[],[f35,f92])).
% 2.75/0.72  fof(f35,plain,(
% 2.75/0.72    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 2.75/0.72    inference(cnf_transformation,[],[f17])).
% 2.75/0.72  fof(f17,plain,(
% 2.75/0.72    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 2.75/0.72    inference(flattening,[],[f16])).
% 2.75/0.72  fof(f16,plain,(
% 2.75/0.72    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.75/0.72    inference(ennf_transformation,[],[f6])).
% 2.75/0.72  fof(f6,axiom,(
% 2.75/0.72    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 2.75/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 2.75/0.72  fof(f90,plain,(
% 2.75/0.72    spl3_13),
% 2.75/0.72    inference(avatar_split_clause,[],[f34,f88])).
% 2.75/0.72  fof(f34,plain,(
% 2.75/0.72    ( ! [X2,X0,X1] : (r1_xboole_0(X1,k4_xboole_0(X0,X2)) | ~r1_xboole_0(X0,k4_xboole_0(X1,X2))) )),
% 2.75/0.72    inference(cnf_transformation,[],[f15])).
% 2.75/0.72  fof(f15,plain,(
% 2.75/0.72    ! [X0,X1,X2] : (r1_xboole_0(X1,k4_xboole_0(X0,X2)) | ~r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 2.75/0.72    inference(ennf_transformation,[],[f8])).
% 2.75/0.72  fof(f8,axiom,(
% 2.75/0.72    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 2.75/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_xboole_1)).
% 2.75/0.72  fof(f86,plain,(
% 2.75/0.72    spl3_12),
% 2.75/0.72    inference(avatar_split_clause,[],[f33,f84])).
% 2.75/0.72  fof(f33,plain,(
% 2.75/0.72    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.75/0.72    inference(cnf_transformation,[],[f5])).
% 2.75/0.72  fof(f5,axiom,(
% 2.75/0.72    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.75/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 2.75/0.72  fof(f82,plain,(
% 2.75/0.72    spl3_11),
% 2.75/0.72    inference(avatar_split_clause,[],[f31,f80])).
% 2.75/0.72  fof(f31,plain,(
% 2.75/0.72    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 2.75/0.72    inference(cnf_transformation,[],[f21])).
% 2.75/0.72  fof(f21,plain,(
% 2.75/0.72    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 2.75/0.72    inference(nnf_transformation,[],[f2])).
% 2.75/0.72  fof(f2,axiom,(
% 2.75/0.72    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 2.75/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 2.75/0.72  fof(f78,plain,(
% 2.75/0.72    spl3_10),
% 2.75/0.72    inference(avatar_split_clause,[],[f32,f76])).
% 2.75/0.72  fof(f32,plain,(
% 2.75/0.72    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 2.75/0.72    inference(cnf_transformation,[],[f21])).
% 2.75/0.72  fof(f74,plain,(
% 2.75/0.72    spl3_9),
% 2.75/0.72    inference(avatar_split_clause,[],[f29,f72])).
% 2.75/0.72  fof(f29,plain,(
% 2.75/0.72    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 2.75/0.72    inference(cnf_transformation,[],[f20])).
% 2.75/0.72  fof(f20,plain,(
% 2.75/0.72    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 2.75/0.72    inference(nnf_transformation,[],[f9])).
% 2.75/0.72  fof(f9,axiom,(
% 2.75/0.72    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 2.75/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 2.75/0.72  fof(f66,plain,(
% 2.75/0.72    spl3_7),
% 2.75/0.72    inference(avatar_split_clause,[],[f28,f64])).
% 2.75/0.72  fof(f28,plain,(
% 2.75/0.72    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 2.75/0.72    inference(cnf_transformation,[],[f14])).
% 2.75/0.72  fof(f14,plain,(
% 2.75/0.72    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 2.75/0.72    inference(ennf_transformation,[],[f1])).
% 2.75/0.72  fof(f1,axiom,(
% 2.75/0.72    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 2.75/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 2.75/0.72  fof(f62,plain,(
% 2.75/0.72    spl3_6),
% 2.75/0.72    inference(avatar_split_clause,[],[f27,f60])).
% 2.75/0.72  fof(f27,plain,(
% 2.75/0.72    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.75/0.72    inference(cnf_transformation,[],[f3])).
% 2.75/0.72  fof(f3,axiom,(
% 2.75/0.72    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.75/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.75/0.72  fof(f58,plain,(
% 2.75/0.72    spl3_5),
% 2.75/0.72    inference(avatar_split_clause,[],[f26,f56])).
% 2.75/0.72  fof(f26,plain,(
% 2.75/0.72    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.75/0.72    inference(cnf_transformation,[],[f4])).
% 2.75/0.72  fof(f4,axiom,(
% 2.75/0.72    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.75/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 2.75/0.72  fof(f54,plain,(
% 2.75/0.72    spl3_4),
% 2.75/0.72    inference(avatar_split_clause,[],[f25,f52])).
% 2.75/0.72  fof(f25,plain,(
% 2.75/0.72    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 2.75/0.72    inference(cnf_transformation,[],[f7])).
% 2.75/0.72  fof(f7,axiom,(
% 2.75/0.72    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 2.75/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 2.75/0.72  fof(f50,plain,(
% 2.75/0.72    spl3_3),
% 2.75/0.72    inference(avatar_split_clause,[],[f22,f47])).
% 2.75/0.72  fof(f22,plain,(
% 2.75/0.72    r1_tarski(sK0,sK1)),
% 2.75/0.72    inference(cnf_transformation,[],[f19])).
% 2.75/0.72  fof(f19,plain,(
% 2.75/0.72    ~r1_tarski(sK0,k4_xboole_0(sK1,sK2)) & r1_xboole_0(sK0,sK2) & r1_tarski(sK0,sK1)),
% 2.75/0.72    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f18])).
% 2.75/0.72  fof(f18,plain,(
% 2.75/0.72    ? [X0,X1,X2] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) & r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => (~r1_tarski(sK0,k4_xboole_0(sK1,sK2)) & r1_xboole_0(sK0,sK2) & r1_tarski(sK0,sK1))),
% 2.75/0.72    introduced(choice_axiom,[])).
% 2.75/0.72  fof(f13,plain,(
% 2.75/0.72    ? [X0,X1,X2] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) & r1_xboole_0(X0,X2) & r1_tarski(X0,X1))),
% 2.75/0.72    inference(flattening,[],[f12])).
% 2.75/0.72  fof(f12,plain,(
% 2.75/0.72    ? [X0,X1,X2] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) & (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 2.75/0.72    inference(ennf_transformation,[],[f11])).
% 2.75/0.72  fof(f11,negated_conjecture,(
% 2.75/0.72    ~! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 2.75/0.72    inference(negated_conjecture,[],[f10])).
% 2.75/0.72  fof(f10,conjecture,(
% 2.75/0.72    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 2.75/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).
% 2.75/0.72  fof(f45,plain,(
% 2.75/0.72    spl3_2),
% 2.75/0.72    inference(avatar_split_clause,[],[f23,f42])).
% 2.75/0.72  fof(f23,plain,(
% 2.75/0.72    r1_xboole_0(sK0,sK2)),
% 2.75/0.72    inference(cnf_transformation,[],[f19])).
% 2.75/0.72  fof(f40,plain,(
% 2.75/0.72    ~spl3_1),
% 2.75/0.72    inference(avatar_split_clause,[],[f24,f37])).
% 2.75/0.72  fof(f24,plain,(
% 2.75/0.72    ~r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 2.75/0.72    inference(cnf_transformation,[],[f19])).
% 2.75/0.72  % SZS output end Proof for theBenchmark
% 2.75/0.72  % (13993)------------------------------
% 2.75/0.72  % (13993)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.75/0.72  % (13993)Termination reason: Refutation
% 2.75/0.72  
% 2.75/0.72  % (13993)Memory used [KB]: 17398
% 2.75/0.72  % (13993)Time elapsed: 0.278 s
% 2.75/0.72  % (13993)------------------------------
% 2.75/0.72  % (13993)------------------------------
% 2.75/0.73  % (13987)Success in time 0.357 s
%------------------------------------------------------------------------------
