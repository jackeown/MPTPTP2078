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
% DateTime   : Thu Dec  3 12:30:53 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 226 expanded)
%              Number of leaves         :   27 (  92 expanded)
%              Depth                    :    9
%              Number of atoms          :  207 ( 426 expanded)
%              Number of equality atoms :   95 ( 231 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1392,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f46,f50,f54,f79,f83,f211,f327,f331,f352,f431,f1067,f1088,f1315,f1354,f1378])).

fof(f1378,plain,
    ( spl4_1
    | ~ spl4_71
    | ~ spl4_73 ),
    inference(avatar_split_clause,[],[f1376,f1351,f1086,f40])).

fof(f40,plain,
    ( spl4_1
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f1086,plain,
    ( spl4_71
  <=> sK2 = k2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_71])])).

fof(f1351,plain,
    ( spl4_73
  <=> k1_xboole_0 = k4_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_73])])).

fof(f1376,plain,
    ( sK1 = sK2
    | ~ spl4_71
    | ~ spl4_73 ),
    inference(forward_demodulation,[],[f1375,f26])).

fof(f26,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f1375,plain,
    ( sK2 = k2_xboole_0(sK1,k1_xboole_0)
    | ~ spl4_71
    | ~ spl4_73 ),
    inference(forward_demodulation,[],[f1366,f1087])).

fof(f1087,plain,
    ( sK2 = k2_xboole_0(sK1,sK2)
    | ~ spl4_71 ),
    inference(avatar_component_clause,[],[f1086])).

fof(f1366,plain,
    ( k2_xboole_0(sK1,k1_xboole_0) = k2_xboole_0(sK1,sK2)
    | ~ spl4_73 ),
    inference(superposition,[],[f30,f1352])).

fof(f1352,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,sK1)
    | ~ spl4_73 ),
    inference(avatar_component_clause,[],[f1351])).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f1354,plain,
    ( spl4_73
    | ~ spl4_25
    | ~ spl4_72 ),
    inference(avatar_split_clause,[],[f1344,f1313,f349,f1351])).

fof(f349,plain,
    ( spl4_25
  <=> sK2 = k4_xboole_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f1313,plain,
    ( spl4_72
  <=> k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_72])])).

fof(f1344,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,sK1)
    | ~ spl4_25
    | ~ spl4_72 ),
    inference(superposition,[],[f371,f1314])).

fof(f1314,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1))
    | ~ spl4_72 ),
    inference(avatar_component_clause,[],[f1313])).

fof(f371,plain,
    ( ! [X1] : k4_xboole_0(sK2,k2_xboole_0(sK0,X1)) = k4_xboole_0(sK2,X1)
    | ~ spl4_25 ),
    inference(superposition,[],[f33,f350])).

fof(f350,plain,
    ( sK2 = k4_xboole_0(sK2,sK0)
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f349])).

fof(f33,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

% (11622)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
fof(f8,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f1315,plain,
    ( spl4_72
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f1311,f52,f1313])).

fof(f52,plain,
    ( spl4_4
  <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f1311,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1))
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f1263,f730])).

fof(f730,plain,(
    ! [X5] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X5) ),
    inference(superposition,[],[f136,f26])).

fof(f136,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,X5)) ),
    inference(forward_demodulation,[],[f135,f30])).

fof(f135,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,X6))) ),
    inference(forward_demodulation,[],[f125,f25])).

fof(f25,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f125,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(k4_xboole_0(X5,X6),k1_xboole_0))) ),
    inference(superposition,[],[f33,f35])).

fof(f35,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f24,f29])).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f24,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f1263,plain,
    ( k4_xboole_0(k1_xboole_0,sK3) = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1))
    | ~ spl4_4 ),
    inference(superposition,[],[f132,f53])).

fof(f53,plain,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f52])).

fof(f132,plain,(
    ! [X2,X3] : k4_xboole_0(k1_xboole_0,X3) = k4_xboole_0(X2,k2_xboole_0(X2,X3)) ),
    inference(forward_demodulation,[],[f119,f25])).

fof(f119,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X2,k1_xboole_0),X3)) = k4_xboole_0(k1_xboole_0,X3) ),
    inference(superposition,[],[f33,f35])).

fof(f1088,plain,
    ( spl4_71
    | ~ spl4_70 ),
    inference(avatar_split_clause,[],[f1084,f1065,f1086])).

fof(f1065,plain,
    ( spl4_70
  <=> k1_xboole_0 = k4_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_70])])).

fof(f1084,plain,
    ( sK2 = k2_xboole_0(sK1,sK2)
    | ~ spl4_70 ),
    inference(forward_demodulation,[],[f1083,f26])).

fof(f1083,plain,
    ( k2_xboole_0(sK2,k1_xboole_0) = k2_xboole_0(sK1,sK2)
    | ~ spl4_70 ),
    inference(forward_demodulation,[],[f1076,f28])).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f1076,plain,
    ( k2_xboole_0(sK2,k1_xboole_0) = k2_xboole_0(sK2,sK1)
    | ~ spl4_70 ),
    inference(superposition,[],[f30,f1066])).

fof(f1066,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK2)
    | ~ spl4_70 ),
    inference(avatar_component_clause,[],[f1065])).

fof(f1067,plain,
    ( spl4_70
    | ~ spl4_4
    | ~ spl4_37 ),
    inference(avatar_split_clause,[],[f1063,f428,f52,f1065])).

fof(f428,plain,
    ( spl4_37
  <=> sK1 = k4_xboole_0(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f1063,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK2)
    | ~ spl4_4
    | ~ spl4_37 ),
    inference(forward_demodulation,[],[f1056,f136])).

fof(f1056,plain,
    ( k4_xboole_0(sK1,k2_xboole_0(sK0,sK1)) = k4_xboole_0(sK1,sK2)
    | ~ spl4_4
    | ~ spl4_37 ),
    inference(superposition,[],[f604,f53])).

fof(f604,plain,
    ( ! [X0] : k4_xboole_0(sK1,X0) = k4_xboole_0(sK1,k2_xboole_0(X0,sK3))
    | ~ spl4_37 ),
    inference(superposition,[],[f446,f28])).

fof(f446,plain,
    ( ! [X0] : k4_xboole_0(sK1,k2_xboole_0(sK3,X0)) = k4_xboole_0(sK1,X0)
    | ~ spl4_37 ),
    inference(superposition,[],[f33,f429])).

fof(f429,plain,
    ( sK1 = k4_xboole_0(sK1,sK3)
    | ~ spl4_37 ),
    inference(avatar_component_clause,[],[f428])).

fof(f431,plain,
    ( spl4_37
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f426,f325,f428])).

fof(f325,plain,
    ( spl4_22
  <=> sK1 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f426,plain,
    ( sK1 = k4_xboole_0(sK1,sK3)
    | ~ spl4_22 ),
    inference(superposition,[],[f55,f326])).

fof(f326,plain,
    ( sK1 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK3))
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f325])).

fof(f55,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f28,f26])).

fof(f352,plain,
    ( spl4_25
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f347,f329,f349])).

fof(f329,plain,
    ( spl4_23
  <=> sK2 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f347,plain,
    ( sK2 = k4_xboole_0(sK2,sK0)
    | ~ spl4_23 ),
    inference(superposition,[],[f55,f330])).

fof(f330,plain,
    ( sK2 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK0))
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f329])).

fof(f331,plain,
    ( spl4_23
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f293,f81,f329])).

fof(f81,plain,
    ( spl4_6
  <=> k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f293,plain,
    ( sK2 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK0))
    | ~ spl4_6 ),
    inference(superposition,[],[f37,f82])).

fof(f82,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f81])).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f31,f29])).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f327,plain,
    ( spl4_22
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f292,f197,f325])).

fof(f197,plain,
    ( spl4_14
  <=> k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f292,plain,
    ( sK1 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK3))
    | ~ spl4_14 ),
    inference(superposition,[],[f37,f198])).

fof(f198,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f197])).

fof(f211,plain,
    ( spl4_14
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f189,f77,f197])).

fof(f77,plain,
    ( spl4_5
  <=> k1_xboole_0 = k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f189,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))
    | ~ spl4_5 ),
    inference(superposition,[],[f78,f36])).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f27,f29,f29])).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f78,plain,
    ( k1_xboole_0 = k4_xboole_0(sK3,k4_xboole_0(sK3,sK1))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f77])).

fof(f83,plain,
    ( spl4_6
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f75,f48,f81])).

fof(f48,plain,
    ( spl4_3
  <=> r1_xboole_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f75,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))
    | ~ spl4_3 ),
    inference(resolution,[],[f38,f49])).

fof(f49,plain,
    ( r1_xboole_0(sK2,sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f48])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f32,f29])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f79,plain,
    ( spl4_5
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f74,f44,f77])).

fof(f44,plain,
    ( spl4_2
  <=> r1_xboole_0(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f74,plain,
    ( k1_xboole_0 = k4_xboole_0(sK3,k4_xboole_0(sK3,sK1))
    | ~ spl4_2 ),
    inference(resolution,[],[f38,f45])).

fof(f45,plain,
    ( r1_xboole_0(sK3,sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f54,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f20,f52])).

fof(f20,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( sK1 != sK2
    & r1_xboole_0(sK3,sK1)
    & r1_xboole_0(sK2,sK0)
    & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2,X3] :
        ( X1 != X2
        & r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
   => ( sK1 != sK2
      & r1_xboole_0(sK3,sK1)
      & r1_xboole_0(sK2,sK0)
      & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X3,X1)
          & r1_xboole_0(X2,X0)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).

fof(f50,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f21,f48])).

fof(f21,plain,(
    r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f46,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f22,f44])).

fof(f22,plain,(
    r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f42,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f23,f40])).

fof(f23,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:28:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.37  ipcrm: permission denied for id (805437440)
% 0.13/0.37  ipcrm: permission denied for id (805470210)
% 0.13/0.38  ipcrm: permission denied for id (805535753)
% 0.13/0.38  ipcrm: permission denied for id (805568522)
% 0.13/0.39  ipcrm: permission denied for id (805634061)
% 0.13/0.39  ipcrm: permission denied for id (805699600)
% 0.21/0.39  ipcrm: permission denied for id (805797908)
% 0.21/0.40  ipcrm: permission denied for id (805830677)
% 0.21/0.40  ipcrm: permission denied for id (805896215)
% 0.21/0.40  ipcrm: permission denied for id (805961754)
% 0.21/0.41  ipcrm: permission denied for id (806158369)
% 0.21/0.42  ipcrm: permission denied for id (806223909)
% 0.21/0.42  ipcrm: permission denied for id (806289448)
% 0.21/0.42  ipcrm: permission denied for id (806354987)
% 0.21/0.43  ipcrm: permission denied for id (806453293)
% 0.21/0.43  ipcrm: permission denied for id (806420527)
% 0.21/0.43  ipcrm: permission denied for id (806518833)
% 0.21/0.45  ipcrm: permission denied for id (806780989)
% 0.21/0.46  ipcrm: permission denied for id (807043148)
% 0.21/0.46  ipcrm: permission denied for id (807075917)
% 0.21/0.47  ipcrm: permission denied for id (807206993)
% 0.21/0.47  ipcrm: permission denied for id (807272531)
% 0.21/0.47  ipcrm: permission denied for id (807305300)
% 0.21/0.48  ipcrm: permission denied for id (807403607)
% 0.21/0.49  ipcrm: permission denied for id (807501920)
% 0.21/0.49  ipcrm: permission denied for id (807534690)
% 0.21/0.49  ipcrm: permission denied for id (807567460)
% 0.21/0.50  ipcrm: permission denied for id (807632998)
% 0.21/0.50  ipcrm: permission denied for id (807665769)
% 0.21/0.51  ipcrm: permission denied for id (807862383)
% 0.21/0.51  ipcrm: permission denied for id (807927921)
% 0.21/0.51  ipcrm: permission denied for id (807960690)
% 0.34/0.52  ipcrm: permission denied for id (808026231)
% 0.34/0.52  ipcrm: permission denied for id (808124540)
% 0.34/0.53  ipcrm: permission denied for id (808222847)
% 0.38/0.64  % (11604)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.38/0.65  % (11621)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.38/0.69  % (11611)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.38/0.70  % (11619)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.38/0.70  % (11611)Refutation not found, incomplete strategy% (11611)------------------------------
% 0.38/0.70  % (11611)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.38/0.70  % (11611)Termination reason: Refutation not found, incomplete strategy
% 0.38/0.70  
% 0.38/0.70  % (11611)Memory used [KB]: 10618
% 0.38/0.70  % (11611)Time elapsed: 0.083 s
% 0.38/0.70  % (11611)------------------------------
% 0.38/0.70  % (11611)------------------------------
% 0.38/0.70  % (11606)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.38/0.71  % (11619)Refutation not found, incomplete strategy% (11619)------------------------------
% 0.38/0.71  % (11619)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.38/0.71  % (11619)Termination reason: Refutation not found, incomplete strategy
% 0.38/0.71  
% 0.38/0.71  % (11619)Memory used [KB]: 10618
% 0.38/0.71  % (11619)Time elapsed: 0.087 s
% 0.38/0.71  % (11619)------------------------------
% 0.38/0.71  % (11619)------------------------------
% 0.38/0.71  % (11621)Refutation found. Thanks to Tanya!
% 0.38/0.71  % SZS status Theorem for theBenchmark
% 0.38/0.71  % SZS output start Proof for theBenchmark
% 0.38/0.71  fof(f1392,plain,(
% 0.38/0.71    $false),
% 0.38/0.71    inference(avatar_sat_refutation,[],[f42,f46,f50,f54,f79,f83,f211,f327,f331,f352,f431,f1067,f1088,f1315,f1354,f1378])).
% 0.38/0.71  fof(f1378,plain,(
% 0.38/0.71    spl4_1 | ~spl4_71 | ~spl4_73),
% 0.38/0.71    inference(avatar_split_clause,[],[f1376,f1351,f1086,f40])).
% 0.38/0.71  fof(f40,plain,(
% 0.38/0.71    spl4_1 <=> sK1 = sK2),
% 0.38/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.38/0.71  fof(f1086,plain,(
% 0.38/0.71    spl4_71 <=> sK2 = k2_xboole_0(sK1,sK2)),
% 0.38/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_71])])).
% 0.38/0.71  fof(f1351,plain,(
% 0.38/0.71    spl4_73 <=> k1_xboole_0 = k4_xboole_0(sK2,sK1)),
% 0.38/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_73])])).
% 0.38/0.71  fof(f1376,plain,(
% 0.38/0.71    sK1 = sK2 | (~spl4_71 | ~spl4_73)),
% 0.38/0.71    inference(forward_demodulation,[],[f1375,f26])).
% 0.38/0.71  fof(f26,plain,(
% 0.38/0.71    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.38/0.71    inference(cnf_transformation,[],[f4])).
% 0.38/0.71  fof(f4,axiom,(
% 0.38/0.71    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.38/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.38/0.71  fof(f1375,plain,(
% 0.38/0.71    sK2 = k2_xboole_0(sK1,k1_xboole_0) | (~spl4_71 | ~spl4_73)),
% 0.38/0.71    inference(forward_demodulation,[],[f1366,f1087])).
% 0.38/0.71  fof(f1087,plain,(
% 0.38/0.71    sK2 = k2_xboole_0(sK1,sK2) | ~spl4_71),
% 0.38/0.71    inference(avatar_component_clause,[],[f1086])).
% 0.38/0.71  fof(f1366,plain,(
% 0.38/0.71    k2_xboole_0(sK1,k1_xboole_0) = k2_xboole_0(sK1,sK2) | ~spl4_73),
% 0.38/0.71    inference(superposition,[],[f30,f1352])).
% 0.38/0.71  fof(f1352,plain,(
% 0.38/0.71    k1_xboole_0 = k4_xboole_0(sK2,sK1) | ~spl4_73),
% 0.38/0.71    inference(avatar_component_clause,[],[f1351])).
% 0.38/0.71  fof(f30,plain,(
% 0.38/0.71    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.38/0.71    inference(cnf_transformation,[],[f6])).
% 0.38/0.71  fof(f6,axiom,(
% 0.38/0.71    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.38/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.38/0.71  fof(f1354,plain,(
% 0.38/0.71    spl4_73 | ~spl4_25 | ~spl4_72),
% 0.38/0.71    inference(avatar_split_clause,[],[f1344,f1313,f349,f1351])).
% 0.38/0.71  fof(f349,plain,(
% 0.38/0.71    spl4_25 <=> sK2 = k4_xboole_0(sK2,sK0)),
% 0.38/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.38/0.71  fof(f1313,plain,(
% 0.38/0.71    spl4_72 <=> k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1))),
% 0.38/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_72])])).
% 0.38/0.71  fof(f1344,plain,(
% 0.38/0.71    k1_xboole_0 = k4_xboole_0(sK2,sK1) | (~spl4_25 | ~spl4_72)),
% 0.38/0.71    inference(superposition,[],[f371,f1314])).
% 0.38/0.71  fof(f1314,plain,(
% 0.38/0.71    k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) | ~spl4_72),
% 0.38/0.71    inference(avatar_component_clause,[],[f1313])).
% 0.38/0.71  fof(f371,plain,(
% 0.38/0.71    ( ! [X1] : (k4_xboole_0(sK2,k2_xboole_0(sK0,X1)) = k4_xboole_0(sK2,X1)) ) | ~spl4_25),
% 0.38/0.71    inference(superposition,[],[f33,f350])).
% 0.38/0.71  fof(f350,plain,(
% 0.38/0.71    sK2 = k4_xboole_0(sK2,sK0) | ~spl4_25),
% 0.38/0.71    inference(avatar_component_clause,[],[f349])).
% 0.38/0.71  fof(f33,plain,(
% 0.38/0.71    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.38/0.71    inference(cnf_transformation,[],[f8])).
% 0.38/0.71  % (11622)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.38/0.71  fof(f8,axiom,(
% 0.38/0.71    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.38/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.38/0.71  fof(f1315,plain,(
% 0.38/0.71    spl4_72 | ~spl4_4),
% 0.38/0.71    inference(avatar_split_clause,[],[f1311,f52,f1313])).
% 0.38/0.71  fof(f52,plain,(
% 0.38/0.71    spl4_4 <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 0.38/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.38/0.71  fof(f1311,plain,(
% 0.38/0.71    k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) | ~spl4_4),
% 0.38/0.71    inference(forward_demodulation,[],[f1263,f730])).
% 0.38/0.71  fof(f730,plain,(
% 0.38/0.71    ( ! [X5] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X5)) )),
% 0.38/0.71    inference(superposition,[],[f136,f26])).
% 0.38/0.71  fof(f136,plain,(
% 0.38/0.71    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,X5))) )),
% 0.38/0.71    inference(forward_demodulation,[],[f135,f30])).
% 0.38/0.71  fof(f135,plain,(
% 0.38/0.71    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,X6)))) )),
% 0.38/0.71    inference(forward_demodulation,[],[f125,f25])).
% 0.38/0.71  fof(f25,plain,(
% 0.38/0.71    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.38/0.71    inference(cnf_transformation,[],[f7])).
% 0.38/0.71  fof(f7,axiom,(
% 0.38/0.71    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.38/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.38/0.71  fof(f125,plain,(
% 0.38/0.71    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(k4_xboole_0(X5,X6),k1_xboole_0)))) )),
% 0.38/0.71    inference(superposition,[],[f33,f35])).
% 0.38/0.71  fof(f35,plain,(
% 0.38/0.71    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.38/0.71    inference(definition_unfolding,[],[f24,f29])).
% 0.38/0.71  fof(f29,plain,(
% 0.38/0.71    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.38/0.71    inference(cnf_transformation,[],[f10])).
% 0.38/0.71  fof(f10,axiom,(
% 0.38/0.71    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.38/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.38/0.71  fof(f24,plain,(
% 0.38/0.71    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.38/0.71    inference(cnf_transformation,[],[f5])).
% 0.38/0.71  fof(f5,axiom,(
% 0.38/0.71    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.38/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.38/0.71  fof(f1263,plain,(
% 0.38/0.71    k4_xboole_0(k1_xboole_0,sK3) = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) | ~spl4_4),
% 0.38/0.71    inference(superposition,[],[f132,f53])).
% 0.38/0.71  fof(f53,plain,(
% 0.38/0.71    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) | ~spl4_4),
% 0.38/0.71    inference(avatar_component_clause,[],[f52])).
% 0.38/0.71  fof(f132,plain,(
% 0.38/0.71    ( ! [X2,X3] : (k4_xboole_0(k1_xboole_0,X3) = k4_xboole_0(X2,k2_xboole_0(X2,X3))) )),
% 0.38/0.71    inference(forward_demodulation,[],[f119,f25])).
% 0.38/0.71  fof(f119,plain,(
% 0.38/0.71    ( ! [X2,X3] : (k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X2,k1_xboole_0),X3)) = k4_xboole_0(k1_xboole_0,X3)) )),
% 0.38/0.71    inference(superposition,[],[f33,f35])).
% 0.38/0.71  fof(f1088,plain,(
% 0.38/0.71    spl4_71 | ~spl4_70),
% 0.38/0.71    inference(avatar_split_clause,[],[f1084,f1065,f1086])).
% 0.38/0.71  fof(f1065,plain,(
% 0.38/0.71    spl4_70 <=> k1_xboole_0 = k4_xboole_0(sK1,sK2)),
% 0.38/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_70])])).
% 0.38/0.71  fof(f1084,plain,(
% 0.38/0.71    sK2 = k2_xboole_0(sK1,sK2) | ~spl4_70),
% 0.38/0.71    inference(forward_demodulation,[],[f1083,f26])).
% 0.38/0.71  fof(f1083,plain,(
% 0.38/0.71    k2_xboole_0(sK2,k1_xboole_0) = k2_xboole_0(sK1,sK2) | ~spl4_70),
% 0.38/0.71    inference(forward_demodulation,[],[f1076,f28])).
% 0.38/0.71  fof(f28,plain,(
% 0.38/0.71    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.38/0.71    inference(cnf_transformation,[],[f1])).
% 0.38/0.71  fof(f1,axiom,(
% 0.38/0.71    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.38/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.38/0.71  fof(f1076,plain,(
% 0.38/0.71    k2_xboole_0(sK2,k1_xboole_0) = k2_xboole_0(sK2,sK1) | ~spl4_70),
% 0.38/0.71    inference(superposition,[],[f30,f1066])).
% 0.38/0.71  fof(f1066,plain,(
% 0.38/0.71    k1_xboole_0 = k4_xboole_0(sK1,sK2) | ~spl4_70),
% 0.38/0.71    inference(avatar_component_clause,[],[f1065])).
% 0.38/0.71  fof(f1067,plain,(
% 0.38/0.71    spl4_70 | ~spl4_4 | ~spl4_37),
% 0.38/0.71    inference(avatar_split_clause,[],[f1063,f428,f52,f1065])).
% 0.38/0.71  fof(f428,plain,(
% 0.38/0.71    spl4_37 <=> sK1 = k4_xboole_0(sK1,sK3)),
% 0.38/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 0.38/0.71  fof(f1063,plain,(
% 0.38/0.71    k1_xboole_0 = k4_xboole_0(sK1,sK2) | (~spl4_4 | ~spl4_37)),
% 0.38/0.71    inference(forward_demodulation,[],[f1056,f136])).
% 0.38/0.71  fof(f1056,plain,(
% 0.38/0.71    k4_xboole_0(sK1,k2_xboole_0(sK0,sK1)) = k4_xboole_0(sK1,sK2) | (~spl4_4 | ~spl4_37)),
% 0.38/0.71    inference(superposition,[],[f604,f53])).
% 0.38/0.71  fof(f604,plain,(
% 0.38/0.71    ( ! [X0] : (k4_xboole_0(sK1,X0) = k4_xboole_0(sK1,k2_xboole_0(X0,sK3))) ) | ~spl4_37),
% 0.38/0.71    inference(superposition,[],[f446,f28])).
% 0.38/0.71  fof(f446,plain,(
% 0.38/0.71    ( ! [X0] : (k4_xboole_0(sK1,k2_xboole_0(sK3,X0)) = k4_xboole_0(sK1,X0)) ) | ~spl4_37),
% 0.38/0.71    inference(superposition,[],[f33,f429])).
% 0.38/0.71  fof(f429,plain,(
% 0.38/0.71    sK1 = k4_xboole_0(sK1,sK3) | ~spl4_37),
% 0.38/0.71    inference(avatar_component_clause,[],[f428])).
% 0.38/0.71  fof(f431,plain,(
% 0.38/0.71    spl4_37 | ~spl4_22),
% 0.38/0.71    inference(avatar_split_clause,[],[f426,f325,f428])).
% 0.38/0.71  fof(f325,plain,(
% 0.38/0.71    spl4_22 <=> sK1 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK3))),
% 0.38/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.38/0.71  fof(f426,plain,(
% 0.38/0.71    sK1 = k4_xboole_0(sK1,sK3) | ~spl4_22),
% 0.38/0.71    inference(superposition,[],[f55,f326])).
% 0.38/0.71  fof(f326,plain,(
% 0.38/0.71    sK1 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK3)) | ~spl4_22),
% 0.38/0.71    inference(avatar_component_clause,[],[f325])).
% 0.38/0.71  fof(f55,plain,(
% 0.38/0.71    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.38/0.71    inference(superposition,[],[f28,f26])).
% 0.38/0.71  fof(f352,plain,(
% 0.38/0.71    spl4_25 | ~spl4_23),
% 0.38/0.71    inference(avatar_split_clause,[],[f347,f329,f349])).
% 0.38/0.71  fof(f329,plain,(
% 0.38/0.71    spl4_23 <=> sK2 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK0))),
% 0.38/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.38/0.71  fof(f347,plain,(
% 0.38/0.71    sK2 = k4_xboole_0(sK2,sK0) | ~spl4_23),
% 0.38/0.71    inference(superposition,[],[f55,f330])).
% 0.38/0.71  fof(f330,plain,(
% 0.38/0.71    sK2 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK0)) | ~spl4_23),
% 0.38/0.71    inference(avatar_component_clause,[],[f329])).
% 0.38/0.71  fof(f331,plain,(
% 0.38/0.71    spl4_23 | ~spl4_6),
% 0.38/0.71    inference(avatar_split_clause,[],[f293,f81,f329])).
% 0.38/0.71  fof(f81,plain,(
% 0.38/0.71    spl4_6 <=> k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))),
% 0.38/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.38/0.71  fof(f293,plain,(
% 0.38/0.71    sK2 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK0)) | ~spl4_6),
% 0.38/0.71    inference(superposition,[],[f37,f82])).
% 0.38/0.71  fof(f82,plain,(
% 0.38/0.71    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) | ~spl4_6),
% 0.38/0.71    inference(avatar_component_clause,[],[f81])).
% 0.38/0.71  fof(f37,plain,(
% 0.38/0.71    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 0.38/0.71    inference(definition_unfolding,[],[f31,f29])).
% 0.38/0.71  fof(f31,plain,(
% 0.38/0.71    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 0.38/0.71    inference(cnf_transformation,[],[f11])).
% 0.38/0.71  fof(f11,axiom,(
% 0.38/0.71    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.38/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.38/0.71  fof(f327,plain,(
% 0.38/0.71    spl4_22 | ~spl4_14),
% 0.38/0.71    inference(avatar_split_clause,[],[f292,f197,f325])).
% 0.38/0.71  fof(f197,plain,(
% 0.38/0.71    spl4_14 <=> k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))),
% 0.38/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.38/0.71  fof(f292,plain,(
% 0.38/0.71    sK1 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK3)) | ~spl4_14),
% 0.38/0.71    inference(superposition,[],[f37,f198])).
% 0.38/0.71  fof(f198,plain,(
% 0.38/0.71    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) | ~spl4_14),
% 0.38/0.71    inference(avatar_component_clause,[],[f197])).
% 0.38/0.71  fof(f211,plain,(
% 0.38/0.71    spl4_14 | ~spl4_5),
% 0.38/0.71    inference(avatar_split_clause,[],[f189,f77,f197])).
% 0.38/0.71  fof(f77,plain,(
% 0.38/0.71    spl4_5 <=> k1_xboole_0 = k4_xboole_0(sK3,k4_xboole_0(sK3,sK1))),
% 0.38/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.38/0.71  fof(f189,plain,(
% 0.38/0.71    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) | ~spl4_5),
% 0.38/0.71    inference(superposition,[],[f78,f36])).
% 0.38/0.71  fof(f36,plain,(
% 0.38/0.71    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.38/0.71    inference(definition_unfolding,[],[f27,f29,f29])).
% 0.38/0.71  fof(f27,plain,(
% 0.38/0.71    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.38/0.71    inference(cnf_transformation,[],[f2])).
% 0.38/0.71  fof(f2,axiom,(
% 0.38/0.71    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.38/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.38/0.71  fof(f78,plain,(
% 0.38/0.71    k1_xboole_0 = k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) | ~spl4_5),
% 0.38/0.71    inference(avatar_component_clause,[],[f77])).
% 0.38/0.71  fof(f83,plain,(
% 0.38/0.71    spl4_6 | ~spl4_3),
% 0.38/0.71    inference(avatar_split_clause,[],[f75,f48,f81])).
% 0.38/0.71  fof(f48,plain,(
% 0.38/0.71    spl4_3 <=> r1_xboole_0(sK2,sK0)),
% 0.38/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.38/0.71  fof(f75,plain,(
% 0.38/0.71    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) | ~spl4_3),
% 0.38/0.71    inference(resolution,[],[f38,f49])).
% 0.38/0.71  fof(f49,plain,(
% 0.38/0.71    r1_xboole_0(sK2,sK0) | ~spl4_3),
% 0.38/0.71    inference(avatar_component_clause,[],[f48])).
% 0.38/0.71  fof(f38,plain,(
% 0.38/0.71    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.38/0.71    inference(definition_unfolding,[],[f32,f29])).
% 0.38/0.71  fof(f32,plain,(
% 0.38/0.71    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.38/0.71    inference(cnf_transformation,[],[f17])).
% 0.38/0.71  fof(f17,plain,(
% 0.38/0.71    ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 0.38/0.71    inference(ennf_transformation,[],[f14])).
% 0.38/0.71  fof(f14,plain,(
% 0.38/0.71    ! [X0,X1] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.38/0.71    inference(unused_predicate_definition_removal,[],[f3])).
% 0.38/0.71  fof(f3,axiom,(
% 0.38/0.71    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.38/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.38/0.71  fof(f79,plain,(
% 0.38/0.71    spl4_5 | ~spl4_2),
% 0.38/0.71    inference(avatar_split_clause,[],[f74,f44,f77])).
% 0.38/0.71  fof(f44,plain,(
% 0.38/0.71    spl4_2 <=> r1_xboole_0(sK3,sK1)),
% 0.38/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.38/0.71  fof(f74,plain,(
% 0.38/0.71    k1_xboole_0 = k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) | ~spl4_2),
% 0.38/0.71    inference(resolution,[],[f38,f45])).
% 0.38/0.71  fof(f45,plain,(
% 0.38/0.71    r1_xboole_0(sK3,sK1) | ~spl4_2),
% 0.38/0.71    inference(avatar_component_clause,[],[f44])).
% 0.38/0.71  fof(f54,plain,(
% 0.38/0.71    spl4_4),
% 0.38/0.71    inference(avatar_split_clause,[],[f20,f52])).
% 0.38/0.71  fof(f20,plain,(
% 0.38/0.71    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 0.38/0.71    inference(cnf_transformation,[],[f19])).
% 0.38/0.71  fof(f19,plain,(
% 0.38/0.71    sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 0.38/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f18])).
% 0.38/0.71  fof(f18,plain,(
% 0.38/0.71    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => (sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3))),
% 0.38/0.71    introduced(choice_axiom,[])).
% 0.38/0.71  fof(f16,plain,(
% 0.38/0.71    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3))),
% 0.38/0.71    inference(flattening,[],[f15])).
% 0.38/0.71  fof(f15,plain,(
% 0.38/0.71    ? [X0,X1,X2,X3] : (X1 != X2 & (r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)))),
% 0.38/0.71    inference(ennf_transformation,[],[f13])).
% 0.38/0.71  fof(f13,negated_conjecture,(
% 0.38/0.71    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 0.38/0.71    inference(negated_conjecture,[],[f12])).
% 0.38/0.71  fof(f12,conjecture,(
% 0.38/0.71    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 0.38/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).
% 0.38/0.71  fof(f50,plain,(
% 0.38/0.71    spl4_3),
% 0.38/0.71    inference(avatar_split_clause,[],[f21,f48])).
% 0.38/0.71  fof(f21,plain,(
% 0.38/0.71    r1_xboole_0(sK2,sK0)),
% 0.38/0.71    inference(cnf_transformation,[],[f19])).
% 0.38/0.71  fof(f46,plain,(
% 0.38/0.71    spl4_2),
% 0.38/0.71    inference(avatar_split_clause,[],[f22,f44])).
% 0.38/0.71  fof(f22,plain,(
% 0.38/0.71    r1_xboole_0(sK3,sK1)),
% 0.38/0.71    inference(cnf_transformation,[],[f19])).
% 0.38/0.71  fof(f42,plain,(
% 0.38/0.71    ~spl4_1),
% 0.38/0.71    inference(avatar_split_clause,[],[f23,f40])).
% 0.38/0.71  fof(f23,plain,(
% 0.38/0.71    sK1 != sK2),
% 0.38/0.71    inference(cnf_transformation,[],[f19])).
% 0.38/0.71  % SZS output end Proof for theBenchmark
% 0.38/0.71  % (11621)------------------------------
% 0.38/0.71  % (11621)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.38/0.71  % (11621)Termination reason: Refutation
% 0.38/0.71  
% 0.38/0.71  % (11621)Memory used [KB]: 11769
% 0.38/0.71  % (11621)Time elapsed: 0.122 s
% 0.38/0.71  % (11621)------------------------------
% 0.38/0.71  % (11621)------------------------------
% 0.38/0.72  % (11460)Success in time 0.35 s
%------------------------------------------------------------------------------
