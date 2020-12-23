%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:52 EST 2020

% Result     : Theorem 2.06s
% Output     : Refutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 132 expanded)
%              Number of leaves         :   18 (  46 expanded)
%              Depth                    :   11
%              Number of atoms          :  174 ( 262 expanded)
%              Number of equality atoms :   61 ( 109 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1354,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f87,f111,f200,f949,f1172,f1189,f1241,f1351])).

fof(f1351,plain,(
    ~ spl6_32 ),
    inference(avatar_contradiction_clause,[],[f1346])).

fof(f1346,plain,
    ( $false
    | ~ spl6_32 ),
    inference(resolution,[],[f1230,f94])).

fof(f94,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f91,f72])).

fof(f72,plain,(
    ! [X2] : r2_hidden(X2,k2_enumset1(X2,X2,X2,X2)) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k2_enumset1(X2,X2,X2,X2) != X1 ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f33,f54])).

fof(f54,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f23,f53])).

fof(f53,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f24,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f24,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f23,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X1,k1_xboole_0) ) ),
    inference(superposition,[],[f74,f22])).

fof(f22,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f74,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f1230,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f1228])).

fof(f1228,plain,
    ( spl6_32
  <=> r2_hidden(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f1241,plain,
    ( spl6_32
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f1207,f946,f1228])).

fof(f946,plain,
    ( spl6_20
  <=> k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f1207,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | ~ spl6_20 ),
    inference(superposition,[],[f81,f948])).

fof(f948,plain,
    ( k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f946])).

fof(f81,plain,(
    ! [X4,X2,X1] : r2_hidden(X4,k2_enumset1(X4,X4,X1,X2)) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X4,X2,X3,X1] :
      ( r2_hidden(X4,X3)
      | k2_enumset1(X4,X4,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 != X4
      | r2_hidden(X4,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f50,f37])).

fof(f50,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 != X4
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f1189,plain,(
    spl6_30 ),
    inference(avatar_contradiction_clause,[],[f1188])).

fof(f1188,plain,
    ( $false
    | spl6_30 ),
    inference(resolution,[],[f1171,f68])).

fof(f68,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1171,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl6_30 ),
    inference(avatar_component_clause,[],[f1169])).

fof(f1169,plain,
    ( spl6_30
  <=> r1_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f1172,plain,
    ( spl6_3
    | spl6_20
    | ~ spl6_30
    | ~ spl6_19 ),
    inference(avatar_split_clause,[],[f1166,f942,f1169,f946,f107])).

fof(f107,plain,
    ( spl6_3
  <=> r1_tarski(sK0,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f942,plain,
    ( spl6_19
  <=> sK0 = sK1(k2_enumset1(sK0,sK0,sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f1166,plain,
    ( ~ r1_tarski(sK0,sK0)
    | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | r1_tarski(sK0,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)))
    | ~ spl6_19 ),
    inference(superposition,[],[f26,f944])).

fof(f944,plain,
    ( sK0 = sK1(k2_enumset1(sK0,sK0,sK0,sK0),sK0)
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f942])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,sK1(X0,X1))
      | k1_xboole_0 = X0
      | r1_tarski(X1,k1_setfam_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X1,X2) )
     => ( r1_tarski(X1,k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_setfam_1)).

fof(f949,plain,
    ( spl6_19
    | spl6_20
    | spl6_3 ),
    inference(avatar_split_clause,[],[f931,f107,f946,f942])).

fof(f931,plain,
    ( k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | sK0 = sK1(k2_enumset1(sK0,sK0,sK0,sK0),sK0)
    | spl6_3 ),
    inference(resolution,[],[f155,f109])).

fof(f109,plain,
    ( ~ r1_tarski(sK0,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)))
    | spl6_3 ),
    inference(avatar_component_clause,[],[f107])).

fof(f155,plain,(
    ! [X19,X18] :
      ( r1_tarski(X19,k1_setfam_1(k2_enumset1(X18,X18,X18,X18)))
      | k1_xboole_0 = k2_enumset1(X18,X18,X18,X18)
      | sK1(k2_enumset1(X18,X18,X18,X18),X19) = X18 ) ),
    inference(resolution,[],[f25,f70])).

fof(f70,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k2_enumset1(X0,X0,X0,X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f34,f54])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | k1_xboole_0 = X0
      | r1_tarski(X1,k1_setfam_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f200,plain,(
    spl6_2 ),
    inference(avatar_contradiction_clause,[],[f195])).

fof(f195,plain,
    ( $false
    | spl6_2 ),
    inference(resolution,[],[f189,f105])).

fof(f105,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)),sK0)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl6_2
  <=> r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f189,plain,(
    ! [X0] : r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X0)),X0) ),
    inference(resolution,[],[f118,f68])).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X0)),X1) ) ),
    inference(resolution,[],[f38,f72])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X0,X2)
      | r1_tarski(k1_setfam_1(X1),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r2_hidden(X0,X1) )
     => r1_tarski(k1_setfam_1(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_setfam_1)).

fof(f111,plain,
    ( ~ spl6_3
    | ~ spl6_2
    | spl6_1 ),
    inference(avatar_split_clause,[],[f100,f84,f103,f107])).

fof(f84,plain,
    ( spl6_1
  <=> sK0 = k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f100,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)),sK0)
    | ~ r1_tarski(sK0,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)))
    | spl6_1 ),
    inference(extensionality_resolution,[],[f29,f86])).

fof(f86,plain,
    ( sK0 != k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f84])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f87,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f55,f84])).

fof(f55,plain,(
    sK0 != k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(definition_unfolding,[],[f21,f54])).

fof(f21,plain,(
    sK0 != k1_setfam_1(k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:43:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.14/0.52  % (14795)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.14/0.52  % (14810)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.14/0.52  % (14797)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.14/0.52  % (14795)Refutation not found, incomplete strategy% (14795)------------------------------
% 1.14/0.52  % (14795)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.14/0.52  % (14802)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.14/0.53  % (14796)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.14/0.53  % (14795)Termination reason: Refutation not found, incomplete strategy
% 1.14/0.53  
% 1.14/0.53  % (14795)Memory used [KB]: 1663
% 1.14/0.53  % (14795)Time elapsed: 0.101 s
% 1.14/0.53  % (14795)------------------------------
% 1.14/0.53  % (14795)------------------------------
% 1.14/0.53  % (14814)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.14/0.53  % (14803)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.14/0.54  % (14803)Refutation not found, incomplete strategy% (14803)------------------------------
% 1.14/0.54  % (14803)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.14/0.54  % (14803)Termination reason: Refutation not found, incomplete strategy
% 1.14/0.54  
% 1.14/0.54  % (14803)Memory used [KB]: 10618
% 1.14/0.54  % (14803)Time elapsed: 0.132 s
% 1.14/0.54  % (14803)------------------------------
% 1.14/0.54  % (14803)------------------------------
% 1.14/0.54  % (14809)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.14/0.54  % (14822)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.14/0.54  % (14797)Refutation not found, incomplete strategy% (14797)------------------------------
% 1.14/0.54  % (14797)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.14/0.54  % (14797)Termination reason: Refutation not found, incomplete strategy
% 1.14/0.54  
% 1.14/0.54  % (14797)Memory used [KB]: 10618
% 1.14/0.54  % (14797)Time elapsed: 0.128 s
% 1.14/0.54  % (14797)------------------------------
% 1.14/0.54  % (14797)------------------------------
% 1.14/0.54  % (14799)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.14/0.54  % (14801)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.14/0.54  % (14820)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.14/0.54  % (14800)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.36/0.55  % (14818)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.36/0.55  % (14798)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.36/0.55  % (14818)Refutation not found, incomplete strategy% (14818)------------------------------
% 1.36/0.55  % (14818)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.55  % (14818)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.55  
% 1.36/0.55  % (14818)Memory used [KB]: 1791
% 1.36/0.55  % (14818)Time elapsed: 0.116 s
% 1.36/0.55  % (14818)------------------------------
% 1.36/0.55  % (14818)------------------------------
% 1.36/0.55  % (14817)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.36/0.55  % (14823)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.36/0.55  % (14812)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.36/0.55  % (14824)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.36/0.55  % (14815)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.36/0.55  % (14816)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.36/0.56  % (14815)Refutation not found, incomplete strategy% (14815)------------------------------
% 1.36/0.56  % (14815)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.56  % (14815)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.56  
% 1.36/0.56  % (14815)Memory used [KB]: 10746
% 1.36/0.56  % (14815)Time elapsed: 0.151 s
% 1.36/0.56  % (14815)------------------------------
% 1.36/0.56  % (14815)------------------------------
% 1.36/0.56  % (14816)Refutation not found, incomplete strategy% (14816)------------------------------
% 1.36/0.56  % (14816)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.56  % (14816)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.56  
% 1.36/0.56  % (14816)Memory used [KB]: 1663
% 1.36/0.56  % (14816)Time elapsed: 0.151 s
% 1.36/0.56  % (14816)------------------------------
% 1.36/0.56  % (14816)------------------------------
% 1.36/0.56  % (14808)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.36/0.56  % (14804)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.36/0.56  % (14807)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.36/0.56  % (14813)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.36/0.56  % (14806)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.36/0.57  % (14819)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.36/0.57  % (14805)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.36/0.57  % (14805)Refutation not found, incomplete strategy% (14805)------------------------------
% 1.36/0.57  % (14805)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.57  % (14805)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.57  
% 1.36/0.57  % (14805)Memory used [KB]: 10618
% 1.36/0.57  % (14805)Time elapsed: 0.140 s
% 1.36/0.57  % (14805)------------------------------
% 1.36/0.57  % (14805)------------------------------
% 1.36/0.57  % (14811)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.36/0.57  % (14821)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.36/0.59  % (14806)Refutation not found, incomplete strategy% (14806)------------------------------
% 1.36/0.59  % (14806)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.59  % (14806)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.59  
% 1.36/0.59  % (14806)Memory used [KB]: 10746
% 1.36/0.59  % (14806)Time elapsed: 0.166 s
% 1.36/0.59  % (14806)------------------------------
% 1.36/0.59  % (14806)------------------------------
% 2.06/0.65  % (14836)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.06/0.67  % (14835)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.06/0.67  % (14835)Refutation not found, incomplete strategy% (14835)------------------------------
% 2.06/0.67  % (14835)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.06/0.67  % (14835)Termination reason: Refutation not found, incomplete strategy
% 2.06/0.67  
% 2.06/0.67  % (14835)Memory used [KB]: 6140
% 2.06/0.67  % (14835)Time elapsed: 0.113 s
% 2.06/0.67  % (14835)------------------------------
% 2.06/0.67  % (14835)------------------------------
% 2.06/0.67  % (14837)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.06/0.68  % (14839)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.06/0.68  % (14838)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.06/0.69  % (14811)Refutation found. Thanks to Tanya!
% 2.06/0.69  % SZS status Theorem for theBenchmark
% 2.06/0.69  % SZS output start Proof for theBenchmark
% 2.06/0.69  fof(f1354,plain,(
% 2.06/0.69    $false),
% 2.06/0.69    inference(avatar_sat_refutation,[],[f87,f111,f200,f949,f1172,f1189,f1241,f1351])).
% 2.06/0.69  fof(f1351,plain,(
% 2.06/0.69    ~spl6_32),
% 2.06/0.69    inference(avatar_contradiction_clause,[],[f1346])).
% 2.06/0.69  fof(f1346,plain,(
% 2.06/0.69    $false | ~spl6_32),
% 2.06/0.69    inference(resolution,[],[f1230,f94])).
% 2.06/0.69  fof(f94,plain,(
% 2.06/0.69    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 2.06/0.69    inference(resolution,[],[f91,f72])).
% 2.06/0.69  fof(f72,plain,(
% 2.06/0.69    ( ! [X2] : (r2_hidden(X2,k2_enumset1(X2,X2,X2,X2))) )),
% 2.06/0.69    inference(equality_resolution,[],[f71])).
% 2.06/0.69  fof(f71,plain,(
% 2.06/0.69    ( ! [X2,X1] : (r2_hidden(X2,X1) | k2_enumset1(X2,X2,X2,X2) != X1) )),
% 2.06/0.69    inference(equality_resolution,[],[f59])).
% 2.06/0.69  fof(f59,plain,(
% 2.06/0.69    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 2.06/0.69    inference(definition_unfolding,[],[f33,f54])).
% 2.06/0.69  fof(f54,plain,(
% 2.06/0.69    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 2.06/0.69    inference(definition_unfolding,[],[f23,f53])).
% 2.06/0.69  fof(f53,plain,(
% 2.06/0.69    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.06/0.69    inference(definition_unfolding,[],[f24,f37])).
% 2.06/0.69  fof(f37,plain,(
% 2.06/0.69    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.06/0.69    inference(cnf_transformation,[],[f9])).
% 2.06/0.69  fof(f9,axiom,(
% 2.06/0.69    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.06/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 2.06/0.69  fof(f24,plain,(
% 2.06/0.69    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.06/0.69    inference(cnf_transformation,[],[f8])).
% 2.06/0.69  fof(f8,axiom,(
% 2.06/0.69    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.06/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.06/0.69  fof(f23,plain,(
% 2.06/0.69    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 2.06/0.69    inference(cnf_transformation,[],[f7])).
% 2.06/0.69  fof(f7,axiom,(
% 2.06/0.69    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 2.06/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 2.06/0.69  fof(f33,plain,(
% 2.06/0.69    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 2.06/0.69    inference(cnf_transformation,[],[f6])).
% 2.06/0.69  fof(f6,axiom,(
% 2.06/0.69    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.06/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 2.06/0.69  fof(f91,plain,(
% 2.06/0.69    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X1,k1_xboole_0)) )),
% 2.06/0.69    inference(superposition,[],[f74,f22])).
% 2.06/0.69  fof(f22,plain,(
% 2.06/0.69    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.06/0.69    inference(cnf_transformation,[],[f4])).
% 2.06/0.69  fof(f4,axiom,(
% 2.06/0.69    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.06/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 2.06/0.69  fof(f74,plain,(
% 2.06/0.69    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | ~r2_hidden(X3,X1)) )),
% 2.06/0.69    inference(equality_resolution,[],[f43])).
% 2.06/0.69  fof(f43,plain,(
% 2.06/0.69    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.06/0.69    inference(cnf_transformation,[],[f2])).
% 2.06/0.69  fof(f2,axiom,(
% 2.06/0.69    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.06/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 2.06/0.69  fof(f1230,plain,(
% 2.06/0.69    r2_hidden(sK0,k1_xboole_0) | ~spl6_32),
% 2.06/0.69    inference(avatar_component_clause,[],[f1228])).
% 2.06/0.69  fof(f1228,plain,(
% 2.06/0.69    spl6_32 <=> r2_hidden(sK0,k1_xboole_0)),
% 2.06/0.69    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).
% 2.06/0.69  fof(f1241,plain,(
% 2.06/0.69    spl6_32 | ~spl6_20),
% 2.06/0.69    inference(avatar_split_clause,[],[f1207,f946,f1228])).
% 2.06/0.69  fof(f946,plain,(
% 2.06/0.69    spl6_20 <=> k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 2.06/0.69    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 2.06/0.69  fof(f1207,plain,(
% 2.06/0.69    r2_hidden(sK0,k1_xboole_0) | ~spl6_20),
% 2.06/0.69    inference(superposition,[],[f81,f948])).
% 2.06/0.69  fof(f948,plain,(
% 2.06/0.69    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | ~spl6_20),
% 2.06/0.69    inference(avatar_component_clause,[],[f946])).
% 2.06/0.69  fof(f81,plain,(
% 2.06/0.69    ( ! [X4,X2,X1] : (r2_hidden(X4,k2_enumset1(X4,X4,X1,X2))) )),
% 2.06/0.69    inference(equality_resolution,[],[f80])).
% 2.06/0.69  fof(f80,plain,(
% 2.06/0.69    ( ! [X4,X2,X3,X1] : (r2_hidden(X4,X3) | k2_enumset1(X4,X4,X1,X2) != X3) )),
% 2.06/0.69    inference(equality_resolution,[],[f62])).
% 2.06/0.69  fof(f62,plain,(
% 2.06/0.69    ( ! [X4,X2,X0,X3,X1] : (X0 != X4 | r2_hidden(X4,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 2.06/0.69    inference(definition_unfolding,[],[f50,f37])).
% 2.06/0.69  fof(f50,plain,(
% 2.06/0.69    ( ! [X4,X2,X0,X3,X1] : (X0 != X4 | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 2.06/0.69    inference(cnf_transformation,[],[f20])).
% 2.06/0.69  fof(f20,plain,(
% 2.06/0.69    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 2.06/0.69    inference(ennf_transformation,[],[f5])).
% 2.06/0.69  fof(f5,axiom,(
% 2.06/0.69    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 2.06/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 2.06/0.69  fof(f1189,plain,(
% 2.06/0.69    spl6_30),
% 2.06/0.69    inference(avatar_contradiction_clause,[],[f1188])).
% 2.06/0.69  fof(f1188,plain,(
% 2.06/0.69    $false | spl6_30),
% 2.06/0.69    inference(resolution,[],[f1171,f68])).
% 2.06/0.69  fof(f68,plain,(
% 2.06/0.69    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.06/0.69    inference(equality_resolution,[],[f28])).
% 2.06/0.69  fof(f28,plain,(
% 2.06/0.69    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.06/0.69    inference(cnf_transformation,[],[f3])).
% 2.06/0.69  fof(f3,axiom,(
% 2.06/0.69    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.06/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.06/0.69  fof(f1171,plain,(
% 2.06/0.69    ~r1_tarski(sK0,sK0) | spl6_30),
% 2.06/0.69    inference(avatar_component_clause,[],[f1169])).
% 2.06/0.69  fof(f1169,plain,(
% 2.06/0.69    spl6_30 <=> r1_tarski(sK0,sK0)),
% 2.06/0.69    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 2.06/0.69  fof(f1172,plain,(
% 2.06/0.69    spl6_3 | spl6_20 | ~spl6_30 | ~spl6_19),
% 2.06/0.69    inference(avatar_split_clause,[],[f1166,f942,f1169,f946,f107])).
% 2.06/0.69  fof(f107,plain,(
% 2.06/0.69    spl6_3 <=> r1_tarski(sK0,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)))),
% 2.06/0.69    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 2.06/0.69  fof(f942,plain,(
% 2.06/0.69    spl6_19 <=> sK0 = sK1(k2_enumset1(sK0,sK0,sK0,sK0),sK0)),
% 2.06/0.69    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 2.06/0.69  fof(f1166,plain,(
% 2.06/0.69    ~r1_tarski(sK0,sK0) | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | r1_tarski(sK0,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0))) | ~spl6_19),
% 2.06/0.69    inference(superposition,[],[f26,f944])).
% 2.06/0.69  fof(f944,plain,(
% 2.06/0.69    sK0 = sK1(k2_enumset1(sK0,sK0,sK0,sK0),sK0) | ~spl6_19),
% 2.06/0.69    inference(avatar_component_clause,[],[f942])).
% 2.06/0.69  fof(f26,plain,(
% 2.06/0.69    ( ! [X0,X1] : (~r1_tarski(X1,sK1(X0,X1)) | k1_xboole_0 = X0 | r1_tarski(X1,k1_setfam_1(X0))) )),
% 2.06/0.69    inference(cnf_transformation,[],[f16])).
% 2.06/0.69  fof(f16,plain,(
% 2.06/0.69    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 2.06/0.69    inference(flattening,[],[f15])).
% 2.06/0.69  fof(f15,plain,(
% 2.06/0.69    ! [X0,X1] : ((r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0) | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 2.06/0.69    inference(ennf_transformation,[],[f10])).
% 2.06/0.69  fof(f10,axiom,(
% 2.06/0.69    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X1,X2)) => (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 2.06/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_setfam_1)).
% 2.06/0.69  fof(f949,plain,(
% 2.06/0.69    spl6_19 | spl6_20 | spl6_3),
% 2.06/0.69    inference(avatar_split_clause,[],[f931,f107,f946,f942])).
% 2.06/0.69  fof(f931,plain,(
% 2.06/0.69    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | sK0 = sK1(k2_enumset1(sK0,sK0,sK0,sK0),sK0) | spl6_3),
% 2.06/0.69    inference(resolution,[],[f155,f109])).
% 2.06/0.69  fof(f109,plain,(
% 2.06/0.69    ~r1_tarski(sK0,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0))) | spl6_3),
% 2.06/0.69    inference(avatar_component_clause,[],[f107])).
% 2.06/0.69  fof(f155,plain,(
% 2.06/0.69    ( ! [X19,X18] : (r1_tarski(X19,k1_setfam_1(k2_enumset1(X18,X18,X18,X18))) | k1_xboole_0 = k2_enumset1(X18,X18,X18,X18) | sK1(k2_enumset1(X18,X18,X18,X18),X19) = X18) )),
% 2.06/0.69    inference(resolution,[],[f25,f70])).
% 2.06/0.69  fof(f70,plain,(
% 2.06/0.69    ( ! [X2,X0] : (~r2_hidden(X2,k2_enumset1(X0,X0,X0,X0)) | X0 = X2) )),
% 2.06/0.69    inference(equality_resolution,[],[f58])).
% 2.06/0.69  fof(f58,plain,(
% 2.06/0.69    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 2.06/0.69    inference(definition_unfolding,[],[f34,f54])).
% 2.06/0.69  fof(f34,plain,(
% 2.06/0.69    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 2.06/0.69    inference(cnf_transformation,[],[f6])).
% 2.06/0.69  fof(f25,plain,(
% 2.06/0.69    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | k1_xboole_0 = X0 | r1_tarski(X1,k1_setfam_1(X0))) )),
% 2.06/0.69    inference(cnf_transformation,[],[f16])).
% 2.06/0.69  fof(f200,plain,(
% 2.06/0.69    spl6_2),
% 2.06/0.69    inference(avatar_contradiction_clause,[],[f195])).
% 2.06/0.69  fof(f195,plain,(
% 2.06/0.69    $false | spl6_2),
% 2.06/0.69    inference(resolution,[],[f189,f105])).
% 2.06/0.69  fof(f105,plain,(
% 2.06/0.69    ~r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)),sK0) | spl6_2),
% 2.06/0.69    inference(avatar_component_clause,[],[f103])).
% 2.06/0.69  fof(f103,plain,(
% 2.06/0.69    spl6_2 <=> r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)),sK0)),
% 2.06/0.69    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 2.06/0.69  fof(f189,plain,(
% 2.06/0.69    ( ! [X0] : (r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X0)),X0)) )),
% 2.06/0.69    inference(resolution,[],[f118,f68])).
% 2.06/0.69  fof(f118,plain,(
% 2.06/0.69    ( ! [X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X0)),X1)) )),
% 2.06/0.69    inference(resolution,[],[f38,f72])).
% 2.06/0.69  fof(f38,plain,(
% 2.06/0.69    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X0,X2) | r1_tarski(k1_setfam_1(X1),X2)) )),
% 2.06/0.69    inference(cnf_transformation,[],[f19])).
% 2.06/0.69  fof(f19,plain,(
% 2.06/0.69    ! [X0,X1,X2] : (r1_tarski(k1_setfam_1(X1),X2) | ~r1_tarski(X0,X2) | ~r2_hidden(X0,X1))),
% 2.06/0.69    inference(flattening,[],[f18])).
% 2.06/0.69  fof(f18,plain,(
% 2.06/0.69    ! [X0,X1,X2] : (r1_tarski(k1_setfam_1(X1),X2) | (~r1_tarski(X0,X2) | ~r2_hidden(X0,X1)))),
% 2.06/0.69    inference(ennf_transformation,[],[f11])).
% 2.06/0.69  fof(f11,axiom,(
% 2.06/0.69    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r2_hidden(X0,X1)) => r1_tarski(k1_setfam_1(X1),X2))),
% 2.06/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_setfam_1)).
% 2.06/0.69  fof(f111,plain,(
% 2.06/0.69    ~spl6_3 | ~spl6_2 | spl6_1),
% 2.06/0.69    inference(avatar_split_clause,[],[f100,f84,f103,f107])).
% 2.06/0.69  fof(f84,plain,(
% 2.06/0.69    spl6_1 <=> sK0 = k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0))),
% 2.06/0.69    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 2.06/0.69  fof(f100,plain,(
% 2.06/0.69    ~r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)),sK0) | ~r1_tarski(sK0,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0))) | spl6_1),
% 2.06/0.69    inference(extensionality_resolution,[],[f29,f86])).
% 2.06/0.69  fof(f86,plain,(
% 2.06/0.69    sK0 != k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)) | spl6_1),
% 2.06/0.69    inference(avatar_component_clause,[],[f84])).
% 2.06/0.69  fof(f29,plain,(
% 2.06/0.69    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 2.06/0.69    inference(cnf_transformation,[],[f3])).
% 2.06/0.69  fof(f87,plain,(
% 2.06/0.69    ~spl6_1),
% 2.06/0.69    inference(avatar_split_clause,[],[f55,f84])).
% 2.06/0.69  fof(f55,plain,(
% 2.06/0.69    sK0 != k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0))),
% 2.06/0.69    inference(definition_unfolding,[],[f21,f54])).
% 2.06/0.69  fof(f21,plain,(
% 2.06/0.69    sK0 != k1_setfam_1(k1_tarski(sK0))),
% 2.06/0.69    inference(cnf_transformation,[],[f14])).
% 2.06/0.69  fof(f14,plain,(
% 2.06/0.69    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0),
% 2.06/0.69    inference(ennf_transformation,[],[f13])).
% 2.06/0.69  fof(f13,negated_conjecture,(
% 2.06/0.69    ~! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 2.06/0.69    inference(negated_conjecture,[],[f12])).
% 2.06/0.69  fof(f12,conjecture,(
% 2.06/0.69    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 2.06/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).
% 2.06/0.69  % SZS output end Proof for theBenchmark
% 2.06/0.69  % (14811)------------------------------
% 2.06/0.69  % (14811)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.06/0.69  % (14811)Termination reason: Refutation
% 2.06/0.69  
% 2.06/0.69  % (14811)Memory used [KB]: 12025
% 2.06/0.69  % (14811)Time elapsed: 0.281 s
% 2.06/0.69  % (14811)------------------------------
% 2.06/0.69  % (14811)------------------------------
% 2.06/0.69  % (14786)Success in time 0.319 s
%------------------------------------------------------------------------------
