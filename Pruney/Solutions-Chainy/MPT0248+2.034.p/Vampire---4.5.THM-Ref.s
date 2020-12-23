%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:54 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 286 expanded)
%              Number of leaves         :   21 ( 117 expanded)
%              Depth                    :    9
%              Number of atoms          :  176 ( 479 expanded)
%              Number of equality atoms :   86 ( 329 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f194,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f56,f61,f66,f72,f96,f139,f142,f154,f161,f166,f184,f190,f193])).

fof(f193,plain,
    ( spl3_17
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f191,f181,f187])).

fof(f187,plain,
    ( spl3_17
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f181,plain,
    ( spl3_16
  <=> sK1 = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f191,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl3_16 ),
    inference(superposition,[],[f87,f183])).

fof(f183,plain,
    ( sK1 = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f181])).

fof(f87,plain,(
    ! [X2,X3] : r1_tarski(X2,k3_tarski(k2_enumset1(X3,X3,X3,X2))) ),
    inference(superposition,[],[f35,f36])).

fof(f36,plain,(
    ! [X0,X1] : k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(X1,X1,X1,X0)) ),
    inference(definition_unfolding,[],[f20,f29,f29])).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f21,f28])).

fof(f28,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f22,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f22,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f19,f29])).

fof(f19,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f190,plain,
    ( ~ spl3_17
    | ~ spl3_3
    | spl3_14 ),
    inference(avatar_split_clause,[],[f185,f151,f53,f187])).

fof(f53,plain,
    ( spl3_3
  <=> sK1 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f151,plain,
    ( spl3_14
  <=> r1_tarski(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f185,plain,
    ( ~ r1_tarski(sK2,sK1)
    | ~ spl3_3
    | spl3_14 ),
    inference(forward_demodulation,[],[f152,f54])).

fof(f54,plain,
    ( sK1 = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f53])).

fof(f152,plain,
    ( ~ r1_tarski(sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | spl3_14 ),
    inference(avatar_component_clause,[],[f151])).

fof(f184,plain,
    ( spl3_16
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f179,f53,f44,f181])).

fof(f44,plain,
    ( spl3_1
  <=> k2_enumset1(sK0,sK0,sK0,sK0) = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f179,plain,
    ( sK1 = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2))
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f46,f54])).

fof(f46,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f44])).

fof(f166,plain,
    ( spl3_9
    | ~ spl3_5
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f165,f101,f63,f106])).

fof(f106,plain,
    ( spl3_9
  <=> k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f63,plain,
    ( spl3_5
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f101,plain,
    ( spl3_8
  <=> k2_enumset1(sK0,sK0,sK0,sK0) = k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f165,plain,
    ( k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl3_5
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f163,f81])).

fof(f81,plain,(
    ! [X2] : k3_tarski(k2_enumset1(X2,X2,X2,k1_xboole_0)) = X2 ),
    inference(forward_demodulation,[],[f74,f17])).

fof(f17,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f74,plain,(
    ! [X2] : k3_tarski(k2_enumset1(X2,X2,X2,k1_xboole_0)) = k4_xboole_0(X2,k1_xboole_0) ),
    inference(superposition,[],[f37,f17])).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k3_tarski(k2_enumset1(X0,X0,X0,X1)),X1) ),
    inference(definition_unfolding,[],[f23,f29])).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f163,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | ~ spl3_5
    | ~ spl3_8 ),
    inference(backward_demodulation,[],[f103,f64])).

fof(f64,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f63])).

fof(f103,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,sK2))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f101])).

fof(f161,plain,
    ( spl3_5
    | spl3_2
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f160,f151,f49,f63])).

fof(f49,plain,
    ( spl3_2
  <=> sK2 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f160,plain,
    ( sK2 = k2_enumset1(sK0,sK0,sK0,sK0)
    | k1_xboole_0 = sK2
    | ~ spl3_14 ),
    inference(resolution,[],[f153,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
      | k2_enumset1(X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f24,f30,f30])).

fof(f30,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f18,f28])).

fof(f18,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f153,plain,
    ( r1_tarski(sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f151])).

fof(f154,plain,
    ( spl3_14
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f147,f101,f151])).

fof(f147,plain,
    ( r1_tarski(sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl3_8 ),
    inference(superposition,[],[f87,f103])).

% (30153)Refutation not found, incomplete strategy% (30153)------------------------------
% (30153)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f142,plain,
    ( spl3_8
    | ~ spl3_1
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f141,f58,f44,f101])).

% (30153)Termination reason: Refutation not found, incomplete strategy

% (30153)Memory used [KB]: 10618
% (30153)Time elapsed: 0.098 s
% (30153)------------------------------
% (30153)------------------------------
fof(f58,plain,
    ( spl3_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f141,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,sK2))
    | ~ spl3_1
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f46,f59])).

fof(f59,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f58])).

fof(f139,plain,
    ( ~ spl3_9
    | spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f138,f58,f53,f106])).

fof(f138,plain,
    ( k1_xboole_0 != k2_enumset1(sK0,sK0,sK0,sK0)
    | spl3_3
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f55,f59])).

fof(f55,plain,
    ( sK1 != k2_enumset1(sK0,sK0,sK0,sK0)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f53])).

fof(f96,plain,
    ( spl3_4
    | spl3_3
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f95,f69,f53,f58])).

fof(f69,plain,
    ( spl3_6
  <=> r1_tarski(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

% (30148)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f95,plain,
    ( sK1 = k2_enumset1(sK0,sK0,sK0,sK0)
    | k1_xboole_0 = sK1
    | ~ spl3_6 ),
    inference(resolution,[],[f40,f71])).

fof(f71,plain,
    ( r1_tarski(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f69])).

fof(f72,plain,
    ( spl3_6
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f67,f44,f69])).

fof(f67,plain,
    ( r1_tarski(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl3_1 ),
    inference(superposition,[],[f35,f46])).

fof(f66,plain,
    ( ~ spl3_5
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f34,f53,f63])).

fof(f34,plain,
    ( sK1 != k2_enumset1(sK0,sK0,sK0,sK0)
    | k1_xboole_0 != sK2 ),
    inference(definition_unfolding,[],[f13,f30])).

fof(f13,plain,
    ( sK1 != k1_tarski(sK0)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f61,plain,
    ( ~ spl3_2
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f33,f58,f49])).

fof(f33,plain,
    ( k1_xboole_0 != sK1
    | sK2 != k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f14,f30])).

fof(f14,plain,
    ( k1_xboole_0 != sK1
    | sK2 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f56,plain,
    ( ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f32,f53,f49])).

fof(f32,plain,
    ( sK1 != k2_enumset1(sK0,sK0,sK0,sK0)
    | sK2 != k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f15,f30,f30])).

fof(f15,plain,
    ( sK1 != k1_tarski(sK0)
    | sK2 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f47,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f31,f44])).

fof(f31,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f16,f30,f29])).

fof(f16,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.15  % Command    : run_vampire %s %d
% 0.15/0.36  % Computer   : n022.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 11:46:11 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.21/0.50  % (30143)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (30143)Refutation not found, incomplete strategy% (30143)------------------------------
% 0.21/0.51  % (30143)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (30143)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (30143)Memory used [KB]: 1663
% 0.21/0.51  % (30143)Time elapsed: 0.088 s
% 0.21/0.51  % (30143)------------------------------
% 0.21/0.51  % (30143)------------------------------
% 0.21/0.51  % (30156)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.51  % (30161)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.51  % (30168)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (30169)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (30160)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (30151)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (30160)Refutation not found, incomplete strategy% (30160)------------------------------
% 0.21/0.52  % (30160)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (30160)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (30160)Memory used [KB]: 6140
% 0.21/0.52  % (30160)Time elapsed: 0.004 s
% 0.21/0.52  % (30160)------------------------------
% 0.21/0.52  % (30160)------------------------------
% 0.21/0.52  % (30156)Refutation not found, incomplete strategy% (30156)------------------------------
% 0.21/0.52  % (30156)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (30161)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % (30168)Refutation not found, incomplete strategy% (30168)------------------------------
% 0.21/0.52  % (30168)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (30150)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (30168)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (30168)Memory used [KB]: 10746
% 0.21/0.52  % (30168)Time elapsed: 0.058 s
% 0.21/0.52  % (30168)------------------------------
% 0.21/0.52  % (30168)------------------------------
% 0.21/0.53  % (30145)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (30157)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (30156)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (30156)Memory used [KB]: 10618
% 0.21/0.53  % (30156)Time elapsed: 0.095 s
% 0.21/0.53  % (30156)------------------------------
% 0.21/0.53  % (30156)------------------------------
% 0.21/0.53  % (30153)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f194,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f47,f56,f61,f66,f72,f96,f139,f142,f154,f161,f166,f184,f190,f193])).
% 0.21/0.53  fof(f193,plain,(
% 0.21/0.53    spl3_17 | ~spl3_16),
% 0.21/0.53    inference(avatar_split_clause,[],[f191,f181,f187])).
% 0.21/0.53  fof(f187,plain,(
% 0.21/0.53    spl3_17 <=> r1_tarski(sK2,sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.53  fof(f181,plain,(
% 0.21/0.53    spl3_16 <=> sK1 = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.53  fof(f191,plain,(
% 0.21/0.53    r1_tarski(sK2,sK1) | ~spl3_16),
% 0.21/0.53    inference(superposition,[],[f87,f183])).
% 0.21/0.53  fof(f183,plain,(
% 0.21/0.53    sK1 = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2)) | ~spl3_16),
% 0.21/0.53    inference(avatar_component_clause,[],[f181])).
% 0.21/0.53  fof(f87,plain,(
% 0.21/0.53    ( ! [X2,X3] : (r1_tarski(X2,k3_tarski(k2_enumset1(X3,X3,X3,X2)))) )),
% 0.21/0.53    inference(superposition,[],[f35,f36])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(X1,X1,X1,X0))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f20,f29,f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f21,f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f22,f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1)))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f19,f29])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.53  fof(f190,plain,(
% 0.21/0.53    ~spl3_17 | ~spl3_3 | spl3_14),
% 0.21/0.53    inference(avatar_split_clause,[],[f185,f151,f53,f187])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    spl3_3 <=> sK1 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.53  fof(f151,plain,(
% 0.21/0.53    spl3_14 <=> r1_tarski(sK2,k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.53  fof(f185,plain,(
% 0.21/0.53    ~r1_tarski(sK2,sK1) | (~spl3_3 | spl3_14)),
% 0.21/0.53    inference(forward_demodulation,[],[f152,f54])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    sK1 = k2_enumset1(sK0,sK0,sK0,sK0) | ~spl3_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f53])).
% 0.21/0.53  fof(f152,plain,(
% 0.21/0.53    ~r1_tarski(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | spl3_14),
% 0.21/0.53    inference(avatar_component_clause,[],[f151])).
% 0.21/0.53  fof(f184,plain,(
% 0.21/0.53    spl3_16 | ~spl3_1 | ~spl3_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f179,f53,f44,f181])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    spl3_1 <=> k2_enumset1(sK0,sK0,sK0,sK0) = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.53  fof(f179,plain,(
% 0.21/0.53    sK1 = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2)) | (~spl3_1 | ~spl3_3)),
% 0.21/0.53    inference(forward_demodulation,[],[f46,f54])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    k2_enumset1(sK0,sK0,sK0,sK0) = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2)) | ~spl3_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f44])).
% 0.21/0.53  fof(f166,plain,(
% 0.21/0.53    spl3_9 | ~spl3_5 | ~spl3_8),
% 0.21/0.53    inference(avatar_split_clause,[],[f165,f101,f63,f106])).
% 0.21/0.53  fof(f106,plain,(
% 0.21/0.53    spl3_9 <=> k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    spl3_5 <=> k1_xboole_0 = sK2),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.53  fof(f101,plain,(
% 0.21/0.53    spl3_8 <=> k2_enumset1(sK0,sK0,sK0,sK0) = k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,sK2))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.53  fof(f165,plain,(
% 0.21/0.53    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | (~spl3_5 | ~spl3_8)),
% 0.21/0.53    inference(forward_demodulation,[],[f163,f81])).
% 0.21/0.53  fof(f81,plain,(
% 0.21/0.53    ( ! [X2] : (k3_tarski(k2_enumset1(X2,X2,X2,k1_xboole_0)) = X2) )),
% 0.21/0.53    inference(forward_demodulation,[],[f74,f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.53  fof(f74,plain,(
% 0.21/0.53    ( ! [X2] : (k3_tarski(k2_enumset1(X2,X2,X2,k1_xboole_0)) = k4_xboole_0(X2,k1_xboole_0)) )),
% 0.21/0.53    inference(superposition,[],[f37,f17])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k3_tarski(k2_enumset1(X0,X0,X0,X1)),X1)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f23,f29])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 0.21/0.53  fof(f163,plain,(
% 0.21/0.53    k2_enumset1(sK0,sK0,sK0,sK0) = k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) | (~spl3_5 | ~spl3_8)),
% 0.21/0.53    inference(backward_demodulation,[],[f103,f64])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    k1_xboole_0 = sK2 | ~spl3_5),
% 0.21/0.53    inference(avatar_component_clause,[],[f63])).
% 0.21/0.53  fof(f103,plain,(
% 0.21/0.53    k2_enumset1(sK0,sK0,sK0,sK0) = k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,sK2)) | ~spl3_8),
% 0.21/0.53    inference(avatar_component_clause,[],[f101])).
% 0.21/0.53  fof(f161,plain,(
% 0.21/0.53    spl3_5 | spl3_2 | ~spl3_14),
% 0.21/0.53    inference(avatar_split_clause,[],[f160,f151,f49,f63])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    spl3_2 <=> sK2 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.53  fof(f160,plain,(
% 0.21/0.53    sK2 = k2_enumset1(sK0,sK0,sK0,sK0) | k1_xboole_0 = sK2 | ~spl3_14),
% 0.21/0.53    inference(resolution,[],[f153,f40])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) | k2_enumset1(X1,X1,X1,X1) = X0 | k1_xboole_0 = X0) )),
% 0.21/0.53    inference(definition_unfolding,[],[f24,f30,f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f18,f28])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 0.21/0.53  fof(f153,plain,(
% 0.21/0.53    r1_tarski(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl3_14),
% 0.21/0.53    inference(avatar_component_clause,[],[f151])).
% 0.21/0.53  fof(f154,plain,(
% 0.21/0.53    spl3_14 | ~spl3_8),
% 0.21/0.53    inference(avatar_split_clause,[],[f147,f101,f151])).
% 0.21/0.53  fof(f147,plain,(
% 0.21/0.53    r1_tarski(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl3_8),
% 0.21/0.53    inference(superposition,[],[f87,f103])).
% 0.21/0.53  % (30153)Refutation not found, incomplete strategy% (30153)------------------------------
% 0.21/0.53  % (30153)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  fof(f142,plain,(
% 0.21/0.53    spl3_8 | ~spl3_1 | ~spl3_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f141,f58,f44,f101])).
% 0.21/0.53  % (30153)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (30153)Memory used [KB]: 10618
% 0.21/0.53  % (30153)Time elapsed: 0.098 s
% 0.21/0.53  % (30153)------------------------------
% 0.21/0.53  % (30153)------------------------------
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    spl3_4 <=> k1_xboole_0 = sK1),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.53  fof(f141,plain,(
% 0.21/0.53    k2_enumset1(sK0,sK0,sK0,sK0) = k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,sK2)) | (~spl3_1 | ~spl3_4)),
% 0.21/0.53    inference(forward_demodulation,[],[f46,f59])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    k1_xboole_0 = sK1 | ~spl3_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f58])).
% 0.21/0.53  fof(f139,plain,(
% 0.21/0.53    ~spl3_9 | spl3_3 | ~spl3_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f138,f58,f53,f106])).
% 0.21/0.53  fof(f138,plain,(
% 0.21/0.53    k1_xboole_0 != k2_enumset1(sK0,sK0,sK0,sK0) | (spl3_3 | ~spl3_4)),
% 0.21/0.53    inference(forward_demodulation,[],[f55,f59])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    sK1 != k2_enumset1(sK0,sK0,sK0,sK0) | spl3_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f53])).
% 0.21/0.53  fof(f96,plain,(
% 0.21/0.53    spl3_4 | spl3_3 | ~spl3_6),
% 0.21/0.53    inference(avatar_split_clause,[],[f95,f69,f53,f58])).
% 0.21/0.53  fof(f69,plain,(
% 0.21/0.53    spl3_6 <=> r1_tarski(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.53  % (30148)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  fof(f95,plain,(
% 0.21/0.53    sK1 = k2_enumset1(sK0,sK0,sK0,sK0) | k1_xboole_0 = sK1 | ~spl3_6),
% 0.21/0.53    inference(resolution,[],[f40,f71])).
% 0.21/0.53  fof(f71,plain,(
% 0.21/0.53    r1_tarski(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl3_6),
% 0.21/0.53    inference(avatar_component_clause,[],[f69])).
% 0.21/0.53  fof(f72,plain,(
% 0.21/0.53    spl3_6 | ~spl3_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f67,f44,f69])).
% 0.21/0.53  fof(f67,plain,(
% 0.21/0.53    r1_tarski(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl3_1),
% 0.21/0.53    inference(superposition,[],[f35,f46])).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    ~spl3_5 | ~spl3_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f34,f53,f63])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    sK1 != k2_enumset1(sK0,sK0,sK0,sK0) | k1_xboole_0 != sK2),
% 0.21/0.53    inference(definition_unfolding,[],[f13,f30])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    sK1 != k1_tarski(sK0) | k1_xboole_0 != sK2),
% 0.21/0.53    inference(cnf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,plain,(
% 0.21/0.53    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.21/0.53    inference(ennf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.21/0.53    inference(negated_conjecture,[],[f10])).
% 0.21/0.53  fof(f10,conjecture,(
% 0.21/0.53    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    ~spl3_2 | ~spl3_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f33,f58,f49])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    k1_xboole_0 != sK1 | sK2 != k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.21/0.53    inference(definition_unfolding,[],[f14,f30])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    k1_xboole_0 != sK1 | sK2 != k1_tarski(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f12])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    ~spl3_2 | ~spl3_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f32,f53,f49])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    sK1 != k2_enumset1(sK0,sK0,sK0,sK0) | sK2 != k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.21/0.53    inference(definition_unfolding,[],[f15,f30,f30])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    sK1 != k1_tarski(sK0) | sK2 != k1_tarski(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f12])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    spl3_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f31,f44])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    k2_enumset1(sK0,sK0,sK0,sK0) = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2))),
% 0.21/0.53    inference(definition_unfolding,[],[f16,f30,f29])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f12])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (30161)------------------------------
% 0.21/0.53  % (30161)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (30161)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (30161)Memory used [KB]: 10746
% 0.21/0.53  % (30161)Time elapsed: 0.115 s
% 0.21/0.53  % (30161)------------------------------
% 0.21/0.53  % (30161)------------------------------
% 0.21/0.53  % (30149)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (30136)Success in time 0.157 s
%------------------------------------------------------------------------------
