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
% DateTime   : Thu Dec  3 12:37:53 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 517 expanded)
%              Number of leaves         :   23 ( 187 expanded)
%              Depth                    :   17
%              Number of atoms          :  178 ( 689 expanded)
%              Number of equality atoms :  109 ( 576 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f467,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f62,f71,f76,f81,f124,f148,f153,f426,f427,f442])).

fof(f442,plain,
    ( spl3_2
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f441,f121,f73,f64])).

fof(f64,plain,
    ( spl3_2
  <=> sK2 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f73,plain,
    ( spl3_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f121,plain,
    ( spl3_7
  <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(sK1,k4_xboole_0(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f441,plain,
    ( sK2 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f440,f24])).

fof(f24,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f440,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k4_xboole_0(sK2,k1_xboole_0)
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f429,f335])).

fof(f335,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f333,f24])).

fof(f333,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(resolution,[],[f329,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    inference(backward_demodulation,[],[f51,f50])).

fof(f50,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f31,f41])).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f29,f40])).

fof(f40,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f30,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f36,f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f36,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f30,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

% (3492)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X1 ) ),
    inference(definition_unfolding,[],[f32,f41])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f329,plain,(
    ! [X10] : r1_tarski(k1_xboole_0,X10) ),
    inference(forward_demodulation,[],[f322,f23])).

fof(f23,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

% (3482)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% (3466)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% (3486)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% (3493)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% (3478)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% (3484)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% (3485)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% (3483)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% (3476)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% (3477)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% (3476)Refutation not found, incomplete strategy% (3476)------------------------------
% (3476)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (3476)Termination reason: Refutation not found, incomplete strategy

% (3476)Memory used [KB]: 10618
% (3476)Time elapsed: 0.141 s
% (3476)------------------------------
% (3476)------------------------------
% (3487)Refutation not found, incomplete strategy% (3487)------------------------------
% (3487)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (3474)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% (3487)Termination reason: Refutation not found, incomplete strategy

% (3487)Memory used [KB]: 10746
% (3487)Time elapsed: 0.140 s
% (3487)------------------------------
% (3487)------------------------------
% (3490)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% (3467)Refutation not found, incomplete strategy% (3467)------------------------------
% (3467)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f322,plain,(
    ! [X10] : r1_tarski(k1_xboole_0,k5_xboole_0(X10,k1_xboole_0)) ),
    inference(superposition,[],[f314,f196])).

fof(f196,plain,(
    ! [X5] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X5) ),
    inference(forward_demodulation,[],[f182,f24])).

fof(f182,plain,(
    ! [X5] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k1_xboole_0,k1_xboole_0),X5) ),
    inference(superposition,[],[f175,f94])).

fof(f94,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f85,f24])).

fof(f85,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(backward_demodulation,[],[f48,f50])).

fof(f48,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f27,f41])).

fof(f27,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f175,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    inference(forward_demodulation,[],[f55,f50])).

fof(f55,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(definition_unfolding,[],[f37,f41])).

fof(f37,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f314,plain,(
    ! [X8,X7] : r1_tarski(X7,k5_xboole_0(X8,k4_xboole_0(X7,X8))) ),
    inference(forward_demodulation,[],[f303,f50])).

fof(f303,plain,(
    ! [X8,X7] : r1_tarski(X7,k3_tarski(k3_enumset1(X8,X8,X8,X8,X7))) ),
    inference(superposition,[],[f86,f164])).

fof(f164,plain,(
    ! [X4,X5] : k5_xboole_0(X4,k4_xboole_0(X5,X4)) = k3_tarski(k3_enumset1(X5,X5,X5,X5,X4)) ),
    inference(superposition,[],[f49,f50])).

fof(f49,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) ),
    inference(definition_unfolding,[],[f28,f41,f41])).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f86,plain,(
    ! [X0,X1] : r1_tarski(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(backward_demodulation,[],[f47,f50])).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f26,f41])).

fof(f26,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f429,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(sK2,k1_xboole_0))
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(backward_demodulation,[],[f123,f74])).

fof(f74,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f73])).

fof(f123,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(sK1,k4_xboole_0(sK2,sK1))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f121])).

fof(f427,plain,
    ( spl3_5
    | spl3_9
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f421,f121,f150,f78])).

fof(f78,plain,
    ( spl3_5
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f150,plain,
    ( spl3_9
  <=> sK2 = k5_xboole_0(sK1,k4_xboole_0(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f421,plain,
    ( sK2 = k5_xboole_0(sK1,k4_xboole_0(sK2,sK1))
    | k1_xboole_0 = sK2
    | ~ spl3_7 ),
    inference(resolution,[],[f218,f314])).

fof(f218,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k5_xboole_0(sK1,k4_xboole_0(sK2,sK1)))
        | k5_xboole_0(sK1,k4_xboole_0(sK2,sK1)) = X0
        | k1_xboole_0 = X0 )
    | ~ spl3_7 ),
    inference(superposition,[],[f54,f123])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1))
      | k3_enumset1(X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f33,f42,f42])).

fof(f42,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f25,f40])).

fof(f25,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f426,plain,
    ( spl3_4
    | spl3_8
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f420,f121,f145,f73])).

fof(f145,plain,
    ( spl3_8
  <=> sK1 = k5_xboole_0(sK1,k4_xboole_0(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f420,plain,
    ( sK1 = k5_xboole_0(sK1,k4_xboole_0(sK2,sK1))
    | k1_xboole_0 = sK1
    | ~ spl3_7 ),
    inference(resolution,[],[f218,f86])).

fof(f153,plain,
    ( ~ spl3_9
    | spl3_2
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f140,f121,f64,f150])).

fof(f140,plain,
    ( sK2 != k5_xboole_0(sK1,k4_xboole_0(sK2,sK1))
    | spl3_2
    | ~ spl3_7 ),
    inference(superposition,[],[f66,f123])).

fof(f66,plain,
    ( sK2 != k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f64])).

fof(f148,plain,
    ( ~ spl3_8
    | spl3_3
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f139,f121,f68,f145])).

fof(f68,plain,
    ( spl3_3
  <=> sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f139,plain,
    ( sK1 != k5_xboole_0(sK1,k4_xboole_0(sK2,sK1))
    | spl3_3
    | ~ spl3_7 ),
    inference(superposition,[],[f70,f123])).

fof(f70,plain,
    ( sK1 != k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f68])).

fof(f124,plain,
    ( spl3_7
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f119,f59,f121])).

fof(f59,plain,
    ( spl3_1
  <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f119,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(sK1,k4_xboole_0(sK2,sK1))
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f61,f50])).

fof(f61,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK2))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f81,plain,
    ( ~ spl3_5
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f46,f68,f78])).

fof(f46,plain,
    ( sK1 != k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | k1_xboole_0 != sK2 ),
    inference(definition_unfolding,[],[f19,f42])).

fof(f19,plain,
    ( sK1 != k1_tarski(sK0)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f76,plain,
    ( ~ spl3_2
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f45,f73,f64])).

fof(f45,plain,
    ( k1_xboole_0 != sK1
    | sK2 != k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f20,f42])).

fof(f20,plain,
    ( k1_xboole_0 != sK1
    | sK2 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f71,plain,
    ( ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f44,f68,f64])).

fof(f44,plain,
    ( sK1 != k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | sK2 != k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f21,f42,f42])).

fof(f21,plain,
    ( sK1 != k1_tarski(sK0)
    | sK2 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f62,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f43,f59])).

fof(f43,plain,(
    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f22,f42,f41])).

fof(f22,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:51:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.52  % (3481)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.52  % (3471)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (3489)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.53  % (3487)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (3470)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (3473)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % (3467)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (3488)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (3479)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (3473)Refutation not found, incomplete strategy% (3473)------------------------------
% 0.21/0.54  % (3473)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (3480)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (3473)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (3473)Memory used [KB]: 10746
% 0.21/0.54  % (3473)Time elapsed: 0.120 s
% 0.21/0.54  % (3473)------------------------------
% 0.21/0.54  % (3473)------------------------------
% 0.21/0.54  % (3465)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (3480)Refutation not found, incomplete strategy% (3480)------------------------------
% 0.21/0.54  % (3480)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (3480)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (3480)Memory used [KB]: 6140
% 0.21/0.54  % (3480)Time elapsed: 0.002 s
% 0.21/0.54  % (3480)------------------------------
% 0.21/0.54  % (3480)------------------------------
% 0.21/0.54  % (3468)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (3469)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (3472)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (3494)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (3481)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f467,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f62,f71,f76,f81,f124,f148,f153,f426,f427,f442])).
% 0.21/0.54  fof(f442,plain,(
% 0.21/0.54    spl3_2 | ~spl3_4 | ~spl3_7),
% 0.21/0.54    inference(avatar_split_clause,[],[f441,f121,f73,f64])).
% 0.21/0.54  fof(f64,plain,(
% 0.21/0.54    spl3_2 <=> sK2 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.54  fof(f73,plain,(
% 0.21/0.54    spl3_4 <=> k1_xboole_0 = sK1),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.54  fof(f121,plain,(
% 0.21/0.54    spl3_7 <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(sK1,k4_xboole_0(sK2,sK1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.54  fof(f441,plain,(
% 0.21/0.54    sK2 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) | (~spl3_4 | ~spl3_7)),
% 0.21/0.54    inference(forward_demodulation,[],[f440,f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.54  fof(f440,plain,(
% 0.21/0.54    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k4_xboole_0(sK2,k1_xboole_0) | (~spl3_4 | ~spl3_7)),
% 0.21/0.54    inference(forward_demodulation,[],[f429,f335])).
% 0.21/0.54  fof(f335,plain,(
% 0.21/0.54    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.21/0.54    inference(forward_demodulation,[],[f333,f24])).
% 0.21/0.54  fof(f333,plain,(
% 0.21/0.54    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0)) = X0) )),
% 0.21/0.54    inference(resolution,[],[f329,f84])).
% 0.21/0.54  fof(f84,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X1) )),
% 0.21/0.54    inference(backward_demodulation,[],[f51,f50])).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 0.21/0.54    inference(definition_unfolding,[],[f31,f41])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 0.21/0.54    inference(definition_unfolding,[],[f29,f40])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f30,f39])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f36,f38])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,axiom,(
% 0.21/0.54    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,axiom,(
% 0.21/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f14])).
% 0.21/0.54  fof(f14,axiom,(
% 0.21/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.21/0.54  % (3492)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X1) )),
% 0.21/0.54    inference(definition_unfolding,[],[f32,f41])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f18])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.54  fof(f329,plain,(
% 0.21/0.54    ( ! [X10] : (r1_tarski(k1_xboole_0,X10)) )),
% 0.21/0.54    inference(forward_demodulation,[],[f322,f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.21/0.54  % (3482)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (3466)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.55  % (3486)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (3493)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  % (3478)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.55  % (3484)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (3485)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (3483)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (3476)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (3477)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (3476)Refutation not found, incomplete strategy% (3476)------------------------------
% 0.21/0.55  % (3476)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (3476)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (3476)Memory used [KB]: 10618
% 0.21/0.55  % (3476)Time elapsed: 0.141 s
% 0.21/0.55  % (3476)------------------------------
% 0.21/0.55  % (3476)------------------------------
% 0.21/0.55  % (3487)Refutation not found, incomplete strategy% (3487)------------------------------
% 0.21/0.55  % (3487)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (3474)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.55  % (3487)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (3487)Memory used [KB]: 10746
% 0.21/0.55  % (3487)Time elapsed: 0.140 s
% 0.21/0.55  % (3487)------------------------------
% 0.21/0.55  % (3487)------------------------------
% 0.21/0.55  % (3490)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.49/0.56  % (3467)Refutation not found, incomplete strategy% (3467)------------------------------
% 1.49/0.56  % (3467)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.56  fof(f322,plain,(
% 1.49/0.56    ( ! [X10] : (r1_tarski(k1_xboole_0,k5_xboole_0(X10,k1_xboole_0))) )),
% 1.49/0.56    inference(superposition,[],[f314,f196])).
% 1.49/0.56  fof(f196,plain,(
% 1.49/0.56    ( ! [X5] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X5)) )),
% 1.49/0.56    inference(forward_demodulation,[],[f182,f24])).
% 1.49/0.56  fof(f182,plain,(
% 1.49/0.56    ( ! [X5] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k1_xboole_0,k1_xboole_0),X5)) )),
% 1.49/0.56    inference(superposition,[],[f175,f94])).
% 1.49/0.56  fof(f94,plain,(
% 1.49/0.56    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0))) )),
% 1.49/0.56    inference(superposition,[],[f85,f24])).
% 1.49/0.56  fof(f85,plain,(
% 1.49/0.56    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 1.49/0.56    inference(backward_demodulation,[],[f48,f50])).
% 1.49/0.56  fof(f48,plain,(
% 1.49/0.56    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 1.49/0.56    inference(definition_unfolding,[],[f27,f41])).
% 1.49/0.56  fof(f27,plain,(
% 1.49/0.56    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 1.49/0.56    inference(cnf_transformation,[],[f5])).
% 1.49/0.56  fof(f5,axiom,(
% 1.49/0.56    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 1.49/0.56  fof(f175,plain,(
% 1.49/0.56    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1)))) )),
% 1.49/0.56    inference(forward_demodulation,[],[f55,f50])).
% 1.49/0.56  fof(f55,plain,(
% 1.49/0.56    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))) )),
% 1.49/0.56    inference(definition_unfolding,[],[f37,f41])).
% 1.49/0.56  fof(f37,plain,(
% 1.49/0.56    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.49/0.56    inference(cnf_transformation,[],[f4])).
% 1.49/0.56  fof(f4,axiom,(
% 1.49/0.56    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 1.49/0.56  fof(f314,plain,(
% 1.49/0.56    ( ! [X8,X7] : (r1_tarski(X7,k5_xboole_0(X8,k4_xboole_0(X7,X8)))) )),
% 1.49/0.56    inference(forward_demodulation,[],[f303,f50])).
% 1.49/0.56  fof(f303,plain,(
% 1.49/0.56    ( ! [X8,X7] : (r1_tarski(X7,k3_tarski(k3_enumset1(X8,X8,X8,X8,X7)))) )),
% 1.49/0.56    inference(superposition,[],[f86,f164])).
% 1.49/0.56  fof(f164,plain,(
% 1.49/0.56    ( ! [X4,X5] : (k5_xboole_0(X4,k4_xboole_0(X5,X4)) = k3_tarski(k3_enumset1(X5,X5,X5,X5,X4))) )),
% 1.49/0.56    inference(superposition,[],[f49,f50])).
% 1.49/0.56  fof(f49,plain,(
% 1.49/0.56    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0))) )),
% 1.49/0.56    inference(definition_unfolding,[],[f28,f41,f41])).
% 1.49/0.56  fof(f28,plain,(
% 1.49/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f1])).
% 1.49/0.56  fof(f1,axiom,(
% 1.49/0.56    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.49/0.56  fof(f86,plain,(
% 1.49/0.56    ( ! [X0,X1] : (r1_tarski(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 1.49/0.56    inference(backward_demodulation,[],[f47,f50])).
% 1.49/0.56  fof(f47,plain,(
% 1.49/0.56    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 1.49/0.56    inference(definition_unfolding,[],[f26,f41])).
% 1.49/0.56  fof(f26,plain,(
% 1.49/0.56    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.49/0.56    inference(cnf_transformation,[],[f7])).
% 1.49/0.56  fof(f7,axiom,(
% 1.49/0.56    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.49/0.56  fof(f429,plain,(
% 1.49/0.56    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(sK2,k1_xboole_0)) | (~spl3_4 | ~spl3_7)),
% 1.49/0.56    inference(backward_demodulation,[],[f123,f74])).
% 1.49/0.56  fof(f74,plain,(
% 1.49/0.56    k1_xboole_0 = sK1 | ~spl3_4),
% 1.49/0.56    inference(avatar_component_clause,[],[f73])).
% 1.49/0.56  fof(f123,plain,(
% 1.49/0.56    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(sK1,k4_xboole_0(sK2,sK1)) | ~spl3_7),
% 1.49/0.56    inference(avatar_component_clause,[],[f121])).
% 1.49/0.56  fof(f427,plain,(
% 1.49/0.56    spl3_5 | spl3_9 | ~spl3_7),
% 1.49/0.56    inference(avatar_split_clause,[],[f421,f121,f150,f78])).
% 1.49/0.56  fof(f78,plain,(
% 1.49/0.56    spl3_5 <=> k1_xboole_0 = sK2),
% 1.49/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.49/0.56  fof(f150,plain,(
% 1.49/0.56    spl3_9 <=> sK2 = k5_xboole_0(sK1,k4_xboole_0(sK2,sK1))),
% 1.49/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 1.49/0.56  fof(f421,plain,(
% 1.49/0.56    sK2 = k5_xboole_0(sK1,k4_xboole_0(sK2,sK1)) | k1_xboole_0 = sK2 | ~spl3_7),
% 1.49/0.56    inference(resolution,[],[f218,f314])).
% 1.49/0.56  fof(f218,plain,(
% 1.49/0.56    ( ! [X0] : (~r1_tarski(X0,k5_xboole_0(sK1,k4_xboole_0(sK2,sK1))) | k5_xboole_0(sK1,k4_xboole_0(sK2,sK1)) = X0 | k1_xboole_0 = X0) ) | ~spl3_7),
% 1.49/0.56    inference(superposition,[],[f54,f123])).
% 1.49/0.56  fof(f54,plain,(
% 1.49/0.56    ( ! [X0,X1] : (~r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1)) | k3_enumset1(X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0) )),
% 1.49/0.56    inference(definition_unfolding,[],[f33,f42,f42])).
% 1.49/0.56  fof(f42,plain,(
% 1.49/0.56    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.49/0.56    inference(definition_unfolding,[],[f25,f40])).
% 1.49/0.56  fof(f25,plain,(
% 1.49/0.56    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f9])).
% 1.49/0.56  fof(f9,axiom,(
% 1.49/0.56    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.49/0.56  fof(f33,plain,(
% 1.49/0.56    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 1.49/0.56    inference(cnf_transformation,[],[f13])).
% 1.49/0.56  fof(f13,axiom,(
% 1.49/0.56    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.49/0.56  fof(f426,plain,(
% 1.49/0.56    spl3_4 | spl3_8 | ~spl3_7),
% 1.49/0.56    inference(avatar_split_clause,[],[f420,f121,f145,f73])).
% 1.49/0.56  fof(f145,plain,(
% 1.49/0.56    spl3_8 <=> sK1 = k5_xboole_0(sK1,k4_xboole_0(sK2,sK1))),
% 1.49/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 1.49/0.56  fof(f420,plain,(
% 1.49/0.56    sK1 = k5_xboole_0(sK1,k4_xboole_0(sK2,sK1)) | k1_xboole_0 = sK1 | ~spl3_7),
% 1.49/0.56    inference(resolution,[],[f218,f86])).
% 1.49/0.56  fof(f153,plain,(
% 1.49/0.56    ~spl3_9 | spl3_2 | ~spl3_7),
% 1.49/0.56    inference(avatar_split_clause,[],[f140,f121,f64,f150])).
% 1.49/0.56  fof(f140,plain,(
% 1.49/0.56    sK2 != k5_xboole_0(sK1,k4_xboole_0(sK2,sK1)) | (spl3_2 | ~spl3_7)),
% 1.49/0.56    inference(superposition,[],[f66,f123])).
% 1.49/0.56  fof(f66,plain,(
% 1.49/0.56    sK2 != k3_enumset1(sK0,sK0,sK0,sK0,sK0) | spl3_2),
% 1.49/0.56    inference(avatar_component_clause,[],[f64])).
% 1.49/0.56  fof(f148,plain,(
% 1.49/0.56    ~spl3_8 | spl3_3 | ~spl3_7),
% 1.49/0.56    inference(avatar_split_clause,[],[f139,f121,f68,f145])).
% 1.49/0.56  fof(f68,plain,(
% 1.49/0.56    spl3_3 <=> sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 1.49/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.49/0.56  fof(f139,plain,(
% 1.49/0.56    sK1 != k5_xboole_0(sK1,k4_xboole_0(sK2,sK1)) | (spl3_3 | ~spl3_7)),
% 1.49/0.56    inference(superposition,[],[f70,f123])).
% 1.49/0.56  fof(f70,plain,(
% 1.49/0.56    sK1 != k3_enumset1(sK0,sK0,sK0,sK0,sK0) | spl3_3),
% 1.49/0.56    inference(avatar_component_clause,[],[f68])).
% 1.49/0.56  fof(f124,plain,(
% 1.49/0.56    spl3_7 | ~spl3_1),
% 1.49/0.56    inference(avatar_split_clause,[],[f119,f59,f121])).
% 1.49/0.56  fof(f59,plain,(
% 1.49/0.56    spl3_1 <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK2))),
% 1.49/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.49/0.56  fof(f119,plain,(
% 1.49/0.56    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(sK1,k4_xboole_0(sK2,sK1)) | ~spl3_1),
% 1.49/0.56    inference(forward_demodulation,[],[f61,f50])).
% 1.49/0.56  fof(f61,plain,(
% 1.49/0.56    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK2)) | ~spl3_1),
% 1.49/0.56    inference(avatar_component_clause,[],[f59])).
% 1.49/0.56  fof(f81,plain,(
% 1.49/0.56    ~spl3_5 | ~spl3_3),
% 1.49/0.56    inference(avatar_split_clause,[],[f46,f68,f78])).
% 1.49/0.56  fof(f46,plain,(
% 1.49/0.56    sK1 != k3_enumset1(sK0,sK0,sK0,sK0,sK0) | k1_xboole_0 != sK2),
% 1.49/0.56    inference(definition_unfolding,[],[f19,f42])).
% 1.49/0.56  fof(f19,plain,(
% 1.49/0.56    sK1 != k1_tarski(sK0) | k1_xboole_0 != sK2),
% 1.49/0.56    inference(cnf_transformation,[],[f17])).
% 1.49/0.56  fof(f17,plain,(
% 1.49/0.56    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 1.49/0.56    inference(ennf_transformation,[],[f16])).
% 1.49/0.56  fof(f16,negated_conjecture,(
% 1.49/0.56    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 1.49/0.56    inference(negated_conjecture,[],[f15])).
% 1.49/0.56  fof(f15,conjecture,(
% 1.49/0.56    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 1.49/0.56  fof(f76,plain,(
% 1.49/0.56    ~spl3_2 | ~spl3_4),
% 1.49/0.56    inference(avatar_split_clause,[],[f45,f73,f64])).
% 1.49/0.56  fof(f45,plain,(
% 1.49/0.56    k1_xboole_0 != sK1 | sK2 != k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 1.49/0.56    inference(definition_unfolding,[],[f20,f42])).
% 1.49/0.56  fof(f20,plain,(
% 1.49/0.56    k1_xboole_0 != sK1 | sK2 != k1_tarski(sK0)),
% 1.49/0.56    inference(cnf_transformation,[],[f17])).
% 1.49/0.56  fof(f71,plain,(
% 1.49/0.56    ~spl3_2 | ~spl3_3),
% 1.49/0.56    inference(avatar_split_clause,[],[f44,f68,f64])).
% 1.49/0.56  fof(f44,plain,(
% 1.49/0.56    sK1 != k3_enumset1(sK0,sK0,sK0,sK0,sK0) | sK2 != k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 1.49/0.56    inference(definition_unfolding,[],[f21,f42,f42])).
% 1.49/0.56  fof(f21,plain,(
% 1.49/0.56    sK1 != k1_tarski(sK0) | sK2 != k1_tarski(sK0)),
% 1.49/0.56    inference(cnf_transformation,[],[f17])).
% 1.49/0.56  fof(f62,plain,(
% 1.49/0.56    spl3_1),
% 1.49/0.56    inference(avatar_split_clause,[],[f43,f59])).
% 1.49/0.56  fof(f43,plain,(
% 1.49/0.56    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK2))),
% 1.49/0.56    inference(definition_unfolding,[],[f22,f42,f41])).
% 1.49/0.56  fof(f22,plain,(
% 1.49/0.56    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.49/0.56    inference(cnf_transformation,[],[f17])).
% 1.49/0.56  % SZS output end Proof for theBenchmark
% 1.49/0.56  % (3481)------------------------------
% 1.49/0.56  % (3481)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.56  % (3481)Termination reason: Refutation
% 1.49/0.56  
% 1.49/0.56  % (3481)Memory used [KB]: 11001
% 1.49/0.56  % (3481)Time elapsed: 0.129 s
% 1.49/0.56  % (3481)------------------------------
% 1.49/0.56  % (3481)------------------------------
% 1.49/0.56  % (3467)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.56  
% 1.49/0.56  % (3467)Memory used [KB]: 10746
% 1.49/0.56  % (3467)Time elapsed: 0.127 s
% 1.49/0.56  % (3467)------------------------------
% 1.49/0.56  % (3467)------------------------------
% 1.49/0.56  % (3486)Refutation not found, incomplete strategy% (3486)------------------------------
% 1.49/0.56  % (3486)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.56  % (3486)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.56  
% 1.49/0.56  % (3486)Memory used [KB]: 1791
% 1.49/0.56  % (3486)Time elapsed: 0.153 s
% 1.49/0.56  % (3486)------------------------------
% 1.49/0.56  % (3486)------------------------------
% 1.49/0.56  % (3464)Success in time 0.186 s
%------------------------------------------------------------------------------
