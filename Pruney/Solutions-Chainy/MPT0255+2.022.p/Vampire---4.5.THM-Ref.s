%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:37 EST 2020

% Result     : Theorem 1.60s
% Output     : Refutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 267 expanded)
%              Number of leaves         :   16 (  88 expanded)
%              Depth                    :   15
%              Number of atoms          :  129 ( 331 expanded)
%              Number of equality atoms :   84 ( 283 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f260,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f243,f245,f254])).

fof(f254,plain,(
    ~ spl3_1 ),
    inference(avatar_contradiction_clause,[],[f253])).

fof(f253,plain,
    ( $false
    | ~ spl3_1 ),
    inference(trivial_inequality_removal,[],[f249])).

fof(f249,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl3_1 ),
    inference(superposition,[],[f246,f188])).

fof(f188,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f131,f25])).

fof(f25,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f131,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X0),X1) ),
    inference(superposition,[],[f50,f48])).

fof(f48,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f28,f44])).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f30,f43])).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f31,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f31,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f28,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f50,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2))) ),
    inference(definition_unfolding,[],[f37,f44])).

fof(f37,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f246,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_xboole_0,k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl3_1 ),
    inference(resolution,[],[f97,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | k4_xboole_0(X1,X0) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X1,X0) != k1_xboole_0
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( k4_xboole_0(X1,X0) = k1_xboole_0
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_xboole_1)).

fof(f97,plain,
    ( r2_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k1_xboole_0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f95])).

% (18150)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
fof(f95,plain,
    ( spl3_1
  <=> r2_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f245,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f244,f99,f95])).

fof(f99,plain,
    ( spl3_2
  <=> k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f244,plain,
    ( k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | r2_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k1_xboole_0) ),
    inference(resolution,[],[f90,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f90,plain,(
    r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k1_xboole_0) ),
    inference(superposition,[],[f58,f63])).

fof(f63,plain,(
    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK1) ),
    inference(superposition,[],[f62,f25])).

fof(f62,plain,(
    k1_xboole_0 = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k1_xboole_0) ),
    inference(superposition,[],[f48,f46])).

fof(f46,plain,(
    k1_xboole_0 = k3_tarski(k2_enumset1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK0,sK0,sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f24,f44,f43])).

fof(f24,plain,(
    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2)
   => k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).

fof(f58,plain,(
    ! [X2,X1] : r1_tarski(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X1,X1,X1,X2)) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_enumset1(X1,X1,X1,X2))
      | k2_enumset1(X2,X2,X2,X2) != X0 ) ),
    inference(definition_unfolding,[],[f41,f43,f45])).

fof(f45,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f26,f43])).

fof(f26,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X2) != X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(f243,plain,(
    ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f242])).

fof(f242,plain,
    ( $false
    | ~ spl3_2 ),
    inference(trivial_inequality_removal,[],[f241])).

fof(f241,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl3_2 ),
    inference(superposition,[],[f236,f82])).

fof(f82,plain,(
    k1_xboole_0 = k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f66,f79])).

fof(f79,plain,(
    k1_xboole_0 = sK2 ),
    inference(superposition,[],[f78,f25])).

fof(f78,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[],[f71,f66])).

fof(f71,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X0))) ),
    inference(superposition,[],[f48,f49])).

fof(f49,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f29,f43,f43])).

fof(f29,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f66,plain,(
    k1_xboole_0 = k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,sK2)) ),
    inference(backward_demodulation,[],[f46,f63])).

fof(f236,plain,
    ( ! [X4] : k1_xboole_0 != k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X4))
    | ~ spl3_2 ),
    inference(superposition,[],[f47,f101])).

fof(f101,plain,
    ( k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f99])).

fof(f47,plain,(
    ! [X0,X1] : k1_xboole_0 != k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),X1)) ),
    inference(definition_unfolding,[],[f27,f44,f45])).

fof(f27,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:02:44 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.55  % (18144)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.56  % (18135)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.56  % (18144)Refutation not found, incomplete strategy% (18144)------------------------------
% 0.21/0.56  % (18144)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.57  % (18135)Refutation found. Thanks to Tanya!
% 1.60/0.57  % SZS status Theorem for theBenchmark
% 1.60/0.57  % (18144)Termination reason: Refutation not found, incomplete strategy
% 1.60/0.57  
% 1.60/0.57  % (18144)Memory used [KB]: 10618
% 1.60/0.57  % (18144)Time elapsed: 0.127 s
% 1.60/0.57  % (18144)------------------------------
% 1.60/0.57  % (18144)------------------------------
% 1.60/0.57  % (18138)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.60/0.57  % (18137)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.60/0.57  % (18160)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.60/0.57  % (18142)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.60/0.58  % (18145)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.60/0.58  % SZS output start Proof for theBenchmark
% 1.60/0.58  fof(f260,plain,(
% 1.60/0.58    $false),
% 1.60/0.58    inference(avatar_sat_refutation,[],[f243,f245,f254])).
% 1.60/0.58  fof(f254,plain,(
% 1.60/0.58    ~spl3_1),
% 1.60/0.58    inference(avatar_contradiction_clause,[],[f253])).
% 1.60/0.58  fof(f253,plain,(
% 1.60/0.58    $false | ~spl3_1),
% 1.60/0.58    inference(trivial_inequality_removal,[],[f249])).
% 1.60/0.58  fof(f249,plain,(
% 1.60/0.58    k1_xboole_0 != k1_xboole_0 | ~spl3_1),
% 1.60/0.58    inference(superposition,[],[f246,f188])).
% 1.60/0.58  fof(f188,plain,(
% 1.60/0.58    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.60/0.58    inference(superposition,[],[f131,f25])).
% 1.60/0.58  fof(f25,plain,(
% 1.60/0.58    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.60/0.58    inference(cnf_transformation,[],[f3])).
% 1.60/0.58  fof(f3,axiom,(
% 1.60/0.58    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.60/0.58  fof(f131,plain,(
% 1.60/0.58    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X0),X1)) )),
% 1.60/0.58    inference(superposition,[],[f50,f48])).
% 1.60/0.58  fof(f48,plain,(
% 1.60/0.58    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1)))) )),
% 1.60/0.58    inference(definition_unfolding,[],[f28,f44])).
% 1.60/0.58  fof(f44,plain,(
% 1.60/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 1.60/0.58    inference(definition_unfolding,[],[f30,f43])).
% 1.60/0.58  fof(f43,plain,(
% 1.60/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.60/0.58    inference(definition_unfolding,[],[f31,f36])).
% 1.60/0.58  fof(f36,plain,(
% 1.60/0.58    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f9])).
% 1.60/0.58  fof(f9,axiom,(
% 1.60/0.58    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.60/0.58  fof(f31,plain,(
% 1.60/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f8])).
% 1.60/0.58  fof(f8,axiom,(
% 1.60/0.58    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.60/0.58  fof(f30,plain,(
% 1.60/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.60/0.58    inference(cnf_transformation,[],[f11])).
% 1.60/0.58  fof(f11,axiom,(
% 1.60/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.60/0.58  fof(f28,plain,(
% 1.60/0.58    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 1.60/0.58    inference(cnf_transformation,[],[f5])).
% 1.60/0.58  fof(f5,axiom,(
% 1.60/0.58    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 1.60/0.58  fof(f50,plain,(
% 1.60/0.58    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2)))) )),
% 1.60/0.58    inference(definition_unfolding,[],[f37,f44])).
% 1.60/0.58  fof(f37,plain,(
% 1.60/0.58    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.60/0.58    inference(cnf_transformation,[],[f4])).
% 1.60/0.58  fof(f4,axiom,(
% 1.60/0.58    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 1.60/0.58  fof(f246,plain,(
% 1.60/0.58    k1_xboole_0 != k4_xboole_0(k1_xboole_0,k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl3_1),
% 1.60/0.58    inference(resolution,[],[f97,f35])).
% 1.60/0.58  fof(f35,plain,(
% 1.60/0.58    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | k4_xboole_0(X1,X0) != k1_xboole_0) )),
% 1.60/0.58    inference(cnf_transformation,[],[f16])).
% 1.60/0.58  fof(f16,plain,(
% 1.60/0.58    ! [X0,X1] : (k4_xboole_0(X1,X0) != k1_xboole_0 | ~r2_xboole_0(X0,X1))),
% 1.60/0.58    inference(ennf_transformation,[],[f2])).
% 1.60/0.58  fof(f2,axiom,(
% 1.60/0.58    ! [X0,X1] : ~(k4_xboole_0(X1,X0) = k1_xboole_0 & r2_xboole_0(X0,X1))),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_xboole_1)).
% 1.60/0.58  fof(f97,plain,(
% 1.60/0.58    r2_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k1_xboole_0) | ~spl3_1),
% 1.60/0.58    inference(avatar_component_clause,[],[f95])).
% 1.60/0.58  % (18150)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.60/0.58  fof(f95,plain,(
% 1.60/0.58    spl3_1 <=> r2_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k1_xboole_0)),
% 1.60/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.60/0.58  fof(f245,plain,(
% 1.60/0.58    spl3_1 | spl3_2),
% 1.60/0.58    inference(avatar_split_clause,[],[f244,f99,f95])).
% 1.60/0.58  fof(f99,plain,(
% 1.60/0.58    spl3_2 <=> k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)),
% 1.60/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.60/0.58  fof(f244,plain,(
% 1.60/0.58    k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | r2_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k1_xboole_0)),
% 1.60/0.58    inference(resolution,[],[f90,f34])).
% 1.60/0.58  fof(f34,plain,(
% 1.60/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f21])).
% 1.60/0.58  fof(f21,plain,(
% 1.60/0.58    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 1.60/0.58    inference(flattening,[],[f20])).
% 1.60/0.58  fof(f20,plain,(
% 1.60/0.58    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 1.60/0.58    inference(nnf_transformation,[],[f1])).
% 1.60/0.58  fof(f1,axiom,(
% 1.60/0.58    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 1.60/0.58  fof(f90,plain,(
% 1.60/0.58    r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k1_xboole_0)),
% 1.60/0.58    inference(superposition,[],[f58,f63])).
% 1.60/0.58  fof(f63,plain,(
% 1.60/0.58    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK1)),
% 1.60/0.58    inference(superposition,[],[f62,f25])).
% 1.60/0.58  fof(f62,plain,(
% 1.60/0.58    k1_xboole_0 = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k1_xboole_0)),
% 1.60/0.58    inference(superposition,[],[f48,f46])).
% 1.60/0.58  fof(f46,plain,(
% 1.60/0.58    k1_xboole_0 = k3_tarski(k2_enumset1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK0,sK0,sK0,sK1),sK2))),
% 1.60/0.58    inference(definition_unfolding,[],[f24,f44,f43])).
% 1.60/0.58  fof(f24,plain,(
% 1.60/0.58    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 1.60/0.58    inference(cnf_transformation,[],[f19])).
% 1.60/0.58  fof(f19,plain,(
% 1.60/0.58    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 1.60/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f18])).
% 1.60/0.58  fof(f18,plain,(
% 1.60/0.58    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2) => k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 1.60/0.58    introduced(choice_axiom,[])).
% 1.60/0.58  fof(f15,plain,(
% 1.60/0.58    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2)),
% 1.60/0.58    inference(ennf_transformation,[],[f14])).
% 1.60/0.58  fof(f14,negated_conjecture,(
% 1.60/0.58    ~! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2)),
% 1.60/0.58    inference(negated_conjecture,[],[f13])).
% 1.60/0.58  fof(f13,conjecture,(
% 1.60/0.58    ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2)),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).
% 1.60/0.58  fof(f58,plain,(
% 1.60/0.58    ( ! [X2,X1] : (r1_tarski(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X1,X1,X1,X2))) )),
% 1.60/0.58    inference(equality_resolution,[],[f52])).
% 1.60/0.58  fof(f52,plain,(
% 1.60/0.58    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_enumset1(X1,X1,X1,X2)) | k2_enumset1(X2,X2,X2,X2) != X0) )),
% 1.60/0.58    inference(definition_unfolding,[],[f41,f43,f45])).
% 1.60/0.58  fof(f45,plain,(
% 1.60/0.58    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.60/0.58    inference(definition_unfolding,[],[f26,f43])).
% 1.60/0.58  fof(f26,plain,(
% 1.60/0.58    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f7])).
% 1.60/0.58  fof(f7,axiom,(
% 1.60/0.58    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.60/0.58  fof(f41,plain,(
% 1.60/0.58    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_tarski(X2) != X0) )),
% 1.60/0.58    inference(cnf_transformation,[],[f23])).
% 1.60/0.58  fof(f23,plain,(
% 1.60/0.58    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 1.60/0.58    inference(flattening,[],[f22])).
% 1.60/0.58  fof(f22,plain,(
% 1.60/0.58    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 1.60/0.58    inference(nnf_transformation,[],[f17])).
% 1.60/0.58  fof(f17,plain,(
% 1.60/0.58    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.60/0.58    inference(ennf_transformation,[],[f10])).
% 1.60/0.58  fof(f10,axiom,(
% 1.60/0.58    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).
% 1.60/0.58  fof(f243,plain,(
% 1.60/0.58    ~spl3_2),
% 1.60/0.58    inference(avatar_contradiction_clause,[],[f242])).
% 1.60/0.58  fof(f242,plain,(
% 1.60/0.58    $false | ~spl3_2),
% 1.60/0.58    inference(trivial_inequality_removal,[],[f241])).
% 1.60/0.58  fof(f241,plain,(
% 1.60/0.58    k1_xboole_0 != k1_xboole_0 | ~spl3_2),
% 1.60/0.58    inference(superposition,[],[f236,f82])).
% 1.60/0.58  fof(f82,plain,(
% 1.60/0.58    k1_xboole_0 = k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))),
% 1.60/0.58    inference(backward_demodulation,[],[f66,f79])).
% 1.60/0.58  fof(f79,plain,(
% 1.60/0.58    k1_xboole_0 = sK2),
% 1.60/0.58    inference(superposition,[],[f78,f25])).
% 1.60/0.58  fof(f78,plain,(
% 1.60/0.58    k1_xboole_0 = k4_xboole_0(sK2,k1_xboole_0)),
% 1.60/0.58    inference(superposition,[],[f71,f66])).
% 1.60/0.58  fof(f71,plain,(
% 1.60/0.58    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X0)))) )),
% 1.60/0.58    inference(superposition,[],[f48,f49])).
% 1.60/0.58  fof(f49,plain,(
% 1.60/0.58    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 1.60/0.58    inference(definition_unfolding,[],[f29,f43,f43])).
% 1.60/0.58  fof(f29,plain,(
% 1.60/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f6])).
% 1.60/0.58  fof(f6,axiom,(
% 1.60/0.58    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.60/0.58  fof(f66,plain,(
% 1.60/0.58    k1_xboole_0 = k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,sK2))),
% 1.60/0.58    inference(backward_demodulation,[],[f46,f63])).
% 1.60/0.58  fof(f236,plain,(
% 1.60/0.58    ( ! [X4] : (k1_xboole_0 != k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X4))) ) | ~spl3_2),
% 1.60/0.58    inference(superposition,[],[f47,f101])).
% 1.60/0.58  fof(f101,plain,(
% 1.60/0.58    k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | ~spl3_2),
% 1.60/0.58    inference(avatar_component_clause,[],[f99])).
% 1.60/0.58  fof(f47,plain,(
% 1.60/0.58    ( ! [X0,X1] : (k1_xboole_0 != k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),X1))) )),
% 1.60/0.58    inference(definition_unfolding,[],[f27,f44,f45])).
% 1.60/0.58  fof(f27,plain,(
% 1.60/0.58    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f12])).
% 1.60/0.58  fof(f12,axiom,(
% 1.60/0.58    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 1.60/0.58  % SZS output end Proof for theBenchmark
% 1.60/0.58  % (18135)------------------------------
% 1.60/0.58  % (18135)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.58  % (18135)Termination reason: Refutation
% 1.60/0.58  
% 1.60/0.58  % (18135)Memory used [KB]: 10874
% 1.60/0.58  % (18135)Time elapsed: 0.148 s
% 1.60/0.58  % (18135)------------------------------
% 1.60/0.58  % (18135)------------------------------
% 1.60/0.58  % (18133)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.60/0.58  % (18158)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.60/0.58  % (18131)Success in time 0.222 s
%------------------------------------------------------------------------------
