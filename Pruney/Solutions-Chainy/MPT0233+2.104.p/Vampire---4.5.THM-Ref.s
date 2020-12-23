%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:17 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 184 expanded)
%              Number of leaves         :   18 (  58 expanded)
%              Depth                    :   19
%              Number of atoms          :  114 ( 249 expanded)
%              Number of equality atoms :   81 ( 205 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f128,plain,(
    $false ),
    inference(subsumption_resolution,[],[f127,f26])).

fof(f26,plain,(
    sK0 != sK3 ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( X0 != X3
      & X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( X0 != X3
          & X0 != X2
          & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).

fof(f127,plain,(
    sK0 = sK3 ),
    inference(subsumption_resolution,[],[f126,f25])).

fof(f25,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f20])).

fof(f126,plain,
    ( sK0 = sK2
    | sK0 = sK3 ),
    inference(duplicate_literal_removal,[],[f125])).

fof(f125,plain,
    ( sK0 = sK2
    | sK0 = sK3
    | sK0 = sK2 ),
    inference(resolution,[],[f122,f75])).

fof(f75,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))
      | X1 = X4
      | X2 = X4
      | X0 = X4 ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 = X4
      | X1 = X4
      | X2 = X4
      | ~ r2_hidden(X4,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f43,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f36,f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f38,f53])).

% (9169)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% (9170)Refutation not found, incomplete strategy% (9170)------------------------------
% (9170)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (9153)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% (9161)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% (9162)Refutation not found, incomplete strategy% (9162)------------------------------
% (9162)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (9162)Termination reason: Refutation not found, incomplete strategy

% (9162)Memory used [KB]: 10618
% (9162)Time elapsed: 0.208 s
% (9162)------------------------------
% (9162)------------------------------
% (9167)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% (9170)Termination reason: Refutation not found, incomplete strategy

% (9170)Memory used [KB]: 6396
% (9170)Time elapsed: 0.202 s
% (9170)------------------------------
% (9170)------------------------------
% (9157)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% (9166)Refutation not found, incomplete strategy% (9166)------------------------------
% (9166)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (9154)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% (9154)Refutation not found, incomplete strategy% (9154)------------------------------
% (9154)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (9154)Termination reason: Refutation not found, incomplete strategy

% (9154)Memory used [KB]: 10618
% (9154)Time elapsed: 0.219 s
% (9154)------------------------------
% (9154)------------------------------
% (9166)Termination reason: Refutation not found, incomplete strategy

% (9166)Memory used [KB]: 1791
% (9166)Time elapsed: 0.222 s
% (9166)------------------------------
% (9166)------------------------------
fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f47,f52])).

fof(f52,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f48,f49])).

fof(f49,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f48,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f38,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f36,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f43,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 = X4
      | X1 = X4
      | X2 = X4
      | ~ r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f122,plain,(
    r2_hidden(sK0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
    inference(superposition,[],[f70,f116])).

fof(f116,plain,(
    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3,sK0) ),
    inference(forward_demodulation,[],[f115,f28])).

fof(f28,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f115,plain,(
    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3,sK0) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k1_xboole_0) ),
    inference(forward_demodulation,[],[f110,f27])).

fof(f27,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f110,plain,(
    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3,sK0) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(superposition,[],[f58,f92])).

fof(f92,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
    inference(resolution,[],[f91,f60])).

fof(f60,plain,(
    ! [X0,X1] : r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f30,f57,f56])).

fof(f56,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f32,f55])).

fof(f32,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f57,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f29,f56])).

fof(f29,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f30,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

fof(f91,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
      | k3_xboole_0(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) = X0 ) ),
    inference(resolution,[],[f88,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f88,plain,(
    ! [X0] :
      ( r1_tarski(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))
      | ~ r1_tarski(X0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) ) ),
    inference(superposition,[],[f79,f83])).

fof(f83,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
    inference(resolution,[],[f59,f35])).

fof(f59,plain,(
    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
    inference(definition_unfolding,[],[f24,f56,f56])).

fof(f24,plain,(
    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(cnf_transformation,[],[f20])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k3_xboole_0(X1,X0))
      | r1_tarski(X2,X0) ) ),
    inference(superposition,[],[f37,f31])).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_xboole_0(X1,X2))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).

fof(f58,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)))) ),
    inference(definition_unfolding,[],[f50,f51,f49,f57])).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f33,f34])).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f50,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_enumset1)).

fof(f70,plain,(
    ! [X4,X0,X1] : r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X4)) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X4,X0,X3,X1] :
      ( r2_hidden(X4,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X4) != X3 ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X2 != X4
      | r2_hidden(X4,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f46,f55])).

fof(f46,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X2 != X4
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:58:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.53  % (9149)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.55  % (9149)Refutation not found, incomplete strategy% (9149)------------------------------
% 0.21/0.55  % (9149)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (9171)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.56  % (9173)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.56  % (9149)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (9149)Memory used [KB]: 6140
% 0.21/0.56  % (9149)Time elapsed: 0.131 s
% 0.21/0.56  % (9149)------------------------------
% 0.21/0.56  % (9149)------------------------------
% 0.21/0.56  % (9163)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.57  % (9165)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.57  % (9155)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.57  % (9165)Refutation not found, incomplete strategy% (9165)------------------------------
% 0.21/0.57  % (9165)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (9165)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (9165)Memory used [KB]: 10746
% 0.21/0.57  % (9165)Time elapsed: 0.149 s
% 0.21/0.57  % (9165)------------------------------
% 0.21/0.57  % (9165)------------------------------
% 0.21/0.58  % (9155)Refutation not found, incomplete strategy% (9155)------------------------------
% 0.21/0.58  % (9155)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (9155)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (9155)Memory used [KB]: 10618
% 0.21/0.58  % (9155)Time elapsed: 0.158 s
% 0.21/0.58  % (9155)------------------------------
% 0.21/0.58  % (9155)------------------------------
% 0.21/0.58  % (9145)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.58  % (9145)Refutation not found, incomplete strategy% (9145)------------------------------
% 0.21/0.58  % (9145)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (9145)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (9145)Memory used [KB]: 1663
% 0.21/0.58  % (9145)Time elapsed: 0.159 s
% 0.21/0.58  % (9145)------------------------------
% 0.21/0.58  % (9145)------------------------------
% 0.21/0.59  % (9147)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.59  % (9147)Refutation not found, incomplete strategy% (9147)------------------------------
% 0.21/0.59  % (9147)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.59  % (9148)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.59  % (9168)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.60  % (9160)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.60  % (9150)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.60  % (9146)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.60  % (9158)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.60  % (9151)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.60  % (9159)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.60  % (9147)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.60  
% 0.21/0.60  % (9147)Memory used [KB]: 10746
% 0.21/0.60  % (9147)Time elapsed: 0.169 s
% 0.21/0.60  % (9147)------------------------------
% 0.21/0.60  % (9147)------------------------------
% 0.21/0.60  % (9152)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.60  % (9164)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.61  % (9156)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.61  % (9168)Refutation not found, incomplete strategy% (9168)------------------------------
% 0.21/0.61  % (9168)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.61  % (9160)Refutation not found, incomplete strategy% (9160)------------------------------
% 0.21/0.61  % (9160)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.61  % (9168)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.61  
% 0.21/0.61  % (9168)Memory used [KB]: 1791
% 0.21/0.61  % (9168)Time elapsed: 0.145 s
% 0.21/0.61  % (9168)------------------------------
% 0.21/0.61  % (9168)------------------------------
% 0.21/0.61  % (9160)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.61  
% 0.21/0.61  % (9160)Memory used [KB]: 6268
% 0.21/0.61  % (9160)Time elapsed: 0.147 s
% 0.21/0.61  % (9160)------------------------------
% 0.21/0.61  % (9160)------------------------------
% 0.21/0.62  % (9172)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.62  % (9174)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.62  % (9162)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.62  % (9170)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.62  % (9166)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.62  % (9151)Refutation found. Thanks to Tanya!
% 0.21/0.62  % SZS status Theorem for theBenchmark
% 0.21/0.62  % SZS output start Proof for theBenchmark
% 0.21/0.62  fof(f128,plain,(
% 0.21/0.62    $false),
% 0.21/0.62    inference(subsumption_resolution,[],[f127,f26])).
% 0.21/0.62  fof(f26,plain,(
% 0.21/0.62    sK0 != sK3),
% 0.21/0.62    inference(cnf_transformation,[],[f20])).
% 0.21/0.62  fof(f20,plain,(
% 0.21/0.62    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 0.21/0.62    inference(ennf_transformation,[],[f19])).
% 0.21/0.62  fof(f19,negated_conjecture,(
% 0.21/0.62    ~! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 0.21/0.62    inference(negated_conjecture,[],[f18])).
% 0.21/0.62  fof(f18,conjecture,(
% 0.21/0.62    ! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 0.21/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).
% 0.21/0.62  fof(f127,plain,(
% 0.21/0.62    sK0 = sK3),
% 0.21/0.62    inference(subsumption_resolution,[],[f126,f25])).
% 0.21/0.62  fof(f25,plain,(
% 0.21/0.62    sK0 != sK2),
% 0.21/0.62    inference(cnf_transformation,[],[f20])).
% 0.21/0.62  fof(f126,plain,(
% 0.21/0.62    sK0 = sK2 | sK0 = sK3),
% 0.21/0.62    inference(duplicate_literal_removal,[],[f125])).
% 0.21/0.62  fof(f125,plain,(
% 0.21/0.62    sK0 = sK2 | sK0 = sK3 | sK0 = sK2),
% 0.21/0.62    inference(resolution,[],[f122,f75])).
% 0.21/0.62  fof(f75,plain,(
% 0.21/0.62    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) | X1 = X4 | X2 = X4 | X0 = X4) )),
% 0.21/0.62    inference(equality_resolution,[],[f64])).
% 0.21/0.62  fof(f64,plain,(
% 0.21/0.62    ( ! [X4,X2,X0,X3,X1] : (X0 = X4 | X1 = X4 | X2 = X4 | ~r2_hidden(X4,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 0.21/0.62    inference(definition_unfolding,[],[f43,f55])).
% 0.21/0.62  fof(f55,plain,(
% 0.21/0.62    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.21/0.62    inference(definition_unfolding,[],[f36,f54])).
% 0.21/0.62  fof(f54,plain,(
% 0.21/0.62    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.21/0.62    inference(definition_unfolding,[],[f38,f53])).
% 0.21/0.62  % (9169)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.63  % (9170)Refutation not found, incomplete strategy% (9170)------------------------------
% 0.21/0.63  % (9170)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.63  % (9153)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.63  % (9161)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.93/0.63  % (9162)Refutation not found, incomplete strategy% (9162)------------------------------
% 1.93/0.63  % (9162)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.93/0.63  % (9162)Termination reason: Refutation not found, incomplete strategy
% 1.93/0.63  
% 1.93/0.63  % (9162)Memory used [KB]: 10618
% 1.93/0.63  % (9162)Time elapsed: 0.208 s
% 1.93/0.63  % (9162)------------------------------
% 1.93/0.63  % (9162)------------------------------
% 1.93/0.64  % (9167)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.93/0.64  % (9170)Termination reason: Refutation not found, incomplete strategy
% 1.93/0.64  
% 1.93/0.64  % (9170)Memory used [KB]: 6396
% 1.93/0.64  % (9170)Time elapsed: 0.202 s
% 1.93/0.64  % (9170)------------------------------
% 1.93/0.64  % (9170)------------------------------
% 1.93/0.64  % (9157)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.93/0.64  % (9166)Refutation not found, incomplete strategy% (9166)------------------------------
% 1.93/0.64  % (9166)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.93/0.64  % (9154)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.93/0.64  % (9154)Refutation not found, incomplete strategy% (9154)------------------------------
% 1.93/0.64  % (9154)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.93/0.64  % (9154)Termination reason: Refutation not found, incomplete strategy
% 1.93/0.64  
% 1.93/0.64  % (9154)Memory used [KB]: 10618
% 1.93/0.64  % (9154)Time elapsed: 0.219 s
% 1.93/0.64  % (9154)------------------------------
% 1.93/0.64  % (9154)------------------------------
% 1.93/0.64  % (9166)Termination reason: Refutation not found, incomplete strategy
% 1.93/0.64  
% 1.93/0.64  % (9166)Memory used [KB]: 1791
% 1.93/0.64  % (9166)Time elapsed: 0.222 s
% 1.93/0.64  % (9166)------------------------------
% 1.93/0.64  % (9166)------------------------------
% 1.93/0.64  fof(f53,plain,(
% 1.93/0.64    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.93/0.64    inference(definition_unfolding,[],[f47,f52])).
% 1.93/0.64  fof(f52,plain,(
% 1.93/0.64    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.93/0.64    inference(definition_unfolding,[],[f48,f49])).
% 1.93/0.64  fof(f49,plain,(
% 1.93/0.64    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 1.93/0.64    inference(cnf_transformation,[],[f16])).
% 1.93/0.64  fof(f16,axiom,(
% 1.93/0.64    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 1.93/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 1.93/0.64  fof(f48,plain,(
% 1.93/0.64    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.93/0.64    inference(cnf_transformation,[],[f15])).
% 1.93/0.64  fof(f15,axiom,(
% 1.93/0.64    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.93/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.93/0.64  fof(f47,plain,(
% 1.93/0.64    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.93/0.64    inference(cnf_transformation,[],[f14])).
% 1.93/0.64  fof(f14,axiom,(
% 1.93/0.64    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.93/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.93/0.64  fof(f38,plain,(
% 1.93/0.64    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.93/0.64    inference(cnf_transformation,[],[f13])).
% 1.93/0.64  fof(f13,axiom,(
% 1.93/0.64    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.93/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.93/0.64  fof(f36,plain,(
% 1.93/0.64    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.93/0.64    inference(cnf_transformation,[],[f12])).
% 1.93/0.64  fof(f12,axiom,(
% 1.93/0.64    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.93/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.93/0.64  fof(f43,plain,(
% 1.93/0.64    ( ! [X4,X2,X0,X3,X1] : (X0 = X4 | X1 = X4 | X2 = X4 | ~r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.93/0.64    inference(cnf_transformation,[],[f23])).
% 1.93/0.64  fof(f23,plain,(
% 1.93/0.64    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.93/0.64    inference(ennf_transformation,[],[f8])).
% 1.93/0.64  fof(f8,axiom,(
% 1.93/0.64    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.93/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 1.93/0.64  fof(f122,plain,(
% 1.93/0.64    r2_hidden(sK0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))),
% 1.93/0.64    inference(superposition,[],[f70,f116])).
% 1.93/0.64  fof(f116,plain,(
% 1.93/0.64    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3,sK0)),
% 1.93/0.64    inference(forward_demodulation,[],[f115,f28])).
% 1.93/0.64  fof(f28,plain,(
% 1.93/0.64    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.93/0.64    inference(cnf_transformation,[],[f5])).
% 1.93/0.64  fof(f5,axiom,(
% 1.93/0.64    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.93/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 1.93/0.64  fof(f115,plain,(
% 1.93/0.64    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3,sK0) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k1_xboole_0)),
% 1.93/0.64    inference(forward_demodulation,[],[f110,f27])).
% 1.93/0.64  fof(f27,plain,(
% 1.93/0.64    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.93/0.64    inference(cnf_transformation,[],[f6])).
% 1.93/0.64  fof(f6,axiom,(
% 1.93/0.64    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.93/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.93/0.64  fof(f110,plain,(
% 1.93/0.64    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3,sK0) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 1.93/0.64    inference(superposition,[],[f58,f92])).
% 1.93/0.64  fof(f92,plain,(
% 1.93/0.64    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))),
% 1.93/0.64    inference(resolution,[],[f91,f60])).
% 1.93/0.64  fof(f60,plain,(
% 1.93/0.64    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.93/0.64    inference(definition_unfolding,[],[f30,f57,f56])).
% 1.93/0.64  fof(f56,plain,(
% 1.93/0.64    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.93/0.64    inference(definition_unfolding,[],[f32,f55])).
% 1.93/0.64  fof(f32,plain,(
% 1.93/0.64    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.93/0.64    inference(cnf_transformation,[],[f11])).
% 1.93/0.64  fof(f11,axiom,(
% 1.93/0.64    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.93/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.93/0.64  fof(f57,plain,(
% 1.93/0.64    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.93/0.64    inference(definition_unfolding,[],[f29,f56])).
% 1.93/0.64  fof(f29,plain,(
% 1.93/0.64    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.93/0.64    inference(cnf_transformation,[],[f10])).
% 1.93/0.64  fof(f10,axiom,(
% 1.93/0.64    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.93/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.93/0.64  fof(f30,plain,(
% 1.93/0.64    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 1.93/0.64    inference(cnf_transformation,[],[f17])).
% 1.93/0.64  fof(f17,axiom,(
% 1.93/0.64    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 1.93/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).
% 1.93/0.64  fof(f91,plain,(
% 1.93/0.64    ( ! [X0] : (~r1_tarski(X0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | k3_xboole_0(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) = X0) )),
% 1.93/0.64    inference(resolution,[],[f88,f35])).
% 1.93/0.64  fof(f35,plain,(
% 1.93/0.64    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.93/0.64    inference(cnf_transformation,[],[f21])).
% 1.93/0.64  fof(f21,plain,(
% 1.93/0.64    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.93/0.64    inference(ennf_transformation,[],[f4])).
% 1.93/0.64  fof(f4,axiom,(
% 1.93/0.64    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.93/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.93/0.64  fof(f88,plain,(
% 1.93/0.64    ( ! [X0] : (r1_tarski(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) | ~r1_tarski(X0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) )),
% 1.93/0.64    inference(superposition,[],[f79,f83])).
% 1.93/0.64  fof(f83,plain,(
% 1.93/0.64    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))),
% 1.93/0.64    inference(resolution,[],[f59,f35])).
% 1.93/0.64  fof(f59,plain,(
% 1.93/0.64    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))),
% 1.93/0.64    inference(definition_unfolding,[],[f24,f56,f56])).
% 1.93/0.64  fof(f24,plain,(
% 1.93/0.64    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),
% 1.93/0.64    inference(cnf_transformation,[],[f20])).
% 1.93/0.64  fof(f79,plain,(
% 1.93/0.64    ( ! [X2,X0,X1] : (~r1_tarski(X2,k3_xboole_0(X1,X0)) | r1_tarski(X2,X0)) )),
% 1.93/0.64    inference(superposition,[],[f37,f31])).
% 1.93/0.64  fof(f31,plain,(
% 1.93/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.93/0.64    inference(cnf_transformation,[],[f1])).
% 1.93/0.64  fof(f1,axiom,(
% 1.93/0.64    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.93/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.93/0.64  fof(f37,plain,(
% 1.93/0.64    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_xboole_0(X1,X2)) | r1_tarski(X0,X1)) )),
% 1.93/0.64    inference(cnf_transformation,[],[f22])).
% 1.93/0.64  fof(f22,plain,(
% 1.93/0.64    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 1.93/0.64    inference(ennf_transformation,[],[f3])).
% 1.93/0.64  fof(f3,axiom,(
% 1.93/0.64    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 1.93/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).
% 1.93/0.64  fof(f58,plain,(
% 1.93/0.64    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6))))) )),
% 1.93/0.64    inference(definition_unfolding,[],[f50,f51,f49,f57])).
% 1.93/0.64  fof(f51,plain,(
% 1.93/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 1.93/0.64    inference(definition_unfolding,[],[f33,f34])).
% 1.93/0.64  fof(f34,plain,(
% 1.93/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.93/0.64    inference(cnf_transformation,[],[f2])).
% 1.93/0.64  fof(f2,axiom,(
% 1.93/0.64    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.93/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.93/0.64  fof(f33,plain,(
% 1.93/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.93/0.64    inference(cnf_transformation,[],[f7])).
% 1.93/0.64  fof(f7,axiom,(
% 1.93/0.64    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.93/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.93/0.64  fof(f50,plain,(
% 1.93/0.64    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))) )),
% 1.93/0.64    inference(cnf_transformation,[],[f9])).
% 1.93/0.64  fof(f9,axiom,(
% 1.93/0.64    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))),
% 1.93/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_enumset1)).
% 1.93/0.64  fof(f70,plain,(
% 1.93/0.64    ( ! [X4,X0,X1] : (r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X4))) )),
% 1.93/0.64    inference(equality_resolution,[],[f69])).
% 1.93/0.64  fof(f69,plain,(
% 1.93/0.64    ( ! [X4,X0,X3,X1] : (r2_hidden(X4,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X4) != X3) )),
% 1.93/0.64    inference(equality_resolution,[],[f61])).
% 1.93/0.64  fof(f61,plain,(
% 1.93/0.64    ( ! [X4,X2,X0,X3,X1] : (X2 != X4 | r2_hidden(X4,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 1.93/0.64    inference(definition_unfolding,[],[f46,f55])).
% 1.93/0.64  fof(f46,plain,(
% 1.93/0.64    ( ! [X4,X2,X0,X3,X1] : (X2 != X4 | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.93/0.64    inference(cnf_transformation,[],[f23])).
% 1.93/0.64  % SZS output end Proof for theBenchmark
% 1.93/0.64  % (9151)------------------------------
% 1.93/0.64  % (9151)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.93/0.64  % (9151)Termination reason: Refutation
% 1.93/0.64  
% 1.93/0.64  % (9151)Memory used [KB]: 6268
% 1.93/0.64  % (9151)Time elapsed: 0.203 s
% 1.93/0.64  % (9151)------------------------------
% 1.93/0.64  % (9151)------------------------------
% 1.93/0.64  % (9153)Refutation not found, incomplete strategy% (9153)------------------------------
% 1.93/0.64  % (9153)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.93/0.64  % (9153)Termination reason: Refutation not found, incomplete strategy
% 1.93/0.64  
% 1.93/0.64  % (9153)Memory used [KB]: 10746
% 1.93/0.64  % (9153)Time elapsed: 0.218 s
% 1.93/0.64  % (9153)------------------------------
% 1.93/0.64  % (9153)------------------------------
% 1.93/0.64  % (9144)Success in time 0.273 s
%------------------------------------------------------------------------------
