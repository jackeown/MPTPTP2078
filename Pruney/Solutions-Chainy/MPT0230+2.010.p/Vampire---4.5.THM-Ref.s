%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:36:36 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 104 expanded)
%              Number of leaves         :   14 (  31 expanded)
%              Depth                    :   14
%              Number of atoms          :   94 ( 160 expanded)
%              Number of equality atoms :   74 ( 124 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f234,plain,(
    $false ),
    inference(subsumption_resolution,[],[f233,f59])).

fof(f59,plain,(
    ! [X1] : k1_xboole_0 != k2_tarski(X1,X1) ),
    inference(forward_demodulation,[],[f56,f57])).

fof(f57,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f48,f28])).

fof(f28,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f48,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f27,f33])).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f27,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f56,plain,(
    ! [X1] : k2_tarski(X1,X1) != k4_xboole_0(k2_tarski(X1,X1),k2_tarski(X1,X1)) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k2_tarski(X0,X0) != k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1)) ) ),
    inference(definition_unfolding,[],[f42,f29,f29,f29])).

fof(f29,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f233,plain,(
    k1_xboole_0 = k2_tarski(sK0,sK0) ),
    inference(forward_demodulation,[],[f227,f62])).

fof(f62,plain,(
    k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)) ),
    inference(resolution,[],[f40,f47])).

fof(f47,plain,(
    r1_tarski(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)) ),
    inference(definition_unfolding,[],[f24,f29])).

fof(f24,plain,(
    r1_tarski(k1_tarski(sK0),k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & X0 != X1
      & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( X0 != X2
          & X0 != X1
          & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ~ ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f227,plain,(
    k2_tarski(sK0,sK0) = k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)) ),
    inference(trivial_inequality_removal,[],[f225])).

fof(f225,plain,
    ( k2_tarski(sK1,sK2) != k2_tarski(sK1,sK2)
    | k2_tarski(sK0,sK0) = k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)) ),
    inference(superposition,[],[f63,f210])).

fof(f210,plain,(
    k2_tarski(sK1,sK2) = k4_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0)) ),
    inference(subsumption_resolution,[],[f209,f25])).

fof(f25,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f20])).

fof(f209,plain,
    ( k2_tarski(sK1,sK2) = k4_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0))
    | sK0 = sK1 ),
    inference(subsumption_resolution,[],[f196,f26])).

fof(f26,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f20])).

fof(f196,plain,
    ( k2_tarski(sK1,sK2) = k4_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0))
    | sK0 = sK2
    | sK0 = sK1 ),
    inference(superposition,[],[f55,f93])).

fof(f93,plain,(
    k2_tarski(sK1,sK2) = k5_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0))) ),
    inference(forward_demodulation,[],[f86,f58])).

fof(f58,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f49,f57])).

fof(f49,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f30,f34])).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f30,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f86,plain,(
    k5_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0))) = k5_xboole_0(k2_tarski(sK1,sK2),k1_xboole_0) ),
    inference(superposition,[],[f50,f62])).

fof(f50,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f31,f34,f34])).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = k4_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))),k2_tarski(X0,X0))
      | X0 = X2
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f44,f45,f29])).

fof(f45,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))) ),
    inference(definition_unfolding,[],[f43,f34,f29])).

fof(f43,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( X0 = X1
      | X0 = X2
      | k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2)
        & X0 != X2
        & X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t136_enumset1)).

fof(f63,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | k4_xboole_0(X1,X0) = X1 ) ),
    inference(resolution,[],[f60,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(resolution,[],[f38,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n020.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 18:48:37 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.51  % (8866)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (8874)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (8866)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % (8887)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (8864)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (8862)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (8883)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (8865)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.38/0.54  % (8870)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.38/0.54  % (8863)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.38/0.54  % (8879)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.38/0.55  % (8883)Refutation not found, incomplete strategy% (8883)------------------------------
% 1.38/0.55  % (8883)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (8869)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.38/0.55  % (8867)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.38/0.55  % (8883)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.55  
% 1.38/0.55  % (8883)Memory used [KB]: 1791
% 1.38/0.55  % (8883)Time elapsed: 0.052 s
% 1.38/0.55  % (8883)------------------------------
% 1.38/0.55  % (8883)------------------------------
% 1.38/0.55  % (8882)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.38/0.55  % (8880)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.38/0.55  % (8885)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.38/0.55  % (8878)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.38/0.55  % (8882)Refutation not found, incomplete strategy% (8882)------------------------------
% 1.38/0.55  % (8882)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (8882)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.55  
% 1.38/0.55  % (8882)Memory used [KB]: 10618
% 1.38/0.55  % (8882)Time elapsed: 0.140 s
% 1.38/0.55  % (8882)------------------------------
% 1.38/0.55  % (8882)------------------------------
% 1.38/0.55  % (8861)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.38/0.55  % SZS output start Proof for theBenchmark
% 1.38/0.55  fof(f234,plain,(
% 1.38/0.55    $false),
% 1.38/0.55    inference(subsumption_resolution,[],[f233,f59])).
% 1.38/0.55  fof(f59,plain,(
% 1.38/0.55    ( ! [X1] : (k1_xboole_0 != k2_tarski(X1,X1)) )),
% 1.38/0.55    inference(forward_demodulation,[],[f56,f57])).
% 1.38/0.55  fof(f57,plain,(
% 1.38/0.55    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.38/0.55    inference(backward_demodulation,[],[f48,f28])).
% 1.38/0.55  fof(f28,plain,(
% 1.38/0.55    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.38/0.55    inference(cnf_transformation,[],[f7])).
% 1.38/0.55  fof(f7,axiom,(
% 1.38/0.55    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.38/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.38/0.55  fof(f48,plain,(
% 1.38/0.55    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 1.38/0.55    inference(definition_unfolding,[],[f27,f33])).
% 1.38/0.55  fof(f33,plain,(
% 1.38/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.38/0.55    inference(cnf_transformation,[],[f8])).
% 1.38/0.55  fof(f8,axiom,(
% 1.38/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.38/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.38/0.55  fof(f27,plain,(
% 1.38/0.55    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.38/0.55    inference(cnf_transformation,[],[f6])).
% 1.38/0.55  fof(f6,axiom,(
% 1.38/0.55    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.38/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 1.38/0.55  fof(f56,plain,(
% 1.38/0.55    ( ! [X1] : (k2_tarski(X1,X1) != k4_xboole_0(k2_tarski(X1,X1),k2_tarski(X1,X1))) )),
% 1.38/0.55    inference(equality_resolution,[],[f53])).
% 1.38/0.55  fof(f53,plain,(
% 1.38/0.55    ( ! [X0,X1] : (X0 != X1 | k2_tarski(X0,X0) != k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1))) )),
% 1.38/0.55    inference(definition_unfolding,[],[f42,f29,f29,f29])).
% 1.38/0.55  fof(f29,plain,(
% 1.38/0.55    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.38/0.55    inference(cnf_transformation,[],[f13])).
% 1.38/0.55  fof(f13,axiom,(
% 1.38/0.55    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.38/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.38/0.55  fof(f42,plain,(
% 1.38/0.55    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 1.38/0.55    inference(cnf_transformation,[],[f15])).
% 1.38/0.55  fof(f15,axiom,(
% 1.38/0.55    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 1.38/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 1.38/0.55  fof(f233,plain,(
% 1.38/0.55    k1_xboole_0 = k2_tarski(sK0,sK0)),
% 1.38/0.55    inference(forward_demodulation,[],[f227,f62])).
% 1.38/0.55  fof(f62,plain,(
% 1.38/0.55    k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2))),
% 1.38/0.55    inference(resolution,[],[f40,f47])).
% 1.38/0.55  fof(f47,plain,(
% 1.38/0.55    r1_tarski(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2))),
% 1.38/0.55    inference(definition_unfolding,[],[f24,f29])).
% 1.38/0.55  fof(f24,plain,(
% 1.38/0.55    r1_tarski(k1_tarski(sK0),k2_tarski(sK1,sK2))),
% 1.38/0.55    inference(cnf_transformation,[],[f20])).
% 1.38/0.55  fof(f20,plain,(
% 1.38/0.55    ? [X0,X1,X2] : (X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 1.38/0.55    inference(ennf_transformation,[],[f17])).
% 1.38/0.55  fof(f17,negated_conjecture,(
% 1.38/0.55    ~! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 1.38/0.55    inference(negated_conjecture,[],[f16])).
% 1.38/0.55  fof(f16,conjecture,(
% 1.38/0.55    ! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 1.38/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).
% 1.38/0.55  fof(f40,plain,(
% 1.38/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 1.38/0.55    inference(cnf_transformation,[],[f22])).
% 1.38/0.55  fof(f22,plain,(
% 1.38/0.55    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1))),
% 1.38/0.55    inference(ennf_transformation,[],[f19])).
% 1.38/0.55  fof(f19,plain,(
% 1.38/0.55    ! [X0,X1] : (r1_tarski(X0,X1) => k1_xboole_0 = k4_xboole_0(X0,X1))),
% 1.38/0.55    inference(unused_predicate_definition_removal,[],[f5])).
% 1.38/0.55  fof(f5,axiom,(
% 1.38/0.55    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 1.38/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.38/0.55  fof(f227,plain,(
% 1.38/0.55    k2_tarski(sK0,sK0) = k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2))),
% 1.38/0.55    inference(trivial_inequality_removal,[],[f225])).
% 1.38/0.55  fof(f225,plain,(
% 1.38/0.55    k2_tarski(sK1,sK2) != k2_tarski(sK1,sK2) | k2_tarski(sK0,sK0) = k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2))),
% 1.38/0.55    inference(superposition,[],[f63,f210])).
% 1.38/0.55  fof(f210,plain,(
% 1.38/0.55    k2_tarski(sK1,sK2) = k4_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0))),
% 1.38/0.55    inference(subsumption_resolution,[],[f209,f25])).
% 1.38/0.55  fof(f25,plain,(
% 1.38/0.55    sK0 != sK1),
% 1.38/0.55    inference(cnf_transformation,[],[f20])).
% 1.38/0.55  fof(f209,plain,(
% 1.38/0.55    k2_tarski(sK1,sK2) = k4_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0)) | sK0 = sK1),
% 1.38/0.55    inference(subsumption_resolution,[],[f196,f26])).
% 1.38/0.55  fof(f26,plain,(
% 1.38/0.55    sK0 != sK2),
% 1.38/0.55    inference(cnf_transformation,[],[f20])).
% 1.38/0.55  fof(f196,plain,(
% 1.38/0.55    k2_tarski(sK1,sK2) = k4_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0)) | sK0 = sK2 | sK0 = sK1),
% 1.38/0.55    inference(superposition,[],[f55,f93])).
% 1.38/0.55  fof(f93,plain,(
% 1.38/0.55    k2_tarski(sK1,sK2) = k5_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0)))),
% 1.38/0.55    inference(forward_demodulation,[],[f86,f58])).
% 1.38/0.55  fof(f58,plain,(
% 1.38/0.55    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.38/0.55    inference(forward_demodulation,[],[f49,f57])).
% 1.38/0.55  fof(f49,plain,(
% 1.38/0.55    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 1.38/0.55    inference(definition_unfolding,[],[f30,f34])).
% 1.38/0.55  fof(f34,plain,(
% 1.38/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.38/0.55    inference(cnf_transformation,[],[f10])).
% 1.38/0.55  fof(f10,axiom,(
% 1.38/0.55    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.38/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.38/0.55  fof(f30,plain,(
% 1.38/0.55    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 1.38/0.55    inference(cnf_transformation,[],[f18])).
% 1.38/0.55  fof(f18,plain,(
% 1.38/0.55    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 1.38/0.55    inference(rectify,[],[f3])).
% 1.38/0.55  fof(f3,axiom,(
% 1.38/0.55    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 1.38/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 1.38/0.55  fof(f86,plain,(
% 1.38/0.55    k5_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0))) = k5_xboole_0(k2_tarski(sK1,sK2),k1_xboole_0)),
% 1.38/0.55    inference(superposition,[],[f50,f62])).
% 1.38/0.55  fof(f50,plain,(
% 1.38/0.55    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1))) )),
% 1.38/0.55    inference(definition_unfolding,[],[f31,f34,f34])).
% 1.38/0.55  fof(f31,plain,(
% 1.38/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.38/0.55    inference(cnf_transformation,[],[f1])).
% 1.38/0.55  fof(f1,axiom,(
% 1.38/0.55    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.38/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.38/0.55  fof(f55,plain,(
% 1.38/0.55    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) = k4_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))),k2_tarski(X0,X0)) | X0 = X2 | X0 = X1) )),
% 1.38/0.55    inference(definition_unfolding,[],[f44,f45,f29])).
% 1.38/0.55  fof(f45,plain,(
% 1.38/0.55    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) )),
% 1.38/0.55    inference(definition_unfolding,[],[f43,f34,f29])).
% 1.38/0.55  fof(f43,plain,(
% 1.38/0.55    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 1.38/0.55    inference(cnf_transformation,[],[f12])).
% 1.38/0.55  fof(f12,axiom,(
% 1.38/0.55    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 1.38/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).
% 1.38/0.55  fof(f44,plain,(
% 1.38/0.55    ( ! [X2,X0,X1] : (X0 = X1 | X0 = X2 | k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2)) )),
% 1.38/0.55    inference(cnf_transformation,[],[f23])).
% 1.38/0.55  fof(f23,plain,(
% 1.38/0.55    ! [X0,X1,X2] : (k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2) | X0 = X2 | X0 = X1)),
% 1.38/0.55    inference(ennf_transformation,[],[f11])).
% 1.38/0.55  fof(f11,axiom,(
% 1.38/0.55    ! [X0,X1,X2] : ~(k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2) & X0 != X2 & X0 != X1)),
% 1.38/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t136_enumset1)).
% 1.38/0.55  fof(f63,plain,(
% 1.38/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | k4_xboole_0(X1,X0) = X1) )),
% 1.38/0.55    inference(resolution,[],[f60,f39])).
% 1.38/0.55  fof(f39,plain,(
% 1.38/0.55    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 1.38/0.55    inference(cnf_transformation,[],[f9])).
% 1.38/0.55  fof(f9,axiom,(
% 1.38/0.55    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.38/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.38/0.55  fof(f60,plain,(
% 1.38/0.55    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | k4_xboole_0(X0,X1) != X0) )),
% 1.38/0.55    inference(resolution,[],[f38,f35])).
% 1.38/0.55  fof(f35,plain,(
% 1.38/0.55    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 1.38/0.55    inference(cnf_transformation,[],[f21])).
% 1.38/0.55  fof(f21,plain,(
% 1.38/0.55    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.38/0.55    inference(ennf_transformation,[],[f4])).
% 1.38/0.56  fof(f4,axiom,(
% 1.38/0.56    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.38/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.38/0.56  fof(f38,plain,(
% 1.38/0.56    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 1.38/0.56    inference(cnf_transformation,[],[f9])).
% 1.38/0.56  % SZS output end Proof for theBenchmark
% 1.38/0.56  % (8866)------------------------------
% 1.38/0.56  % (8866)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.56  % (8866)Termination reason: Refutation
% 1.38/0.56  
% 1.38/0.56  % (8866)Memory used [KB]: 6268
% 1.38/0.56  % (8866)Time elapsed: 0.123 s
% 1.38/0.56  % (8866)------------------------------
% 1.38/0.56  % (8866)------------------------------
% 1.38/0.56  % (8859)Success in time 0.195 s
%------------------------------------------------------------------------------
