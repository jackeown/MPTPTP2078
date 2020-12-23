%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:43 EST 2020

% Result     : Theorem 1.74s
% Output     : Refutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 266 expanded)
%              Number of leaves         :   16 (  89 expanded)
%              Depth                    :   13
%              Number of atoms          :   99 ( 312 expanded)
%              Number of equality atoms :   63 ( 259 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f125,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f123])).

fof(f123,plain,(
    sK1 != sK1 ),
    inference(superposition,[],[f79,f122])).

fof(f122,plain,(
    sK1 = k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(forward_demodulation,[],[f121,f51])).

fof(f51,plain,(
    ! [X0] : k3_tarski(k2_enumset1(X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f30,f45])).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f41,f44])).

fof(f44,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f40,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f40,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f30,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f121,plain,(
    k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0))) = k3_tarski(k2_enumset1(sK1,sK1,sK1,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f118,f109])).

fof(f109,plain,(
    ! [X7] : k1_xboole_0 = k5_xboole_0(X7,X7) ),
    inference(forward_demodulation,[],[f108,f97])).

fof(f97,plain,(
    ! [X3] : k5_xboole_0(X3,k1_xboole_0) = X3 ),
    inference(forward_demodulation,[],[f96,f58])).

fof(f58,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f56,f42])).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f56,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f39,f35])).

fof(f35,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f96,plain,(
    ! [X3] : k5_xboole_0(X3,k3_xboole_0(X3,k1_xboole_0)) = X3 ),
    inference(forward_demodulation,[],[f92,f77])).

fof(f77,plain,(
    ! [X0] : k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
    inference(superposition,[],[f48,f51])).

fof(f48,plain,(
    ! [X0,X1] : k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(X1,X1,X1,X0)) ),
    inference(definition_unfolding,[],[f27,f45,f45])).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f92,plain,(
    ! [X3] : k5_xboole_0(X3,k3_xboole_0(X3,k1_xboole_0)) = k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X3)) ),
    inference(superposition,[],[f77,f49])).

fof(f49,plain,(
    ! [X0,X1] : k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f28,f45,f45,f34])).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f108,plain,(
    ! [X7] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k5_xboole_0(X7,X7) ),
    inference(forward_demodulation,[],[f107,f56])).

fof(f107,plain,(
    ! [X7] : k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X7)) = k5_xboole_0(X7,X7) ),
    inference(forward_demodulation,[],[f104,f57])).

fof(f57,plain,(
    ! [X1] : k3_xboole_0(X1,X1) = X1 ),
    inference(resolution,[],[f39,f54])).

fof(f54,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f104,plain,(
    ! [X7] : k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X7)) = k5_xboole_0(X7,k3_xboole_0(X7,X7)) ),
    inference(superposition,[],[f89,f77])).

fof(f89,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k3_tarski(k2_enumset1(X0,X0,X0,X1)),k3_xboole_0(X1,k3_tarski(k2_enumset1(X0,X0,X0,X1)))) ),
    inference(forward_demodulation,[],[f50,f42])).

fof(f50,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k3_tarski(k2_enumset1(X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k2_enumset1(X0,X0,X0,X1)),X1)) ),
    inference(definition_unfolding,[],[f29,f34,f34,f45])).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f118,plain,(
    k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0))) = k3_tarski(k2_enumset1(sK1,sK1,sK1,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)))) ),
    inference(superposition,[],[f49,f114])).

fof(f114,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) = k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(resolution,[],[f73,f25])).

fof(f25,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( sK1 != k2_xboole_0(k1_tarski(sK0),sK1)
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f20])).

fof(f20,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),X1) != X1
        & r2_hidden(X0,X1) )
   => ( sK1 != k2_xboole_0(k1_tarski(sK0),sK1)
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

fof(f73,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,X5)
      | k2_enumset1(X4,X4,X4,X4) = k3_xboole_0(k2_enumset1(X4,X4,X4,X4),X5) ) ),
    inference(resolution,[],[f52,f39])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_enumset1(X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f32,f46])).

fof(f46,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f33,f44])).

fof(f33,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f79,plain,(
    sK1 != k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(superposition,[],[f47,f48])).

fof(f47,plain,(
    sK1 != k3_tarski(k2_enumset1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
    inference(definition_unfolding,[],[f26,f45,f46])).

fof(f26,plain,(
    sK1 != k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:43:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.56  % (18026)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.55/0.56  % (18028)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.55/0.56  % (18036)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.55/0.57  % (18036)Refutation not found, incomplete strategy% (18036)------------------------------
% 1.55/0.57  % (18036)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.57  % (18036)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.57  
% 1.55/0.57  % (18036)Memory used [KB]: 10618
% 1.55/0.57  % (18036)Time elapsed: 0.133 s
% 1.55/0.57  % (18036)------------------------------
% 1.55/0.57  % (18036)------------------------------
% 1.55/0.57  % (18035)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.55/0.58  % (18027)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.55/0.58  % (18055)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.74/0.58  % (18027)Refutation not found, incomplete strategy% (18027)------------------------------
% 1.74/0.58  % (18027)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.74/0.58  % (18027)Termination reason: Refutation not found, incomplete strategy
% 1.74/0.58  
% 1.74/0.58  % (18027)Memory used [KB]: 1663
% 1.74/0.58  % (18027)Time elapsed: 0.153 s
% 1.74/0.58  % (18027)------------------------------
% 1.74/0.58  % (18027)------------------------------
% 1.74/0.58  % (18055)Refutation not found, incomplete strategy% (18055)------------------------------
% 1.74/0.58  % (18055)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.74/0.58  % (18055)Termination reason: Refutation not found, incomplete strategy
% 1.74/0.58  
% 1.74/0.58  % (18055)Memory used [KB]: 1663
% 1.74/0.58  % (18055)Time elapsed: 0.149 s
% 1.74/0.58  % (18055)------------------------------
% 1.74/0.58  % (18055)------------------------------
% 1.74/0.59  % (18042)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.74/0.59  % (18043)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.74/0.59  % (18042)Refutation not found, incomplete strategy% (18042)------------------------------
% 1.74/0.59  % (18042)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.74/0.59  % (18032)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.74/0.59  % (18043)Refutation not found, incomplete strategy% (18043)------------------------------
% 1.74/0.59  % (18043)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.74/0.59  % (18031)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.74/0.59  % (18034)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.74/0.59  % (18042)Termination reason: Refutation not found, incomplete strategy
% 1.74/0.59  
% 1.74/0.59  % (18042)Memory used [KB]: 10618
% 1.74/0.59  % (18042)Time elapsed: 0.151 s
% 1.74/0.59  % (18042)------------------------------
% 1.74/0.59  % (18042)------------------------------
% 1.74/0.59  % (18043)Termination reason: Refutation not found, incomplete strategy
% 1.74/0.59  
% 1.74/0.59  % (18043)Memory used [KB]: 1791
% 1.74/0.59  % (18043)Time elapsed: 0.164 s
% 1.74/0.59  % (18043)------------------------------
% 1.74/0.59  % (18043)------------------------------
% 1.74/0.59  % (18029)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.74/0.60  % (18031)Refutation found. Thanks to Tanya!
% 1.74/0.60  % SZS status Theorem for theBenchmark
% 1.74/0.60  % SZS output start Proof for theBenchmark
% 1.74/0.60  fof(f125,plain,(
% 1.74/0.60    $false),
% 1.74/0.60    inference(trivial_inequality_removal,[],[f123])).
% 1.74/0.60  fof(f123,plain,(
% 1.74/0.60    sK1 != sK1),
% 1.74/0.60    inference(superposition,[],[f79,f122])).
% 1.74/0.60  fof(f122,plain,(
% 1.74/0.60    sK1 = k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0)))),
% 1.74/0.60    inference(forward_demodulation,[],[f121,f51])).
% 1.74/0.60  fof(f51,plain,(
% 1.74/0.60    ( ! [X0] : (k3_tarski(k2_enumset1(X0,X0,X0,k1_xboole_0)) = X0) )),
% 1.74/0.60    inference(definition_unfolding,[],[f30,f45])).
% 1.74/0.60  fof(f45,plain,(
% 1.74/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 1.74/0.60    inference(definition_unfolding,[],[f41,f44])).
% 1.74/0.60  fof(f44,plain,(
% 1.74/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.74/0.60    inference(definition_unfolding,[],[f40,f43])).
% 1.74/0.60  fof(f43,plain,(
% 1.74/0.60    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.74/0.60    inference(cnf_transformation,[],[f12])).
% 1.74/0.60  fof(f12,axiom,(
% 1.74/0.60    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.74/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.74/0.60  fof(f40,plain,(
% 1.74/0.60    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.74/0.60    inference(cnf_transformation,[],[f11])).
% 1.74/0.60  fof(f11,axiom,(
% 1.74/0.60    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.74/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.74/0.60  fof(f41,plain,(
% 1.74/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.74/0.60    inference(cnf_transformation,[],[f15])).
% 1.74/0.60  fof(f15,axiom,(
% 1.74/0.60    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.74/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.74/0.60  fof(f30,plain,(
% 1.74/0.60    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.74/0.60    inference(cnf_transformation,[],[f5])).
% 1.74/0.60  fof(f5,axiom,(
% 1.74/0.60    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.74/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 1.74/0.60  fof(f121,plain,(
% 1.74/0.60    k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0))) = k3_tarski(k2_enumset1(sK1,sK1,sK1,k1_xboole_0))),
% 1.74/0.60    inference(forward_demodulation,[],[f118,f109])).
% 1.74/0.60  fof(f109,plain,(
% 1.74/0.60    ( ! [X7] : (k1_xboole_0 = k5_xboole_0(X7,X7)) )),
% 1.74/0.60    inference(forward_demodulation,[],[f108,f97])).
% 1.74/0.60  fof(f97,plain,(
% 1.74/0.60    ( ! [X3] : (k5_xboole_0(X3,k1_xboole_0) = X3) )),
% 1.74/0.60    inference(forward_demodulation,[],[f96,f58])).
% 1.74/0.60  fof(f58,plain,(
% 1.74/0.60    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)) )),
% 1.74/0.60    inference(superposition,[],[f56,f42])).
% 1.74/0.60  fof(f42,plain,(
% 1.74/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.74/0.60    inference(cnf_transformation,[],[f2])).
% 1.74/0.60  fof(f2,axiom,(
% 1.74/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.74/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.74/0.60  fof(f56,plain,(
% 1.74/0.60    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 1.74/0.60    inference(resolution,[],[f39,f35])).
% 1.74/0.60  fof(f35,plain,(
% 1.74/0.60    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.74/0.60    inference(cnf_transformation,[],[f7])).
% 1.74/0.60  fof(f7,axiom,(
% 1.74/0.60    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.74/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.74/0.60  fof(f39,plain,(
% 1.74/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.74/0.60    inference(cnf_transformation,[],[f19])).
% 1.74/0.60  fof(f19,plain,(
% 1.74/0.60    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.74/0.60    inference(ennf_transformation,[],[f6])).
% 1.74/0.60  fof(f6,axiom,(
% 1.74/0.60    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.74/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.74/0.60  fof(f96,plain,(
% 1.74/0.60    ( ! [X3] : (k5_xboole_0(X3,k3_xboole_0(X3,k1_xboole_0)) = X3) )),
% 1.74/0.60    inference(forward_demodulation,[],[f92,f77])).
% 1.74/0.60  fof(f77,plain,(
% 1.74/0.60    ( ! [X0] : (k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0) )),
% 1.74/0.60    inference(superposition,[],[f48,f51])).
% 1.74/0.60  fof(f48,plain,(
% 1.74/0.60    ( ! [X0,X1] : (k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(X1,X1,X1,X0))) )),
% 1.74/0.60    inference(definition_unfolding,[],[f27,f45,f45])).
% 1.74/0.60  fof(f27,plain,(
% 1.74/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.74/0.60    inference(cnf_transformation,[],[f1])).
% 1.74/0.60  fof(f1,axiom,(
% 1.74/0.60    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.74/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.74/0.60  fof(f92,plain,(
% 1.74/0.60    ( ! [X3] : (k5_xboole_0(X3,k3_xboole_0(X3,k1_xboole_0)) = k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X3))) )),
% 1.74/0.60    inference(superposition,[],[f77,f49])).
% 1.74/0.60  fof(f49,plain,(
% 1.74/0.60    ( ! [X0,X1] : (k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 1.74/0.60    inference(definition_unfolding,[],[f28,f45,f45,f34])).
% 1.74/0.60  fof(f34,plain,(
% 1.74/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.74/0.60    inference(cnf_transformation,[],[f4])).
% 1.74/0.60  fof(f4,axiom,(
% 1.74/0.60    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.74/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.74/0.60  fof(f28,plain,(
% 1.74/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.74/0.60    inference(cnf_transformation,[],[f8])).
% 1.74/0.60  fof(f8,axiom,(
% 1.74/0.60    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.74/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.74/0.60  fof(f108,plain,(
% 1.74/0.60    ( ! [X7] : (k5_xboole_0(k1_xboole_0,k1_xboole_0) = k5_xboole_0(X7,X7)) )),
% 1.74/0.60    inference(forward_demodulation,[],[f107,f56])).
% 1.74/0.60  fof(f107,plain,(
% 1.74/0.60    ( ! [X7] : (k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X7)) = k5_xboole_0(X7,X7)) )),
% 1.74/0.60    inference(forward_demodulation,[],[f104,f57])).
% 1.74/0.60  fof(f57,plain,(
% 1.74/0.60    ( ! [X1] : (k3_xboole_0(X1,X1) = X1) )),
% 1.74/0.60    inference(resolution,[],[f39,f54])).
% 1.74/0.60  fof(f54,plain,(
% 1.74/0.60    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.74/0.60    inference(equality_resolution,[],[f37])).
% 1.74/0.60  fof(f37,plain,(
% 1.74/0.60    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.74/0.60    inference(cnf_transformation,[],[f24])).
% 1.74/0.60  fof(f24,plain,(
% 1.74/0.60    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.74/0.60    inference(flattening,[],[f23])).
% 1.74/0.60  fof(f23,plain,(
% 1.74/0.60    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.74/0.60    inference(nnf_transformation,[],[f3])).
% 1.74/0.60  fof(f3,axiom,(
% 1.74/0.60    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.74/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.74/0.60  fof(f104,plain,(
% 1.74/0.60    ( ! [X7] : (k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X7)) = k5_xboole_0(X7,k3_xboole_0(X7,X7))) )),
% 1.74/0.60    inference(superposition,[],[f89,f77])).
% 1.74/0.60  fof(f89,plain,(
% 1.74/0.60    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k3_tarski(k2_enumset1(X0,X0,X0,X1)),k3_xboole_0(X1,k3_tarski(k2_enumset1(X0,X0,X0,X1))))) )),
% 1.74/0.60    inference(forward_demodulation,[],[f50,f42])).
% 1.74/0.60  fof(f50,plain,(
% 1.74/0.60    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k3_tarski(k2_enumset1(X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k2_enumset1(X0,X0,X0,X1)),X1))) )),
% 1.74/0.60    inference(definition_unfolding,[],[f29,f34,f34,f45])).
% 1.74/0.60  fof(f29,plain,(
% 1.74/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 1.74/0.60    inference(cnf_transformation,[],[f9])).
% 1.74/0.60  fof(f9,axiom,(
% 1.74/0.60    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 1.74/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 1.74/0.60  fof(f118,plain,(
% 1.74/0.60    k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0))) = k3_tarski(k2_enumset1(sK1,sK1,sK1,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0))))),
% 1.74/0.60    inference(superposition,[],[f49,f114])).
% 1.74/0.60  fof(f114,plain,(
% 1.74/0.60    k2_enumset1(sK0,sK0,sK0,sK0) = k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 1.74/0.60    inference(resolution,[],[f73,f25])).
% 1.74/0.60  fof(f25,plain,(
% 1.74/0.60    r2_hidden(sK0,sK1)),
% 1.74/0.60    inference(cnf_transformation,[],[f21])).
% 1.74/0.60  fof(f21,plain,(
% 1.74/0.60    sK1 != k2_xboole_0(k1_tarski(sK0),sK1) & r2_hidden(sK0,sK1)),
% 1.74/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f20])).
% 1.74/0.60  fof(f20,plain,(
% 1.74/0.60    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1)) => (sK1 != k2_xboole_0(k1_tarski(sK0),sK1) & r2_hidden(sK0,sK1))),
% 1.74/0.60    introduced(choice_axiom,[])).
% 1.74/0.60  fof(f18,plain,(
% 1.74/0.60    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1))),
% 1.74/0.60    inference(ennf_transformation,[],[f17])).
% 1.74/0.60  fof(f17,negated_conjecture,(
% 1.74/0.60    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 1.74/0.60    inference(negated_conjecture,[],[f16])).
% 1.74/0.60  fof(f16,conjecture,(
% 1.74/0.60    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 1.74/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).
% 1.74/0.60  fof(f73,plain,(
% 1.74/0.60    ( ! [X4,X5] : (~r2_hidden(X4,X5) | k2_enumset1(X4,X4,X4,X4) = k3_xboole_0(k2_enumset1(X4,X4,X4,X4),X5)) )),
% 1.74/0.60    inference(resolution,[],[f52,f39])).
% 1.74/0.60  fof(f52,plain,(
% 1.74/0.60    ( ! [X0,X1] : (r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.74/0.60    inference(definition_unfolding,[],[f32,f46])).
% 1.74/0.60  fof(f46,plain,(
% 1.74/0.60    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.74/0.60    inference(definition_unfolding,[],[f33,f44])).
% 1.74/0.60  fof(f33,plain,(
% 1.74/0.60    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.74/0.60    inference(cnf_transformation,[],[f10])).
% 1.74/0.60  fof(f10,axiom,(
% 1.74/0.60    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.74/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.74/0.60  fof(f32,plain,(
% 1.74/0.60    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.74/0.60    inference(cnf_transformation,[],[f22])).
% 1.74/0.60  fof(f22,plain,(
% 1.74/0.60    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 1.74/0.60    inference(nnf_transformation,[],[f14])).
% 1.74/0.60  fof(f14,axiom,(
% 1.74/0.60    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.74/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.74/0.60  fof(f79,plain,(
% 1.74/0.60    sK1 != k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0)))),
% 1.74/0.60    inference(superposition,[],[f47,f48])).
% 1.74/0.60  fof(f47,plain,(
% 1.74/0.60    sK1 != k3_tarski(k2_enumset1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),sK1))),
% 1.74/0.60    inference(definition_unfolding,[],[f26,f45,f46])).
% 1.74/0.60  fof(f26,plain,(
% 1.74/0.60    sK1 != k2_xboole_0(k1_tarski(sK0),sK1)),
% 1.74/0.60    inference(cnf_transformation,[],[f21])).
% 1.74/0.60  % SZS output end Proof for theBenchmark
% 1.74/0.60  % (18031)------------------------------
% 1.74/0.60  % (18031)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.74/0.60  % (18031)Termination reason: Refutation
% 1.74/0.60  
% 1.74/0.60  % (18031)Memory used [KB]: 1791
% 1.74/0.60  % (18031)Time elapsed: 0.161 s
% 1.74/0.60  % (18031)------------------------------
% 1.74/0.60  % (18031)------------------------------
% 1.74/0.60  % (18030)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.74/0.61  % (18038)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.74/0.62  % (18040)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.74/0.62  % (18039)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.74/0.62  % (18048)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.74/0.62  % (18025)Success in time 0.255 s
%------------------------------------------------------------------------------
