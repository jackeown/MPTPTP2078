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
% DateTime   : Thu Dec  3 12:35:37 EST 2020

% Result     : Theorem 2.48s
% Output     : Refutation 2.48s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 148 expanded)
%              Number of leaves         :   18 (  49 expanded)
%              Depth                    :   10
%              Number of atoms          :   86 ( 178 expanded)
%              Number of equality atoms :   61 ( 148 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2185,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f58,f110,f918])).

fof(f918,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X0,X1))) = X2
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f815,f33])).

fof(f33,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f815,plain,(
    ! [X10,X8,X9] :
      ( k5_xboole_0(X8,k5_xboole_0(k3_xboole_0(X8,X9),X10)) = X10
      | ~ r1_tarski(X8,X9) ) ),
    inference(backward_demodulation,[],[f80,f98])).

fof(f98,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f73,f33])).

fof(f73,plain,(
    ! [X2] : k5_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(subsumption_resolution,[],[f71,f61])).

fof(f61,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f71,plain,(
    ! [X2] :
      ( k5_xboole_0(X2,k1_xboole_0) = X2
      | ~ r1_tarski(X2,X2) ) ),
    inference(superposition,[],[f56,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f41,f36])).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f56,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f29,f48])).

fof(f48,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f35,f36])).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f29,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f80,plain,(
    ! [X10,X8,X9] :
      ( k5_xboole_0(X8,k5_xboole_0(k3_xboole_0(X8,X9),X10)) = k5_xboole_0(k1_xboole_0,X10)
      | ~ r1_tarski(X8,X9) ) ),
    inference(superposition,[],[f43,f59])).

fof(f43,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f110,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) ),
    inference(forward_demodulation,[],[f55,f32])).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f55,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) ),
    inference(definition_unfolding,[],[f27,f53,f48,f54,f53])).

fof(f54,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f28,f53])).

fof(f28,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f53,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f34,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f42,f51])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f44,f50])).

fof(f50,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f45,f49])).

fof(f49,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f46,f47])).

fof(f47,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f46,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f44,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f42,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f34,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f27,plain,(
    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f22])).

fof(f22,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))
   => k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_zfmisc_1)).

fof(f58,plain,(
    ! [X0,X1] : r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f31,f54,f53])).

fof(f31,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n014.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 14:11:07 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.50  % (24720)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.51  % (24725)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.28/0.52  % (24731)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.28/0.53  % (24727)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.28/0.53  % (24735)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.28/0.53  % (24730)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.28/0.54  % (24730)Refutation not found, incomplete strategy% (24730)------------------------------
% 1.28/0.54  % (24730)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.54  % (24730)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.54  
% 1.28/0.54  % (24730)Memory used [KB]: 10618
% 1.28/0.54  % (24730)Time elapsed: 0.125 s
% 1.28/0.54  % (24730)------------------------------
% 1.28/0.54  % (24730)------------------------------
% 1.28/0.54  % (24744)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.28/0.54  % (24722)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.28/0.54  % (24721)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.28/0.54  % (24726)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.28/0.54  % (24724)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.28/0.54  % (24721)Refutation not found, incomplete strategy% (24721)------------------------------
% 1.28/0.54  % (24721)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.54  % (24721)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.54  
% 1.28/0.54  % (24721)Memory used [KB]: 1663
% 1.28/0.54  % (24721)Time elapsed: 0.124 s
% 1.28/0.54  % (24721)------------------------------
% 1.28/0.54  % (24721)------------------------------
% 1.28/0.54  % (24723)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.28/0.54  % (24729)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.28/0.54  % (24736)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.28/0.54  % (24731)Refutation not found, incomplete strategy% (24731)------------------------------
% 1.28/0.54  % (24731)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.54  % (24731)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.54  
% 1.28/0.54  % (24731)Memory used [KB]: 6140
% 1.28/0.54  % (24731)Time elapsed: 0.136 s
% 1.28/0.54  % (24731)------------------------------
% 1.28/0.54  % (24731)------------------------------
% 1.28/0.54  % (24743)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.28/0.54  % (24749)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.28/0.54  % (24749)Refutation not found, incomplete strategy% (24749)------------------------------
% 1.28/0.54  % (24749)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.54  % (24749)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.54  
% 1.28/0.54  % (24749)Memory used [KB]: 1663
% 1.28/0.54  % (24749)Time elapsed: 0.140 s
% 1.28/0.54  % (24749)------------------------------
% 1.28/0.54  % (24749)------------------------------
% 1.28/0.55  % (24728)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.28/0.55  % (24747)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.28/0.55  % (24747)Refutation not found, incomplete strategy% (24747)------------------------------
% 1.28/0.55  % (24747)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.55  % (24747)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.55  
% 1.28/0.55  % (24747)Memory used [KB]: 6140
% 1.28/0.55  % (24747)Time elapsed: 0.140 s
% 1.28/0.55  % (24747)------------------------------
% 1.28/0.55  % (24747)------------------------------
% 1.28/0.55  % (24742)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.28/0.55  % (24736)Refutation not found, incomplete strategy% (24736)------------------------------
% 1.28/0.55  % (24736)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.55  % (24736)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.55  
% 1.28/0.55  % (24736)Memory used [KB]: 10618
% 1.28/0.55  % (24736)Time elapsed: 0.140 s
% 1.28/0.55  % (24736)------------------------------
% 1.28/0.55  % (24736)------------------------------
% 1.28/0.55  % (24746)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.28/0.55  % (24738)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.28/0.55  % (24741)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.46/0.55  % (24739)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.46/0.55  % (24738)Refutation not found, incomplete strategy% (24738)------------------------------
% 1.46/0.55  % (24738)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.55  % (24744)Refutation not found, incomplete strategy% (24744)------------------------------
% 1.46/0.55  % (24744)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.55  % (24744)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.55  
% 1.46/0.55  % (24744)Memory used [KB]: 10618
% 1.46/0.55  % (24744)Time elapsed: 0.137 s
% 1.46/0.55  % (24744)------------------------------
% 1.46/0.55  % (24744)------------------------------
% 1.46/0.55  % (24745)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.46/0.55  % (24745)Refutation not found, incomplete strategy% (24745)------------------------------
% 1.46/0.55  % (24745)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.55  % (24745)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.55  
% 1.46/0.55  % (24745)Memory used [KB]: 6140
% 1.46/0.55  % (24745)Time elapsed: 0.140 s
% 1.46/0.55  % (24745)------------------------------
% 1.46/0.55  % (24745)------------------------------
% 1.46/0.55  % (24734)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.46/0.55  % (24734)Refutation not found, incomplete strategy% (24734)------------------------------
% 1.46/0.55  % (24734)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.55  % (24734)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.55  
% 1.46/0.55  % (24734)Memory used [KB]: 1663
% 1.46/0.55  % (24734)Time elapsed: 0.114 s
% 1.46/0.55  % (24734)------------------------------
% 1.46/0.55  % (24734)------------------------------
% 1.46/0.55  % (24733)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.46/0.55  % (24737)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.46/0.55  % (24737)Refutation not found, incomplete strategy% (24737)------------------------------
% 1.46/0.55  % (24737)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.55  % (24737)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.55  
% 1.46/0.55  % (24737)Memory used [KB]: 1663
% 1.46/0.55  % (24737)Time elapsed: 0.151 s
% 1.46/0.55  % (24737)------------------------------
% 1.46/0.55  % (24737)------------------------------
% 1.46/0.56  % (24746)Refutation not found, incomplete strategy% (24746)------------------------------
% 1.46/0.56  % (24746)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.56  % (24746)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.56  
% 1.46/0.56  % (24746)Memory used [KB]: 6140
% 1.46/0.56  % (24746)Time elapsed: 0.148 s
% 1.46/0.56  % (24746)------------------------------
% 1.46/0.56  % (24746)------------------------------
% 1.46/0.56  % (24738)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.56  
% 1.46/0.56  % (24738)Memory used [KB]: 1663
% 1.46/0.56  % (24738)Time elapsed: 0.143 s
% 1.46/0.56  % (24738)------------------------------
% 1.46/0.56  % (24738)------------------------------
% 1.46/0.57  % (24748)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.46/0.57  % (24740)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.46/0.57  % (24732)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.46/0.58  % (24732)Refutation not found, incomplete strategy% (24732)------------------------------
% 1.46/0.58  % (24732)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.58  % (24732)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.58  
% 1.46/0.58  % (24732)Memory used [KB]: 10618
% 1.46/0.58  % (24732)Time elapsed: 0.139 s
% 1.46/0.58  % (24732)------------------------------
% 1.46/0.58  % (24732)------------------------------
% 1.46/0.58  % (24748)Refutation not found, incomplete strategy% (24748)------------------------------
% 1.46/0.58  % (24748)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.58  % (24748)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.58  
% 1.46/0.58  % (24748)Memory used [KB]: 10618
% 1.46/0.58  % (24748)Time elapsed: 0.143 s
% 1.46/0.58  % (24748)------------------------------
% 1.46/0.58  % (24748)------------------------------
% 2.00/0.66  % (24723)Refutation not found, incomplete strategy% (24723)------------------------------
% 2.00/0.66  % (24723)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.00/0.66  % (24723)Termination reason: Refutation not found, incomplete strategy
% 2.00/0.66  
% 2.00/0.66  % (24723)Memory used [KB]: 6140
% 2.00/0.66  % (24723)Time elapsed: 0.248 s
% 2.00/0.66  % (24723)------------------------------
% 2.00/0.66  % (24723)------------------------------
% 2.00/0.67  % (24722)Refutation not found, incomplete strategy% (24722)------------------------------
% 2.00/0.67  % (24722)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.00/0.67  % (24722)Termination reason: Refutation not found, incomplete strategy
% 2.00/0.67  
% 2.00/0.67  % (24722)Memory used [KB]: 6140
% 2.00/0.67  % (24722)Time elapsed: 0.256 s
% 2.00/0.67  % (24722)------------------------------
% 2.00/0.67  % (24722)------------------------------
% 2.00/0.67  % (24728)Refutation not found, incomplete strategy% (24728)------------------------------
% 2.00/0.67  % (24728)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.00/0.67  % (24728)Termination reason: Refutation not found, incomplete strategy
% 2.00/0.67  
% 2.00/0.67  % (24728)Memory used [KB]: 6140
% 2.00/0.67  % (24728)Time elapsed: 0.244 s
% 2.00/0.67  % (24728)------------------------------
% 2.00/0.67  % (24728)------------------------------
% 2.00/0.67  % (24751)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.00/0.67  % (24760)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 2.00/0.67  % (24753)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.00/0.68  % (24752)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.00/0.68  % (24753)Refutation not found, incomplete strategy% (24753)------------------------------
% 2.00/0.68  % (24753)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.00/0.68  % (24753)Termination reason: Refutation not found, incomplete strategy
% 2.00/0.68  
% 2.00/0.68  % (24753)Memory used [KB]: 10618
% 2.00/0.68  % (24753)Time elapsed: 0.105 s
% 2.00/0.68  % (24753)------------------------------
% 2.00/0.68  % (24753)------------------------------
% 2.00/0.68  % (24752)Refutation not found, incomplete strategy% (24752)------------------------------
% 2.00/0.68  % (24752)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.00/0.68  % (24752)Termination reason: Refutation not found, incomplete strategy
% 2.00/0.68  
% 2.00/0.68  % (24752)Memory used [KB]: 6140
% 2.00/0.68  % (24752)Time elapsed: 0.105 s
% 2.00/0.68  % (24752)------------------------------
% 2.00/0.68  % (24752)------------------------------
% 2.00/0.68  % (24750)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.00/0.68  % (24755)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 2.00/0.68  % (24755)Refutation not found, incomplete strategy% (24755)------------------------------
% 2.00/0.68  % (24755)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.00/0.68  % (24755)Termination reason: Refutation not found, incomplete strategy
% 2.00/0.68  
% 2.00/0.68  % (24755)Memory used [KB]: 1663
% 2.00/0.68  % (24755)Time elapsed: 0.095 s
% 2.00/0.68  % (24755)------------------------------
% 2.00/0.68  % (24755)------------------------------
% 2.00/0.68  % (24754)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.00/0.68  % (24761)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 2.00/0.68  % (24754)Refutation not found, incomplete strategy% (24754)------------------------------
% 2.00/0.68  % (24754)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.00/0.68  % (24754)Termination reason: Refutation not found, incomplete strategy
% 2.00/0.68  
% 2.00/0.68  % (24754)Memory used [KB]: 10618
% 2.00/0.68  % (24754)Time elapsed: 0.103 s
% 2.00/0.68  % (24754)------------------------------
% 2.00/0.68  % (24754)------------------------------
% 2.00/0.68  % (24761)Refutation not found, incomplete strategy% (24761)------------------------------
% 2.00/0.68  % (24761)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.00/0.68  % (24761)Termination reason: Refutation not found, incomplete strategy
% 2.00/0.68  
% 2.00/0.68  % (24761)Memory used [KB]: 10618
% 2.00/0.68  % (24761)Time elapsed: 0.107 s
% 2.00/0.68  % (24761)------------------------------
% 2.00/0.68  % (24761)------------------------------
% 2.00/0.68  % (24759)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 2.00/0.68  % (24759)Refutation not found, incomplete strategy% (24759)------------------------------
% 2.00/0.68  % (24759)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.00/0.68  % (24759)Termination reason: Refutation not found, incomplete strategy
% 2.00/0.68  
% 2.00/0.68  % (24759)Memory used [KB]: 10618
% 2.00/0.68  % (24759)Time elapsed: 0.106 s
% 2.00/0.68  % (24759)------------------------------
% 2.00/0.68  % (24759)------------------------------
% 2.00/0.69  % (24756)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 2.00/0.69  % (24757)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 2.00/0.69  % (24756)Refutation not found, incomplete strategy% (24756)------------------------------
% 2.00/0.69  % (24756)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.00/0.69  % (24756)Termination reason: Refutation not found, incomplete strategy
% 2.00/0.69  
% 2.00/0.69  % (24756)Memory used [KB]: 10618
% 2.00/0.69  % (24756)Time elapsed: 0.106 s
% 2.00/0.69  % (24756)------------------------------
% 2.00/0.69  % (24756)------------------------------
% 2.00/0.69  % (24735)Refutation not found, incomplete strategy% (24735)------------------------------
% 2.00/0.69  % (24735)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.00/0.69  % (24735)Termination reason: Refutation not found, incomplete strategy
% 2.00/0.69  
% 2.00/0.69  % (24735)Memory used [KB]: 6140
% 2.00/0.69  % (24735)Time elapsed: 0.238 s
% 2.00/0.69  % (24735)------------------------------
% 2.00/0.69  % (24735)------------------------------
% 2.00/0.69  % (24758)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 2.48/0.70  % (24762)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 2.48/0.71  % (24763)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 2.48/0.72  % (24763)Refutation not found, incomplete strategy% (24763)------------------------------
% 2.48/0.72  % (24763)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.48/0.72  % (24763)Termination reason: Refutation not found, incomplete strategy
% 2.48/0.72  
% 2.48/0.72  % (24763)Memory used [KB]: 10618
% 2.48/0.72  % (24763)Time elapsed: 0.029 s
% 2.48/0.72  % (24763)------------------------------
% 2.48/0.72  % (24763)------------------------------
% 2.48/0.72  % (24724)Refutation found. Thanks to Tanya!
% 2.48/0.72  % SZS status Theorem for theBenchmark
% 2.48/0.72  % SZS output start Proof for theBenchmark
% 2.48/0.72  fof(f2185,plain,(
% 2.48/0.72    $false),
% 2.48/0.72    inference(unit_resulting_resolution,[],[f58,f110,f918])).
% 2.48/0.72  fof(f918,plain,(
% 2.48/0.72    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X0,X1))) = X2 | ~r1_tarski(X0,X1)) )),
% 2.48/0.72    inference(superposition,[],[f815,f33])).
% 2.48/0.72  fof(f33,plain,(
% 2.48/0.72    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 2.48/0.72    inference(cnf_transformation,[],[f2])).
% 2.48/0.72  fof(f2,axiom,(
% 2.48/0.72    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 2.48/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 2.48/0.72  fof(f815,plain,(
% 2.48/0.72    ( ! [X10,X8,X9] : (k5_xboole_0(X8,k5_xboole_0(k3_xboole_0(X8,X9),X10)) = X10 | ~r1_tarski(X8,X9)) )),
% 2.48/0.72    inference(backward_demodulation,[],[f80,f98])).
% 2.48/0.72  fof(f98,plain,(
% 2.48/0.72    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 2.48/0.72    inference(superposition,[],[f73,f33])).
% 2.48/0.72  fof(f73,plain,(
% 2.48/0.72    ( ! [X2] : (k5_xboole_0(X2,k1_xboole_0) = X2) )),
% 2.48/0.72    inference(subsumption_resolution,[],[f71,f61])).
% 2.48/0.72  fof(f61,plain,(
% 2.48/0.72    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.48/0.72    inference(equality_resolution,[],[f38])).
% 2.48/0.72  fof(f38,plain,(
% 2.48/0.72    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.48/0.72    inference(cnf_transformation,[],[f25])).
% 2.48/0.72  fof(f25,plain,(
% 2.48/0.72    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.48/0.72    inference(flattening,[],[f24])).
% 2.48/0.72  fof(f24,plain,(
% 2.48/0.72    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.48/0.72    inference(nnf_transformation,[],[f4])).
% 2.48/0.72  fof(f4,axiom,(
% 2.48/0.72    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.48/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.48/0.72  fof(f71,plain,(
% 2.48/0.72    ( ! [X2] : (k5_xboole_0(X2,k1_xboole_0) = X2 | ~r1_tarski(X2,X2)) )),
% 2.48/0.72    inference(superposition,[],[f56,f59])).
% 2.48/0.72  fof(f59,plain,(
% 2.48/0.72    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) | ~r1_tarski(X0,X1)) )),
% 2.48/0.72    inference(definition_unfolding,[],[f41,f36])).
% 2.48/0.72  fof(f36,plain,(
% 2.48/0.72    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.48/0.72    inference(cnf_transformation,[],[f6])).
% 2.48/0.72  fof(f6,axiom,(
% 2.48/0.72    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.48/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.48/0.72  fof(f41,plain,(
% 2.48/0.72    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 2.48/0.72    inference(cnf_transformation,[],[f26])).
% 2.48/0.72  fof(f26,plain,(
% 2.48/0.72    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 2.48/0.72    inference(nnf_transformation,[],[f5])).
% 2.48/0.72  fof(f5,axiom,(
% 2.48/0.72    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 2.48/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 2.48/0.72  fof(f56,plain,(
% 2.48/0.72    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0) )),
% 2.48/0.72    inference(definition_unfolding,[],[f29,f48])).
% 2.48/0.72  fof(f48,plain,(
% 2.48/0.72    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 2.48/0.72    inference(definition_unfolding,[],[f35,f36])).
% 2.48/0.72  fof(f35,plain,(
% 2.48/0.72    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.48/0.72    inference(cnf_transformation,[],[f9])).
% 2.48/0.72  fof(f9,axiom,(
% 2.48/0.72    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.48/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 2.48/0.72  fof(f29,plain,(
% 2.48/0.72    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 2.48/0.72    inference(cnf_transformation,[],[f20])).
% 2.48/0.72  fof(f20,plain,(
% 2.48/0.72    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 2.48/0.72    inference(rectify,[],[f3])).
% 2.48/0.72  fof(f3,axiom,(
% 2.48/0.72    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 2.48/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 2.48/0.72  fof(f80,plain,(
% 2.48/0.72    ( ! [X10,X8,X9] : (k5_xboole_0(X8,k5_xboole_0(k3_xboole_0(X8,X9),X10)) = k5_xboole_0(k1_xboole_0,X10) | ~r1_tarski(X8,X9)) )),
% 2.48/0.72    inference(superposition,[],[f43,f59])).
% 2.48/0.72  fof(f43,plain,(
% 2.48/0.72    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.48/0.72    inference(cnf_transformation,[],[f8])).
% 2.48/0.72  fof(f8,axiom,(
% 2.48/0.72    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.48/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.48/0.72  fof(f110,plain,(
% 2.48/0.72    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))),
% 2.48/0.72    inference(forward_demodulation,[],[f55,f32])).
% 2.48/0.72  fof(f32,plain,(
% 2.48/0.72    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.48/0.72    inference(cnf_transformation,[],[f1])).
% 2.48/0.72  fof(f1,axiom,(
% 2.48/0.72    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.48/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.48/0.72  fof(f55,plain,(
% 2.48/0.72    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))),
% 2.48/0.72    inference(definition_unfolding,[],[f27,f53,f48,f54,f53])).
% 2.48/0.72  fof(f54,plain,(
% 2.48/0.72    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 2.48/0.72    inference(definition_unfolding,[],[f28,f53])).
% 2.48/0.72  fof(f28,plain,(
% 2.48/0.72    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.48/0.72    inference(cnf_transformation,[],[f10])).
% 2.48/0.72  fof(f10,axiom,(
% 2.48/0.72    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.48/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 2.48/0.72  fof(f53,plain,(
% 2.48/0.72    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.48/0.72    inference(definition_unfolding,[],[f34,f52])).
% 2.48/0.72  fof(f52,plain,(
% 2.48/0.72    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.48/0.72    inference(definition_unfolding,[],[f42,f51])).
% 2.48/0.72  fof(f51,plain,(
% 2.48/0.72    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.48/0.72    inference(definition_unfolding,[],[f44,f50])).
% 2.48/0.72  fof(f50,plain,(
% 2.48/0.72    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.48/0.72    inference(definition_unfolding,[],[f45,f49])).
% 2.48/0.72  fof(f49,plain,(
% 2.48/0.72    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.48/0.72    inference(definition_unfolding,[],[f46,f47])).
% 2.48/0.72  fof(f47,plain,(
% 2.48/0.72    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 2.48/0.72    inference(cnf_transformation,[],[f16])).
% 2.48/0.72  fof(f16,axiom,(
% 2.48/0.72    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 2.48/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 2.48/0.72  fof(f46,plain,(
% 2.48/0.72    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 2.48/0.72    inference(cnf_transformation,[],[f15])).
% 2.48/0.72  fof(f15,axiom,(
% 2.48/0.72    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 2.48/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 2.48/0.72  fof(f45,plain,(
% 2.48/0.72    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.48/0.72    inference(cnf_transformation,[],[f14])).
% 2.48/0.72  fof(f14,axiom,(
% 2.48/0.72    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 2.48/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 2.48/0.72  fof(f44,plain,(
% 2.48/0.72    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.48/0.72    inference(cnf_transformation,[],[f13])).
% 2.48/0.72  fof(f13,axiom,(
% 2.48/0.72    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 2.48/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 2.48/0.72  fof(f42,plain,(
% 2.48/0.72    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.48/0.72    inference(cnf_transformation,[],[f12])).
% 2.48/0.72  fof(f12,axiom,(
% 2.48/0.72    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.48/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 2.48/0.72  fof(f34,plain,(
% 2.48/0.72    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.48/0.72    inference(cnf_transformation,[],[f11])).
% 2.48/0.72  fof(f11,axiom,(
% 2.48/0.72    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.48/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.48/0.72  fof(f27,plain,(
% 2.48/0.72    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 2.48/0.72    inference(cnf_transformation,[],[f23])).
% 2.48/0.72  fof(f23,plain,(
% 2.48/0.72    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 2.48/0.72    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f22])).
% 2.48/0.72  fof(f22,plain,(
% 2.48/0.72    ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) => k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 2.48/0.72    introduced(choice_axiom,[])).
% 2.48/0.72  fof(f21,plain,(
% 2.48/0.72    ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 2.48/0.72    inference(ennf_transformation,[],[f19])).
% 2.48/0.72  fof(f19,negated_conjecture,(
% 2.48/0.72    ~! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 2.48/0.72    inference(negated_conjecture,[],[f18])).
% 2.48/0.72  fof(f18,conjecture,(
% 2.48/0.72    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 2.48/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_zfmisc_1)).
% 2.48/0.72  fof(f58,plain,(
% 2.48/0.72    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 2.48/0.72    inference(definition_unfolding,[],[f31,f54,f53])).
% 2.48/0.72  fof(f31,plain,(
% 2.48/0.72    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 2.48/0.72    inference(cnf_transformation,[],[f17])).
% 2.48/0.72  fof(f17,axiom,(
% 2.48/0.72    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 2.48/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).
% 2.48/0.72  % SZS output end Proof for theBenchmark
% 2.48/0.72  % (24724)------------------------------
% 2.48/0.72  % (24724)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.48/0.72  % (24724)Termination reason: Refutation
% 2.48/0.72  
% 2.48/0.72  % (24724)Memory used [KB]: 4093
% 2.48/0.72  % (24724)Time elapsed: 0.311 s
% 2.48/0.72  % (24724)------------------------------
% 2.48/0.72  % (24724)------------------------------
% 2.48/0.72  % (24719)Success in time 0.351 s
%------------------------------------------------------------------------------
