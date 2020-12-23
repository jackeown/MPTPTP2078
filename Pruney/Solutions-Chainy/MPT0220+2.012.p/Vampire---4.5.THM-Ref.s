%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:38 EST 2020

% Result     : Theorem 1.68s
% Output     : Refutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 268 expanded)
%              Number of leaves         :   19 (  90 expanded)
%              Depth                    :   16
%              Number of atoms          :  102 ( 314 expanded)
%              Number of equality atoms :   71 ( 258 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1001,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f53,f52,f903])).

fof(f903,plain,(
    ! [X14,X15] :
      ( k5_xboole_0(X15,k4_xboole_0(X14,X15)) = X14
      | ~ r1_tarski(X15,X14) ) ),
    inference(forward_demodulation,[],[f883,f28])).

fof(f28,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f883,plain,(
    ! [X14,X15] :
      ( k5_xboole_0(k4_xboole_0(X14,X15),X15) = X14
      | ~ r1_tarski(X15,X14) ) ),
    inference(superposition,[],[f431,f362])).

fof(f362,plain,(
    ! [X12,X13] :
      ( k5_xboole_0(X12,k4_xboole_0(X12,X13)) = X13
      | ~ r1_tarski(X13,X12) ) ),
    inference(superposition,[],[f51,f107])).

fof(f107,plain,(
    ! [X4,X5] :
      ( k4_xboole_0(X5,k4_xboole_0(X5,X4)) = X4
      | ~ r1_tarski(X4,X5) ) ),
    inference(superposition,[],[f54,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f33,f31])).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f54,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f27,f31,f31])).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f51,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f32,f31])).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f431,plain,(
    ! [X4,X5] : k5_xboole_0(X4,k5_xboole_0(X5,X4)) = X5 ),
    inference(superposition,[],[f427,f28])).

fof(f427,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(X2,X3)) = X3 ),
    inference(forward_demodulation,[],[f285,f262])).

fof(f262,plain,(
    ! [X2] : k5_xboole_0(k1_xboole_0,X2) = X2 ),
    inference(subsumption_resolution,[],[f187,f260])).

fof(f260,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f249,f56])).

fof(f56,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f249,plain,(
    ! [X6] :
      ( ~ r1_tarski(X6,X6)
      | r1_tarski(k1_xboole_0,X6) ) ),
    inference(trivial_inequality_removal,[],[f245])).

fof(f245,plain,(
    ! [X6] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(k1_xboole_0,X6)
      | ~ r1_tarski(X6,X6) ) ),
    inference(superposition,[],[f38,f232])).

fof(f232,plain,(
    ! [X3] :
      ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,X3)
      | ~ r1_tarski(X3,X3) ) ),
    inference(forward_demodulation,[],[f222,f97])).

fof(f97,plain,(
    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f88,f24])).

fof(f24,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f88,plain,(
    ! [X5] : k5_xboole_0(X5,k4_xboole_0(X5,X5)) = X5 ),
    inference(superposition,[],[f51,f24])).

fof(f222,plain,(
    ! [X3] :
      ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,X3)
      | ~ r1_tarski(X3,X3) ) ),
    inference(superposition,[],[f162,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f162,plain,(
    ! [X2] : k4_xboole_0(k1_xboole_0,X2) = k5_xboole_0(k1_xboole_0,k4_xboole_0(X2,X2)) ),
    inference(superposition,[],[f51,f106])).

fof(f106,plain,(
    ! [X9] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X9)) = k4_xboole_0(X9,X9) ),
    inference(superposition,[],[f54,f24])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f187,plain,(
    ! [X2] :
      ( k5_xboole_0(k1_xboole_0,X2) = X2
      | ~ r1_tarski(k1_xboole_0,X2) ) ),
    inference(superposition,[],[f179,f28])).

fof(f179,plain,(
    ! [X1] :
      ( k5_xboole_0(X1,k1_xboole_0) = X1
      | ~ r1_tarski(k1_xboole_0,X1) ) ),
    inference(superposition,[],[f88,f155])).

fof(f155,plain,(
    ! [X3] :
      ( k1_xboole_0 = k4_xboole_0(X3,X3)
      | ~ r1_tarski(k1_xboole_0,X3) ) ),
    inference(superposition,[],[f106,f55])).

fof(f285,plain,(
    ! [X2,X3] : k5_xboole_0(k1_xboole_0,X3) = k5_xboole_0(X2,k5_xboole_0(X2,X3)) ),
    inference(superposition,[],[f40,f263])).

fof(f263,plain,(
    ! [X5] : k1_xboole_0 = k5_xboole_0(X5,X5) ),
    inference(subsumption_resolution,[],[f186,f260])).

fof(f186,plain,(
    ! [X5] :
      ( k1_xboole_0 = k5_xboole_0(X5,X5)
      | ~ r1_tarski(k1_xboole_0,X5) ) ),
    inference(forward_demodulation,[],[f181,f24])).

fof(f181,plain,(
    ! [X5] :
      ( k1_xboole_0 = k5_xboole_0(X5,k4_xboole_0(X5,k1_xboole_0))
      | ~ r1_tarski(k1_xboole_0,X5) ) ),
    inference(superposition,[],[f51,f155])).

fof(f40,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f52,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(definition_unfolding,[],[f23,f49,f30,f50,f49])).

fof(f50,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f25,f49])).

fof(f25,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f29,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f39,f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f41,f46])).

fof(f46,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f42,f45])).

fof(f45,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f43,f44])).

fof(f44,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f43,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f41,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f39,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f29,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f23,plain,(
    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_zfmisc_1)).

fof(f53,plain,(
    ! [X0,X1] : r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f26,f50,f49])).

fof(f26,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 13:03:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (30993)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.50  % (30991)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.51  % (30986)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.51  % (30994)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.52  % (31008)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.52  % (30987)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.52  % (31013)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.52  % (30987)Refutation not found, incomplete strategy% (30987)------------------------------
% 0.20/0.52  % (30987)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (30987)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (30987)Memory used [KB]: 1663
% 0.20/0.52  % (30987)Time elapsed: 0.102 s
% 0.20/0.52  % (30987)------------------------------
% 0.20/0.52  % (30987)------------------------------
% 0.20/0.52  % (30997)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.52  % (30998)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.52  % (30992)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (30988)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.52  % (31011)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.52  % (31011)Refutation not found, incomplete strategy% (31011)------------------------------
% 0.20/0.52  % (31011)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (31009)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.52  % (31003)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.53  % (31011)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (31011)Memory used [KB]: 6140
% 0.20/0.53  % (31011)Time elapsed: 0.116 s
% 0.20/0.53  % (31011)------------------------------
% 0.20/0.53  % (31011)------------------------------
% 0.20/0.53  % (31015)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.53  % (31003)Refutation not found, incomplete strategy% (31003)------------------------------
% 0.20/0.53  % (31003)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (31003)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (31003)Memory used [KB]: 1663
% 0.20/0.53  % (31003)Time elapsed: 0.115 s
% 0.20/0.53  % (31003)------------------------------
% 0.20/0.53  % (31003)------------------------------
% 0.20/0.53  % (31015)Refutation not found, incomplete strategy% (31015)------------------------------
% 0.20/0.53  % (31015)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (31015)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (31015)Memory used [KB]: 1663
% 0.20/0.53  % (31015)Time elapsed: 0.091 s
% 0.20/0.53  % (31015)------------------------------
% 0.20/0.53  % (31015)------------------------------
% 0.20/0.53  % (31000)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.53  % (31000)Refutation not found, incomplete strategy% (31000)------------------------------
% 0.20/0.53  % (31000)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (31000)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (31000)Memory used [KB]: 1663
% 0.20/0.53  % (31000)Time elapsed: 0.116 s
% 0.20/0.53  % (31000)------------------------------
% 0.20/0.53  % (31000)------------------------------
% 0.20/0.53  % (30989)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.53  % (31007)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.53  % (30997)Refutation not found, incomplete strategy% (30997)------------------------------
% 0.20/0.53  % (30997)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (30997)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (30997)Memory used [KB]: 6140
% 0.20/0.53  % (30997)Time elapsed: 0.122 s
% 0.20/0.53  % (30997)------------------------------
% 0.20/0.53  % (30997)------------------------------
% 0.20/0.53  % (31006)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.53  % (31004)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.53  % (31004)Refutation not found, incomplete strategy% (31004)------------------------------
% 0.20/0.53  % (31004)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (31004)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (31004)Memory used [KB]: 1663
% 0.20/0.53  % (31004)Time elapsed: 0.139 s
% 0.20/0.53  % (31004)------------------------------
% 0.20/0.53  % (31004)------------------------------
% 0.20/0.54  % (30999)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.54  % (31001)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.54  % (31014)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.54  % (30990)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.54  % (31014)Refutation not found, incomplete strategy% (31014)------------------------------
% 0.20/0.54  % (31014)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (31014)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (31014)Memory used [KB]: 10618
% 0.20/0.54  % (31014)Time elapsed: 0.139 s
% 0.20/0.54  % (31014)------------------------------
% 0.20/0.54  % (31014)------------------------------
% 0.20/0.54  % (30998)Refutation not found, incomplete strategy% (30998)------------------------------
% 0.20/0.54  % (30998)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (30998)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (30998)Memory used [KB]: 10618
% 0.20/0.54  % (30998)Time elapsed: 0.143 s
% 0.20/0.54  % (30998)------------------------------
% 0.20/0.54  % (30998)------------------------------
% 0.20/0.54  % (31012)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.54  % (31012)Refutation not found, incomplete strategy% (31012)------------------------------
% 0.20/0.54  % (31012)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (31012)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (31012)Memory used [KB]: 6140
% 0.20/0.54  % (31012)Time elapsed: 0.149 s
% 0.20/0.54  % (31012)------------------------------
% 0.20/0.54  % (31012)------------------------------
% 0.20/0.54  % (30995)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.46/0.54  % (31013)Refutation not found, incomplete strategy% (31013)------------------------------
% 1.46/0.54  % (31013)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.54  % (31013)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.54  
% 1.46/0.55  % (31013)Memory used [KB]: 6140
% 1.46/0.55  % (31013)Time elapsed: 0.139 s
% 1.46/0.55  % (31013)------------------------------
% 1.46/0.55  % (31013)------------------------------
% 1.46/0.55  % (31002)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.46/0.55  % (31002)Refutation not found, incomplete strategy% (31002)------------------------------
% 1.46/0.55  % (31002)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.55  % (31002)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.55  
% 1.46/0.55  % (31002)Memory used [KB]: 10618
% 1.46/0.55  % (31002)Time elapsed: 0.149 s
% 1.46/0.55  % (31002)------------------------------
% 1.46/0.55  % (31002)------------------------------
% 1.46/0.55  % (31010)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.46/0.55  % (31010)Refutation not found, incomplete strategy% (31010)------------------------------
% 1.46/0.55  % (31010)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.55  % (31010)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.55  
% 1.46/0.55  % (31010)Memory used [KB]: 10618
% 1.46/0.55  % (31010)Time elapsed: 0.148 s
% 1.46/0.55  % (31010)------------------------------
% 1.46/0.55  % (31010)------------------------------
% 1.46/0.56  % (30996)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.68/0.56  % (30996)Refutation not found, incomplete strategy% (30996)------------------------------
% 1.68/0.56  % (30996)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.68/0.56  % (30996)Termination reason: Refutation not found, incomplete strategy
% 1.68/0.56  
% 1.68/0.56  % (30996)Memory used [KB]: 10618
% 1.68/0.56  % (30996)Time elapsed: 0.159 s
% 1.68/0.56  % (30996)------------------------------
% 1.68/0.56  % (30996)------------------------------
% 1.68/0.56  % (31005)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.68/0.58  % (30999)Refutation found. Thanks to Tanya!
% 1.68/0.58  % SZS status Theorem for theBenchmark
% 1.68/0.59  % SZS output start Proof for theBenchmark
% 1.68/0.59  fof(f1001,plain,(
% 1.68/0.59    $false),
% 1.68/0.59    inference(unit_resulting_resolution,[],[f53,f52,f903])).
% 1.68/0.59  fof(f903,plain,(
% 1.68/0.59    ( ! [X14,X15] : (k5_xboole_0(X15,k4_xboole_0(X14,X15)) = X14 | ~r1_tarski(X15,X14)) )),
% 1.68/0.59    inference(forward_demodulation,[],[f883,f28])).
% 1.68/0.59  fof(f28,plain,(
% 1.68/0.59    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.68/0.59    inference(cnf_transformation,[],[f2])).
% 1.68/0.59  fof(f2,axiom,(
% 1.68/0.59    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.68/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.68/0.59  fof(f883,plain,(
% 1.68/0.59    ( ! [X14,X15] : (k5_xboole_0(k4_xboole_0(X14,X15),X15) = X14 | ~r1_tarski(X15,X14)) )),
% 1.68/0.59    inference(superposition,[],[f431,f362])).
% 1.68/0.59  fof(f362,plain,(
% 1.68/0.59    ( ! [X12,X13] : (k5_xboole_0(X12,k4_xboole_0(X12,X13)) = X13 | ~r1_tarski(X13,X12)) )),
% 1.68/0.59    inference(superposition,[],[f51,f107])).
% 1.68/0.59  fof(f107,plain,(
% 1.68/0.59    ( ! [X4,X5] : (k4_xboole_0(X5,k4_xboole_0(X5,X4)) = X4 | ~r1_tarski(X4,X5)) )),
% 1.68/0.59    inference(superposition,[],[f54,f55])).
% 1.68/0.59  fof(f55,plain,(
% 1.68/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 1.68/0.59    inference(definition_unfolding,[],[f33,f31])).
% 1.68/0.59  fof(f31,plain,(
% 1.68/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.68/0.59    inference(cnf_transformation,[],[f8])).
% 1.68/0.59  fof(f8,axiom,(
% 1.68/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.68/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.68/0.59  fof(f33,plain,(
% 1.68/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.68/0.59    inference(cnf_transformation,[],[f22])).
% 1.68/0.59  fof(f22,plain,(
% 1.68/0.59    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.68/0.59    inference(ennf_transformation,[],[f6])).
% 1.68/0.59  fof(f6,axiom,(
% 1.68/0.59    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.68/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.68/0.59  fof(f54,plain,(
% 1.68/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.68/0.59    inference(definition_unfolding,[],[f27,f31,f31])).
% 1.68/0.59  fof(f27,plain,(
% 1.68/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.68/0.59    inference(cnf_transformation,[],[f1])).
% 1.68/0.59  fof(f1,axiom,(
% 1.68/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.68/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.68/0.59  fof(f51,plain,(
% 1.68/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.68/0.59    inference(definition_unfolding,[],[f32,f31])).
% 1.68/0.59  fof(f32,plain,(
% 1.68/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.68/0.59    inference(cnf_transformation,[],[f5])).
% 1.68/0.59  fof(f5,axiom,(
% 1.68/0.59    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.68/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.68/0.59  fof(f431,plain,(
% 1.68/0.59    ( ! [X4,X5] : (k5_xboole_0(X4,k5_xboole_0(X5,X4)) = X5) )),
% 1.68/0.59    inference(superposition,[],[f427,f28])).
% 1.68/0.59  fof(f427,plain,(
% 1.68/0.59    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X2,X3)) = X3) )),
% 1.68/0.59    inference(forward_demodulation,[],[f285,f262])).
% 1.68/0.59  fof(f262,plain,(
% 1.68/0.59    ( ! [X2] : (k5_xboole_0(k1_xboole_0,X2) = X2) )),
% 1.68/0.59    inference(subsumption_resolution,[],[f187,f260])).
% 1.68/0.59  fof(f260,plain,(
% 1.68/0.59    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.68/0.59    inference(resolution,[],[f249,f56])).
% 1.68/0.59  fof(f56,plain,(
% 1.68/0.59    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.68/0.59    inference(equality_resolution,[],[f35])).
% 1.68/0.59  fof(f35,plain,(
% 1.68/0.59    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.68/0.59    inference(cnf_transformation,[],[f3])).
% 1.68/0.59  fof(f3,axiom,(
% 1.68/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.68/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.68/0.59  fof(f249,plain,(
% 1.68/0.59    ( ! [X6] : (~r1_tarski(X6,X6) | r1_tarski(k1_xboole_0,X6)) )),
% 1.68/0.59    inference(trivial_inequality_removal,[],[f245])).
% 1.68/0.59  fof(f245,plain,(
% 1.68/0.59    ( ! [X6] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(k1_xboole_0,X6) | ~r1_tarski(X6,X6)) )),
% 1.68/0.59    inference(superposition,[],[f38,f232])).
% 1.68/0.59  fof(f232,plain,(
% 1.68/0.59    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X3) | ~r1_tarski(X3,X3)) )),
% 1.68/0.59    inference(forward_demodulation,[],[f222,f97])).
% 1.68/0.59  fof(f97,plain,(
% 1.68/0.59    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.68/0.59    inference(superposition,[],[f88,f24])).
% 1.68/0.59  fof(f24,plain,(
% 1.68/0.59    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.68/0.59    inference(cnf_transformation,[],[f7])).
% 1.68/0.59  fof(f7,axiom,(
% 1.68/0.59    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.68/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.68/0.59  fof(f88,plain,(
% 1.68/0.59    ( ! [X5] : (k5_xboole_0(X5,k4_xboole_0(X5,X5)) = X5) )),
% 1.68/0.59    inference(superposition,[],[f51,f24])).
% 1.68/0.59  fof(f222,plain,(
% 1.68/0.59    ( ! [X3] : (k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,X3) | ~r1_tarski(X3,X3)) )),
% 1.68/0.59    inference(superposition,[],[f162,f37])).
% 1.68/0.59  fof(f37,plain,(
% 1.68/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 1.68/0.59    inference(cnf_transformation,[],[f4])).
% 1.68/0.59  fof(f4,axiom,(
% 1.68/0.59    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.68/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.68/0.59  fof(f162,plain,(
% 1.68/0.59    ( ! [X2] : (k4_xboole_0(k1_xboole_0,X2) = k5_xboole_0(k1_xboole_0,k4_xboole_0(X2,X2))) )),
% 1.68/0.59    inference(superposition,[],[f51,f106])).
% 1.68/0.59  fof(f106,plain,(
% 1.68/0.59    ( ! [X9] : (k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X9)) = k4_xboole_0(X9,X9)) )),
% 1.68/0.59    inference(superposition,[],[f54,f24])).
% 1.68/0.59  fof(f38,plain,(
% 1.68/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 1.68/0.59    inference(cnf_transformation,[],[f4])).
% 1.68/0.59  fof(f187,plain,(
% 1.68/0.59    ( ! [X2] : (k5_xboole_0(k1_xboole_0,X2) = X2 | ~r1_tarski(k1_xboole_0,X2)) )),
% 1.68/0.59    inference(superposition,[],[f179,f28])).
% 1.68/0.59  fof(f179,plain,(
% 1.68/0.59    ( ! [X1] : (k5_xboole_0(X1,k1_xboole_0) = X1 | ~r1_tarski(k1_xboole_0,X1)) )),
% 1.68/0.59    inference(superposition,[],[f88,f155])).
% 1.68/0.59  fof(f155,plain,(
% 1.68/0.59    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(X3,X3) | ~r1_tarski(k1_xboole_0,X3)) )),
% 1.68/0.59    inference(superposition,[],[f106,f55])).
% 1.68/0.59  fof(f285,plain,(
% 1.68/0.59    ( ! [X2,X3] : (k5_xboole_0(k1_xboole_0,X3) = k5_xboole_0(X2,k5_xboole_0(X2,X3))) )),
% 1.68/0.59    inference(superposition,[],[f40,f263])).
% 1.68/0.59  fof(f263,plain,(
% 1.68/0.59    ( ! [X5] : (k1_xboole_0 = k5_xboole_0(X5,X5)) )),
% 1.68/0.59    inference(subsumption_resolution,[],[f186,f260])).
% 1.68/0.59  fof(f186,plain,(
% 1.68/0.59    ( ! [X5] : (k1_xboole_0 = k5_xboole_0(X5,X5) | ~r1_tarski(k1_xboole_0,X5)) )),
% 1.68/0.59    inference(forward_demodulation,[],[f181,f24])).
% 1.68/0.59  fof(f181,plain,(
% 1.68/0.59    ( ! [X5] : (k1_xboole_0 = k5_xboole_0(X5,k4_xboole_0(X5,k1_xboole_0)) | ~r1_tarski(k1_xboole_0,X5)) )),
% 1.68/0.59    inference(superposition,[],[f51,f155])).
% 1.68/0.59  fof(f40,plain,(
% 1.68/0.59    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.68/0.59    inference(cnf_transformation,[],[f9])).
% 1.68/0.59  fof(f9,axiom,(
% 1.68/0.59    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.68/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.68/0.59  fof(f52,plain,(
% 1.68/0.59    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 1.68/0.59    inference(definition_unfolding,[],[f23,f49,f30,f50,f49])).
% 1.68/0.59  fof(f50,plain,(
% 1.68/0.59    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.68/0.59    inference(definition_unfolding,[],[f25,f49])).
% 1.68/0.59  fof(f25,plain,(
% 1.68/0.59    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.68/0.59    inference(cnf_transformation,[],[f11])).
% 1.68/0.59  fof(f11,axiom,(
% 1.68/0.59    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.68/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.68/0.59  fof(f30,plain,(
% 1.68/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.68/0.59    inference(cnf_transformation,[],[f10])).
% 1.68/0.59  fof(f10,axiom,(
% 1.68/0.59    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.68/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.68/0.59  fof(f49,plain,(
% 1.68/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.68/0.59    inference(definition_unfolding,[],[f29,f48])).
% 1.68/0.59  fof(f48,plain,(
% 1.68/0.59    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.68/0.59    inference(definition_unfolding,[],[f39,f47])).
% 1.68/0.59  fof(f47,plain,(
% 1.68/0.59    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.68/0.59    inference(definition_unfolding,[],[f41,f46])).
% 1.68/0.59  fof(f46,plain,(
% 1.68/0.59    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.68/0.59    inference(definition_unfolding,[],[f42,f45])).
% 1.68/0.59  fof(f45,plain,(
% 1.68/0.59    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.68/0.59    inference(definition_unfolding,[],[f43,f44])).
% 1.68/0.59  fof(f44,plain,(
% 1.68/0.59    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.68/0.59    inference(cnf_transformation,[],[f17])).
% 1.68/0.59  fof(f17,axiom,(
% 1.68/0.59    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.68/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 1.68/0.59  fof(f43,plain,(
% 1.68/0.59    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.68/0.59    inference(cnf_transformation,[],[f16])).
% 1.68/0.59  fof(f16,axiom,(
% 1.68/0.59    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.68/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.68/0.59  fof(f42,plain,(
% 1.68/0.59    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.68/0.59    inference(cnf_transformation,[],[f15])).
% 1.68/0.59  fof(f15,axiom,(
% 1.68/0.59    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.68/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.68/0.59  fof(f41,plain,(
% 1.68/0.59    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.68/0.59    inference(cnf_transformation,[],[f14])).
% 1.68/0.59  fof(f14,axiom,(
% 1.68/0.59    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.68/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.68/0.59  fof(f39,plain,(
% 1.68/0.59    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.68/0.59    inference(cnf_transformation,[],[f13])).
% 1.68/0.59  fof(f13,axiom,(
% 1.68/0.59    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.68/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.68/0.59  fof(f29,plain,(
% 1.68/0.59    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.68/0.59    inference(cnf_transformation,[],[f12])).
% 1.68/0.59  fof(f12,axiom,(
% 1.68/0.59    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.68/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.68/0.59  fof(f23,plain,(
% 1.68/0.59    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 1.68/0.59    inference(cnf_transformation,[],[f21])).
% 1.68/0.59  fof(f21,plain,(
% 1.68/0.59    ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 1.68/0.59    inference(ennf_transformation,[],[f20])).
% 1.68/0.59  fof(f20,negated_conjecture,(
% 1.68/0.59    ~! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 1.68/0.59    inference(negated_conjecture,[],[f19])).
% 1.68/0.59  fof(f19,conjecture,(
% 1.68/0.59    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 1.68/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_zfmisc_1)).
% 1.68/0.59  fof(f53,plain,(
% 1.68/0.59    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.68/0.59    inference(definition_unfolding,[],[f26,f50,f49])).
% 1.68/0.59  fof(f26,plain,(
% 1.68/0.59    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 1.68/0.59    inference(cnf_transformation,[],[f18])).
% 1.68/0.59  fof(f18,axiom,(
% 1.68/0.59    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 1.68/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).
% 1.68/0.59  % SZS output end Proof for theBenchmark
% 1.68/0.59  % (30999)------------------------------
% 1.68/0.59  % (30999)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.68/0.59  % (30999)Termination reason: Refutation
% 1.68/0.59  
% 1.68/0.59  % (30999)Memory used [KB]: 6780
% 1.68/0.59  % (30999)Time elapsed: 0.149 s
% 1.68/0.59  % (30999)------------------------------
% 1.68/0.59  % (30999)------------------------------
% 1.68/0.60  % (30985)Success in time 0.238 s
%------------------------------------------------------------------------------
