%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:42 EST 2020

% Result     : Theorem 1.66s
% Output     : Refutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 742 expanded)
%              Number of leaves         :   18 ( 202 expanded)
%              Depth                    :   18
%              Number of atoms          :   93 (1290 expanded)
%              Number of equality atoms :   74 ( 773 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f591,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f590])).

% (1432)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
fof(f590,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(superposition,[],[f120,f479])).

fof(f479,plain,(
    ! [X14,X12] : k5_xboole_0(X14,k5_xboole_0(X12,X14)) = X12 ),
    inference(forward_demodulation,[],[f478,f99])).

fof(f99,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f60,f98])).

fof(f98,plain,(
    ! [X4] : k1_xboole_0 = k5_xboole_0(X4,X4) ),
    inference(forward_demodulation,[],[f97,f59])).

fof(f59,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(resolution,[],[f35,f56])).

fof(f56,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f97,plain,(
    ! [X4] : k1_xboole_0 = k5_xboole_0(X4,k3_xboole_0(X4,X4)) ),
    inference(forward_demodulation,[],[f89,f60])).

fof(f89,plain,(
    ! [X4] : k1_xboole_0 = k5_xboole_0(X4,k3_xboole_0(X4,k5_xboole_0(X4,k5_xboole_0(X4,X4)))) ),
    inference(superposition,[],[f55,f59])).

fof(f55,plain,(
    ! [X0,X1] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) ),
    inference(definition_unfolding,[],[f31,f33,f45])).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f34,f33])).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

% (1434)Refutation not found, incomplete strategy% (1434)------------------------------
% (1434)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (1434)Termination reason: Refutation not found, incomplete strategy

% (1434)Memory used [KB]: 1663
% (1434)Time elapsed: 0.184 s
% (1434)------------------------------
% (1434)------------------------------
fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f60,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(X0,X0)) = X0 ),
    inference(backward_demodulation,[],[f53,f59])).

fof(f53,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f28,f45])).

fof(f28,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f478,plain,(
    ! [X14,X12] : k5_xboole_0(X12,k1_xboole_0) = k5_xboole_0(X14,k5_xboole_0(X12,X14)) ),
    inference(forward_demodulation,[],[f435,f459])).

fof(f459,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(forward_demodulation,[],[f431,f99])).

fof(f431,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f353,f98])).

fof(f353,plain,(
    ! [X4,X2,X3] : k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2)))),X4)) = X4 ),
    inference(backward_demodulation,[],[f95,f352])).

fof(f352,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f323,f99])).

fof(f323,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f112,f98])).

fof(f112,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X1,X2)) = k5_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[],[f40,f98])).

fof(f40,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

% (1432)Refutation not found, incomplete strategy% (1432)------------------------------
% (1432)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (1432)Termination reason: Refutation not found, incomplete strategy

% (1432)Memory used [KB]: 6140
% (1432)Time elapsed: 0.183 s
% (1432)------------------------------
% (1432)------------------------------
fof(f7,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f95,plain,(
    ! [X4,X2,X3] : k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2)))),X4)) = k5_xboole_0(k1_xboole_0,X4) ),
    inference(superposition,[],[f40,f55])).

fof(f435,plain,(
    ! [X14,X12,X13] : k5_xboole_0(X12,k1_xboole_0) = k5_xboole_0(X14,k5_xboole_0(k3_xboole_0(X12,k5_xboole_0(X12,k5_xboole_0(X13,k3_xboole_0(X13,X12)))),X14)) ),
    inference(superposition,[],[f353,f110])).

fof(f110,plain,(
    ! [X2,X1] : k1_xboole_0 = k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2))) ),
    inference(superposition,[],[f98,f40])).

fof(f120,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(backward_demodulation,[],[f58,f119])).

fof(f119,plain,(
    ! [X2,X3] : k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = k3_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)) ),
    inference(resolution,[],[f54,f35])).

fof(f54,plain,(
    ! [X0,X1] : r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f29,f51,f50])).

fof(f50,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f32,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f39,f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f41,f47])).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f42,f46])).

fof(f46,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f43,f44])).

fof(f44,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f43,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f41,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f39,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f32,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f51,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f27,f50])).

fof(f27,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

% (1433)Refutation not found, incomplete strategy% (1433)------------------------------
% (1433)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (1433)Termination reason: Refutation not found, incomplete strategy

% (1433)Memory used [KB]: 10746
% (1433)Time elapsed: 0.185 s
% (1433)------------------------------
% (1433)------------------------------
fof(f29,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

fof(f58,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) ),
    inference(backward_demodulation,[],[f52,f30])).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f52,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) ),
    inference(definition_unfolding,[],[f26,f50,f45,f51,f50])).

fof(f26,plain,(
    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f23])).

% (1406)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
fof(f23,plain,(
    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f22])).

fof(f22,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))
   => k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:47:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.35/0.56  % (1411)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.35/0.56  % (1427)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.35/0.57  % (1405)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.66/0.58  % (1419)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.66/0.58  % (1419)Refutation not found, incomplete strategy% (1419)------------------------------
% 1.66/0.58  % (1419)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.58  % (1419)Termination reason: Refutation not found, incomplete strategy
% 1.66/0.58  
% 1.66/0.58  % (1419)Memory used [KB]: 1663
% 1.66/0.58  % (1419)Time elapsed: 0.146 s
% 1.66/0.58  % (1419)------------------------------
% 1.66/0.58  % (1419)------------------------------
% 1.66/0.59  % (1421)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.66/0.59  % (1421)Refutation not found, incomplete strategy% (1421)------------------------------
% 1.66/0.59  % (1421)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.59  % (1413)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.66/0.60  % (1421)Termination reason: Refutation not found, incomplete strategy
% 1.66/0.60  
% 1.66/0.60  % (1421)Memory used [KB]: 10618
% 1.66/0.60  % (1421)Time elapsed: 0.152 s
% 1.66/0.60  % (1421)------------------------------
% 1.66/0.60  % (1421)------------------------------
% 1.66/0.60  % (1407)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.66/0.61  % (1428)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.66/0.61  % (1410)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.66/0.61  % (1409)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.66/0.61  % (1408)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.66/0.62  % (1429)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.66/0.62  % (1412)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.66/0.62  % (1433)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.66/0.62  % (1434)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.66/0.62  % (1427)Refutation found. Thanks to Tanya!
% 1.66/0.62  % SZS status Theorem for theBenchmark
% 1.66/0.62  % SZS output start Proof for theBenchmark
% 1.66/0.62  fof(f591,plain,(
% 1.66/0.62    $false),
% 1.66/0.62    inference(trivial_inequality_removal,[],[f590])).
% 1.66/0.62  % (1432)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.66/0.62  fof(f590,plain,(
% 1.66/0.62    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),
% 1.66/0.62    inference(superposition,[],[f120,f479])).
% 1.66/0.62  fof(f479,plain,(
% 1.66/0.62    ( ! [X14,X12] : (k5_xboole_0(X14,k5_xboole_0(X12,X14)) = X12) )),
% 1.66/0.62    inference(forward_demodulation,[],[f478,f99])).
% 1.66/0.62  fof(f99,plain,(
% 1.66/0.62    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.66/0.62    inference(backward_demodulation,[],[f60,f98])).
% 1.66/0.62  fof(f98,plain,(
% 1.66/0.62    ( ! [X4] : (k1_xboole_0 = k5_xboole_0(X4,X4)) )),
% 1.66/0.62    inference(forward_demodulation,[],[f97,f59])).
% 1.66/0.62  fof(f59,plain,(
% 1.66/0.62    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.66/0.62    inference(resolution,[],[f35,f56])).
% 1.66/0.62  fof(f56,plain,(
% 1.66/0.62    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.66/0.62    inference(equality_resolution,[],[f37])).
% 1.66/0.62  fof(f37,plain,(
% 1.66/0.62    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.66/0.62    inference(cnf_transformation,[],[f25])).
% 1.66/0.62  fof(f25,plain,(
% 1.66/0.62    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.66/0.62    inference(flattening,[],[f24])).
% 1.66/0.62  fof(f24,plain,(
% 1.66/0.62    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.66/0.62    inference(nnf_transformation,[],[f3])).
% 1.66/0.62  fof(f3,axiom,(
% 1.66/0.62    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.66/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.66/0.62  fof(f35,plain,(
% 1.66/0.62    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.66/0.62    inference(cnf_transformation,[],[f21])).
% 1.66/0.62  fof(f21,plain,(
% 1.66/0.62    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.66/0.62    inference(ennf_transformation,[],[f5])).
% 1.66/0.62  fof(f5,axiom,(
% 1.66/0.62    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.66/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.66/0.62  fof(f97,plain,(
% 1.66/0.62    ( ! [X4] : (k1_xboole_0 = k5_xboole_0(X4,k3_xboole_0(X4,X4))) )),
% 1.66/0.62    inference(forward_demodulation,[],[f89,f60])).
% 1.66/0.62  fof(f89,plain,(
% 1.66/0.62    ( ! [X4] : (k1_xboole_0 = k5_xboole_0(X4,k3_xboole_0(X4,k5_xboole_0(X4,k5_xboole_0(X4,X4))))) )),
% 1.66/0.62    inference(superposition,[],[f55,f59])).
% 1.66/0.62  fof(f55,plain,(
% 1.66/0.62    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))) )),
% 1.66/0.62    inference(definition_unfolding,[],[f31,f33,f45])).
% 1.66/0.62  fof(f45,plain,(
% 1.66/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 1.66/0.62    inference(definition_unfolding,[],[f34,f33])).
% 1.66/0.62  fof(f34,plain,(
% 1.66/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.66/0.62    inference(cnf_transformation,[],[f8])).
% 1.66/0.62  fof(f8,axiom,(
% 1.66/0.62    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.66/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.66/0.62  fof(f33,plain,(
% 1.66/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.66/0.62    inference(cnf_transformation,[],[f4])).
% 1.66/0.63  fof(f4,axiom,(
% 1.66/0.63    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.66/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.66/0.63  fof(f31,plain,(
% 1.66/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 1.66/0.63    inference(cnf_transformation,[],[f6])).
% 1.66/0.63  % (1434)Refutation not found, incomplete strategy% (1434)------------------------------
% 1.66/0.63  % (1434)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.63  % (1434)Termination reason: Refutation not found, incomplete strategy
% 1.66/0.63  
% 1.66/0.63  % (1434)Memory used [KB]: 1663
% 1.66/0.63  % (1434)Time elapsed: 0.184 s
% 1.66/0.63  % (1434)------------------------------
% 1.66/0.63  % (1434)------------------------------
% 1.66/0.63  fof(f6,axiom,(
% 1.66/0.63    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 1.66/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 1.66/0.63  fof(f60,plain,(
% 1.66/0.63    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(X0,X0)) = X0) )),
% 1.66/0.63    inference(backward_demodulation,[],[f53,f59])).
% 1.66/0.63  fof(f53,plain,(
% 1.66/0.63    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0) )),
% 1.66/0.63    inference(definition_unfolding,[],[f28,f45])).
% 1.66/0.63  fof(f28,plain,(
% 1.66/0.63    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 1.66/0.63    inference(cnf_transformation,[],[f19])).
% 1.66/0.63  fof(f19,plain,(
% 1.66/0.63    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 1.66/0.63    inference(rectify,[],[f2])).
% 1.66/0.63  fof(f2,axiom,(
% 1.66/0.63    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 1.66/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 1.66/0.63  fof(f478,plain,(
% 1.66/0.63    ( ! [X14,X12] : (k5_xboole_0(X12,k1_xboole_0) = k5_xboole_0(X14,k5_xboole_0(X12,X14))) )),
% 1.66/0.63    inference(forward_demodulation,[],[f435,f459])).
% 1.66/0.63  fof(f459,plain,(
% 1.66/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0) )),
% 1.66/0.63    inference(forward_demodulation,[],[f431,f99])).
% 1.66/0.63  fof(f431,plain,(
% 1.66/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k5_xboole_0(X0,k1_xboole_0)) )),
% 1.66/0.63    inference(superposition,[],[f353,f98])).
% 1.66/0.63  fof(f353,plain,(
% 1.66/0.63    ( ! [X4,X2,X3] : (k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2)))),X4)) = X4) )),
% 1.66/0.63    inference(backward_demodulation,[],[f95,f352])).
% 1.66/0.63  fof(f352,plain,(
% 1.66/0.63    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.66/0.63    inference(forward_demodulation,[],[f323,f99])).
% 1.66/0.63  fof(f323,plain,(
% 1.66/0.63    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0)) )),
% 1.66/0.63    inference(superposition,[],[f112,f98])).
% 1.66/0.63  fof(f112,plain,(
% 1.66/0.63    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X1,X2)) = k5_xboole_0(k1_xboole_0,X2)) )),
% 1.66/0.63    inference(superposition,[],[f40,f98])).
% 1.66/0.63  fof(f40,plain,(
% 1.66/0.63    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.66/0.63    inference(cnf_transformation,[],[f7])).
% 1.66/0.63  % (1432)Refutation not found, incomplete strategy% (1432)------------------------------
% 1.66/0.63  % (1432)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.63  % (1432)Termination reason: Refutation not found, incomplete strategy
% 1.66/0.63  
% 1.66/0.63  % (1432)Memory used [KB]: 6140
% 1.66/0.63  % (1432)Time elapsed: 0.183 s
% 1.66/0.63  % (1432)------------------------------
% 1.66/0.63  % (1432)------------------------------
% 1.66/0.63  fof(f7,axiom,(
% 1.66/0.63    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.66/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.66/0.63  fof(f95,plain,(
% 1.66/0.63    ( ! [X4,X2,X3] : (k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2)))),X4)) = k5_xboole_0(k1_xboole_0,X4)) )),
% 1.66/0.63    inference(superposition,[],[f40,f55])).
% 1.66/0.63  fof(f435,plain,(
% 1.66/0.63    ( ! [X14,X12,X13] : (k5_xboole_0(X12,k1_xboole_0) = k5_xboole_0(X14,k5_xboole_0(k3_xboole_0(X12,k5_xboole_0(X12,k5_xboole_0(X13,k3_xboole_0(X13,X12)))),X14))) )),
% 1.66/0.63    inference(superposition,[],[f353,f110])).
% 1.66/0.63  fof(f110,plain,(
% 1.66/0.63    ( ! [X2,X1] : (k1_xboole_0 = k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2)))) )),
% 1.66/0.63    inference(superposition,[],[f98,f40])).
% 1.66/0.63  fof(f120,plain,(
% 1.66/0.63    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 1.66/0.63    inference(backward_demodulation,[],[f58,f119])).
% 1.66/0.63  fof(f119,plain,(
% 1.66/0.63    ( ! [X2,X3] : (k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = k3_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))) )),
% 1.66/0.63    inference(resolution,[],[f54,f35])).
% 1.66/0.63  fof(f54,plain,(
% 1.66/0.63    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.66/0.63    inference(definition_unfolding,[],[f29,f51,f50])).
% 1.66/0.63  fof(f50,plain,(
% 1.66/0.63    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.66/0.63    inference(definition_unfolding,[],[f32,f49])).
% 1.66/0.63  fof(f49,plain,(
% 1.66/0.63    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.66/0.63    inference(definition_unfolding,[],[f39,f48])).
% 1.66/0.63  fof(f48,plain,(
% 1.66/0.63    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.66/0.63    inference(definition_unfolding,[],[f41,f47])).
% 1.66/0.63  fof(f47,plain,(
% 1.66/0.63    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.66/0.63    inference(definition_unfolding,[],[f42,f46])).
% 1.66/0.63  fof(f46,plain,(
% 1.66/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.66/0.63    inference(definition_unfolding,[],[f43,f44])).
% 1.66/0.63  fof(f44,plain,(
% 1.66/0.63    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.66/0.63    inference(cnf_transformation,[],[f15])).
% 1.66/0.63  fof(f15,axiom,(
% 1.66/0.63    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.66/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 1.66/0.63  fof(f43,plain,(
% 1.66/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.66/0.63    inference(cnf_transformation,[],[f14])).
% 1.66/0.63  fof(f14,axiom,(
% 1.66/0.63    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.66/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.66/0.63  fof(f42,plain,(
% 1.66/0.63    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.66/0.63    inference(cnf_transformation,[],[f13])).
% 1.66/0.63  fof(f13,axiom,(
% 1.66/0.63    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.66/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.66/0.63  fof(f41,plain,(
% 1.66/0.63    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.66/0.63    inference(cnf_transformation,[],[f12])).
% 1.66/0.63  fof(f12,axiom,(
% 1.66/0.63    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.66/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.66/0.63  fof(f39,plain,(
% 1.66/0.63    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.66/0.63    inference(cnf_transformation,[],[f11])).
% 1.66/0.63  fof(f11,axiom,(
% 1.66/0.63    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.66/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.66/0.63  fof(f32,plain,(
% 1.66/0.63    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.66/0.63    inference(cnf_transformation,[],[f10])).
% 1.66/0.63  fof(f10,axiom,(
% 1.66/0.63    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.66/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.66/0.63  fof(f51,plain,(
% 1.66/0.63    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.66/0.63    inference(definition_unfolding,[],[f27,f50])).
% 1.66/0.63  fof(f27,plain,(
% 1.66/0.63    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.66/0.63    inference(cnf_transformation,[],[f9])).
% 1.66/0.63  fof(f9,axiom,(
% 1.66/0.63    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.66/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.66/0.63  % (1433)Refutation not found, incomplete strategy% (1433)------------------------------
% 1.66/0.63  % (1433)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.63  % (1433)Termination reason: Refutation not found, incomplete strategy
% 1.66/0.63  
% 1.66/0.63  % (1433)Memory used [KB]: 10746
% 1.66/0.63  % (1433)Time elapsed: 0.185 s
% 1.66/0.63  % (1433)------------------------------
% 1.66/0.63  % (1433)------------------------------
% 1.66/0.63  fof(f29,plain,(
% 1.66/0.63    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 1.66/0.63    inference(cnf_transformation,[],[f16])).
% 1.66/0.63  fof(f16,axiom,(
% 1.66/0.63    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 1.66/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).
% 1.66/0.63  fof(f58,plain,(
% 1.66/0.63    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))),
% 1.66/0.63    inference(backward_demodulation,[],[f52,f30])).
% 1.66/0.63  fof(f30,plain,(
% 1.66/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.66/0.63    inference(cnf_transformation,[],[f1])).
% 1.66/0.63  fof(f1,axiom,(
% 1.66/0.63    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.66/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.66/0.63  fof(f52,plain,(
% 1.66/0.63    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))),
% 1.66/0.63    inference(definition_unfolding,[],[f26,f50,f45,f51,f50])).
% 1.66/0.63  fof(f26,plain,(
% 1.66/0.63    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 1.66/0.63    inference(cnf_transformation,[],[f23])).
% 1.66/0.63  % (1406)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.66/0.63  fof(f23,plain,(
% 1.66/0.63    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 1.66/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f22])).
% 1.66/0.63  fof(f22,plain,(
% 1.66/0.63    ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) => k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 1.66/0.63    introduced(choice_axiom,[])).
% 1.66/0.63  fof(f20,plain,(
% 1.66/0.63    ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 1.66/0.63    inference(ennf_transformation,[],[f18])).
% 1.66/0.63  fof(f18,negated_conjecture,(
% 1.66/0.63    ~! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 1.66/0.63    inference(negated_conjecture,[],[f17])).
% 1.66/0.63  fof(f17,conjecture,(
% 1.66/0.63    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 1.66/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_zfmisc_1)).
% 1.66/0.63  % SZS output end Proof for theBenchmark
% 1.66/0.63  % (1427)------------------------------
% 1.66/0.63  % (1427)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.63  % (1427)Termination reason: Refutation
% 1.66/0.63  
% 1.66/0.63  % (1427)Memory used [KB]: 6652
% 1.66/0.63  % (1427)Time elapsed: 0.172 s
% 1.66/0.63  % (1427)------------------------------
% 1.66/0.63  % (1427)------------------------------
% 1.66/0.63  % (1420)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.66/0.63  % (1406)Refutation not found, incomplete strategy% (1406)------------------------------
% 1.66/0.63  % (1406)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.63  % (1406)Termination reason: Refutation not found, incomplete strategy
% 1.66/0.63  
% 1.66/0.63  % (1406)Memory used [KB]: 1663
% 1.66/0.63  % (1406)Time elapsed: 0.195 s
% 1.66/0.63  % (1406)------------------------------
% 1.66/0.63  % (1406)------------------------------
% 1.66/0.63  % (1404)Success in time 0.265 s
%------------------------------------------------------------------------------
