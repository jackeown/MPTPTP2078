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
% DateTime   : Thu Dec  3 12:38:10 EST 2020

% Result     : Theorem 1.61s
% Output     : Refutation 1.77s
% Verified   : 
% Statistics : Number of formulae       :   80 (1272 expanded)
%              Number of leaves         :   17 ( 420 expanded)
%              Depth                    :   18
%              Number of atoms          :  131 (1674 expanded)
%              Number of equality atoms :  109 (1589 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f262,plain,(
    $false ),
    inference(global_subsumption,[],[f52,f240,f261])).

fof(f261,plain,(
    sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(forward_demodulation,[],[f241,f105])).

fof(f105,plain,(
    ! [X0] : k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
    inference(unit_resulting_resolution,[],[f25,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f34,f47])).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f31,f46])).

fof(f46,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f32,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f38,f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f40,f43])).

fof(f43,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f41,f42])).

fof(f42,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f41,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f40,plain,(
    ! [X2,X0,X3,X1] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_enumset1)).

fof(f38,plain,(
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

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f25,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f241,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK2)) ),
    inference(backward_demodulation,[],[f50,f240])).

fof(f50,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f24,f49,f47])).

fof(f49,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f28,f46])).

fof(f28,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f24,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f240,plain,(
    k1_xboole_0 = sK1 ),
    inference(global_subsumption,[],[f185,f184,f236])).

fof(f236,plain,
    ( sK1 = sK2
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f235])).

fof(f235,plain,
    ( sK1 = sK2
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f182,f213])).

fof(f213,plain,
    ( r1_tarski(sK2,sK1)
    | k1_xboole_0 = sK1 ),
    inference(backward_demodulation,[],[f178,f211])).

fof(f211,plain,(
    ! [X2,X1] : k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1 ),
    inference(forward_demodulation,[],[f200,f27])).

fof(f27,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f200,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X1,X2)) ),
    inference(superposition,[],[f80,f66])).

fof(f66,plain,(
    ! [X4,X3] : k1_xboole_0 = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X4))) ),
    inference(superposition,[],[f39,f26])).

fof(f26,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f39,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f80,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(backward_demodulation,[],[f63,f79])).

fof(f79,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f72,f27])).

fof(f72,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f63,f26])).

fof(f63,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f39,f26])).

fof(f178,plain,
    ( r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)),sK1)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f121,f157])).

fof(f157,plain,
    ( sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f59,f91])).

fof(f91,plain,(
    r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f54,f50])).

fof(f54,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f29,f47])).

fof(f29,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f35,f49,f49])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f121,plain,(
    r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) ),
    inference(superposition,[],[f62,f50])).

fof(f62,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X0) ),
    inference(backward_demodulation,[],[f55,f39])).

fof(f55,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0) ),
    inference(definition_unfolding,[],[f30,f48])).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f33,f47])).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f30,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f182,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | sK1 = X0
      | k1_xboole_0 = X0
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f59,f157])).

fof(f184,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f175])).

fof(f175,plain,
    ( sK1 != sK1
    | k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f53,f157])).

fof(f53,plain,
    ( sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | k1_xboole_0 != sK2 ),
    inference(definition_unfolding,[],[f21,f49])).

fof(f21,plain,
    ( sK1 != k1_tarski(sK0)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f19])).

fof(f185,plain,
    ( sK1 != sK2
    | k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f173])).

fof(f173,plain,
    ( sK1 != sK2
    | sK1 != sK1
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f51,f157])).

fof(f51,plain,
    ( sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f23,f49,f49])).

% (1384)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
fof(f23,plain,
    ( sK1 != k1_tarski(sK0)
    | sK2 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f52,plain,
    ( sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | k1_xboole_0 != sK1 ),
    inference(definition_unfolding,[],[f22,f49])).

fof(f22,plain,
    ( k1_xboole_0 != sK1
    | sK2 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:23:37 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.22/0.47  % (1375)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.48  % (1383)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.49  % (1383)Refutation not found, incomplete strategy% (1383)------------------------------
% 0.22/0.49  % (1383)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (1383)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (1383)Memory used [KB]: 6140
% 0.22/0.49  % (1383)Time elapsed: 0.003 s
% 0.22/0.49  % (1383)------------------------------
% 0.22/0.49  % (1383)------------------------------
% 0.22/0.53  % (1377)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.53  % (1391)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.53  % (1369)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (1390)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.54  % (1387)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.54  % (1382)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.54  % (1371)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (1372)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (1368)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (1373)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.55  % (1394)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.55  % (1376)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.55  % (1370)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.55  % (1374)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.55  % (1376)Refutation not found, incomplete strategy% (1376)------------------------------
% 0.22/0.55  % (1376)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (1376)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (1376)Memory used [KB]: 10746
% 0.22/0.55  % (1376)Time elapsed: 0.121 s
% 0.22/0.55  % (1376)------------------------------
% 0.22/0.55  % (1376)------------------------------
% 0.22/0.55  % (1370)Refutation not found, incomplete strategy% (1370)------------------------------
% 0.22/0.55  % (1370)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (1370)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (1370)Memory used [KB]: 10746
% 0.22/0.55  % (1370)Time elapsed: 0.125 s
% 0.22/0.55  % (1370)------------------------------
% 0.22/0.55  % (1370)------------------------------
% 0.22/0.55  % (1377)Refutation not found, incomplete strategy% (1377)------------------------------
% 0.22/0.55  % (1377)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (1377)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (1377)Memory used [KB]: 10746
% 0.22/0.55  % (1377)Time elapsed: 0.127 s
% 0.22/0.55  % (1377)------------------------------
% 0.22/0.55  % (1377)------------------------------
% 0.22/0.55  % (1395)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.55  % (1396)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.55  % (1397)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.55  % (1378)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.56  % (1378)Refutation not found, incomplete strategy% (1378)------------------------------
% 0.22/0.56  % (1378)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (1378)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (1378)Memory used [KB]: 10618
% 0.22/0.56  % (1378)Time elapsed: 0.140 s
% 0.22/0.56  % (1378)------------------------------
% 0.22/0.56  % (1378)------------------------------
% 0.22/0.56  % (1386)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.56  % (1379)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.56  % (1388)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.56  % (1379)Refutation not found, incomplete strategy% (1379)------------------------------
% 0.22/0.56  % (1379)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (1379)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (1379)Memory used [KB]: 10746
% 0.22/0.56  % (1379)Time elapsed: 0.140 s
% 0.22/0.56  % (1379)------------------------------
% 0.22/0.56  % (1379)------------------------------
% 0.22/0.56  % (1381)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.56  % (1393)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.56  % (1380)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.57  % (1389)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.57  % (1385)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.57  % (1385)Refutation not found, incomplete strategy% (1385)------------------------------
% 0.22/0.57  % (1385)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (1385)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (1385)Memory used [KB]: 10618
% 0.22/0.57  % (1385)Time elapsed: 0.152 s
% 0.22/0.57  % (1385)------------------------------
% 0.22/0.57  % (1385)------------------------------
% 1.61/0.57  % (1368)Refutation not found, incomplete strategy% (1368)------------------------------
% 1.61/0.57  % (1368)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.57  % (1368)Termination reason: Refutation not found, incomplete strategy
% 1.61/0.57  
% 1.61/0.57  % (1368)Memory used [KB]: 1663
% 1.61/0.57  % (1368)Time elapsed: 0.155 s
% 1.61/0.57  % (1368)------------------------------
% 1.61/0.57  % (1368)------------------------------
% 1.61/0.58  % (1392)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.61/0.58  % (1392)Refutation found. Thanks to Tanya!
% 1.61/0.58  % SZS status Theorem for theBenchmark
% 1.61/0.58  % SZS output start Proof for theBenchmark
% 1.61/0.58  fof(f262,plain,(
% 1.61/0.58    $false),
% 1.61/0.58    inference(global_subsumption,[],[f52,f240,f261])).
% 1.61/0.58  fof(f261,plain,(
% 1.61/0.58    sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 1.61/0.58    inference(forward_demodulation,[],[f241,f105])).
% 1.61/0.58  fof(f105,plain,(
% 1.61/0.58    ( ! [X0] : (k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0) )),
% 1.61/0.58    inference(unit_resulting_resolution,[],[f25,f56])).
% 1.61/0.58  fof(f56,plain,(
% 1.61/0.58    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 1.61/0.58    inference(definition_unfolding,[],[f34,f47])).
% 1.61/0.58  fof(f47,plain,(
% 1.61/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.61/0.58    inference(definition_unfolding,[],[f31,f46])).
% 1.61/0.58  fof(f46,plain,(
% 1.61/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.61/0.58    inference(definition_unfolding,[],[f32,f45])).
% 1.61/0.58  fof(f45,plain,(
% 1.61/0.58    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.61/0.58    inference(definition_unfolding,[],[f38,f44])).
% 1.61/0.58  fof(f44,plain,(
% 1.61/0.58    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.61/0.58    inference(definition_unfolding,[],[f40,f43])).
% 1.61/0.58  fof(f43,plain,(
% 1.61/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.61/0.58    inference(definition_unfolding,[],[f41,f42])).
% 1.61/0.58  fof(f42,plain,(
% 1.61/0.58    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.61/0.58    inference(cnf_transformation,[],[f13])).
% 1.61/0.58  fof(f13,axiom,(
% 1.61/0.58    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.61/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 1.61/0.58  fof(f41,plain,(
% 1.61/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.61/0.58    inference(cnf_transformation,[],[f12])).
% 1.61/0.58  fof(f12,axiom,(
% 1.61/0.58    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.61/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.61/0.58  fof(f40,plain,(
% 1.61/0.58    ( ! [X2,X0,X3,X1] : (k4_enumset1(X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.61/0.58    inference(cnf_transformation,[],[f14])).
% 1.61/0.58  fof(f14,axiom,(
% 1.61/0.58    ! [X0,X1,X2,X3] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.61/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_enumset1)).
% 1.61/0.58  fof(f38,plain,(
% 1.61/0.58    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.61/0.58    inference(cnf_transformation,[],[f11])).
% 1.61/0.58  fof(f11,axiom,(
% 1.61/0.58    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.61/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.61/0.58  fof(f32,plain,(
% 1.61/0.58    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.61/0.58    inference(cnf_transformation,[],[f10])).
% 1.61/0.58  fof(f10,axiom,(
% 1.61/0.58    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.61/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.61/0.58  fof(f31,plain,(
% 1.61/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.61/0.58    inference(cnf_transformation,[],[f16])).
% 1.61/0.58  fof(f16,axiom,(
% 1.61/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.61/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.61/0.58  fof(f34,plain,(
% 1.61/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.61/0.58    inference(cnf_transformation,[],[f20])).
% 1.61/0.58  fof(f20,plain,(
% 1.61/0.58    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.61/0.58    inference(ennf_transformation,[],[f1])).
% 1.61/0.58  fof(f1,axiom,(
% 1.61/0.58    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.61/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.61/0.58  fof(f25,plain,(
% 1.61/0.58    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.61/0.58    inference(cnf_transformation,[],[f3])).
% 1.61/0.58  fof(f3,axiom,(
% 1.61/0.58    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.61/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.61/0.58  fof(f241,plain,(
% 1.61/0.58    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK2))),
% 1.61/0.58    inference(backward_demodulation,[],[f50,f240])).
% 1.61/0.58  fof(f50,plain,(
% 1.61/0.58    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),
% 1.61/0.58    inference(definition_unfolding,[],[f24,f49,f47])).
% 1.61/0.58  fof(f49,plain,(
% 1.61/0.58    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.61/0.58    inference(definition_unfolding,[],[f28,f46])).
% 1.61/0.58  fof(f28,plain,(
% 1.61/0.58    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.61/0.58    inference(cnf_transformation,[],[f9])).
% 1.61/0.58  fof(f9,axiom,(
% 1.61/0.58    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.61/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.61/0.58  fof(f24,plain,(
% 1.61/0.58    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.61/0.58    inference(cnf_transformation,[],[f19])).
% 1.61/0.58  fof(f19,plain,(
% 1.61/0.58    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.61/0.58    inference(ennf_transformation,[],[f18])).
% 1.61/0.58  fof(f18,negated_conjecture,(
% 1.61/0.58    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.61/0.58    inference(negated_conjecture,[],[f17])).
% 1.61/0.58  fof(f17,conjecture,(
% 1.61/0.58    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.61/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 1.61/0.58  fof(f240,plain,(
% 1.61/0.58    k1_xboole_0 = sK1),
% 1.61/0.58    inference(global_subsumption,[],[f185,f184,f236])).
% 1.61/0.58  fof(f236,plain,(
% 1.61/0.58    sK1 = sK2 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 1.61/0.58    inference(duplicate_literal_removal,[],[f235])).
% 1.61/0.58  fof(f235,plain,(
% 1.61/0.58    sK1 = sK2 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK1),
% 1.61/0.58    inference(resolution,[],[f182,f213])).
% 1.61/0.58  fof(f213,plain,(
% 1.61/0.58    r1_tarski(sK2,sK1) | k1_xboole_0 = sK1),
% 1.61/0.58    inference(backward_demodulation,[],[f178,f211])).
% 1.61/0.58  fof(f211,plain,(
% 1.61/0.58    ( ! [X2,X1] : (k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1) )),
% 1.61/0.58    inference(forward_demodulation,[],[f200,f27])).
% 1.61/0.58  fof(f27,plain,(
% 1.61/0.58    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.61/0.58    inference(cnf_transformation,[],[f4])).
% 1.61/0.58  fof(f4,axiom,(
% 1.61/0.58    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.61/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 1.61/0.58  fof(f200,plain,(
% 1.61/0.58    ( ! [X2,X1] : (k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X1,X2))) )),
% 1.61/0.58    inference(superposition,[],[f80,f66])).
% 1.61/0.58  fof(f66,plain,(
% 1.61/0.58    ( ! [X4,X3] : (k1_xboole_0 = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X4)))) )),
% 1.61/0.58    inference(superposition,[],[f39,f26])).
% 1.61/0.58  fof(f26,plain,(
% 1.61/0.58    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.61/0.58    inference(cnf_transformation,[],[f7])).
% 1.61/0.58  fof(f7,axiom,(
% 1.61/0.58    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.61/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.61/0.58  fof(f39,plain,(
% 1.61/0.58    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.61/0.58    inference(cnf_transformation,[],[f6])).
% 1.61/0.58  fof(f6,axiom,(
% 1.61/0.58    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.61/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.61/0.58  fof(f80,plain,(
% 1.61/0.58    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 1.61/0.58    inference(backward_demodulation,[],[f63,f79])).
% 1.61/0.58  fof(f79,plain,(
% 1.61/0.58    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.61/0.58    inference(forward_demodulation,[],[f72,f27])).
% 1.61/0.58  fof(f72,plain,(
% 1.61/0.58    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0)) )),
% 1.61/0.58    inference(superposition,[],[f63,f26])).
% 1.61/0.58  fof(f63,plain,(
% 1.61/0.58    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)) )),
% 1.61/0.58    inference(superposition,[],[f39,f26])).
% 1.61/0.58  fof(f178,plain,(
% 1.61/0.58    r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)),sK1) | k1_xboole_0 = sK1),
% 1.61/0.58    inference(superposition,[],[f121,f157])).
% 1.61/0.58  fof(f157,plain,(
% 1.61/0.58    sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | k1_xboole_0 = sK1),
% 1.61/0.58    inference(resolution,[],[f59,f91])).
% 1.61/0.58  fof(f91,plain,(
% 1.61/0.58    r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 1.61/0.58    inference(superposition,[],[f54,f50])).
% 1.61/0.58  fof(f54,plain,(
% 1.61/0.58    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.61/0.58    inference(definition_unfolding,[],[f29,f47])).
% 1.61/0.58  fof(f29,plain,(
% 1.61/0.58    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.61/0.58    inference(cnf_transformation,[],[f5])).
% 1.61/0.58  fof(f5,axiom,(
% 1.61/0.58    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.61/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.61/0.58  fof(f59,plain,(
% 1.61/0.58    ( ! [X0,X1] : (~r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0) )),
% 1.61/0.58    inference(definition_unfolding,[],[f35,f49,f49])).
% 1.61/0.58  fof(f35,plain,(
% 1.61/0.58    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 1.61/0.58    inference(cnf_transformation,[],[f15])).
% 1.61/0.58  fof(f15,axiom,(
% 1.61/0.58    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.61/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.61/0.58  fof(f121,plain,(
% 1.61/0.58    r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1)),
% 1.61/0.58    inference(superposition,[],[f62,f50])).
% 1.61/0.58  fof(f62,plain,(
% 1.61/0.58    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X0)) )),
% 1.61/0.58    inference(backward_demodulation,[],[f55,f39])).
% 1.61/0.58  fof(f55,plain,(
% 1.61/0.58    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0)) )),
% 1.61/0.58    inference(definition_unfolding,[],[f30,f48])).
% 1.61/0.58  fof(f48,plain,(
% 1.61/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.61/0.58    inference(definition_unfolding,[],[f33,f47])).
% 1.61/0.58  fof(f33,plain,(
% 1.61/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 1.61/0.58    inference(cnf_transformation,[],[f8])).
% 1.61/0.58  fof(f8,axiom,(
% 1.61/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 1.61/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 1.61/0.58  fof(f30,plain,(
% 1.61/0.58    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.61/0.58    inference(cnf_transformation,[],[f2])).
% 1.61/0.58  fof(f2,axiom,(
% 1.61/0.58    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.61/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.61/0.58  fof(f182,plain,(
% 1.61/0.58    ( ! [X0] : (~r1_tarski(X0,sK1) | sK1 = X0 | k1_xboole_0 = X0 | k1_xboole_0 = sK1) )),
% 1.61/0.58    inference(superposition,[],[f59,f157])).
% 1.61/0.58  fof(f184,plain,(
% 1.61/0.58    k1_xboole_0 != sK2 | k1_xboole_0 = sK1),
% 1.61/0.58    inference(trivial_inequality_removal,[],[f175])).
% 1.61/0.58  fof(f175,plain,(
% 1.61/0.58    sK1 != sK1 | k1_xboole_0 != sK2 | k1_xboole_0 = sK1),
% 1.61/0.58    inference(superposition,[],[f53,f157])).
% 1.61/0.58  fof(f53,plain,(
% 1.61/0.58    sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | k1_xboole_0 != sK2),
% 1.61/0.58    inference(definition_unfolding,[],[f21,f49])).
% 1.61/0.58  fof(f21,plain,(
% 1.61/0.58    sK1 != k1_tarski(sK0) | k1_xboole_0 != sK2),
% 1.61/0.58    inference(cnf_transformation,[],[f19])).
% 1.61/0.58  fof(f185,plain,(
% 1.61/0.58    sK1 != sK2 | k1_xboole_0 = sK1),
% 1.61/0.58    inference(trivial_inequality_removal,[],[f173])).
% 1.61/0.58  fof(f173,plain,(
% 1.61/0.58    sK1 != sK2 | sK1 != sK1 | k1_xboole_0 = sK1),
% 1.61/0.58    inference(superposition,[],[f51,f157])).
% 1.61/0.58  fof(f51,plain,(
% 1.61/0.58    sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 1.61/0.58    inference(definition_unfolding,[],[f23,f49,f49])).
% 1.61/0.58  % (1384)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.77/0.61  fof(f23,plain,(
% 1.77/0.61    sK1 != k1_tarski(sK0) | sK2 != k1_tarski(sK0)),
% 1.77/0.61    inference(cnf_transformation,[],[f19])).
% 1.77/0.61  fof(f52,plain,(
% 1.77/0.61    sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | k1_xboole_0 != sK1),
% 1.77/0.61    inference(definition_unfolding,[],[f22,f49])).
% 1.77/0.61  fof(f22,plain,(
% 1.77/0.61    k1_xboole_0 != sK1 | sK2 != k1_tarski(sK0)),
% 1.77/0.61    inference(cnf_transformation,[],[f19])).
% 1.77/0.61  % SZS output end Proof for theBenchmark
% 1.77/0.61  % (1392)------------------------------
% 1.77/0.61  % (1392)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.77/0.61  % (1392)Termination reason: Refutation
% 1.77/0.61  
% 1.77/0.61  % (1392)Memory used [KB]: 6396
% 1.77/0.61  % (1392)Time elapsed: 0.161 s
% 1.77/0.61  % (1392)------------------------------
% 1.77/0.61  % (1392)------------------------------
% 1.77/0.61  % (1398)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 1.77/0.61  % (1367)Success in time 0.236 s
%------------------------------------------------------------------------------
