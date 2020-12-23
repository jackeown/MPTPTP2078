%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:43 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 185 expanded)
%              Number of leaves         :   17 (  61 expanded)
%              Depth                    :   12
%              Number of atoms          :   98 ( 244 expanded)
%              Number of equality atoms :   54 ( 152 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f796,plain,(
    $false ),
    inference(subsumption_resolution,[],[f795,f33])).

fof(f33,plain,(
    ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f28])).

fof(f28,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).

fof(f795,plain,(
    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(superposition,[],[f775,f462])).

fof(f462,plain,(
    sK1 = k3_tarski(k1_enumset1(sK0,sK0,sK1)) ),
    inference(forward_demodulation,[],[f450,f56])).

fof(f56,plain,(
    ! [X0] : k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f34,f55])).

fof(f55,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f44,f42])).

fof(f42,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f34,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f450,plain,(
    k3_tarski(k1_enumset1(sK1,sK1,k1_xboole_0)) = k3_tarski(k1_enumset1(sK0,sK0,sK1)) ),
    inference(backward_demodulation,[],[f320,f424])).

fof(f424,plain,(
    ! [X3] : k1_xboole_0 = k5_xboole_0(X3,X3) ),
    inference(forward_demodulation,[],[f423,f58])).

fof(f58,plain,(
    ! [X0] : k1_setfam_1(k1_enumset1(X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f37,f53])).

fof(f53,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f43,f42])).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f37,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f423,plain,(
    ! [X3] : k1_xboole_0 = k5_xboole_0(X3,k1_setfam_1(k1_enumset1(X3,X3,X3))) ),
    inference(forward_demodulation,[],[f407,f97])).

fof(f97,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f85,f72])).

fof(f72,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k1_enumset1(k1_xboole_0,k1_xboole_0,X0)) ),
    inference(resolution,[],[f60,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f60,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f39,f53])).

fof(f39,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f85,plain,(
    ! [X0] : k5_xboole_0(X0,k1_setfam_1(k1_enumset1(k1_xboole_0,k1_xboole_0,X0))) = X0 ),
    inference(superposition,[],[f57,f62])).

fof(f62,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f41,f42,f42])).

fof(f41,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f57,plain,(
    ! [X0] : k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,k1_xboole_0))) = X0 ),
    inference(definition_unfolding,[],[f35,f54])).

fof(f54,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f46,f53])).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f35,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f407,plain,(
    ! [X3] : k1_xboole_0 = k5_xboole_0(X3,k1_setfam_1(k1_enumset1(X3,X3,k5_xboole_0(X3,k1_xboole_0)))) ),
    inference(superposition,[],[f63,f90])).

fof(f90,plain,(
    ! [X9] : k1_xboole_0 = k1_setfam_1(k1_enumset1(X9,X9,k1_xboole_0)) ),
    inference(superposition,[],[f72,f62])).

fof(f63,plain,(
    ! [X0,X1] : k1_setfam_1(k1_enumset1(X0,X0,X1)) = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1)))))) ),
    inference(definition_unfolding,[],[f45,f53,f54,f54])).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f320,plain,(
    k3_tarski(k1_enumset1(sK1,sK1,k5_xboole_0(sK0,sK0))) = k3_tarski(k1_enumset1(sK0,sK0,sK1)) ),
    inference(forward_demodulation,[],[f303,f62])).

fof(f303,plain,(
    k3_tarski(k1_enumset1(sK1,sK1,sK0)) = k3_tarski(k1_enumset1(sK1,sK1,k5_xboole_0(sK0,sK0))) ),
    inference(superposition,[],[f64,f128])).

fof(f128,plain,(
    sK0 = k1_setfam_1(k1_enumset1(sK0,sK0,sK1)) ),
    inference(resolution,[],[f65,f32])).

fof(f32,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_setfam_1(k1_enumset1(X0,X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f48,f53])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f64,plain,(
    ! [X0,X1] : k3_tarski(k1_enumset1(X0,X0,X1)) = k3_tarski(k1_enumset1(X0,X0,k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X0))))) ),
    inference(definition_unfolding,[],[f47,f55,f54,f55])).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f775,plain,(
    ! [X10,X11] : r1_tarski(k10_relat_1(sK2,X10),k10_relat_1(sK2,k3_tarski(k1_enumset1(X10,X10,X11)))) ),
    inference(superposition,[],[f59,f596])).

fof(f596,plain,(
    ! [X0,X1] : k10_relat_1(sK2,k3_tarski(k1_enumset1(X0,X0,X1))) = k3_tarski(k1_enumset1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))) ),
    inference(resolution,[],[f68,f31])).

fof(f31,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(X2,k3_tarski(k1_enumset1(X0,X0,X1))) = k3_tarski(k1_enumset1(k10_relat_1(X2,X0),k10_relat_1(X2,X0),k10_relat_1(X2,X1))) ) ),
    inference(definition_unfolding,[],[f51,f55,f55])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_relat_1)).

fof(f59,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f38,f55])).

fof(f38,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:12:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (29553)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.46  % (29545)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.46  % (29550)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.46  % (29543)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.47  % (29544)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.47  % (29550)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % (29542)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.47  % (29551)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.48  % (29539)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.48  % (29548)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.48  % (29552)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.48  % (29540)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.48  % (29538)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f796,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(subsumption_resolution,[],[f795,f33])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    ~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 0.20/0.49    inference(cnf_transformation,[],[f29])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK2)),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f28])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ? [X0,X1,X2] : (~r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK2))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ? [X0,X1,X2] : (~r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 0.20/0.49    inference(flattening,[],[f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ? [X0,X1,X2] : ((~r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 0.20/0.49    inference(ennf_transformation,[],[f20])).
% 0.20/0.49  fof(f20,negated_conjecture,(
% 0.20/0.49    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 0.20/0.49    inference(negated_conjecture,[],[f19])).
% 0.20/0.49  fof(f19,conjecture,(
% 0.20/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).
% 0.20/0.49  fof(f795,plain,(
% 0.20/0.49    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 0.20/0.49    inference(superposition,[],[f775,f462])).
% 0.20/0.49  fof(f462,plain,(
% 0.20/0.49    sK1 = k3_tarski(k1_enumset1(sK0,sK0,sK1))),
% 0.20/0.49    inference(forward_demodulation,[],[f450,f56])).
% 0.20/0.49  fof(f56,plain,(
% 0.20/0.49    ( ! [X0] : (k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X0) )),
% 0.20/0.49    inference(definition_unfolding,[],[f34,f55])).
% 0.20/0.49  fof(f55,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 0.20/0.49    inference(definition_unfolding,[],[f44,f42])).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  fof(f15,axiom,(
% 0.20/0.49    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f16])).
% 0.20/0.49  fof(f16,axiom,(
% 0.20/0.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.20/0.49  fof(f450,plain,(
% 0.20/0.49    k3_tarski(k1_enumset1(sK1,sK1,k1_xboole_0)) = k3_tarski(k1_enumset1(sK0,sK0,sK1))),
% 0.20/0.49    inference(backward_demodulation,[],[f320,f424])).
% 0.20/0.49  fof(f424,plain,(
% 0.20/0.49    ( ! [X3] : (k1_xboole_0 = k5_xboole_0(X3,X3)) )),
% 0.20/0.49    inference(forward_demodulation,[],[f423,f58])).
% 0.20/0.49  fof(f58,plain,(
% 0.20/0.49    ( ! [X0] : (k1_setfam_1(k1_enumset1(X0,X0,X0)) = X0) )),
% 0.20/0.49    inference(definition_unfolding,[],[f37,f53])).
% 0.20/0.49  fof(f53,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 0.20/0.49    inference(definition_unfolding,[],[f43,f42])).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  fof(f17,axiom,(
% 0.20/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f21])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.20/0.49    inference(rectify,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.20/0.49  fof(f423,plain,(
% 0.20/0.49    ( ! [X3] : (k1_xboole_0 = k5_xboole_0(X3,k1_setfam_1(k1_enumset1(X3,X3,X3)))) )),
% 0.20/0.49    inference(forward_demodulation,[],[f407,f97])).
% 0.20/0.49  fof(f97,plain,(
% 0.20/0.49    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.49    inference(forward_demodulation,[],[f85,f72])).
% 0.20/0.49  fof(f72,plain,(
% 0.20/0.49    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k1_enumset1(k1_xboole_0,k1_xboole_0,X0))) )),
% 0.20/0.49    inference(resolution,[],[f60,f36])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.20/0.49    inference(ennf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,axiom,(
% 0.20/0.49    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.20/0.49  fof(f60,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0)) )),
% 0.20/0.49    inference(definition_unfolding,[],[f39,f53])).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.20/0.49  fof(f85,plain,(
% 0.20/0.49    ( ! [X0] : (k5_xboole_0(X0,k1_setfam_1(k1_enumset1(k1_xboole_0,k1_xboole_0,X0))) = X0) )),
% 0.20/0.49    inference(superposition,[],[f57,f62])).
% 0.20/0.49  fof(f62,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 0.20/0.49    inference(definition_unfolding,[],[f41,f42,f42])).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f14])).
% 0.20/0.49  fof(f14,axiom,(
% 0.20/0.49    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.20/0.49  fof(f57,plain,(
% 0.20/0.49    ( ! [X0] : (k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,k1_xboole_0))) = X0) )),
% 0.20/0.49    inference(definition_unfolding,[],[f35,f54])).
% 0.20/0.49  fof(f54,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1)))) )),
% 0.20/0.49    inference(definition_unfolding,[],[f46,f53])).
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,axiom,(
% 0.20/0.49    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.20/0.49  fof(f407,plain,(
% 0.20/0.49    ( ! [X3] : (k1_xboole_0 = k5_xboole_0(X3,k1_setfam_1(k1_enumset1(X3,X3,k5_xboole_0(X3,k1_xboole_0))))) )),
% 0.20/0.49    inference(superposition,[],[f63,f90])).
% 0.20/0.49  fof(f90,plain,(
% 0.20/0.49    ( ! [X9] : (k1_xboole_0 = k1_setfam_1(k1_enumset1(X9,X9,k1_xboole_0))) )),
% 0.20/0.49    inference(superposition,[],[f72,f62])).
% 0.20/0.49  fof(f63,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k1_setfam_1(k1_enumset1(X0,X0,X1)) = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))))))) )),
% 0.20/0.49    inference(definition_unfolding,[],[f45,f53,f54,f54])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f10])).
% 0.20/0.49  fof(f10,axiom,(
% 0.20/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.49  fof(f320,plain,(
% 0.20/0.49    k3_tarski(k1_enumset1(sK1,sK1,k5_xboole_0(sK0,sK0))) = k3_tarski(k1_enumset1(sK0,sK0,sK1))),
% 0.20/0.49    inference(forward_demodulation,[],[f303,f62])).
% 0.20/0.49  fof(f303,plain,(
% 0.20/0.49    k3_tarski(k1_enumset1(sK1,sK1,sK0)) = k3_tarski(k1_enumset1(sK1,sK1,k5_xboole_0(sK0,sK0)))),
% 0.20/0.49    inference(superposition,[],[f64,f128])).
% 0.20/0.49  fof(f128,plain,(
% 0.20/0.49    sK0 = k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),
% 0.20/0.49    inference(resolution,[],[f65,f32])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    r1_tarski(sK0,sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f29])).
% 0.20/0.49  fof(f65,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_setfam_1(k1_enumset1(X0,X0,X1)) = X0) )),
% 0.20/0.49    inference(definition_unfolding,[],[f48,f53])).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.49  fof(f64,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k3_tarski(k1_enumset1(X0,X0,X1)) = k3_tarski(k1_enumset1(X0,X0,k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X0)))))) )),
% 0.20/0.49    inference(definition_unfolding,[],[f47,f55,f54,f55])).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.20/0.49  fof(f775,plain,(
% 0.20/0.49    ( ! [X10,X11] : (r1_tarski(k10_relat_1(sK2,X10),k10_relat_1(sK2,k3_tarski(k1_enumset1(X10,X10,X11))))) )),
% 0.20/0.49    inference(superposition,[],[f59,f596])).
% 0.20/0.49  fof(f596,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k10_relat_1(sK2,k3_tarski(k1_enumset1(X0,X0,X1))) = k3_tarski(k1_enumset1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)))) )),
% 0.20/0.49    inference(resolution,[],[f68,f31])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    v1_relat_1(sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f29])).
% 0.20/0.49  fof(f68,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(X2,k3_tarski(k1_enumset1(X0,X0,X1))) = k3_tarski(k1_enumset1(k10_relat_1(X2,X0),k10_relat_1(X2,X0),k10_relat_1(X2,X1)))) )),
% 0.20/0.49    inference(definition_unfolding,[],[f51,f55,f55])).
% 0.20/0.49  fof(f51,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f26])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 0.20/0.49    inference(ennf_transformation,[],[f18])).
% 0.20/0.49  fof(f18,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_relat_1)).
% 0.20/0.49  fof(f59,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1)))) )),
% 0.20/0.49    inference(definition_unfolding,[],[f38,f55])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,axiom,(
% 0.20/0.49    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (29550)------------------------------
% 0.20/0.49  % (29550)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (29550)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (29550)Memory used [KB]: 2046
% 0.20/0.49  % (29550)Time elapsed: 0.065 s
% 0.20/0.49  % (29550)------------------------------
% 0.20/0.49  % (29550)------------------------------
% 0.20/0.49  % (29537)Success in time 0.136 s
%------------------------------------------------------------------------------
