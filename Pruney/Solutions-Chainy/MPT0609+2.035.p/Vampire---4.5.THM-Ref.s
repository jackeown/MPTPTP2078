%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:29 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 177 expanded)
%              Number of leaves         :   10 (  52 expanded)
%              Depth                    :   12
%              Number of atoms          :   67 ( 308 expanded)
%              Number of equality atoms :   45 ( 177 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f98,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f95])).

fof(f95,plain,(
    k6_subset_1(k1_relat_1(sK1),sK0) != k6_subset_1(k1_relat_1(sK1),sK0) ),
    inference(superposition,[],[f38,f80])).

fof(f80,plain,(
    ! [X5] : k6_subset_1(k1_relat_1(sK1),X5) = k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,X5))) ),
    inference(forward_demodulation,[],[f79,f72])).

fof(f72,plain,(
    ! [X4] : k6_subset_1(k1_relat_1(sK1),k6_subset_1(k1_relat_1(sK1),X4)) = k1_relat_1(k7_relat_1(sK1,X4)) ),
    inference(backward_demodulation,[],[f50,f71])).

fof(f71,plain,(
    ! [X1] : k7_relat_1(sK1,X1) = k6_subset_1(sK1,k6_subset_1(sK1,k7_relat_1(sK1,X1))) ),
    inference(forward_demodulation,[],[f64,f42])).

fof(f42,plain,(
    ! [X0] : k6_subset_1(sK1,k7_relat_1(sK1,X0)) = k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),X0)) ),
    inference(superposition,[],[f41,f36])).

fof(f36,plain,(
    sK1 = k7_relat_1(sK1,k1_relat_1(sK1)) ),
    inference(resolution,[],[f21,f19])).

fof(f19,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0)))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f17])).

fof(f17,plain,
    ( ? [X0,X1] :
        ( k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) != k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0)))
        & v1_relat_1(X1) )
   => ( k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0)))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] :
      ( k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) != k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0)))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t213_relat_1)).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

fof(f41,plain,(
    ! [X0,X1] : k7_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k7_relat_1(sK1,X0),k7_relat_1(sK1,X1)) ),
    inference(resolution,[],[f29,f19])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_relat_1)).

fof(f64,plain,(
    ! [X1] : k7_relat_1(sK1,X1) = k6_subset_1(sK1,k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),X1))) ),
    inference(superposition,[],[f46,f42])).

fof(f46,plain,(
    ! [X0] : k7_relat_1(sK1,X0) = k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),k6_subset_1(k1_relat_1(sK1),X0))) ),
    inference(resolution,[],[f35,f19])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),k6_subset_1(k1_relat_1(X1),X0))) ) ),
    inference(forward_demodulation,[],[f33,f32])).

fof(f32,plain,(
    ! [X0,X1] : k1_setfam_1(k1_enumset1(X0,X0,X1)) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(definition_unfolding,[],[f26,f30,f22,f22])).

fof(f22,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f23,f24])).

fof(f24,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f27,f30])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_relat_1)).

fof(f50,plain,(
    ! [X4] : k6_subset_1(k1_relat_1(sK1),k6_subset_1(k1_relat_1(sK1),X4)) = k1_relat_1(k6_subset_1(sK1,k6_subset_1(sK1,k7_relat_1(sK1,X4)))) ),
    inference(superposition,[],[f37,f42])).

fof(f37,plain,(
    ! [X0] : k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,X0))) = k6_subset_1(k1_relat_1(sK1),X0) ),
    inference(resolution,[],[f28,f19])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t212_relat_1)).

fof(f79,plain,(
    ! [X5] : k6_subset_1(k1_relat_1(sK1),X5) = k6_subset_1(k1_relat_1(sK1),k6_subset_1(k1_relat_1(sK1),k6_subset_1(k1_relat_1(sK1),X5))) ),
    inference(forward_demodulation,[],[f68,f37])).

fof(f68,plain,(
    ! [X5] : k6_subset_1(k1_relat_1(sK1),k6_subset_1(k1_relat_1(sK1),k6_subset_1(k1_relat_1(sK1),X5))) = k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,X5))) ),
    inference(superposition,[],[f37,f46])).

fof(f38,plain,(
    k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),sK0) ),
    inference(backward_demodulation,[],[f20,f37])).

fof(f20,plain,(
    k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:33:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (15810)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.47  % (15809)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.47  % (15808)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.47  % (15818)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.47  % (15819)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.48  % (15811)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.48  % (15822)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.48  % (15806)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.48  % (15807)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.48  % (15806)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f98,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(trivial_inequality_removal,[],[f95])).
% 0.22/0.48  fof(f95,plain,(
% 0.22/0.48    k6_subset_1(k1_relat_1(sK1),sK0) != k6_subset_1(k1_relat_1(sK1),sK0)),
% 0.22/0.48    inference(superposition,[],[f38,f80])).
% 0.22/0.48  fof(f80,plain,(
% 0.22/0.48    ( ! [X5] : (k6_subset_1(k1_relat_1(sK1),X5) = k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,X5)))) )),
% 0.22/0.48    inference(forward_demodulation,[],[f79,f72])).
% 0.22/0.48  fof(f72,plain,(
% 0.22/0.48    ( ! [X4] : (k6_subset_1(k1_relat_1(sK1),k6_subset_1(k1_relat_1(sK1),X4)) = k1_relat_1(k7_relat_1(sK1,X4))) )),
% 0.22/0.48    inference(backward_demodulation,[],[f50,f71])).
% 0.22/0.48  fof(f71,plain,(
% 0.22/0.48    ( ! [X1] : (k7_relat_1(sK1,X1) = k6_subset_1(sK1,k6_subset_1(sK1,k7_relat_1(sK1,X1)))) )),
% 0.22/0.48    inference(forward_demodulation,[],[f64,f42])).
% 0.22/0.48  fof(f42,plain,(
% 0.22/0.48    ( ! [X0] : (k6_subset_1(sK1,k7_relat_1(sK1,X0)) = k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),X0))) )),
% 0.22/0.48    inference(superposition,[],[f41,f36])).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    sK1 = k7_relat_1(sK1,k1_relat_1(sK1))),
% 0.22/0.48    inference(resolution,[],[f21,f19])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    v1_relat_1(sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) & v1_relat_1(sK1)),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f17])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ? [X0,X1] : (k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) != k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) & v1_relat_1(X1)) => (k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) & v1_relat_1(sK1))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    ? [X0,X1] : (k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) != k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) & v1_relat_1(X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f11])).
% 0.22/0.48  fof(f11,negated_conjecture,(
% 0.22/0.48    ~! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))))),
% 0.22/0.48    inference(negated_conjecture,[],[f10])).
% 0.22/0.48  fof(f10,conjecture,(
% 0.22/0.48    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t213_relat_1)).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ( ! [X0] : (~v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0) )),
% 0.22/0.48    inference(cnf_transformation,[],[f13])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,axiom,(
% 0.22/0.48    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).
% 0.22/0.48  fof(f41,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k7_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k7_relat_1(sK1,X0),k7_relat_1(sK1,X1))) )),
% 0.22/0.48    inference(resolution,[],[f29,f19])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f16])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (k7_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 0.22/0.48    inference(ennf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_relat_1)).
% 0.22/0.48  fof(f64,plain,(
% 0.22/0.48    ( ! [X1] : (k7_relat_1(sK1,X1) = k6_subset_1(sK1,k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),X1)))) )),
% 0.22/0.48    inference(superposition,[],[f46,f42])).
% 0.22/0.48  fof(f46,plain,(
% 0.22/0.48    ( ! [X0] : (k7_relat_1(sK1,X0) = k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),k6_subset_1(k1_relat_1(sK1),X0)))) )),
% 0.22/0.48    inference(resolution,[],[f35,f19])).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),k6_subset_1(k1_relat_1(X1),X0)))) )),
% 0.22/0.48    inference(forward_demodulation,[],[f33,f32])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k1_setfam_1(k1_enumset1(X0,X0,X1)) = k6_subset_1(X0,k6_subset_1(X0,X1))) )),
% 0.22/0.48    inference(definition_unfolding,[],[f26,f30,f22,f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 0.22/0.48    inference(definition_unfolding,[],[f23,f24])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X0))) | ~v1_relat_1(X1)) )),
% 0.22/0.48    inference(definition_unfolding,[],[f27,f30])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,axiom,(
% 0.22/0.48    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_relat_1)).
% 0.22/0.48  fof(f50,plain,(
% 0.22/0.48    ( ! [X4] : (k6_subset_1(k1_relat_1(sK1),k6_subset_1(k1_relat_1(sK1),X4)) = k1_relat_1(k6_subset_1(sK1,k6_subset_1(sK1,k7_relat_1(sK1,X4))))) )),
% 0.22/0.48    inference(superposition,[],[f37,f42])).
% 0.22/0.48  fof(f37,plain,(
% 0.22/0.48    ( ! [X0] : (k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,X0))) = k6_subset_1(k1_relat_1(sK1),X0)) )),
% 0.22/0.48    inference(resolution,[],[f28,f19])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ! [X0,X1] : (k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,axiom,(
% 0.22/0.48    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t212_relat_1)).
% 0.22/0.48  fof(f79,plain,(
% 0.22/0.48    ( ! [X5] : (k6_subset_1(k1_relat_1(sK1),X5) = k6_subset_1(k1_relat_1(sK1),k6_subset_1(k1_relat_1(sK1),k6_subset_1(k1_relat_1(sK1),X5)))) )),
% 0.22/0.48    inference(forward_demodulation,[],[f68,f37])).
% 0.22/0.48  fof(f68,plain,(
% 0.22/0.48    ( ! [X5] : (k6_subset_1(k1_relat_1(sK1),k6_subset_1(k1_relat_1(sK1),k6_subset_1(k1_relat_1(sK1),X5))) = k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,X5)))) )),
% 0.22/0.48    inference(superposition,[],[f37,f46])).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),sK0)),
% 0.22/0.48    inference(backward_demodulation,[],[f20,f37])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0)))),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (15806)------------------------------
% 0.22/0.48  % (15806)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (15806)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (15806)Memory used [KB]: 1663
% 0.22/0.48  % (15806)Time elapsed: 0.063 s
% 0.22/0.48  % (15806)------------------------------
% 0.22/0.48  % (15806)------------------------------
% 0.22/0.48  % (15817)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.48  % (15804)Success in time 0.119 s
%------------------------------------------------------------------------------
