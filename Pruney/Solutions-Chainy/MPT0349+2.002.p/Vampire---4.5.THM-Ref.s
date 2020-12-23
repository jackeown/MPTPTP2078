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
% DateTime   : Thu Dec  3 12:43:48 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   40 (  46 expanded)
%              Number of leaves         :   12 (  15 expanded)
%              Depth                    :    9
%              Number of atoms          :   44 (  50 expanded)
%              Number of equality atoms :   38 (  44 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f66,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f62])).

fof(f62,plain,(
    sK0 != sK0 ),
    inference(superposition,[],[f35,f59])).

fof(f59,plain,(
    ! [X2] : k4_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(forward_demodulation,[],[f57,f33])).

fof(f33,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f30,f21])).

fof(f21,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f30,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(definition_unfolding,[],[f22,f24])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f22,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f57,plain,(
    ! [X2] : k4_xboole_0(X2,k1_xboole_0) = k5_xboole_0(X2,k1_xboole_0) ),
    inference(superposition,[],[f28,f41])).

fof(f41,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f31,f21])).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f23,f25,f25])).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f26,f25])).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f35,plain,(
    sK0 != k4_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f32,f34])).

fof(f34,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(resolution,[],[f27,f20])).

fof(f20,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f32,plain,(
    sK0 != k3_subset_1(sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f29,f19])).

fof(f19,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f29,plain,(
    k2_subset_1(sK0) != k3_subset_1(sK0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f17,f18])).

fof(f18,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(f17,plain,(
    k2_subset_1(sK0) != k3_subset_1(sK0,k1_subset_1(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    k2_subset_1(sK0) != k3_subset_1(sK0,k1_subset_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f15])).

fof(f15,plain,
    ( ? [X0] : k2_subset_1(X0) != k3_subset_1(X0,k1_subset_1(X0))
   => k2_subset_1(sK0) != k3_subset_1(sK0,k1_subset_1(sK0)) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] : k2_subset_1(X0) != k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.36  % Computer   : n010.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 09:26:29 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.23/0.45  % (17399)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.23/0.48  % (17401)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.23/0.48  % (17401)Refutation found. Thanks to Tanya!
% 0.23/0.48  % SZS status Theorem for theBenchmark
% 0.23/0.48  % SZS output start Proof for theBenchmark
% 0.23/0.48  fof(f66,plain,(
% 0.23/0.48    $false),
% 0.23/0.48    inference(trivial_inequality_removal,[],[f62])).
% 0.23/0.48  fof(f62,plain,(
% 0.23/0.48    sK0 != sK0),
% 0.23/0.48    inference(superposition,[],[f35,f59])).
% 0.23/0.48  fof(f59,plain,(
% 0.23/0.48    ( ! [X2] : (k4_xboole_0(X2,k1_xboole_0) = X2) )),
% 0.23/0.48    inference(forward_demodulation,[],[f57,f33])).
% 0.23/0.48  fof(f33,plain,(
% 0.23/0.48    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.23/0.48    inference(forward_demodulation,[],[f30,f21])).
% 0.23/0.48  fof(f21,plain,(
% 0.23/0.48    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.23/0.48    inference(cnf_transformation,[],[f5])).
% 0.23/0.48  fof(f5,axiom,(
% 0.23/0.48    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.23/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 0.23/0.48  fof(f30,plain,(
% 0.23/0.48    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0) )),
% 0.23/0.48    inference(definition_unfolding,[],[f22,f24])).
% 0.23/0.48  fof(f24,plain,(
% 0.23/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.23/0.48    inference(cnf_transformation,[],[f6])).
% 0.23/0.48  fof(f6,axiom,(
% 0.23/0.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.23/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.23/0.48  fof(f22,plain,(
% 0.23/0.48    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.23/0.48    inference(cnf_transformation,[],[f3])).
% 0.23/0.48  fof(f3,axiom,(
% 0.23/0.48    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.23/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.23/0.48  fof(f57,plain,(
% 0.23/0.48    ( ! [X2] : (k4_xboole_0(X2,k1_xboole_0) = k5_xboole_0(X2,k1_xboole_0)) )),
% 0.23/0.48    inference(superposition,[],[f28,f41])).
% 0.23/0.48  fof(f41,plain,(
% 0.23/0.48    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.23/0.48    inference(superposition,[],[f31,f21])).
% 0.23/0.48  fof(f31,plain,(
% 0.23/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.23/0.48    inference(definition_unfolding,[],[f23,f25,f25])).
% 0.23/0.48  fof(f25,plain,(
% 0.23/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.23/0.48    inference(cnf_transformation,[],[f4])).
% 0.23/0.48  fof(f4,axiom,(
% 0.23/0.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.23/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.23/0.48  fof(f23,plain,(
% 0.23/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.23/0.48    inference(cnf_transformation,[],[f1])).
% 0.23/0.48  fof(f1,axiom,(
% 0.23/0.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.23/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.23/0.48  fof(f28,plain,(
% 0.23/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.23/0.48    inference(definition_unfolding,[],[f26,f25])).
% 0.23/0.48  fof(f26,plain,(
% 0.23/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.23/0.48    inference(cnf_transformation,[],[f2])).
% 0.23/0.48  fof(f2,axiom,(
% 0.23/0.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.23/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.23/0.48  fof(f35,plain,(
% 0.23/0.48    sK0 != k4_xboole_0(sK0,k1_xboole_0)),
% 0.23/0.48    inference(superposition,[],[f32,f34])).
% 0.23/0.48  fof(f34,plain,(
% 0.23/0.48    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = k3_subset_1(X0,k1_xboole_0)) )),
% 0.23/0.48    inference(resolution,[],[f27,f20])).
% 0.23/0.48  fof(f20,plain,(
% 0.23/0.48    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.23/0.48    inference(cnf_transformation,[],[f10])).
% 0.23/0.48  fof(f10,axiom,(
% 0.23/0.48    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.23/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.23/0.48  fof(f27,plain,(
% 0.23/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 0.23/0.48    inference(cnf_transformation,[],[f14])).
% 0.23/0.48  fof(f14,plain,(
% 0.23/0.48    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.23/0.48    inference(ennf_transformation,[],[f9])).
% 0.23/0.48  fof(f9,axiom,(
% 0.23/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.23/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.23/0.48  fof(f32,plain,(
% 0.23/0.48    sK0 != k3_subset_1(sK0,k1_xboole_0)),
% 0.23/0.48    inference(backward_demodulation,[],[f29,f19])).
% 0.23/0.48  fof(f19,plain,(
% 0.23/0.48    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.23/0.48    inference(cnf_transformation,[],[f8])).
% 0.23/0.48  fof(f8,axiom,(
% 0.23/0.48    ! [X0] : k2_subset_1(X0) = X0),
% 0.23/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.23/0.48  fof(f29,plain,(
% 0.23/0.48    k2_subset_1(sK0) != k3_subset_1(sK0,k1_xboole_0)),
% 0.23/0.48    inference(definition_unfolding,[],[f17,f18])).
% 0.23/0.48  fof(f18,plain,(
% 0.23/0.48    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 0.23/0.48    inference(cnf_transformation,[],[f7])).
% 0.23/0.48  fof(f7,axiom,(
% 0.23/0.48    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 0.23/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).
% 0.23/0.48  fof(f17,plain,(
% 0.23/0.48    k2_subset_1(sK0) != k3_subset_1(sK0,k1_subset_1(sK0))),
% 0.23/0.48    inference(cnf_transformation,[],[f16])).
% 0.23/0.48  fof(f16,plain,(
% 0.23/0.48    k2_subset_1(sK0) != k3_subset_1(sK0,k1_subset_1(sK0))),
% 0.23/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f15])).
% 0.23/0.48  fof(f15,plain,(
% 0.23/0.48    ? [X0] : k2_subset_1(X0) != k3_subset_1(X0,k1_subset_1(X0)) => k2_subset_1(sK0) != k3_subset_1(sK0,k1_subset_1(sK0))),
% 0.23/0.48    introduced(choice_axiom,[])).
% 0.23/0.48  fof(f13,plain,(
% 0.23/0.48    ? [X0] : k2_subset_1(X0) != k3_subset_1(X0,k1_subset_1(X0))),
% 0.23/0.48    inference(ennf_transformation,[],[f12])).
% 0.23/0.48  fof(f12,negated_conjecture,(
% 0.23/0.48    ~! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 0.23/0.48    inference(negated_conjecture,[],[f11])).
% 0.23/0.48  fof(f11,conjecture,(
% 0.23/0.48    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 0.23/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).
% 0.23/0.48  % SZS output end Proof for theBenchmark
% 0.23/0.48  % (17401)------------------------------
% 0.23/0.48  % (17401)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.48  % (17401)Termination reason: Refutation
% 0.23/0.48  
% 0.23/0.48  % (17401)Memory used [KB]: 6140
% 0.23/0.48  % (17401)Time elapsed: 0.042 s
% 0.23/0.48  % (17401)------------------------------
% 0.23/0.48  % (17401)------------------------------
% 0.23/0.48  % (17393)Success in time 0.109 s
%------------------------------------------------------------------------------
