%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:49 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   29 (  29 expanded)
%              Number of leaves         :    9 (   9 expanded)
%              Depth                    :    9
%              Number of atoms          :   37 (  37 expanded)
%              Number of equality atoms :   26 (  26 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f29,plain,(
    $false ),
    inference(resolution,[],[f28,f17])).

fof(f17,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f28,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) ),
    inference(trivial_inequality_removal,[],[f27])).

fof(f27,plain,
    ( sK0 != sK0
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f24,f26])).

fof(f26,plain,(
    ! [X0] :
      ( k3_subset_1(X0,k1_xboole_0) = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ) ),
    inference(forward_demodulation,[],[f25,f19])).

fof(f19,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f25,plain,(
    ! [X0] :
      ( k5_xboole_0(X0,k1_xboole_0) = k3_subset_1(X0,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f23,f18])).

fof(f18,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f21,f20])).

fof(f20,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f24,plain,(
    sK0 != k3_subset_1(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f22,f16])).

fof(f16,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f22,plain,(
    k2_subset_1(sK0) != k3_subset_1(sK0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f14,f15])).

fof(f15,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(f14,plain,(
    k2_subset_1(sK0) != k3_subset_1(sK0,k1_subset_1(sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    k2_subset_1(sK0) != k3_subset_1(sK0,k1_subset_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f12])).

fof(f12,plain,
    ( ? [X0] : k2_subset_1(X0) != k3_subset_1(X0,k1_subset_1(X0))
   => k2_subset_1(sK0) != k3_subset_1(sK0,k1_subset_1(sK0)) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] : k2_subset_1(X0) != k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 15:14:35 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.42  % (17199)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.46  % (17203)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.46  % (17203)Refutation found. Thanks to Tanya!
% 0.22/0.46  % SZS status Theorem for theBenchmark
% 0.22/0.46  % SZS output start Proof for theBenchmark
% 0.22/0.46  fof(f29,plain,(
% 0.22/0.46    $false),
% 0.22/0.46    inference(resolution,[],[f28,f17])).
% 0.22/0.46  fof(f17,plain,(
% 0.22/0.46    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.46    inference(cnf_transformation,[],[f7])).
% 0.22/0.46  fof(f7,axiom,(
% 0.22/0.46    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.22/0.46  fof(f28,plain,(
% 0.22/0.46    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))),
% 0.22/0.46    inference(trivial_inequality_removal,[],[f27])).
% 0.22/0.46  fof(f27,plain,(
% 0.22/0.46    sK0 != sK0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))),
% 0.22/0.46    inference(superposition,[],[f24,f26])).
% 0.22/0.46  fof(f26,plain,(
% 0.22/0.46    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.46    inference(forward_demodulation,[],[f25,f19])).
% 0.22/0.46  fof(f19,plain,(
% 0.22/0.46    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.46    inference(cnf_transformation,[],[f3])).
% 0.22/0.46  fof(f3,axiom,(
% 0.22/0.46    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.22/0.46  fof(f25,plain,(
% 0.22/0.46    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k3_subset_1(X0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.46    inference(superposition,[],[f23,f18])).
% 0.22/0.46  fof(f18,plain,(
% 0.22/0.46    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f2])).
% 0.22/0.46  fof(f2,axiom,(
% 0.22/0.46    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.22/0.46  fof(f23,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.46    inference(definition_unfolding,[],[f21,f20])).
% 0.22/0.46  fof(f20,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.46    inference(cnf_transformation,[],[f1])).
% 0.22/0.46  fof(f1,axiom,(
% 0.22/0.46    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.46  fof(f21,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.46    inference(cnf_transformation,[],[f11])).
% 0.22/0.46  fof(f11,plain,(
% 0.22/0.46    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.46    inference(ennf_transformation,[],[f6])).
% 0.22/0.46  fof(f6,axiom,(
% 0.22/0.46    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.22/0.46  fof(f24,plain,(
% 0.22/0.46    sK0 != k3_subset_1(sK0,k1_xboole_0)),
% 0.22/0.46    inference(forward_demodulation,[],[f22,f16])).
% 0.22/0.46  fof(f16,plain,(
% 0.22/0.46    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.22/0.46    inference(cnf_transformation,[],[f5])).
% 0.22/0.46  fof(f5,axiom,(
% 0.22/0.46    ! [X0] : k2_subset_1(X0) = X0),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.22/0.46  fof(f22,plain,(
% 0.22/0.46    k2_subset_1(sK0) != k3_subset_1(sK0,k1_xboole_0)),
% 0.22/0.46    inference(definition_unfolding,[],[f14,f15])).
% 0.22/0.46  fof(f15,plain,(
% 0.22/0.46    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f4])).
% 0.22/0.46  fof(f4,axiom,(
% 0.22/0.46    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).
% 0.22/0.46  fof(f14,plain,(
% 0.22/0.46    k2_subset_1(sK0) != k3_subset_1(sK0,k1_subset_1(sK0))),
% 0.22/0.46    inference(cnf_transformation,[],[f13])).
% 0.22/0.46  fof(f13,plain,(
% 0.22/0.46    k2_subset_1(sK0) != k3_subset_1(sK0,k1_subset_1(sK0))),
% 0.22/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f12])).
% 0.22/0.46  fof(f12,plain,(
% 0.22/0.46    ? [X0] : k2_subset_1(X0) != k3_subset_1(X0,k1_subset_1(X0)) => k2_subset_1(sK0) != k3_subset_1(sK0,k1_subset_1(sK0))),
% 0.22/0.46    introduced(choice_axiom,[])).
% 0.22/0.46  fof(f10,plain,(
% 0.22/0.46    ? [X0] : k2_subset_1(X0) != k3_subset_1(X0,k1_subset_1(X0))),
% 0.22/0.46    inference(ennf_transformation,[],[f9])).
% 0.22/0.46  fof(f9,negated_conjecture,(
% 0.22/0.46    ~! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 0.22/0.46    inference(negated_conjecture,[],[f8])).
% 0.22/0.46  fof(f8,conjecture,(
% 0.22/0.46    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).
% 0.22/0.46  % SZS output end Proof for theBenchmark
% 0.22/0.46  % (17203)------------------------------
% 0.22/0.46  % (17203)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.46  % (17203)Termination reason: Refutation
% 0.22/0.46  
% 0.22/0.46  % (17203)Memory used [KB]: 6012
% 0.22/0.46  % (17203)Time elapsed: 0.042 s
% 0.22/0.46  % (17203)------------------------------
% 0.22/0.46  % (17203)------------------------------
% 0.22/0.46  % (17198)Success in time 0.098 s
%------------------------------------------------------------------------------
