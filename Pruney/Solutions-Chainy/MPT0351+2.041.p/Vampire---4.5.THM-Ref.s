%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:08 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 113 expanded)
%              Number of leaves         :   15 (  35 expanded)
%              Depth                    :   11
%              Number of atoms          :   88 ( 173 expanded)
%              Number of equality atoms :   52 ( 106 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f211,plain,(
    $false ),
    inference(subsumption_resolution,[],[f210,f46])).

fof(f46,plain,(
    sK0 != k4_subset_1(sK0,sK1,sK0) ),
    inference(backward_demodulation,[],[f25,f26])).

fof(f26,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f25,plain,(
    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f22])).

fof(f22,plain,
    ( ? [X0,X1] :
        ( k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0))
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_subset_1)).

fof(f210,plain,(
    sK0 = k4_subset_1(sK0,sK1,sK0) ),
    inference(forward_demodulation,[],[f209,f130])).

fof(f130,plain,(
    sK0 = k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1)) ),
    inference(superposition,[],[f43,f124])).

fof(f124,plain,(
    sK1 = k3_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f123,f121])).

fof(f121,plain,(
    sK1 = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_subset_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f119,f61])).

fof(f61,plain,(
    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) ),
    inference(resolution,[],[f36,f24])).

fof(f24,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f119,plain,(
    k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_subset_1(sK0,sK1))) ),
    inference(resolution,[],[f44,f48])).

fof(f48,plain,(
    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f34,f24])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f35,f33])).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f35,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f123,plain,(
    k3_xboole_0(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_subset_1(sK0,sK1))) ),
    inference(superposition,[],[f41,f117])).

fof(f117,plain,(
    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f44,f24])).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f32,f33,f33])).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f43,plain,(
    ! [X0,X1] : k3_tarski(k2_enumset1(X0,X0,X0,k3_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f29,f40])).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f31,f39])).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f30,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f30,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f31,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f209,plain,(
    k4_subset_1(sK0,sK1,sK0) = k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1)) ),
    inference(forward_demodulation,[],[f203,f42])).

fof(f42,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f28,f39,f39])).

fof(f28,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f203,plain,(
    k4_subset_1(sK0,sK1,sK0) = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK0)) ),
    inference(resolution,[],[f140,f24])).

fof(f140,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X0) = k3_tarski(k2_enumset1(X1,X1,X1,X0)) ) ),
    inference(resolution,[],[f45,f47])).

fof(f47,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f27,f26])).

fof(f27,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k3_tarski(k2_enumset1(X1,X1,X1,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f38,f40])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:27:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.41  % (22230)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.42  % (22230)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f211,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(subsumption_resolution,[],[f210,f46])).
% 0.21/0.42  fof(f46,plain,(
% 0.21/0.42    sK0 != k4_subset_1(sK0,sK1,sK0)),
% 0.21/0.42    inference(backward_demodulation,[],[f25,f26])).
% 0.21/0.42  fof(f26,plain,(
% 0.21/0.42    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.42    inference(cnf_transformation,[],[f8])).
% 0.21/0.42  fof(f8,axiom,(
% 0.21/0.42    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.42  fof(f25,plain,(
% 0.21/0.42    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0))),
% 0.21/0.42    inference(cnf_transformation,[],[f23])).
% 0.21/0.42  fof(f23,plain,(
% 0.21/0.42    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f22])).
% 0.21/0.42  fof(f22,plain,(
% 0.21/0.42    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f16,plain,(
% 0.21/0.42    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.42    inference(ennf_transformation,[],[f15])).
% 0.21/0.42  fof(f15,negated_conjecture,(
% 0.21/0.42    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)))),
% 0.21/0.42    inference(negated_conjecture,[],[f14])).
% 0.21/0.42  fof(f14,conjecture,(
% 0.21/0.42    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_subset_1)).
% 0.21/0.42  fof(f210,plain,(
% 0.21/0.42    sK0 = k4_subset_1(sK0,sK1,sK0)),
% 0.21/0.42    inference(forward_demodulation,[],[f209,f130])).
% 0.21/0.42  fof(f130,plain,(
% 0.21/0.42    sK0 = k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1))),
% 0.21/0.42    inference(superposition,[],[f43,f124])).
% 0.21/0.42  fof(f124,plain,(
% 0.21/0.42    sK1 = k3_xboole_0(sK0,sK1)),
% 0.21/0.42    inference(forward_demodulation,[],[f123,f121])).
% 0.21/0.42  fof(f121,plain,(
% 0.21/0.42    sK1 = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_subset_1(sK0,sK1)))),
% 0.21/0.42    inference(forward_demodulation,[],[f119,f61])).
% 0.21/0.42  fof(f61,plain,(
% 0.21/0.42    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))),
% 0.21/0.42    inference(resolution,[],[f36,f24])).
% 0.21/0.42  fof(f24,plain,(
% 0.21/0.42    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.42    inference(cnf_transformation,[],[f23])).
% 0.21/0.42  fof(f36,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.21/0.42    inference(cnf_transformation,[],[f19])).
% 0.21/0.42  fof(f19,plain,(
% 0.21/0.42    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.42    inference(ennf_transformation,[],[f12])).
% 0.21/0.42  fof(f12,axiom,(
% 0.21/0.42    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.21/0.42  fof(f119,plain,(
% 0.21/0.42    k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_subset_1(sK0,sK1)))),
% 0.21/0.42    inference(resolution,[],[f44,f48])).
% 0.21/0.42  fof(f48,plain,(
% 0.21/0.42    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 0.21/0.42    inference(resolution,[],[f34,f24])).
% 0.21/0.42  fof(f34,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f17])).
% 0.21/0.42  fof(f17,plain,(
% 0.21/0.42    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.42    inference(ennf_transformation,[],[f11])).
% 0.21/0.42  fof(f11,axiom,(
% 0.21/0.42    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.21/0.42  fof(f44,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)) )),
% 0.21/0.42    inference(definition_unfolding,[],[f35,f33])).
% 0.21/0.42  fof(f33,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.42  fof(f35,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f18])).
% 0.21/0.42  fof(f18,plain,(
% 0.21/0.42    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.42    inference(ennf_transformation,[],[f9])).
% 0.21/0.42  fof(f9,axiom,(
% 0.21/0.42    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.21/0.42  fof(f123,plain,(
% 0.21/0.42    k3_xboole_0(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_subset_1(sK0,sK1)))),
% 0.21/0.42    inference(superposition,[],[f41,f117])).
% 0.21/0.42  fof(f117,plain,(
% 0.21/0.42    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.21/0.42    inference(resolution,[],[f44,f24])).
% 0.21/0.42  fof(f41,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) )),
% 0.21/0.42    inference(definition_unfolding,[],[f32,f33,f33])).
% 0.21/0.42  fof(f32,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f3])).
% 0.21/0.42  fof(f3,axiom,(
% 0.21/0.42    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.42  fof(f43,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k3_tarski(k2_enumset1(X0,X0,X0,k3_xboole_0(X0,X1))) = X0) )),
% 0.21/0.42    inference(definition_unfolding,[],[f29,f40])).
% 0.21/0.42  fof(f40,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 0.21/0.42    inference(definition_unfolding,[],[f31,f39])).
% 0.21/0.42  fof(f39,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.42    inference(definition_unfolding,[],[f30,f37])).
% 0.21/0.42  fof(f37,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f6])).
% 0.21/0.42  fof(f6,axiom,(
% 0.21/0.42    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.42  fof(f30,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f5])).
% 0.21/0.42  fof(f5,axiom,(
% 0.21/0.42    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.42  fof(f31,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f7])).
% 0.21/0.42  fof(f7,axiom,(
% 0.21/0.42    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.42  fof(f29,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.21/0.42    inference(cnf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 0.21/0.42  fof(f209,plain,(
% 0.21/0.42    k4_subset_1(sK0,sK1,sK0) = k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1))),
% 0.21/0.42    inference(forward_demodulation,[],[f203,f42])).
% 0.21/0.42  fof(f42,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 0.21/0.42    inference(definition_unfolding,[],[f28,f39,f39])).
% 0.21/0.42  fof(f28,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f4])).
% 0.21/0.42  fof(f4,axiom,(
% 0.21/0.42    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.21/0.42  fof(f203,plain,(
% 0.21/0.42    k4_subset_1(sK0,sK1,sK0) = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK0))),
% 0.21/0.42    inference(resolution,[],[f140,f24])).
% 0.21/0.42  fof(f140,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X0) = k3_tarski(k2_enumset1(X1,X1,X1,X0))) )),
% 0.21/0.42    inference(resolution,[],[f45,f47])).
% 0.21/0.42  fof(f47,plain,(
% 0.21/0.42    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.42    inference(forward_demodulation,[],[f27,f26])).
% 0.21/0.42  fof(f27,plain,(
% 0.21/0.42    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f10])).
% 0.21/0.42  fof(f10,axiom,(
% 0.21/0.42    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.21/0.42  fof(f45,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k2_enumset1(X1,X1,X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.42    inference(definition_unfolding,[],[f38,f40])).
% 0.21/0.42  fof(f38,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f21])).
% 0.21/0.42  fof(f21,plain,(
% 0.21/0.42    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.42    inference(flattening,[],[f20])).
% 0.21/0.42  fof(f20,plain,(
% 0.21/0.42    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.21/0.42    inference(ennf_transformation,[],[f13])).
% 0.21/0.42  fof(f13,axiom,(
% 0.21/0.42    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (22230)------------------------------
% 0.21/0.42  % (22230)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (22230)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (22230)Memory used [KB]: 1791
% 0.21/0.42  % (22230)Time elapsed: 0.010 s
% 0.21/0.42  % (22230)------------------------------
% 0.21/0.42  % (22230)------------------------------
% 0.21/0.42  % (22212)Success in time 0.07 s
%------------------------------------------------------------------------------
