%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:02 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 116 expanded)
%              Number of leaves         :   11 (  40 expanded)
%              Depth                    :   11
%              Number of atoms          :   54 ( 128 expanded)
%              Number of equality atoms :   53 ( 127 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f75,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f72])).

fof(f72,plain,(
    k3_xboole_0(sK0,sK1) != k3_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f37,f61])).

fof(f61,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(superposition,[],[f60,f39])).

fof(f39,plain,(
    ! [X0] : k1_setfam_1(k1_enumset1(X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f21,f33])).

fof(f33,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f22,f24])).

fof(f24,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f22,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f21,plain,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

fof(f60,plain,(
    ! [X6,X4,X5] : k1_setfam_1(k1_enumset1(X4,X5,X6)) = k3_xboole_0(k1_setfam_1(k1_enumset1(X4,X4,X5)),X6) ),
    inference(forward_demodulation,[],[f59,f39])).

fof(f59,plain,(
    ! [X6,X4,X5] : k1_setfam_1(k1_enumset1(X4,X5,X6)) = k3_xboole_0(k1_setfam_1(k1_enumset1(X4,X4,X5)),k1_setfam_1(k1_enumset1(X6,X6,X6))) ),
    inference(subsumption_resolution,[],[f58,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) != k1_xboole_0 ),
    inference(superposition,[],[f40,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X0,X1,X2))) ),
    inference(definition_unfolding,[],[f27,f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X3))) ),
    inference(definition_unfolding,[],[f29,f32,f33])).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f25,f24])).

fof(f25,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f29,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

fof(f27,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f40,plain,(
    ! [X0,X1] : k1_xboole_0 != k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),X1)) ),
    inference(definition_unfolding,[],[f23,f32,f33])).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f58,plain,(
    ! [X6,X4,X5] :
      ( k1_setfam_1(k1_enumset1(X4,X5,X6)) = k3_xboole_0(k1_setfam_1(k1_enumset1(X4,X4,X5)),k1_setfam_1(k1_enumset1(X6,X6,X6)))
      | k1_xboole_0 = k1_enumset1(X4,X4,X5) ) ),
    inference(subsumption_resolution,[],[f57,f50])).

fof(f57,plain,(
    ! [X6,X4,X5] :
      ( k1_setfam_1(k1_enumset1(X4,X5,X6)) = k3_xboole_0(k1_setfam_1(k1_enumset1(X4,X4,X5)),k1_setfam_1(k1_enumset1(X6,X6,X6)))
      | k1_xboole_0 = k1_enumset1(X6,X6,X6)
      | k1_xboole_0 = k1_enumset1(X4,X4,X5) ) ),
    inference(superposition,[],[f41,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2))) ),
    inference(definition_unfolding,[],[f28,f32,f24,f33])).

fof(f28,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) = k1_setfam_1(k3_tarski(k1_enumset1(X0,X0,X1)))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f26,f32])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( k1_setfam_1(k2_xboole_0(X0,X1)) != k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_setfam_1)).

fof(f37,plain,(
    k3_xboole_0(sK0,sK1) != k1_setfam_1(k1_enumset1(sK0,sK0,sK1)) ),
    inference(definition_unfolding,[],[f19,f24])).

fof(f19,plain,(
    k1_setfam_1(k2_tarski(sK0,sK1)) != k3_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    k1_setfam_1(k2_tarski(sK0,sK1)) != k3_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f17])).

fof(f17,plain,
    ( ? [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) != k3_xboole_0(X0,X1)
   => k1_setfam_1(k2_tarski(sK0,sK1)) != k3_xboole_0(sK0,sK1) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) != k3_xboole_0(X0,X1) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:38:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.43  % (16239)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.43  % (16226)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.43  % (16239)Refutation found. Thanks to Tanya!
% 0.20/0.43  % SZS status Theorem for theBenchmark
% 0.20/0.43  % SZS output start Proof for theBenchmark
% 0.20/0.43  fof(f75,plain,(
% 0.20/0.43    $false),
% 0.20/0.43    inference(trivial_inequality_removal,[],[f72])).
% 0.20/0.43  fof(f72,plain,(
% 0.20/0.43    k3_xboole_0(sK0,sK1) != k3_xboole_0(sK0,sK1)),
% 0.20/0.43    inference(superposition,[],[f37,f61])).
% 0.20/0.43  fof(f61,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 0.20/0.43    inference(superposition,[],[f60,f39])).
% 0.20/0.43  fof(f39,plain,(
% 0.20/0.43    ( ! [X0] : (k1_setfam_1(k1_enumset1(X0,X0,X0)) = X0) )),
% 0.20/0.43    inference(definition_unfolding,[],[f21,f33])).
% 0.20/0.43  fof(f33,plain,(
% 0.20/0.43    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.20/0.43    inference(definition_unfolding,[],[f22,f24])).
% 0.20/0.43  fof(f24,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f6])).
% 0.20/0.43  fof(f6,axiom,(
% 0.20/0.43    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.43  fof(f22,plain,(
% 0.20/0.43    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f5])).
% 0.20/0.43  fof(f5,axiom,(
% 0.20/0.43    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.43  fof(f21,plain,(
% 0.20/0.43    ( ! [X0] : (k1_setfam_1(k1_tarski(X0)) = X0) )),
% 0.20/0.43    inference(cnf_transformation,[],[f12])).
% 0.20/0.43  fof(f12,axiom,(
% 0.20/0.43    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).
% 0.20/0.43  fof(f60,plain,(
% 0.20/0.43    ( ! [X6,X4,X5] : (k1_setfam_1(k1_enumset1(X4,X5,X6)) = k3_xboole_0(k1_setfam_1(k1_enumset1(X4,X4,X5)),X6)) )),
% 0.20/0.43    inference(forward_demodulation,[],[f59,f39])).
% 0.20/0.43  fof(f59,plain,(
% 0.20/0.43    ( ! [X6,X4,X5] : (k1_setfam_1(k1_enumset1(X4,X5,X6)) = k3_xboole_0(k1_setfam_1(k1_enumset1(X4,X4,X5)),k1_setfam_1(k1_enumset1(X6,X6,X6)))) )),
% 0.20/0.43    inference(subsumption_resolution,[],[f58,f50])).
% 0.20/0.43  fof(f50,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) != k1_xboole_0) )),
% 0.20/0.43    inference(superposition,[],[f40,f36])).
% 0.20/0.43  fof(f36,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X0,X1,X2)))) )),
% 0.20/0.43    inference(definition_unfolding,[],[f27,f34])).
% 0.20/0.43  fof(f34,plain,(
% 0.20/0.43    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X3)))) )),
% 0.20/0.43    inference(definition_unfolding,[],[f29,f32,f33])).
% 0.20/0.43  fof(f32,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 0.20/0.43    inference(definition_unfolding,[],[f25,f24])).
% 0.20/0.43  fof(f25,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f8])).
% 0.20/0.43  fof(f8,axiom,(
% 0.20/0.43    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.20/0.43  fof(f29,plain,(
% 0.20/0.43    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f3])).
% 0.20/0.43  fof(f3,axiom,(
% 0.20/0.43    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).
% 0.20/0.43  fof(f27,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f7])).
% 0.20/0.43  fof(f7,axiom,(
% 0.20/0.43    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.43  fof(f40,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k1_xboole_0 != k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),X1))) )),
% 0.20/0.43    inference(definition_unfolding,[],[f23,f32,f33])).
% 0.20/0.43  fof(f23,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0) )),
% 0.20/0.43    inference(cnf_transformation,[],[f10])).
% 0.20/0.43  fof(f10,axiom,(
% 0.20/0.43    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.20/0.43  fof(f58,plain,(
% 0.20/0.43    ( ! [X6,X4,X5] : (k1_setfam_1(k1_enumset1(X4,X5,X6)) = k3_xboole_0(k1_setfam_1(k1_enumset1(X4,X4,X5)),k1_setfam_1(k1_enumset1(X6,X6,X6))) | k1_xboole_0 = k1_enumset1(X4,X4,X5)) )),
% 0.20/0.43    inference(subsumption_resolution,[],[f57,f50])).
% 0.20/0.43  fof(f57,plain,(
% 0.20/0.43    ( ! [X6,X4,X5] : (k1_setfam_1(k1_enumset1(X4,X5,X6)) = k3_xboole_0(k1_setfam_1(k1_enumset1(X4,X4,X5)),k1_setfam_1(k1_enumset1(X6,X6,X6))) | k1_xboole_0 = k1_enumset1(X6,X6,X6) | k1_xboole_0 = k1_enumset1(X4,X4,X5)) )),
% 0.20/0.43    inference(superposition,[],[f41,f42])).
% 0.20/0.43  fof(f42,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2)))) )),
% 0.20/0.43    inference(definition_unfolding,[],[f28,f32,f24,f33])).
% 0.20/0.43  fof(f28,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f2])).
% 0.20/0.43  fof(f2,axiom,(
% 0.20/0.43    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).
% 0.20/0.43  fof(f41,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) = k1_setfam_1(k3_tarski(k1_enumset1(X0,X0,X1))) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.43    inference(definition_unfolding,[],[f26,f32])).
% 0.20/0.43  fof(f26,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.43    inference(cnf_transformation,[],[f16])).
% 0.20/0.43  fof(f16,plain,(
% 0.20/0.43    ! [X0,X1] : (k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.20/0.43    inference(ennf_transformation,[],[f11])).
% 0.20/0.43  fof(f11,axiom,(
% 0.20/0.43    ! [X0,X1] : ~(k1_setfam_1(k2_xboole_0(X0,X1)) != k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_setfam_1)).
% 0.20/0.43  fof(f37,plain,(
% 0.20/0.43    k3_xboole_0(sK0,sK1) != k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),
% 0.20/0.43    inference(definition_unfolding,[],[f19,f24])).
% 0.20/0.43  fof(f19,plain,(
% 0.20/0.43    k1_setfam_1(k2_tarski(sK0,sK1)) != k3_xboole_0(sK0,sK1)),
% 0.20/0.43    inference(cnf_transformation,[],[f18])).
% 0.20/0.43  fof(f18,plain,(
% 0.20/0.43    k1_setfam_1(k2_tarski(sK0,sK1)) != k3_xboole_0(sK0,sK1)),
% 0.20/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f17])).
% 0.20/0.43  fof(f17,plain,(
% 0.20/0.43    ? [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) != k3_xboole_0(X0,X1) => k1_setfam_1(k2_tarski(sK0,sK1)) != k3_xboole_0(sK0,sK1)),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f15,plain,(
% 0.20/0.43    ? [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) != k3_xboole_0(X0,X1)),
% 0.20/0.43    inference(ennf_transformation,[],[f14])).
% 0.20/0.43  fof(f14,negated_conjecture,(
% 0.20/0.43    ~! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.20/0.43    inference(negated_conjecture,[],[f13])).
% 0.20/0.43  fof(f13,conjecture,(
% 0.20/0.43    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.43  % SZS output end Proof for theBenchmark
% 0.20/0.43  % (16239)------------------------------
% 0.20/0.43  % (16239)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (16239)Termination reason: Refutation
% 0.20/0.43  
% 0.20/0.43  % (16239)Memory used [KB]: 6140
% 0.20/0.43  % (16239)Time elapsed: 0.006 s
% 0.20/0.43  % (16239)------------------------------
% 0.20/0.43  % (16239)------------------------------
% 0.20/0.43  % (16220)Success in time 0.076 s
%------------------------------------------------------------------------------
