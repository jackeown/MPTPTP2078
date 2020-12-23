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
fof(f71,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f68])).

fof(f68,plain,(
    k3_xboole_0(sK0,sK1) != k3_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f39,f57])).

fof(f57,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(superposition,[],[f56,f40])).

fof(f40,plain,(
    ! [X0] : k1_setfam_1(k1_enumset1(X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f21,f35])).

fof(f35,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f22,f24])).

fof(f24,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f22,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f21,plain,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

fof(f56,plain,(
    ! [X4,X5,X3] : k1_setfam_1(k1_enumset1(X3,X4,X5)) = k3_xboole_0(k1_setfam_1(k1_enumset1(X3,X3,X4)),X5) ),
    inference(forward_demodulation,[],[f55,f40])).

fof(f55,plain,(
    ! [X4,X5,X3] : k1_setfam_1(k1_enumset1(X3,X4,X5)) = k3_xboole_0(k1_setfam_1(k1_enumset1(X3,X3,X4)),k1_setfam_1(k1_enumset1(X5,X5,X5))) ),
    inference(subsumption_resolution,[],[f54,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) != k1_xboole_0 ),
    inference(superposition,[],[f41,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X0,X1,X2))) ),
    inference(definition_unfolding,[],[f27,f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X3))) ),
    inference(definition_unfolding,[],[f29,f34,f35])).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f25,f24])).

fof(f25,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f29,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

fof(f27,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f41,plain,(
    ! [X0,X1] : k1_xboole_0 != k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),X1)) ),
    inference(definition_unfolding,[],[f23,f34,f35])).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f54,plain,(
    ! [X4,X5,X3] :
      ( k1_setfam_1(k1_enumset1(X3,X4,X5)) = k3_xboole_0(k1_setfam_1(k1_enumset1(X3,X3,X4)),k1_setfam_1(k1_enumset1(X5,X5,X5)))
      | k1_xboole_0 = k1_enumset1(X3,X3,X4) ) ),
    inference(subsumption_resolution,[],[f53,f46])).

fof(f53,plain,(
    ! [X4,X5,X3] :
      ( k1_setfam_1(k1_enumset1(X3,X4,X5)) = k3_xboole_0(k1_setfam_1(k1_enumset1(X3,X3,X4)),k1_setfam_1(k1_enumset1(X5,X5,X5)))
      | k1_xboole_0 = k1_enumset1(X5,X5,X5)
      | k1_xboole_0 = k1_enumset1(X3,X3,X4) ) ),
    inference(superposition,[],[f42,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2))) ),
    inference(definition_unfolding,[],[f28,f34,f24,f35])).

fof(f28,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) = k1_setfam_1(k3_tarski(k1_enumset1(X0,X0,X1)))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f26,f34])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ~ ( k1_setfam_1(k2_xboole_0(X0,X1)) != k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_setfam_1)).

fof(f39,plain,(
    k3_xboole_0(sK0,sK1) != k1_setfam_1(k1_enumset1(sK0,sK0,sK1)) ),
    inference(definition_unfolding,[],[f20,f24])).

fof(f20,plain,(
    k1_setfam_1(k2_tarski(sK0,sK1)) != k3_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    k1_setfam_1(k2_tarski(sK0,sK1)) != k3_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f18])).

fof(f18,plain,
    ( ? [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) != k3_xboole_0(X0,X1)
   => k1_setfam_1(k2_tarski(sK0,sK1)) != k3_xboole_0(sK0,sK1) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) != k3_xboole_0(X0,X1) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:47:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.44  % (7567)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.45  % (7575)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.45  % (7575)Refutation found. Thanks to Tanya!
% 0.20/0.45  % SZS status Theorem for theBenchmark
% 0.20/0.45  % SZS output start Proof for theBenchmark
% 0.20/0.45  fof(f71,plain,(
% 0.20/0.45    $false),
% 0.20/0.45    inference(trivial_inequality_removal,[],[f68])).
% 0.20/0.45  fof(f68,plain,(
% 0.20/0.45    k3_xboole_0(sK0,sK1) != k3_xboole_0(sK0,sK1)),
% 0.20/0.45    inference(superposition,[],[f39,f57])).
% 0.20/0.45  fof(f57,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 0.20/0.45    inference(superposition,[],[f56,f40])).
% 0.20/0.45  fof(f40,plain,(
% 0.20/0.45    ( ! [X0] : (k1_setfam_1(k1_enumset1(X0,X0,X0)) = X0) )),
% 0.20/0.45    inference(definition_unfolding,[],[f21,f35])).
% 0.20/0.45  fof(f35,plain,(
% 0.20/0.45    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.20/0.45    inference(definition_unfolding,[],[f22,f24])).
% 0.20/0.45  fof(f24,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f6])).
% 0.20/0.45  fof(f6,axiom,(
% 0.20/0.45    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.45  fof(f22,plain,(
% 0.20/0.45    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f5])).
% 0.20/0.45  fof(f5,axiom,(
% 0.20/0.45    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.45  fof(f21,plain,(
% 0.20/0.45    ( ! [X0] : (k1_setfam_1(k1_tarski(X0)) = X0) )),
% 0.20/0.45    inference(cnf_transformation,[],[f13])).
% 0.20/0.45  fof(f13,axiom,(
% 0.20/0.45    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).
% 0.20/0.45  fof(f56,plain,(
% 0.20/0.45    ( ! [X4,X5,X3] : (k1_setfam_1(k1_enumset1(X3,X4,X5)) = k3_xboole_0(k1_setfam_1(k1_enumset1(X3,X3,X4)),X5)) )),
% 0.20/0.45    inference(forward_demodulation,[],[f55,f40])).
% 0.20/0.45  fof(f55,plain,(
% 0.20/0.45    ( ! [X4,X5,X3] : (k1_setfam_1(k1_enumset1(X3,X4,X5)) = k3_xboole_0(k1_setfam_1(k1_enumset1(X3,X3,X4)),k1_setfam_1(k1_enumset1(X5,X5,X5)))) )),
% 0.20/0.45    inference(subsumption_resolution,[],[f54,f46])).
% 0.20/0.45  fof(f46,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) != k1_xboole_0) )),
% 0.20/0.45    inference(superposition,[],[f41,f38])).
% 0.20/0.45  fof(f38,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X0,X1,X2)))) )),
% 0.20/0.45    inference(definition_unfolding,[],[f27,f36])).
% 0.20/0.45  fof(f36,plain,(
% 0.20/0.45    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X3)))) )),
% 0.20/0.45    inference(definition_unfolding,[],[f29,f34,f35])).
% 0.20/0.45  fof(f34,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 0.20/0.45    inference(definition_unfolding,[],[f25,f24])).
% 0.20/0.45  fof(f25,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f10])).
% 0.20/0.45  fof(f10,axiom,(
% 0.20/0.45    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.20/0.45  fof(f29,plain,(
% 0.20/0.45    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f3])).
% 0.20/0.45  fof(f3,axiom,(
% 0.20/0.45    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).
% 0.20/0.45  fof(f27,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f7])).
% 0.20/0.45  fof(f7,axiom,(
% 0.20/0.45    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.45  fof(f41,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k1_xboole_0 != k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),X1))) )),
% 0.20/0.45    inference(definition_unfolding,[],[f23,f34,f35])).
% 0.20/0.45  fof(f23,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0) )),
% 0.20/0.45    inference(cnf_transformation,[],[f11])).
% 0.20/0.45  fof(f11,axiom,(
% 0.20/0.45    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.20/0.45  fof(f54,plain,(
% 0.20/0.45    ( ! [X4,X5,X3] : (k1_setfam_1(k1_enumset1(X3,X4,X5)) = k3_xboole_0(k1_setfam_1(k1_enumset1(X3,X3,X4)),k1_setfam_1(k1_enumset1(X5,X5,X5))) | k1_xboole_0 = k1_enumset1(X3,X3,X4)) )),
% 0.20/0.45    inference(subsumption_resolution,[],[f53,f46])).
% 0.20/0.45  fof(f53,plain,(
% 0.20/0.45    ( ! [X4,X5,X3] : (k1_setfam_1(k1_enumset1(X3,X4,X5)) = k3_xboole_0(k1_setfam_1(k1_enumset1(X3,X3,X4)),k1_setfam_1(k1_enumset1(X5,X5,X5))) | k1_xboole_0 = k1_enumset1(X5,X5,X5) | k1_xboole_0 = k1_enumset1(X3,X3,X4)) )),
% 0.20/0.45    inference(superposition,[],[f42,f43])).
% 0.20/0.45  fof(f43,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2)))) )),
% 0.20/0.45    inference(definition_unfolding,[],[f28,f34,f24,f35])).
% 0.20/0.45  fof(f28,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f2])).
% 0.20/0.45  fof(f2,axiom,(
% 0.20/0.45    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).
% 0.20/0.45  fof(f42,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) = k1_setfam_1(k3_tarski(k1_enumset1(X0,X0,X1))) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.45    inference(definition_unfolding,[],[f26,f34])).
% 0.20/0.45  fof(f26,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.45    inference(cnf_transformation,[],[f17])).
% 0.20/0.45  fof(f17,plain,(
% 0.20/0.45    ! [X0,X1] : (k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.20/0.45    inference(ennf_transformation,[],[f12])).
% 0.20/0.45  fof(f12,axiom,(
% 0.20/0.45    ! [X0,X1] : ~(k1_setfam_1(k2_xboole_0(X0,X1)) != k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_setfam_1)).
% 0.20/0.45  fof(f39,plain,(
% 0.20/0.45    k3_xboole_0(sK0,sK1) != k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),
% 0.20/0.45    inference(definition_unfolding,[],[f20,f24])).
% 0.20/0.45  fof(f20,plain,(
% 0.20/0.45    k1_setfam_1(k2_tarski(sK0,sK1)) != k3_xboole_0(sK0,sK1)),
% 0.20/0.45    inference(cnf_transformation,[],[f19])).
% 0.20/0.45  fof(f19,plain,(
% 0.20/0.45    k1_setfam_1(k2_tarski(sK0,sK1)) != k3_xboole_0(sK0,sK1)),
% 0.20/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f18])).
% 0.20/0.45  fof(f18,plain,(
% 0.20/0.45    ? [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) != k3_xboole_0(X0,X1) => k1_setfam_1(k2_tarski(sK0,sK1)) != k3_xboole_0(sK0,sK1)),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f16,plain,(
% 0.20/0.45    ? [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) != k3_xboole_0(X0,X1)),
% 0.20/0.45    inference(ennf_transformation,[],[f15])).
% 0.20/0.45  fof(f15,negated_conjecture,(
% 0.20/0.45    ~! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.20/0.45    inference(negated_conjecture,[],[f14])).
% 0.20/0.45  fof(f14,conjecture,(
% 0.20/0.45    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.45  % SZS output end Proof for theBenchmark
% 0.20/0.45  % (7575)------------------------------
% 0.20/0.45  % (7575)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (7575)Termination reason: Refutation
% 0.20/0.45  
% 0.20/0.45  % (7575)Memory used [KB]: 1663
% 0.20/0.45  % (7575)Time elapsed: 0.027 s
% 0.20/0.45  % (7575)------------------------------
% 0.20/0.45  % (7575)------------------------------
% 0.20/0.45  % (7558)Success in time 0.098 s
%------------------------------------------------------------------------------
