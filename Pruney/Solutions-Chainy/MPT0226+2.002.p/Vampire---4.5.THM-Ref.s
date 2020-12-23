%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:36:13 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.30s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 145 expanded)
%              Number of leaves         :   11 (  51 expanded)
%              Depth                    :   14
%              Number of atoms          :   56 ( 178 expanded)
%              Number of equality atoms :   55 ( 177 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f285,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f284])).

fof(f284,plain,(
    sK0 != sK0 ),
    inference(superposition,[],[f28,f278])).

fof(f278,plain,(
    sK0 = sK1 ),
    inference(equality_resolution,[],[f97])).

fof(f97,plain,(
    ! [X4,X3] :
      ( k1_enumset1(sK0,sK0,sK1) != k1_enumset1(X3,X3,X4)
      | X3 = X4 ) ),
    inference(superposition,[],[f49,f93])).

fof(f93,plain,(
    k1_enumset1(sK1,sK1,sK1) = k1_enumset1(sK0,sK0,sK1) ),
    inference(backward_demodulation,[],[f65,f89])).

fof(f89,plain,(
    k1_enumset1(sK1,sK0,sK0) = k1_enumset1(sK0,sK0,sK1) ),
    inference(superposition,[],[f86,f36])).

fof(f36,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f86,plain,(
    k1_enumset1(sK0,sK0,sK1) = k5_xboole_0(k1_enumset1(sK1,sK0,sK0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f60,f65])).

fof(f60,plain,(
    k5_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_xboole_0) = k1_enumset1(sK0,sK0,sK1) ),
    inference(forward_demodulation,[],[f55,f54])).

fof(f54,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f42,f43,f43])).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f42,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f55,plain,(
    k1_enumset1(sK1,sK1,sK0) = k5_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_xboole_0) ),
    inference(superposition,[],[f47,f48])).

fof(f48,plain,(
    k1_xboole_0 = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f27,f30,f45,f45])).

fof(f45,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f35,f43])).

fof(f35,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f27,plain,(
    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( sK0 != sK1
    & k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f25])).

fof(f25,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) )
   => ( sK0 != sK1
      & k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_zfmisc_1)).

fof(f47,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X2,X2),k3_xboole_0(k1_enumset1(X2,X2,X2),k1_enumset1(X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f33,f44,f43,f45])).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f29,f30])).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f33,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

fof(f65,plain,(
    k1_enumset1(sK1,sK1,sK1) = k1_enumset1(sK1,sK0,sK0) ),
    inference(superposition,[],[f56,f36])).

fof(f56,plain,(
    k5_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_xboole_0) = k1_enumset1(sK1,sK0,sK0) ),
    inference(superposition,[],[f50,f48])).

fof(f50,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k1_enumset1(X1,X1,X2),k3_xboole_0(k1_enumset1(X1,X1,X2),k1_enumset1(X0,X0,X0)))) ),
    inference(definition_unfolding,[],[f34,f44,f45,f43])).

fof(f34,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k1_enumset1(X0,X0,X0) != k1_enumset1(X1,X1,X2)
      | X1 = X2 ) ),
    inference(definition_unfolding,[],[f32,f45,f43])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | k1_tarski(X0) != k2_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( X1 = X2
      | k1_tarski(X0) != k2_tarski(X1,X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k2_tarski(X1,X2)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_zfmisc_1)).

fof(f28,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:38:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.52  % (21021)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.54  % (21045)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.54  % (21041)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.54  % (21021)Refutation found. Thanks to Tanya!
% 0.20/0.54  % SZS status Theorem for theBenchmark
% 0.20/0.54  % (21030)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.30/0.54  % (21042)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.30/0.54  % (21037)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.30/0.55  % (21029)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.30/0.55  % SZS output start Proof for theBenchmark
% 1.30/0.55  fof(f285,plain,(
% 1.30/0.55    $false),
% 1.30/0.55    inference(trivial_inequality_removal,[],[f284])).
% 1.30/0.55  fof(f284,plain,(
% 1.30/0.55    sK0 != sK0),
% 1.30/0.55    inference(superposition,[],[f28,f278])).
% 1.30/0.55  fof(f278,plain,(
% 1.30/0.55    sK0 = sK1),
% 1.30/0.55    inference(equality_resolution,[],[f97])).
% 1.30/0.55  fof(f97,plain,(
% 1.30/0.55    ( ! [X4,X3] : (k1_enumset1(sK0,sK0,sK1) != k1_enumset1(X3,X3,X4) | X3 = X4) )),
% 1.30/0.55    inference(superposition,[],[f49,f93])).
% 1.30/0.55  fof(f93,plain,(
% 1.30/0.55    k1_enumset1(sK1,sK1,sK1) = k1_enumset1(sK0,sK0,sK1)),
% 1.30/0.55    inference(backward_demodulation,[],[f65,f89])).
% 1.30/0.55  fof(f89,plain,(
% 1.30/0.55    k1_enumset1(sK1,sK0,sK0) = k1_enumset1(sK0,sK0,sK1)),
% 1.30/0.55    inference(superposition,[],[f86,f36])).
% 1.30/0.55  fof(f36,plain,(
% 1.30/0.55    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.30/0.55    inference(cnf_transformation,[],[f5])).
% 1.30/0.55  fof(f5,axiom,(
% 1.30/0.55    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.30/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 1.30/0.55  fof(f86,plain,(
% 1.30/0.55    k1_enumset1(sK0,sK0,sK1) = k5_xboole_0(k1_enumset1(sK1,sK0,sK0),k1_xboole_0)),
% 1.30/0.55    inference(forward_demodulation,[],[f60,f65])).
% 1.30/0.55  fof(f60,plain,(
% 1.30/0.55    k5_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_xboole_0) = k1_enumset1(sK0,sK0,sK1)),
% 1.30/0.55    inference(forward_demodulation,[],[f55,f54])).
% 1.30/0.55  fof(f54,plain,(
% 1.30/0.55    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 1.30/0.55    inference(definition_unfolding,[],[f42,f43,f43])).
% 1.30/0.55  fof(f43,plain,(
% 1.30/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.30/0.55    inference(cnf_transformation,[],[f16])).
% 1.30/0.55  fof(f16,axiom,(
% 1.30/0.55    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.30/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.30/0.55  fof(f42,plain,(
% 1.30/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.30/0.55    inference(cnf_transformation,[],[f8])).
% 1.30/0.55  fof(f8,axiom,(
% 1.30/0.55    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.30/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.30/0.55  fof(f55,plain,(
% 1.30/0.55    k1_enumset1(sK1,sK1,sK0) = k5_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_xboole_0)),
% 1.30/0.55    inference(superposition,[],[f47,f48])).
% 1.30/0.55  fof(f48,plain,(
% 1.30/0.55    k1_xboole_0 = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1)))),
% 1.30/0.55    inference(definition_unfolding,[],[f27,f30,f45,f45])).
% 1.30/0.55  fof(f45,plain,(
% 1.30/0.55    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 1.30/0.55    inference(definition_unfolding,[],[f35,f43])).
% 1.30/0.55  fof(f35,plain,(
% 1.30/0.55    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.30/0.55    inference(cnf_transformation,[],[f15])).
% 1.30/0.55  fof(f15,axiom,(
% 1.30/0.55    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.30/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.30/0.55  fof(f30,plain,(
% 1.30/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.30/0.55    inference(cnf_transformation,[],[f2])).
% 1.30/0.55  fof(f2,axiom,(
% 1.30/0.55    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.30/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.30/0.55  fof(f27,plain,(
% 1.30/0.55    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 1.30/0.55    inference(cnf_transformation,[],[f26])).
% 1.30/0.55  fof(f26,plain,(
% 1.30/0.55    sK0 != sK1 & k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 1.30/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f25])).
% 1.30/0.55  fof(f25,plain,(
% 1.30/0.55    ? [X0,X1] : (X0 != X1 & k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) => (sK0 != sK1 & k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),
% 1.30/0.55    introduced(choice_axiom,[])).
% 1.30/0.55  fof(f23,plain,(
% 1.30/0.55    ? [X0,X1] : (X0 != X1 & k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 1.30/0.55    inference(ennf_transformation,[],[f22])).
% 1.30/0.55  fof(f22,negated_conjecture,(
% 1.30/0.55    ~! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.30/0.55    inference(negated_conjecture,[],[f21])).
% 1.30/0.55  fof(f21,conjecture,(
% 1.30/0.55    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.30/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_zfmisc_1)).
% 1.30/0.55  fof(f47,plain,(
% 1.30/0.55    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X2,X2),k3_xboole_0(k1_enumset1(X2,X2,X2),k1_enumset1(X0,X0,X1))))) )),
% 1.30/0.55    inference(definition_unfolding,[],[f33,f44,f43,f45])).
% 1.30/0.55  fof(f44,plain,(
% 1.30/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 1.30/0.55    inference(definition_unfolding,[],[f29,f30])).
% 1.30/0.55  fof(f29,plain,(
% 1.30/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.30/0.55    inference(cnf_transformation,[],[f7])).
% 1.30/0.55  fof(f7,axiom,(
% 1.30/0.55    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.30/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.30/0.55  fof(f33,plain,(
% 1.30/0.55    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 1.30/0.55    inference(cnf_transformation,[],[f12])).
% 1.30/0.55  fof(f12,axiom,(
% 1.30/0.55    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))),
% 1.30/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).
% 1.30/0.55  fof(f65,plain,(
% 1.30/0.55    k1_enumset1(sK1,sK1,sK1) = k1_enumset1(sK1,sK0,sK0)),
% 1.30/0.55    inference(superposition,[],[f56,f36])).
% 1.30/0.55  fof(f56,plain,(
% 1.30/0.55    k5_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_xboole_0) = k1_enumset1(sK1,sK0,sK0)),
% 1.30/0.55    inference(superposition,[],[f50,f48])).
% 1.30/0.55  fof(f50,plain,(
% 1.30/0.55    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k1_enumset1(X1,X1,X2),k3_xboole_0(k1_enumset1(X1,X1,X2),k1_enumset1(X0,X0,X0))))) )),
% 1.30/0.55    inference(definition_unfolding,[],[f34,f44,f45,f43])).
% 1.30/0.55  fof(f34,plain,(
% 1.30/0.55    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 1.30/0.55    inference(cnf_transformation,[],[f11])).
% 1.30/0.55  fof(f11,axiom,(
% 1.30/0.55    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 1.30/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).
% 1.30/0.55  fof(f49,plain,(
% 1.30/0.55    ( ! [X2,X0,X1] : (k1_enumset1(X0,X0,X0) != k1_enumset1(X1,X1,X2) | X1 = X2) )),
% 1.30/0.55    inference(definition_unfolding,[],[f32,f45,f43])).
% 1.30/0.55  fof(f32,plain,(
% 1.30/0.55    ( ! [X2,X0,X1] : (X1 = X2 | k1_tarski(X0) != k2_tarski(X1,X2)) )),
% 1.30/0.55    inference(cnf_transformation,[],[f24])).
% 1.30/0.55  fof(f24,plain,(
% 1.30/0.55    ! [X0,X1,X2] : (X1 = X2 | k1_tarski(X0) != k2_tarski(X1,X2))),
% 1.30/0.55    inference(ennf_transformation,[],[f20])).
% 1.30/0.55  fof(f20,axiom,(
% 1.30/0.55    ! [X0,X1,X2] : (k1_tarski(X0) = k2_tarski(X1,X2) => X1 = X2)),
% 1.30/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_zfmisc_1)).
% 1.30/0.55  fof(f28,plain,(
% 1.30/0.55    sK0 != sK1),
% 1.30/0.55    inference(cnf_transformation,[],[f26])).
% 1.30/0.55  % SZS output end Proof for theBenchmark
% 1.30/0.55  % (21021)------------------------------
% 1.30/0.55  % (21021)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.55  % (21021)Termination reason: Refutation
% 1.30/0.55  
% 1.30/0.55  % (21021)Memory used [KB]: 1791
% 1.30/0.55  % (21021)Time elapsed: 0.115 s
% 1.30/0.55  % (21021)------------------------------
% 1.30/0.55  % (21021)------------------------------
% 1.30/0.55  % (21031)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.30/0.55  % (21019)Success in time 0.193 s
%------------------------------------------------------------------------------
