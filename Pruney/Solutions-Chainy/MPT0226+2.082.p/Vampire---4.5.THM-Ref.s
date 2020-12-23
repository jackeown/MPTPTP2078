%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:36:24 EST 2020

% Result     : Theorem 1.27s
% Output     : Refutation 1.27s
% Verified   : 
% Statistics : Number of formulae       :   35 ( 102 expanded)
%              Number of leaves         :    9 (  35 expanded)
%              Depth                    :    9
%              Number of atoms          :   51 ( 129 expanded)
%              Number of equality atoms :   50 ( 128 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f37,plain,(
    $false ),
    inference(subsumption_resolution,[],[f36,f16])).

fof(f16,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( sK0 != sK1
    & k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f12])).

fof(f12,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) )
   => ( sK0 != sK1
      & k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_zfmisc_1)).

fof(f36,plain,(
    sK0 = sK1 ),
    inference(subsumption_resolution,[],[f34,f32])).

fof(f32,plain,(
    ! [X1] : k1_xboole_0 != k2_enumset1(X1,X1,X1,X1) ),
    inference(forward_demodulation,[],[f31,f17])).

fof(f17,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f31,plain,(
    ! [X1] : k2_enumset1(X1,X1,X1,X1) != k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1)) ),
    inference(forward_demodulation,[],[f30,f19])).

fof(f19,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f30,plain,(
    ! [X1] : k2_enumset1(X1,X1,X1,X1) != k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k3_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1))) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k2_enumset1(X0,X0,X0,X0) != k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))) ) ),
    inference(definition_unfolding,[],[f22,f26,f21,f26,f26])).

fof(f21,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f26,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f18,f25])).

fof(f25,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f20,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f20,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f18,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f22,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f34,plain,
    ( k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | sK0 = sK1 ),
    inference(superposition,[],[f28,f27])).

fof(f27,plain,(
    k1_xboole_0 = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f15,f21,f26,f26])).

fof(f15,plain,(
    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X0,X0,X0,X0) = k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)))
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f23,f26,f21,f26,f26])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:34:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.52  % (25246)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.52  % (25242)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (25267)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.52  % (25240)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.52  % (25247)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.52  % (25248)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (25251)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.27/0.53  % (25240)Refutation found. Thanks to Tanya!
% 1.27/0.53  % SZS status Theorem for theBenchmark
% 1.27/0.53  % SZS output start Proof for theBenchmark
% 1.27/0.53  fof(f37,plain,(
% 1.27/0.53    $false),
% 1.27/0.53    inference(subsumption_resolution,[],[f36,f16])).
% 1.27/0.53  fof(f16,plain,(
% 1.27/0.53    sK0 != sK1),
% 1.27/0.53    inference(cnf_transformation,[],[f13])).
% 1.27/0.53  fof(f13,plain,(
% 1.27/0.53    sK0 != sK1 & k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 1.27/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f12])).
% 1.27/0.53  fof(f12,plain,(
% 1.27/0.53    ? [X0,X1] : (X0 != X1 & k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) => (sK0 != sK1 & k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),
% 1.27/0.53    introduced(choice_axiom,[])).
% 1.27/0.53  fof(f11,plain,(
% 1.27/0.53    ? [X0,X1] : (X0 != X1 & k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 1.27/0.53    inference(ennf_transformation,[],[f9])).
% 1.27/0.53  fof(f9,negated_conjecture,(
% 1.27/0.53    ~! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.27/0.53    inference(negated_conjecture,[],[f8])).
% 1.27/0.53  fof(f8,conjecture,(
% 1.27/0.53    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.27/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_zfmisc_1)).
% 1.27/0.53  fof(f36,plain,(
% 1.27/0.53    sK0 = sK1),
% 1.27/0.53    inference(subsumption_resolution,[],[f34,f32])).
% 1.27/0.53  fof(f32,plain,(
% 1.27/0.53    ( ! [X1] : (k1_xboole_0 != k2_enumset1(X1,X1,X1,X1)) )),
% 1.27/0.53    inference(forward_demodulation,[],[f31,f17])).
% 1.27/0.53  fof(f17,plain,(
% 1.27/0.53    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 1.27/0.53    inference(cnf_transformation,[],[f3])).
% 1.27/0.53  fof(f3,axiom,(
% 1.27/0.53    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 1.27/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.27/0.53  fof(f31,plain,(
% 1.27/0.53    ( ! [X1] : (k2_enumset1(X1,X1,X1,X1) != k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1))) )),
% 1.27/0.53    inference(forward_demodulation,[],[f30,f19])).
% 1.27/0.53  fof(f19,plain,(
% 1.27/0.53    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.27/0.53    inference(cnf_transformation,[],[f10])).
% 1.27/0.53  fof(f10,plain,(
% 1.27/0.53    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.27/0.53    inference(rectify,[],[f1])).
% 1.27/0.53  fof(f1,axiom,(
% 1.27/0.53    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.27/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.27/0.53  fof(f30,plain,(
% 1.27/0.53    ( ! [X1] : (k2_enumset1(X1,X1,X1,X1) != k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k3_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1)))) )),
% 1.27/0.53    inference(equality_resolution,[],[f29])).
% 1.27/0.53  fof(f29,plain,(
% 1.27/0.53    ( ! [X0,X1] : (X0 != X1 | k2_enumset1(X0,X0,X0,X0) != k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)))) )),
% 1.27/0.53    inference(definition_unfolding,[],[f22,f26,f21,f26,f26])).
% 1.27/0.53  fof(f21,plain,(
% 1.27/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.27/0.53    inference(cnf_transformation,[],[f2])).
% 1.27/0.53  fof(f2,axiom,(
% 1.27/0.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.27/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.27/0.53  fof(f26,plain,(
% 1.27/0.53    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.27/0.53    inference(definition_unfolding,[],[f18,f25])).
% 1.27/0.53  fof(f25,plain,(
% 1.27/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.27/0.53    inference(definition_unfolding,[],[f20,f24])).
% 1.27/0.53  fof(f24,plain,(
% 1.27/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.27/0.53    inference(cnf_transformation,[],[f6])).
% 1.27/0.53  fof(f6,axiom,(
% 1.27/0.53    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.27/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.27/0.53  fof(f20,plain,(
% 1.27/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.27/0.53    inference(cnf_transformation,[],[f5])).
% 1.27/0.53  fof(f5,axiom,(
% 1.27/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.27/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.27/0.53  fof(f18,plain,(
% 1.27/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.27/0.53    inference(cnf_transformation,[],[f4])).
% 1.27/0.53  fof(f4,axiom,(
% 1.27/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.27/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.27/0.53  fof(f22,plain,(
% 1.27/0.53    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 1.27/0.53    inference(cnf_transformation,[],[f14])).
% 1.27/0.53  fof(f14,plain,(
% 1.27/0.53    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 1.27/0.53    inference(nnf_transformation,[],[f7])).
% 1.27/0.53  fof(f7,axiom,(
% 1.27/0.53    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 1.27/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 1.27/0.53  fof(f34,plain,(
% 1.27/0.53    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | sK0 = sK1),
% 1.27/0.53    inference(superposition,[],[f28,f27])).
% 1.27/0.53  fof(f27,plain,(
% 1.27/0.53    k1_xboole_0 = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)))),
% 1.27/0.53    inference(definition_unfolding,[],[f15,f21,f26,f26])).
% 1.27/0.53  fof(f15,plain,(
% 1.27/0.53    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 1.27/0.53    inference(cnf_transformation,[],[f13])).
% 1.27/0.53  fof(f28,plain,(
% 1.27/0.53    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X0) = k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))) | X0 = X1) )),
% 1.27/0.53    inference(definition_unfolding,[],[f23,f26,f21,f26,f26])).
% 1.27/0.53  fof(f23,plain,(
% 1.27/0.53    ( ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 1.27/0.53    inference(cnf_transformation,[],[f14])).
% 1.27/0.53  % SZS output end Proof for theBenchmark
% 1.27/0.53  % (25240)------------------------------
% 1.27/0.53  % (25240)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.53  % (25240)Termination reason: Refutation
% 1.27/0.53  
% 1.27/0.53  % (25240)Memory used [KB]: 10618
% 1.27/0.53  % (25240)Time elapsed: 0.113 s
% 1.27/0.53  % (25240)------------------------------
% 1.27/0.53  % (25240)------------------------------
% 1.27/0.53  % (25236)Success in time 0.17 s
%------------------------------------------------------------------------------
