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
% DateTime   : Thu Dec  3 12:35:14 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   37 (  88 expanded)
%              Number of leaves         :    8 (  25 expanded)
%              Depth                    :   17
%              Number of atoms          :   49 ( 146 expanded)
%              Number of equality atoms :   48 ( 145 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f218,plain,(
    $false ),
    inference(subsumption_resolution,[],[f217,f55])).

fof(f55,plain,(
    sK0 != sK2 ),
    inference(backward_demodulation,[],[f26,f52])).

fof(f52,plain,(
    sK0 = sK1 ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( k1_tarski(X0) != k1_tarski(sK0)
      | sK1 = X0 ) ),
    inference(superposition,[],[f38,f25])).

fof(f25,plain,(
    k1_tarski(sK0) = k2_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( sK1 != sK2
    & k1_tarski(sK0) = k2_tarski(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f23])).

fof(f23,plain,
    ( ? [X0,X1,X2] :
        ( X1 != X2
        & k1_tarski(X0) = k2_tarski(X1,X2) )
   => ( sK1 != sK2
      & k1_tarski(sK0) = k2_tarski(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( X1 != X2
      & k1_tarski(X0) = k2_tarski(X1,X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k1_tarski(X0) = k2_tarski(X1,X2)
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k2_tarski(X1,X2)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_zfmisc_1)).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) != k2_tarski(X1,X2)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( X0 = X1
      | k1_tarski(X0) != k2_tarski(X1,X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k2_tarski(X1,X2)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_zfmisc_1)).

fof(f26,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f24])).

fof(f217,plain,(
    sK0 = sK2 ),
    inference(equality_resolution,[],[f121])).

fof(f121,plain,(
    ! [X4] :
      ( k1_tarski(sK0) != k1_tarski(X4)
      | sK2 = X4 ) ),
    inference(superposition,[],[f38,f108])).

fof(f108,plain,(
    k1_tarski(sK0) = k2_tarski(sK2,sK0) ),
    inference(forward_demodulation,[],[f102,f54])).

fof(f54,plain,(
    k1_tarski(sK0) = k2_tarski(sK0,sK2) ),
    inference(backward_demodulation,[],[f25,f52])).

fof(f102,plain,(
    k2_tarski(sK0,sK2) = k2_tarski(sK2,sK0) ),
    inference(superposition,[],[f92,f42])).

fof(f42,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X1,X0) ),
    inference(superposition,[],[f34,f30])).

fof(f30,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

% (23811)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% (23793)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
fof(f34,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_enumset1)).

fof(f92,plain,(
    ! [X0] : k1_enumset1(X0,sK0,sK2) = k2_tarski(sK0,X0) ),
    inference(forward_demodulation,[],[f91,f44])).

fof(f44,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X1,X0,X0) ),
    inference(superposition,[],[f34,f30])).

fof(f91,plain,(
    ! [X0] : k1_enumset1(X0,sK0,sK2) = k1_enumset1(X0,sK0,sK0) ),
    inference(forward_demodulation,[],[f87,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f87,plain,(
    ! [X0] : k1_enumset1(X0,sK0,sK2) = k2_enumset1(X0,X0,sK0,sK0) ),
    inference(superposition,[],[f86,f35])).

fof(f86,plain,(
    ! [X4,X3] : k2_enumset1(X3,X4,sK0,sK2) = k2_enumset1(X3,X4,sK0,sK0) ),
    inference(forward_demodulation,[],[f77,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] : k2_enumset1(X1,X2,X0,X0) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X0)) ),
    inference(superposition,[],[f39,f27])).

fof(f27,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f39,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

fof(f77,plain,(
    ! [X4,X3] : k2_enumset1(X3,X4,sK0,sK2) = k2_xboole_0(k2_tarski(X3,X4),k1_tarski(sK0)) ),
    inference(superposition,[],[f39,f54])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:49:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (23791)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.52  % (23798)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.53  % (23803)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.54  % (23798)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f218,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(subsumption_resolution,[],[f217,f55])).
% 0.21/0.55  fof(f55,plain,(
% 0.21/0.55    sK0 != sK2),
% 0.21/0.55    inference(backward_demodulation,[],[f26,f52])).
% 0.21/0.55  fof(f52,plain,(
% 0.21/0.55    sK0 = sK1),
% 0.21/0.55    inference(equality_resolution,[],[f50])).
% 0.21/0.55  fof(f50,plain,(
% 0.21/0.55    ( ! [X0] : (k1_tarski(X0) != k1_tarski(sK0) | sK1 = X0) )),
% 0.21/0.55    inference(superposition,[],[f38,f25])).
% 0.21/0.55  fof(f25,plain,(
% 0.21/0.55    k1_tarski(sK0) = k2_tarski(sK1,sK2)),
% 0.21/0.55    inference(cnf_transformation,[],[f24])).
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    sK1 != sK2 & k1_tarski(sK0) = k2_tarski(sK1,sK2)),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f23])).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    ? [X0,X1,X2] : (X1 != X2 & k1_tarski(X0) = k2_tarski(X1,X2)) => (sK1 != sK2 & k1_tarski(sK0) = k2_tarski(sK1,sK2))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f17,plain,(
% 0.21/0.55    ? [X0,X1,X2] : (X1 != X2 & k1_tarski(X0) = k2_tarski(X1,X2))),
% 0.21/0.55    inference(ennf_transformation,[],[f15])).
% 0.21/0.55  fof(f15,negated_conjecture,(
% 0.21/0.55    ~! [X0,X1,X2] : (k1_tarski(X0) = k2_tarski(X1,X2) => X1 = X2)),
% 0.21/0.55    inference(negated_conjecture,[],[f14])).
% 0.21/0.55  fof(f14,conjecture,(
% 0.21/0.55    ! [X0,X1,X2] : (k1_tarski(X0) = k2_tarski(X1,X2) => X1 = X2)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_zfmisc_1)).
% 0.21/0.55  fof(f38,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k1_tarski(X0) != k2_tarski(X1,X2) | X0 = X1) )),
% 0.21/0.55    inference(cnf_transformation,[],[f22])).
% 0.21/0.55  fof(f22,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (X0 = X1 | k1_tarski(X0) != k2_tarski(X1,X2))),
% 0.21/0.55    inference(ennf_transformation,[],[f13])).
% 0.21/0.55  fof(f13,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (k1_tarski(X0) = k2_tarski(X1,X2) => X0 = X1)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_zfmisc_1)).
% 0.21/0.55  fof(f26,plain,(
% 0.21/0.55    sK1 != sK2),
% 0.21/0.55    inference(cnf_transformation,[],[f24])).
% 0.21/0.55  fof(f217,plain,(
% 0.21/0.55    sK0 = sK2),
% 0.21/0.55    inference(equality_resolution,[],[f121])).
% 0.21/0.55  fof(f121,plain,(
% 0.21/0.55    ( ! [X4] : (k1_tarski(sK0) != k1_tarski(X4) | sK2 = X4) )),
% 0.21/0.55    inference(superposition,[],[f38,f108])).
% 0.21/0.55  fof(f108,plain,(
% 0.21/0.55    k1_tarski(sK0) = k2_tarski(sK2,sK0)),
% 0.21/0.55    inference(forward_demodulation,[],[f102,f54])).
% 0.21/0.55  fof(f54,plain,(
% 0.21/0.55    k1_tarski(sK0) = k2_tarski(sK0,sK2)),
% 0.21/0.55    inference(backward_demodulation,[],[f25,f52])).
% 0.21/0.55  fof(f102,plain,(
% 0.21/0.55    k2_tarski(sK0,sK2) = k2_tarski(sK2,sK0)),
% 0.21/0.55    inference(superposition,[],[f92,f42])).
% 0.21/0.55  fof(f42,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X1,X0)) )),
% 0.21/0.55    inference(superposition,[],[f34,f30])).
% 0.21/0.55  fof(f30,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f10])).
% 0.21/0.55  fof(f10,axiom,(
% 0.21/0.55    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.55  % (23811)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.56  % (23793)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.56  fof(f34,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f8])).
% 0.21/0.56  fof(f8,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_enumset1)).
% 0.21/0.56  fof(f92,plain,(
% 0.21/0.56    ( ! [X0] : (k1_enumset1(X0,sK0,sK2) = k2_tarski(sK0,X0)) )),
% 0.21/0.56    inference(forward_demodulation,[],[f91,f44])).
% 0.21/0.56  fof(f44,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X1,X0,X0)) )),
% 0.21/0.56    inference(superposition,[],[f34,f30])).
% 0.21/0.56  fof(f91,plain,(
% 0.21/0.56    ( ! [X0] : (k1_enumset1(X0,sK0,sK2) = k1_enumset1(X0,sK0,sK0)) )),
% 0.21/0.56    inference(forward_demodulation,[],[f87,f35])).
% 0.21/0.56  fof(f35,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f11])).
% 0.21/0.56  fof(f11,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.56  fof(f87,plain,(
% 0.21/0.56    ( ! [X0] : (k1_enumset1(X0,sK0,sK2) = k2_enumset1(X0,X0,sK0,sK0)) )),
% 0.21/0.56    inference(superposition,[],[f86,f35])).
% 0.21/0.56  fof(f86,plain,(
% 0.21/0.56    ( ! [X4,X3] : (k2_enumset1(X3,X4,sK0,sK2) = k2_enumset1(X3,X4,sK0,sK0)) )),
% 0.21/0.56    inference(forward_demodulation,[],[f77,f76])).
% 0.21/0.56  fof(f76,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (k2_enumset1(X1,X2,X0,X0) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X0))) )),
% 0.21/0.56    inference(superposition,[],[f39,f27])).
% 0.21/0.56  fof(f27,plain,(
% 0.21/0.56    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f9])).
% 0.21/0.56  fof(f9,axiom,(
% 0.21/0.56    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.56  fof(f39,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f7])).
% 0.21/0.56  fof(f7,axiom,(
% 0.21/0.56    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).
% 0.21/0.56  fof(f77,plain,(
% 0.21/0.56    ( ! [X4,X3] : (k2_enumset1(X3,X4,sK0,sK2) = k2_xboole_0(k2_tarski(X3,X4),k1_tarski(sK0))) )),
% 0.21/0.56    inference(superposition,[],[f39,f54])).
% 0.21/0.56  % SZS output end Proof for theBenchmark
% 0.21/0.56  % (23798)------------------------------
% 0.21/0.56  % (23798)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (23798)Termination reason: Refutation
% 0.21/0.56  
% 0.21/0.56  % (23798)Memory used [KB]: 1791
% 0.21/0.56  % (23798)Time elapsed: 0.111 s
% 0.21/0.56  % (23798)------------------------------
% 0.21/0.56  % (23798)------------------------------
% 0.21/0.57  % (23788)Success in time 0.198 s
%------------------------------------------------------------------------------
