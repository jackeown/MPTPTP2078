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
% DateTime   : Thu Dec  3 12:40:47 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   31 (  62 expanded)
%              Number of leaves         :    7 (  19 expanded)
%              Depth                    :   12
%              Number of atoms          :   62 ( 132 expanded)
%              Number of equality atoms :   61 ( 131 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f37,plain,(
    $false ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X0] : k2_tarski(X0,X0) != k2_tarski(sK1,sK1) ),
    inference(subsumption_resolution,[],[f35,f14])).

fof(f14,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( sK0 != k1_tarski(sK1)
    & k1_xboole_0 != sK0
    & k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f11])).

fof(f11,plain,
    ( ? [X0,X1] :
        ( k1_tarski(X1) != X0
        & k1_xboole_0 != X0
        & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) )
   => ( sK0 != k1_tarski(sK1)
      & k1_xboole_0 != sK0
      & k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] :
      ( k1_tarski(X1) != X0
      & k1_xboole_0 != X0
      & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0
          & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ~ ( k1_tarski(X1) != X0
        & k1_xboole_0 != X0
        & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_zfmisc_1)).

fof(f35,plain,(
    ! [X0] :
      ( k2_tarski(X0,X0) != k2_tarski(sK1,sK1)
      | k1_xboole_0 = sK0 ) ),
    inference(subsumption_resolution,[],[f34,f22])).

fof(f22,plain,(
    sK0 != k2_tarski(sK1,sK1) ),
    inference(definition_unfolding,[],[f15,f17])).

fof(f17,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f15,plain,(
    sK0 != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f34,plain,(
    ! [X0] :
      ( k2_tarski(X0,X0) != k2_tarski(sK1,sK1)
      | sK0 = k2_tarski(sK1,sK1)
      | k1_xboole_0 = sK0 ) ),
    inference(subsumption_resolution,[],[f31,f30])).

fof(f30,plain,(
    k1_xboole_0 != k2_tarski(sK1,sK1) ),
    inference(superposition,[],[f24,f27])).

fof(f27,plain,(
    k2_tarski(sK1,sK1) = k2_xboole_0(k2_tarski(sK1,sK1),sK0) ),
    inference(forward_demodulation,[],[f26,f16])).

fof(f16,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f26,plain,(
    k2_xboole_0(k2_tarski(sK1,sK1),sK0) = k2_xboole_0(k2_tarski(sK1,sK1),k1_xboole_0) ),
    inference(superposition,[],[f20,f23])).

fof(f23,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK1)) ),
    inference(definition_unfolding,[],[f13,f17])).

fof(f13,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f24,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X0),X1) ),
    inference(definition_unfolding,[],[f18,f17])).

fof(f18,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f31,plain,(
    ! [X0] :
      ( k2_tarski(X0,X0) != k2_tarski(sK1,sK1)
      | k1_xboole_0 = k2_tarski(sK1,sK1)
      | sK0 = k2_tarski(sK1,sK1)
      | k1_xboole_0 = sK0 ) ),
    inference(superposition,[],[f25,f27])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X0) != k2_xboole_0(X1,X2)
      | k1_xboole_0 = X1
      | X1 = X2
      | k1_xboole_0 = X2 ) ),
    inference(definition_unfolding,[],[f21,f17])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | X1 = X2
      | k1_tarski(X0) != k2_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | X1 = X2
      | k1_tarski(X0) != k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n012.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:07:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.51  % (30449)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.51  % (30441)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.51  % (30449)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(equality_resolution,[],[f36])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    ( ! [X0] : (k2_tarski(X0,X0) != k2_tarski(sK1,sK1)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f35,f14])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    k1_xboole_0 != sK0),
% 0.20/0.51    inference(cnf_transformation,[],[f12])).
% 0.20/0.51  fof(f12,plain,(
% 0.20/0.51    sK0 != k1_tarski(sK1) & k1_xboole_0 != sK0 & k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f11])).
% 0.20/0.51  fof(f11,plain,(
% 0.20/0.51    ? [X0,X1] : (k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1))) => (sK0 != k1_tarski(sK1) & k1_xboole_0 != sK0 & k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f9,plain,(
% 0.20/0.51    ? [X0,X1] : (k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 0.20/0.51    inference(ennf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,negated_conjecture,(
% 0.20/0.51    ~! [X0,X1] : ~(k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 0.20/0.51    inference(negated_conjecture,[],[f7])).
% 0.20/0.51  fof(f7,conjecture,(
% 0.20/0.51    ! [X0,X1] : ~(k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_zfmisc_1)).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    ( ! [X0] : (k2_tarski(X0,X0) != k2_tarski(sK1,sK1) | k1_xboole_0 = sK0) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f34,f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    sK0 != k2_tarski(sK1,sK1)),
% 0.20/0.51    inference(definition_unfolding,[],[f15,f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    sK0 != k1_tarski(sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f12])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ( ! [X0] : (k2_tarski(X0,X0) != k2_tarski(sK1,sK1) | sK0 = k2_tarski(sK1,sK1) | k1_xboole_0 = sK0) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f31,f30])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    k1_xboole_0 != k2_tarski(sK1,sK1)),
% 0.20/0.51    inference(superposition,[],[f24,f27])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    k2_tarski(sK1,sK1) = k2_xboole_0(k2_tarski(sK1,sK1),sK0)),
% 0.20/0.51    inference(forward_demodulation,[],[f26,f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    k2_xboole_0(k2_tarski(sK1,sK1),sK0) = k2_xboole_0(k2_tarski(sK1,sK1),k1_xboole_0)),
% 0.20/0.51    inference(superposition,[],[f20,f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK1))),
% 0.20/0.51    inference(definition_unfolding,[],[f13,f17])).
% 0.20/0.51  fof(f13,plain,(
% 0.20/0.51    k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 0.20/0.51    inference(cnf_transformation,[],[f12])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X0),X1)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f18,f17])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ( ! [X0] : (k2_tarski(X0,X0) != k2_tarski(sK1,sK1) | k1_xboole_0 = k2_tarski(sK1,sK1) | sK0 = k2_tarski(sK1,sK1) | k1_xboole_0 = sK0) )),
% 0.20/0.51    inference(superposition,[],[f25,f27])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k2_tarski(X0,X0) != k2_xboole_0(X1,X2) | k1_xboole_0 = X1 | X1 = X2 | k1_xboole_0 = X2) )),
% 0.20/0.51    inference(definition_unfolding,[],[f21,f17])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | k1_xboole_0 = X1 | X1 = X2 | k1_tarski(X0) != k2_xboole_0(X1,X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (k1_xboole_0 = X2 | k1_xboole_0 = X1 | X1 = X2 | k1_tarski(X0) != k2_xboole_0(X1,X2))),
% 0.20/0.51    inference(ennf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (30449)------------------------------
% 0.20/0.51  % (30449)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (30449)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (30449)Memory used [KB]: 10618
% 0.20/0.51  % (30449)Time elapsed: 0.098 s
% 0.20/0.51  % (30449)------------------------------
% 0.20/0.51  % (30449)------------------------------
% 0.20/0.51  % (30446)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (30439)Success in time 0.153 s
%------------------------------------------------------------------------------
