%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:36:13 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   27 (  51 expanded)
%              Number of leaves         :    5 (  12 expanded)
%              Depth                    :   13
%              Number of atoms          :   62 ( 134 expanded)
%              Number of equality atoms :   45 ( 105 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f29,plain,(
    $false ),
    inference(subsumption_resolution,[],[f28,f20])).

fof(f20,plain,(
    ! [X1] : ~ r1_xboole_0(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( X0 = X1
        & r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_zfmisc_1)).

fof(f28,plain,(
    r1_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) ),
    inference(trivial_inequality_removal,[],[f27])).

fof(f27,plain,
    ( k1_tarski(sK0) != k1_tarski(sK0)
    | r1_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) ),
    inference(superposition,[],[f17,f26])).

fof(f26,plain,(
    k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) ),
    inference(subsumption_resolution,[],[f24,f23])).

fof(f23,plain,(
    sK0 = sK1 ),
    inference(subsumption_resolution,[],[f22,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).

fof(f22,plain,
    ( sK0 = sK1
    | ~ r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(trivial_inequality_removal,[],[f21])).

fof(f21,plain,
    ( k1_tarski(sK0) != k1_tarski(sK0)
    | sK0 = sK1
    | ~ r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(superposition,[],[f15,f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f15,plain,
    ( k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | sK0 = sK1 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( ( sK0 = sK1
      | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) )
    & ( sK0 != sK1
      | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f11])).

fof(f11,plain,
    ( ? [X0,X1] :
        ( ( X0 = X1
          | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) )
        & ( X0 != X1
          | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) )
   => ( ( sK0 = sK1
        | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) )
      & ( sK0 != sK1
        | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ( X0 = X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) )
      & ( X0 != X1
        | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <~> X0 != X1 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
      <=> X0 != X1 ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f24,plain,
    ( k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0))
    | sK0 != sK1 ),
    inference(backward_demodulation,[],[f14,f23])).

fof(f14,plain,
    ( sK0 != sK1
    | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n005.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:59:17 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (17273)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.51  % (17265)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.51  % (17273)Refutation not found, incomplete strategy% (17273)------------------------------
% 0.22/0.51  % (17273)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (17273)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (17273)Memory used [KB]: 10618
% 0.22/0.51  % (17273)Time elapsed: 0.094 s
% 0.22/0.51  % (17273)------------------------------
% 0.22/0.51  % (17273)------------------------------
% 0.22/0.51  % (17265)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(subsumption_resolution,[],[f28,f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ( ! [X1] : (~r1_xboole_0(k1_tarski(X1),k1_tarski(X1))) )),
% 0.22/0.51    inference(equality_resolution,[],[f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ( ! [X0,X1] : (X0 != X1 | ~r1_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,plain,(
% 0.22/0.51    ! [X0,X1] : (X0 != X1 | ~r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.22/0.51    inference(ennf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0,X1] : ~(X0 = X1 & r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_zfmisc_1)).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    r1_xboole_0(k1_tarski(sK0),k1_tarski(sK0))),
% 0.22/0.51    inference(trivial_inequality_removal,[],[f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    k1_tarski(sK0) != k1_tarski(sK0) | r1_xboole_0(k1_tarski(sK0),k1_tarski(sK0))),
% 0.22/0.51    inference(superposition,[],[f17,f26])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0))),
% 0.22/0.51    inference(subsumption_resolution,[],[f24,f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    sK0 = sK1),
% 0.22/0.51    inference(subsumption_resolution,[],[f22,f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 0.22/0.51    inference(cnf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,plain,(
% 0.22/0.51    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1)),
% 0.22/0.51    inference(ennf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0,X1] : (X0 != X1 => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    sK0 = sK1 | ~r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 0.22/0.51    inference(trivial_inequality_removal,[],[f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    k1_tarski(sK0) != k1_tarski(sK0) | sK0 = sK1 | ~r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 0.22/0.51    inference(superposition,[],[f15,f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f13])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.22/0.51    inference(nnf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) | sK0 = sK1),
% 0.22/0.51    inference(cnf_transformation,[],[f12])).
% 0.22/0.51  fof(f12,plain,(
% 0.22/0.51    (sK0 = sK1 | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) & (sK0 != sK1 | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f11])).
% 0.22/0.51  fof(f11,plain,(
% 0.22/0.51    ? [X0,X1] : ((X0 = X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) & (X0 != X1 | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))) => ((sK0 = sK1 | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) & (sK0 != sK1 | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f10,plain,(
% 0.22/0.51    ? [X0,X1] : ((X0 = X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) & (X0 != X1 | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 0.22/0.51    inference(nnf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,plain,(
% 0.22/0.51    ? [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <~> X0 != X1)),
% 0.22/0.51    inference(ennf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,negated_conjecture,(
% 0.22/0.51    ~! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.22/0.51    inference(negated_conjecture,[],[f5])).
% 0.22/0.51  fof(f5,conjecture,(
% 0.22/0.51    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) | sK0 != sK1),
% 0.22/0.51    inference(backward_demodulation,[],[f14,f23])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    sK0 != sK1 | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 0.22/0.51    inference(cnf_transformation,[],[f12])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f13])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (17265)------------------------------
% 0.22/0.51  % (17265)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (17265)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (17265)Memory used [KB]: 1663
% 0.22/0.51  % (17265)Time elapsed: 0.096 s
% 0.22/0.51  % (17265)------------------------------
% 0.22/0.51  % (17265)------------------------------
% 0.22/0.51  % (17264)Success in time 0.147 s
%------------------------------------------------------------------------------
