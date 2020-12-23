%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:44 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   36 ( 112 expanded)
%              Number of leaves         :    6 (  31 expanded)
%              Depth                    :   15
%              Number of atoms          :  101 ( 346 expanded)
%              Number of equality atoms :   64 ( 236 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f53,plain,(
    $false ),
    inference(subsumption_resolution,[],[f52,f32])).

fof(f32,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,k2_tarski(X1,X1)) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X1))
      | k1_xboole_0 != X0 ) ),
    inference(definition_unfolding,[],[f19,f24])).

fof(f24,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f52,plain,(
    ~ r1_tarski(k1_xboole_0,k2_tarski(sK1,sK1)) ),
    inference(forward_demodulation,[],[f50,f49])).

fof(f49,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f48,f33])).

fof(f33,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(superposition,[],[f23,f21])).

fof(f21,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f23,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f48,plain,
    ( ~ r1_tarski(sK0,sK0)
    | k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f43])).

fof(f43,plain,
    ( ~ r1_tarski(sK0,sK0)
    | sK0 != sK0
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f25,f41])).

fof(f41,plain,
    ( sK0 = k2_tarski(sK1,sK1)
    | k1_xboole_0 = sK0 ),
    inference(duplicate_literal_removal,[],[f40])).

fof(f40,plain,
    ( k1_xboole_0 = sK0
    | sK0 = k2_tarski(sK1,sK1)
    | k1_xboole_0 = sK0
    | sK0 = k2_tarski(sK1,sK1) ),
    inference(resolution,[],[f30,f27])).

fof(f27,plain,
    ( r1_tarski(sK0,k2_tarski(sK1,sK1))
    | k1_xboole_0 = sK0
    | sK0 = k2_tarski(sK1,sK1) ),
    inference(definition_unfolding,[],[f15,f24,f24])).

fof(f15,plain,
    ( sK0 = k1_tarski(sK1)
    | k1_xboole_0 = sK0
    | r1_tarski(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( ( ( sK0 != k1_tarski(sK1)
        & k1_xboole_0 != sK0 )
      | ~ r1_tarski(sK0,k1_tarski(sK1)) )
    & ( sK0 = k1_tarski(sK1)
      | k1_xboole_0 = sK0
      | r1_tarski(sK0,k1_tarski(sK1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f11])).

fof(f11,plain,
    ( ? [X0,X1] :
        ( ( ( k1_tarski(X1) != X0
            & k1_xboole_0 != X0 )
          | ~ r1_tarski(X0,k1_tarski(X1)) )
        & ( k1_tarski(X1) = X0
          | k1_xboole_0 = X0
          | r1_tarski(X0,k1_tarski(X1)) ) )
   => ( ( ( sK0 != k1_tarski(sK1)
          & k1_xboole_0 != sK0 )
        | ~ r1_tarski(sK0,k1_tarski(sK1)) )
      & ( sK0 = k1_tarski(sK1)
        | k1_xboole_0 = sK0
        | r1_tarski(sK0,k1_tarski(sK1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ( ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 )
        | ~ r1_tarski(X0,k1_tarski(X1)) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ( ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 )
        | ~ r1_tarski(X0,k1_tarski(X1)) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <~> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,k1_tarski(X1))
      <=> ( k1_tarski(X1) = X0
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_zfmisc_1)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_tarski(X1,X1))
      | k1_xboole_0 = X0
      | k2_tarski(X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f18,f24,f24])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f25,plain,
    ( ~ r1_tarski(sK0,k2_tarski(sK1,sK1))
    | sK0 != k2_tarski(sK1,sK1) ),
    inference(definition_unfolding,[],[f17,f24,f24])).

fof(f17,plain,
    ( sK0 != k1_tarski(sK1)
    | ~ r1_tarski(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f50,plain,(
    ~ r1_tarski(sK0,k2_tarski(sK1,sK1)) ),
    inference(subsumption_resolution,[],[f26,f49])).

fof(f26,plain,
    ( ~ r1_tarski(sK0,k2_tarski(sK1,sK1))
    | k1_xboole_0 != sK0 ),
    inference(definition_unfolding,[],[f16,f24])).

fof(f16,plain,
    ( k1_xboole_0 != sK0
    | ~ r1_tarski(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:46:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (17835)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.48  % (17860)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.48  % (17835)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(subsumption_resolution,[],[f52,f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ( ! [X1] : (r1_tarski(k1_xboole_0,k2_tarski(X1,X1))) )),
% 0.21/0.48    inference(equality_resolution,[],[f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(X0,k2_tarski(X1,X1)) | k1_xboole_0 != X0) )),
% 0.21/0.48    inference(definition_unfolding,[],[f19,f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 != X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.21/0.49    inference(flattening,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.21/0.49    inference(nnf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    ~r1_tarski(k1_xboole_0,k2_tarski(sK1,sK1))),
% 0.21/0.49    inference(forward_demodulation,[],[f50,f49])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    k1_xboole_0 = sK0),
% 0.21/0.49    inference(subsumption_resolution,[],[f48,f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.21/0.49    inference(superposition,[],[f23,f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ~r1_tarski(sK0,sK0) | k1_xboole_0 = sK0),
% 0.21/0.49    inference(trivial_inequality_removal,[],[f43])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ~r1_tarski(sK0,sK0) | sK0 != sK0 | k1_xboole_0 = sK0),
% 0.21/0.49    inference(superposition,[],[f25,f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    sK0 = k2_tarski(sK1,sK1) | k1_xboole_0 = sK0),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    k1_xboole_0 = sK0 | sK0 = k2_tarski(sK1,sK1) | k1_xboole_0 = sK0 | sK0 = k2_tarski(sK1,sK1)),
% 0.21/0.49    inference(resolution,[],[f30,f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    r1_tarski(sK0,k2_tarski(sK1,sK1)) | k1_xboole_0 = sK0 | sK0 = k2_tarski(sK1,sK1)),
% 0.21/0.49    inference(definition_unfolding,[],[f15,f24,f24])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    sK0 = k1_tarski(sK1) | k1_xboole_0 = sK0 | r1_tarski(sK0,k1_tarski(sK1))),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ((sK0 != k1_tarski(sK1) & k1_xboole_0 != sK0) | ~r1_tarski(sK0,k1_tarski(sK1))) & (sK0 = k1_tarski(sK1) | k1_xboole_0 = sK0 | r1_tarski(sK0,k1_tarski(sK1)))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ? [X0,X1] : (((k1_tarski(X1) != X0 & k1_xboole_0 != X0) | ~r1_tarski(X0,k1_tarski(X1))) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | r1_tarski(X0,k1_tarski(X1)))) => (((sK0 != k1_tarski(sK1) & k1_xboole_0 != sK0) | ~r1_tarski(sK0,k1_tarski(sK1))) & (sK0 = k1_tarski(sK1) | k1_xboole_0 = sK0 | r1_tarski(sK0,k1_tarski(sK1))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ? [X0,X1] : (((k1_tarski(X1) != X0 & k1_xboole_0 != X0) | ~r1_tarski(X0,k1_tarski(X1))) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | r1_tarski(X0,k1_tarski(X1))))),
% 0.21/0.49    inference(flattening,[],[f9])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ? [X0,X1] : (((k1_tarski(X1) != X0 & k1_xboole_0 != X0) | ~r1_tarski(X0,k1_tarski(X1))) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | r1_tarski(X0,k1_tarski(X1))))),
% 0.21/0.49    inference(nnf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,plain,(
% 0.21/0.49    ? [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <~> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.21/0.49    inference(negated_conjecture,[],[f6])).
% 0.21/0.49  fof(f6,conjecture,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_zfmisc_1)).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_tarski(X0,k2_tarski(X1,X1)) | k1_xboole_0 = X0 | k2_tarski(X1,X1) = X0) )),
% 0.21/0.49    inference(definition_unfolding,[],[f18,f24,f24])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ~r1_tarski(sK0,k2_tarski(sK1,sK1)) | sK0 != k2_tarski(sK1,sK1)),
% 0.21/0.49    inference(definition_unfolding,[],[f17,f24,f24])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    sK0 != k1_tarski(sK1) | ~r1_tarski(sK0,k1_tarski(sK1))),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    ~r1_tarski(sK0,k2_tarski(sK1,sK1))),
% 0.21/0.49    inference(subsumption_resolution,[],[f26,f49])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ~r1_tarski(sK0,k2_tarski(sK1,sK1)) | k1_xboole_0 != sK0),
% 0.21/0.49    inference(definition_unfolding,[],[f16,f24])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    k1_xboole_0 != sK0 | ~r1_tarski(sK0,k1_tarski(sK1))),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (17835)------------------------------
% 0.21/0.49  % (17835)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (17835)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (17835)Memory used [KB]: 6140
% 0.21/0.49  % (17835)Time elapsed: 0.075 s
% 0.21/0.49  % (17835)------------------------------
% 0.21/0.49  % (17835)------------------------------
% 0.21/0.49  % (17826)Success in time 0.128 s
%------------------------------------------------------------------------------
