%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:36:04 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   37 (  52 expanded)
%              Number of leaves         :   10 (  16 expanded)
%              Depth                    :   11
%              Number of atoms          :   62 (  77 expanded)
%              Number of equality atoms :   26 (  38 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f128,plain,(
    $false ),
    inference(subsumption_resolution,[],[f127,f99])).

fof(f99,plain,(
    ! [X4,X3] : r1_tarski(k2_tarski(X3,X3),k2_tarski(X3,X4)) ),
    inference(superposition,[],[f28,f39])).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f31,f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_enumset1)).

fof(f31,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).

fof(f28,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f127,plain,(
    ~ r1_tarski(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0)) ),
    inference(subsumption_resolution,[],[f125,f99])).

fof(f125,plain,
    ( ~ r1_tarski(k2_tarski(sK0,sK0),k2_tarski(sK0,sK1))
    | ~ r1_tarski(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0)) ),
    inference(resolution,[],[f123,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f123,plain,(
    ~ r1_tarski(k2_tarski(sK0,sK0),k3_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f121,f29])).

fof(f29,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f121,plain,
    ( ~ r1_tarski(k3_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK1)),k2_tarski(sK0,sK0))
    | ~ r1_tarski(k2_tarski(sK0,sK0),k3_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK1))) ),
    inference(extensionality_resolution,[],[f34,f111])).

fof(f111,plain,(
    k2_tarski(sK0,sK0) != k3_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK1)) ),
    inference(forward_demodulation,[],[f40,f26])).

fof(f26,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f40,plain,(
    k2_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0)) != k3_xboole_0(k2_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0)),k2_tarski(sK0,sK1)) ),
    inference(definition_unfolding,[],[f24,f38,f38])).

fof(f38,plain,(
    ! [X0] : k1_tarski(X0) = k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X0)) ),
    inference(definition_unfolding,[],[f25,f37])).

fof(f25,plain,(
    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_enumset1)).

fof(f24,plain,(
    k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f20])).

fof(f20,plain,
    ( ? [X0,X1] : k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))
   => k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] : k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_zfmisc_1)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:32:09 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.51  % (6210)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (6210)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.53  % (6227)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  fof(f128,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(subsumption_resolution,[],[f127,f99])).
% 0.20/0.53  fof(f99,plain,(
% 0.20/0.53    ( ! [X4,X3] : (r1_tarski(k2_tarski(X3,X3),k2_tarski(X3,X4))) )),
% 0.20/0.53    inference(superposition,[],[f28,f39])).
% 0.20/0.53  fof(f39,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X1))) )),
% 0.20/0.53    inference(definition_unfolding,[],[f31,f37])).
% 0.20/0.53  fof(f37,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f9])).
% 0.20/0.53  fof(f9,axiom,(
% 0.20/0.53    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_enumset1)).
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f10])).
% 0.20/0.53  fof(f10,axiom,(
% 0.20/0.53    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f8])).
% 0.20/0.53  fof(f8,axiom,(
% 0.20/0.53    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.20/0.53  fof(f127,plain,(
% 0.20/0.53    ~r1_tarski(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0))),
% 0.20/0.53    inference(subsumption_resolution,[],[f125,f99])).
% 0.20/0.53  fof(f125,plain,(
% 0.20/0.53    ~r1_tarski(k2_tarski(sK0,sK0),k2_tarski(sK0,sK1)) | ~r1_tarski(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0))),
% 0.20/0.53    inference(resolution,[],[f123,f36])).
% 0.20/0.53  fof(f36,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f19])).
% 0.20/0.53  fof(f19,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.53    inference(flattening,[],[f18])).
% 0.20/0.53  fof(f18,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.53    inference(ennf_transformation,[],[f6])).
% 0.20/0.53  fof(f6,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.20/0.53  fof(f123,plain,(
% 0.20/0.53    ~r1_tarski(k2_tarski(sK0,sK0),k3_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK1)))),
% 0.20/0.53    inference(subsumption_resolution,[],[f121,f29])).
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f5])).
% 0.20/0.53  fof(f5,axiom,(
% 0.20/0.53    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.20/0.54  fof(f121,plain,(
% 0.20/0.54    ~r1_tarski(k3_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK1)),k2_tarski(sK0,sK0)) | ~r1_tarski(k2_tarski(sK0,sK0),k3_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK1)))),
% 0.20/0.54    inference(extensionality_resolution,[],[f34,f111])).
% 0.20/0.54  fof(f111,plain,(
% 0.20/0.54    k2_tarski(sK0,sK0) != k3_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK1))),
% 0.20/0.54    inference(forward_demodulation,[],[f40,f26])).
% 0.20/0.54  fof(f26,plain,(
% 0.20/0.54    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.20/0.54    inference(cnf_transformation,[],[f14])).
% 0.20/0.54  fof(f14,plain,(
% 0.20/0.54    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.20/0.54    inference(rectify,[],[f2])).
% 0.20/0.54  fof(f2,axiom,(
% 0.20/0.54    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.20/0.54  fof(f40,plain,(
% 0.20/0.54    k2_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0)) != k3_xboole_0(k2_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0)),k2_tarski(sK0,sK1))),
% 0.20/0.54    inference(definition_unfolding,[],[f24,f38,f38])).
% 0.20/0.54  fof(f38,plain,(
% 0.20/0.54    ( ! [X0] : (k1_tarski(X0) = k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X0))) )),
% 0.20/0.54    inference(definition_unfolding,[],[f25,f37])).
% 0.20/0.54  fof(f25,plain,(
% 0.20/0.54    ( ! [X0] : (k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f11])).
% 0.20/0.54  fof(f11,axiom,(
% 0.20/0.54    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0)),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_enumset1)).
% 0.20/0.54  fof(f24,plain,(
% 0.20/0.54    k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 0.20/0.54    inference(cnf_transformation,[],[f21])).
% 0.20/0.54  fof(f21,plain,(
% 0.20/0.54    k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f20])).
% 0.20/0.54  fof(f20,plain,(
% 0.20/0.54    ? [X0,X1] : k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) => k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f16,plain,(
% 0.20/0.54    ? [X0,X1] : k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.20/0.54    inference(ennf_transformation,[],[f13])).
% 0.20/0.54  fof(f13,negated_conjecture,(
% 0.20/0.54    ~! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.20/0.54    inference(negated_conjecture,[],[f12])).
% 0.20/0.54  fof(f12,conjecture,(
% 0.20/0.54    ! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_zfmisc_1)).
% 0.20/0.54  fof(f34,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f23])).
% 0.20/0.54  fof(f23,plain,(
% 0.20/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.54    inference(flattening,[],[f22])).
% 0.20/0.54  fof(f22,plain,(
% 0.20/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.54    inference(nnf_transformation,[],[f4])).
% 0.20/0.54  fof(f4,axiom,(
% 0.20/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.54  % SZS output end Proof for theBenchmark
% 0.20/0.54  % (6210)------------------------------
% 0.20/0.54  % (6210)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (6210)Termination reason: Refutation
% 0.20/0.54  
% 0.20/0.54  % (6210)Memory used [KB]: 10746
% 0.20/0.54  % (6210)Time elapsed: 0.104 s
% 0.20/0.54  % (6210)------------------------------
% 0.20/0.54  % (6210)------------------------------
% 0.20/0.54  % (6203)Success in time 0.184 s
%------------------------------------------------------------------------------
