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
% DateTime   : Thu Dec  3 12:37:34 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   49 (  95 expanded)
%              Number of leaves         :   13 (  27 expanded)
%              Depth                    :   14
%              Number of atoms          :   76 ( 146 expanded)
%              Number of equality atoms :   46 (  99 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f148,plain,(
    $false ),
    inference(resolution,[],[f130,f52])).

fof(f52,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0) ),
    inference(superposition,[],[f35,f36])).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f130,plain,(
    ! [X0] : ~ r1_tarski(X0,k1_tarski(sK0)) ),
    inference(resolution,[],[f120,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X0)
      | ~ r1_tarski(X1,X0) ) ),
    inference(superposition,[],[f34,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X1,X0) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(forward_demodulation,[],[f78,f32])).

fof(f32,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f78,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X1,X0) = k5_xboole_0(X1,k1_xboole_0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f39,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f120,plain,(
    ~ r1_tarski(k1_tarski(sK0),k1_tarski(sK0)) ),
    inference(subsumption_resolution,[],[f119,f33])).

fof(f33,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f119,plain,
    ( k1_tarski(sK0) != k2_tarski(sK0,sK0)
    | ~ r1_tarski(k1_tarski(sK0),k1_tarski(sK0)) ),
    inference(forward_demodulation,[],[f114,f112])).

fof(f112,plain,(
    sK0 = sK1 ),
    inference(subsumption_resolution,[],[f111,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).

fof(f111,plain,
    ( ~ r1_xboole_0(k1_tarski(sK1),k1_tarski(sK0))
    | sK0 = sK1 ),
    inference(trivial_inequality_removal,[],[f110])).

fof(f110,plain,
    ( k2_tarski(sK0,sK1) != k2_tarski(sK0,sK1)
    | ~ r1_xboole_0(k1_tarski(sK1),k1_tarski(sK0))
    | sK0 = sK1 ),
    inference(superposition,[],[f109,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_zfmisc_1)).

fof(f109,plain,
    ( k2_tarski(sK0,sK1) != k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | ~ r1_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) ),
    inference(superposition,[],[f57,f79])).

fof(f79,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,X2) = k5_xboole_0(X3,X2)
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(superposition,[],[f39,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(X0,X1) = X0 ) ),
    inference(unused_predicate_definition_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f57,plain,(
    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(superposition,[],[f31,f37])).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f31,plain,(
    k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1))) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f28])).

fof(f28,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))
   => k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1))) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_zfmisc_1)).

fof(f114,plain,
    ( ~ r1_tarski(k1_tarski(sK0),k1_tarski(sK0))
    | k2_tarski(sK0,sK1) != k1_tarski(sK0) ),
    inference(backward_demodulation,[],[f84,f112])).

fof(f84,plain,
    ( k2_tarski(sK0,sK1) != k1_tarski(sK0)
    | ~ r1_tarski(k1_tarski(sK1),k1_tarski(sK0)) ),
    inference(superposition,[],[f57,f80])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:17:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.44  % (14604)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.44  % (14602)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.45  % (14602)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f148,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(resolution,[],[f130,f52])).
% 0.21/0.45  fof(f52,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) )),
% 0.21/0.45    inference(superposition,[],[f35,f36])).
% 0.21/0.45  fof(f36,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f1])).
% 0.21/0.45  fof(f1,axiom,(
% 0.21/0.45    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.45  fof(f35,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f4])).
% 0.21/0.45  fof(f4,axiom,(
% 0.21/0.45    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.21/0.45  fof(f130,plain,(
% 0.21/0.45    ( ! [X0] : (~r1_tarski(X0,k1_tarski(sK0))) )),
% 0.21/0.45    inference(resolution,[],[f120,f82])).
% 0.21/0.45  fof(f82,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r1_tarski(X0,X0) | ~r1_tarski(X1,X0)) )),
% 0.21/0.45    inference(superposition,[],[f34,f80])).
% 0.21/0.45  fof(f80,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_xboole_0(X1,X0) = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.45    inference(forward_demodulation,[],[f78,f32])).
% 0.21/0.45  fof(f32,plain,(
% 0.21/0.45    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.45    inference(cnf_transformation,[],[f6])).
% 0.21/0.45  fof(f6,axiom,(
% 0.21/0.45    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 0.21/0.45  fof(f78,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_xboole_0(X1,X0) = k5_xboole_0(X1,k1_xboole_0) | ~r1_tarski(X0,X1)) )),
% 0.21/0.45    inference(superposition,[],[f39,f46])).
% 0.21/0.45  fof(f46,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f30])).
% 0.21/0.45  fof(f30,plain,(
% 0.21/0.45    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.21/0.45    inference(nnf_transformation,[],[f2])).
% 0.21/0.45  fof(f2,axiom,(
% 0.21/0.45    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.45  fof(f39,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f9])).
% 0.21/0.45  fof(f9,axiom,(
% 0.21/0.45    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.21/0.45  fof(f34,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f7])).
% 0.21/0.45  fof(f7,axiom,(
% 0.21/0.45    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.45  fof(f120,plain,(
% 0.21/0.45    ~r1_tarski(k1_tarski(sK0),k1_tarski(sK0))),
% 0.21/0.45    inference(subsumption_resolution,[],[f119,f33])).
% 0.21/0.45  fof(f33,plain,(
% 0.21/0.45    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f10])).
% 0.21/0.45  fof(f10,axiom,(
% 0.21/0.45    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.45  fof(f119,plain,(
% 0.21/0.45    k1_tarski(sK0) != k2_tarski(sK0,sK0) | ~r1_tarski(k1_tarski(sK0),k1_tarski(sK0))),
% 0.21/0.45    inference(forward_demodulation,[],[f114,f112])).
% 0.21/0.45  fof(f112,plain,(
% 0.21/0.45    sK0 = sK1),
% 0.21/0.45    inference(subsumption_resolution,[],[f111,f41])).
% 0.21/0.45  fof(f41,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 0.21/0.45    inference(cnf_transformation,[],[f24])).
% 0.21/0.45  fof(f24,plain,(
% 0.21/0.45    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1)),
% 0.21/0.45    inference(ennf_transformation,[],[f18])).
% 0.21/0.45  fof(f18,axiom,(
% 0.21/0.45    ! [X0,X1] : (X0 != X1 => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).
% 0.21/0.45  fof(f111,plain,(
% 0.21/0.45    ~r1_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) | sK0 = sK1),
% 0.21/0.45    inference(trivial_inequality_removal,[],[f110])).
% 0.21/0.45  fof(f110,plain,(
% 0.21/0.45    k2_tarski(sK0,sK1) != k2_tarski(sK0,sK1) | ~r1_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) | sK0 = sK1),
% 0.21/0.45    inference(superposition,[],[f109,f42])).
% 0.21/0.45  fof(f42,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 0.21/0.45    inference(cnf_transformation,[],[f25])).
% 0.21/0.45  fof(f25,plain,(
% 0.21/0.45    ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1)),
% 0.21/0.45    inference(ennf_transformation,[],[f19])).
% 0.21/0.45  fof(f19,axiom,(
% 0.21/0.45    ! [X0,X1] : (X0 != X1 => k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_zfmisc_1)).
% 0.21/0.45  fof(f109,plain,(
% 0.21/0.45    k2_tarski(sK0,sK1) != k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) | ~r1_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),
% 0.21/0.45    inference(superposition,[],[f57,f79])).
% 0.21/0.45  fof(f79,plain,(
% 0.21/0.45    ( ! [X2,X3] : (k2_xboole_0(X3,X2) = k5_xboole_0(X3,X2) | ~r1_xboole_0(X2,X3)) )),
% 0.21/0.45    inference(superposition,[],[f39,f44])).
% 0.21/0.45  fof(f44,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f27])).
% 0.21/0.45  fof(f27,plain,(
% 0.21/0.45    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f22])).
% 0.21/0.45  fof(f22,plain,(
% 0.21/0.45    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(X0,X1) = X0)),
% 0.21/0.45    inference(unused_predicate_definition_removal,[],[f8])).
% 0.21/0.45  fof(f8,axiom,(
% 0.21/0.45    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.21/0.45  fof(f57,plain,(
% 0.21/0.45    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 0.21/0.45    inference(superposition,[],[f31,f37])).
% 0.21/0.45  fof(f37,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f17])).
% 0.21/0.45  fof(f17,axiom,(
% 0.21/0.45    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.45  fof(f31,plain,(
% 0.21/0.45    k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1)))),
% 0.21/0.45    inference(cnf_transformation,[],[f29])).
% 0.21/0.45  fof(f29,plain,(
% 0.21/0.45    k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1)))),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f28])).
% 0.21/0.45  fof(f28,plain,(
% 0.21/0.45    ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) => k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1)))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f23,plain,(
% 0.21/0.45    ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 0.21/0.45    inference(ennf_transformation,[],[f21])).
% 0.21/0.45  fof(f21,negated_conjecture,(
% 0.21/0.45    ~! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 0.21/0.45    inference(negated_conjecture,[],[f20])).
% 0.21/0.45  fof(f20,conjecture,(
% 0.21/0.45    ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_zfmisc_1)).
% 0.21/0.45  fof(f114,plain,(
% 0.21/0.45    ~r1_tarski(k1_tarski(sK0),k1_tarski(sK0)) | k2_tarski(sK0,sK1) != k1_tarski(sK0)),
% 0.21/0.45    inference(backward_demodulation,[],[f84,f112])).
% 0.21/0.45  fof(f84,plain,(
% 0.21/0.45    k2_tarski(sK0,sK1) != k1_tarski(sK0) | ~r1_tarski(k1_tarski(sK1),k1_tarski(sK0))),
% 0.21/0.45    inference(superposition,[],[f57,f80])).
% 0.21/0.45  % SZS output end Proof for theBenchmark
% 0.21/0.45  % (14602)------------------------------
% 0.21/0.45  % (14602)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (14602)Termination reason: Refutation
% 0.21/0.45  
% 0.21/0.45  % (14602)Memory used [KB]: 1663
% 0.21/0.45  % (14602)Time elapsed: 0.009 s
% 0.21/0.45  % (14602)------------------------------
% 0.21/0.45  % (14602)------------------------------
% 0.21/0.45  % (14594)Success in time 0.096 s
%------------------------------------------------------------------------------
