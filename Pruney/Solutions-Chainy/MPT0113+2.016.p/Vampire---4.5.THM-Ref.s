%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:34 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 283 expanded)
%              Number of leaves         :   12 (  85 expanded)
%              Depth                    :   32
%              Number of atoms          :  103 ( 440 expanded)
%              Number of equality atoms :   35 ( 168 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3982,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3980,f1318])).

fof(f1318,plain,(
    r1_xboole_0(sK0,sK2) ),
    inference(superposition,[],[f659,f55])).

fof(f55,plain,(
    sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    inference(resolution,[],[f28,f34])).

fof(f34,plain,(
    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    inference(definition_unfolding,[],[f20,f27])).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f20,plain,(
    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ( ~ r1_xboole_0(sK0,sK2)
      | ~ r1_tarski(sK0,sK1) )
    & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,X2)
          | ~ r1_tarski(X0,X1) )
        & r1_tarski(X0,k4_xboole_0(X1,X2)) )
   => ( ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_tarski(sK0,sK1) )
      & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
      & r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
       => ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f659,plain,(
    ! [X6,X4,X5] : r1_xboole_0(k3_xboole_0(X4,k5_xboole_0(X5,k3_xboole_0(X5,X6))),X6) ),
    inference(superposition,[],[f620,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(definition_unfolding,[],[f31,f27,f27])).

fof(f31,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f620,plain,(
    ! [X17,X16] : r1_xboole_0(k5_xboole_0(X17,k3_xboole_0(X17,X16)),X16) ),
    inference(trivial_inequality_removal,[],[f604])).

fof(f604,plain,(
    ! [X17,X16] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_xboole_0(k5_xboole_0(X17,k3_xboole_0(X17,X16)),X16) ) ),
    inference(superposition,[],[f82,f454])).

fof(f454,plain,(
    ! [X0,X1] : k1_xboole_0 = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(forward_demodulation,[],[f434,f22])).

fof(f22,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f434,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f36,f242])).

fof(f242,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(k3_xboole_0(X0,X1),X0) ),
    inference(resolution,[],[f198,f28])).

fof(f198,plain,(
    ! [X2,X1] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(resolution,[],[f194,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_xboole_0(X1,X2))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

fof(f194,plain,(
    ! [X6] : r1_tarski(X6,X6) ),
    inference(forward_demodulation,[],[f186,f23])).

fof(f23,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f186,plain,(
    ! [X6] : r1_tarski(k5_xboole_0(X6,k1_xboole_0),X6) ),
    inference(superposition,[],[f45,f172])).

fof(f172,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f166,f28])).

fof(f166,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f164,f33])).

fof(f164,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,k3_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f158,f25])).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f158,plain,(
    ! [X5] : r1_tarski(k1_xboole_0,k3_xboole_0(k1_xboole_0,X5)) ),
    inference(forward_demodulation,[],[f154,f22])).

fof(f154,plain,(
    ! [X5] : r1_tarski(k5_xboole_0(k3_xboole_0(k1_xboole_0,X5),k3_xboole_0(k1_xboole_0,X5)),k3_xboole_0(k1_xboole_0,X5)) ),
    inference(superposition,[],[f35,f134])).

fof(f134,plain,(
    ! [X0] : k3_xboole_0(k1_xboole_0,X0) = k3_xboole_0(k3_xboole_0(k1_xboole_0,X0),sK0) ),
    inference(resolution,[],[f127,f28])).

fof(f127,plain,(
    ! [X0] : r1_tarski(k3_xboole_0(k1_xboole_0,X0),sK0) ),
    inference(resolution,[],[f119,f47])).

fof(f47,plain,(
    ! [X4] : r1_tarski(k3_xboole_0(k1_xboole_0,X4),k1_xboole_0) ),
    inference(superposition,[],[f35,f37])).

fof(f37,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f26,f23])).

fof(f26,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f119,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | r1_tarski(X0,sK0) ) ),
    inference(superposition,[],[f33,f112])).

fof(f112,plain,(
    k1_xboole_0 = k3_xboole_0(sK0,k1_xboole_0) ),
    inference(resolution,[],[f109,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f109,plain,(
    r1_xboole_0(sK0,k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f106])).

fof(f106,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f82,f64])).

fof(f64,plain,(
    k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK0) ),
    inference(resolution,[],[f63,f28])).

fof(f63,plain,(
    r1_tarski(k1_xboole_0,sK0) ),
    inference(forward_demodulation,[],[f61,f22])).

fof(f61,plain,(
    r1_tarski(k5_xboole_0(sK0,sK0),sK0) ),
    inference(superposition,[],[f35,f55])).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f24,f27])).

fof(f24,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f45,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X0) ),
    inference(superposition,[],[f35,f25])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,X0) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(superposition,[],[f30,f25])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3980,plain,(
    ~ r1_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f3941,f21])).

fof(f21,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f3941,plain,(
    r1_tarski(sK0,sK1) ),
    inference(superposition,[],[f954,f55])).

fof(f954,plain,(
    ! [X39,X41,X40] : r1_tarski(k3_xboole_0(X39,k5_xboole_0(X40,k3_xboole_0(X40,X41))),X40) ),
    inference(forward_demodulation,[],[f936,f36])).

fof(f936,plain,(
    ! [X39,X41,X40] : r1_tarski(k5_xboole_0(k3_xboole_0(X39,X40),k3_xboole_0(k3_xboole_0(X39,X40),X41)),X40) ),
    inference(resolution,[],[f889,f35])).

fof(f889,plain,(
    ! [X19,X17,X18] :
      ( ~ r1_tarski(X19,k3_xboole_0(X18,X17))
      | r1_tarski(X19,X17) ) ),
    inference(superposition,[],[f33,f470])).

fof(f470,plain,(
    ! [X4,X3] : k3_xboole_0(X3,X4) = k3_xboole_0(X4,k3_xboole_0(X3,X4)) ),
    inference(superposition,[],[f256,f25])).

fof(f256,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(k3_xboole_0(X0,X1),X1) ),
    inference(resolution,[],[f245,f28])).

fof(f245,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0) ),
    inference(superposition,[],[f198,f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:39:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.41  % (22619)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.45  % (22621)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.45  % (22620)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.47  % (22619)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f3982,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(subsumption_resolution,[],[f3980,f1318])).
% 0.21/0.47  fof(f1318,plain,(
% 0.21/0.47    r1_xboole_0(sK0,sK2)),
% 0.21/0.47    inference(superposition,[],[f659,f55])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 0.21/0.47    inference(resolution,[],[f28,f34])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 0.21/0.47    inference(definition_unfolding,[],[f20,f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    (~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2))) => ((~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2)))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.21/0.47    inference(ennf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.21/0.47    inference(negated_conjecture,[],[f12])).
% 0.21/0.47  fof(f12,conjecture,(
% 0.21/0.47    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.47  fof(f659,plain,(
% 0.21/0.47    ( ! [X6,X4,X5] : (r1_xboole_0(k3_xboole_0(X4,k5_xboole_0(X5,k3_xboole_0(X5,X6))),X6)) )),
% 0.21/0.47    inference(superposition,[],[f620,f36])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f31,f27,f27])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 0.21/0.47  fof(f620,plain,(
% 0.21/0.47    ( ! [X17,X16] : (r1_xboole_0(k5_xboole_0(X17,k3_xboole_0(X17,X16)),X16)) )),
% 0.21/0.47    inference(trivial_inequality_removal,[],[f604])).
% 0.21/0.47  fof(f604,plain,(
% 0.21/0.47    ( ! [X17,X16] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k5_xboole_0(X17,k3_xboole_0(X17,X16)),X16)) )),
% 0.21/0.47    inference(superposition,[],[f82,f454])).
% 0.21/0.47  fof(f454,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 0.21/0.47    inference(forward_demodulation,[],[f434,f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,axiom,(
% 0.21/0.47    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.21/0.47  fof(f434,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.21/0.47    inference(superposition,[],[f36,f242])).
% 0.21/0.47  fof(f242,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(k3_xboole_0(X0,X1),X0)) )),
% 0.21/0.47    inference(resolution,[],[f198,f28])).
% 0.21/0.47  fof(f198,plain,(
% 0.21/0.47    ( ! [X2,X1] : (r1_tarski(k3_xboole_0(X1,X2),X1)) )),
% 0.21/0.47    inference(resolution,[],[f194,f33])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_xboole_0(X1,X2)) | r1_tarski(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).
% 0.21/0.47  fof(f194,plain,(
% 0.21/0.47    ( ! [X6] : (r1_tarski(X6,X6)) )),
% 0.21/0.47    inference(forward_demodulation,[],[f186,f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,axiom,(
% 0.21/0.47    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.21/0.47  fof(f186,plain,(
% 0.21/0.47    ( ! [X6] : (r1_tarski(k5_xboole_0(X6,k1_xboole_0),X6)) )),
% 0.21/0.47    inference(superposition,[],[f45,f172])).
% 0.21/0.47  fof(f172,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.47    inference(resolution,[],[f166,f28])).
% 0.21/0.47  fof(f166,plain,(
% 0.21/0.47    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.47    inference(resolution,[],[f164,f33])).
% 0.21/0.48  fof(f164,plain,(
% 0.21/0.48    ( ! [X0] : (r1_tarski(k1_xboole_0,k3_xboole_0(X0,k1_xboole_0))) )),
% 0.21/0.48    inference(superposition,[],[f158,f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.48  fof(f158,plain,(
% 0.21/0.48    ( ! [X5] : (r1_tarski(k1_xboole_0,k3_xboole_0(k1_xboole_0,X5))) )),
% 0.21/0.48    inference(forward_demodulation,[],[f154,f22])).
% 0.21/0.48  fof(f154,plain,(
% 0.21/0.48    ( ! [X5] : (r1_tarski(k5_xboole_0(k3_xboole_0(k1_xboole_0,X5),k3_xboole_0(k1_xboole_0,X5)),k3_xboole_0(k1_xboole_0,X5))) )),
% 0.21/0.48    inference(superposition,[],[f35,f134])).
% 0.21/0.48  fof(f134,plain,(
% 0.21/0.48    ( ! [X0] : (k3_xboole_0(k1_xboole_0,X0) = k3_xboole_0(k3_xboole_0(k1_xboole_0,X0),sK0)) )),
% 0.21/0.48    inference(resolution,[],[f127,f28])).
% 0.21/0.48  fof(f127,plain,(
% 0.21/0.48    ( ! [X0] : (r1_tarski(k3_xboole_0(k1_xboole_0,X0),sK0)) )),
% 0.21/0.48    inference(resolution,[],[f119,f47])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ( ! [X4] : (r1_tarski(k3_xboole_0(k1_xboole_0,X4),k1_xboole_0)) )),
% 0.21/0.48    inference(superposition,[],[f35,f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 0.21/0.48    inference(superposition,[],[f26,f23])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 0.21/0.48  fof(f119,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | r1_tarski(X0,sK0)) )),
% 0.21/0.48    inference(superposition,[],[f33,f112])).
% 0.21/0.48  fof(f112,plain,(
% 0.21/0.48    k1_xboole_0 = k3_xboole_0(sK0,k1_xboole_0)),
% 0.21/0.48    inference(resolution,[],[f109,f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.48    inference(nnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.48  fof(f109,plain,(
% 0.21/0.48    r1_xboole_0(sK0,k1_xboole_0)),
% 0.21/0.48    inference(trivial_inequality_removal,[],[f106])).
% 0.21/0.48  fof(f106,plain,(
% 0.21/0.48    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK0,k1_xboole_0)),
% 0.21/0.48    inference(superposition,[],[f82,f64])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK0)),
% 0.21/0.48    inference(resolution,[],[f63,f28])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    r1_tarski(k1_xboole_0,sK0)),
% 0.21/0.48    inference(forward_demodulation,[],[f61,f22])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    r1_tarski(k5_xboole_0(sK0,sK0),sK0)),
% 0.21/0.48    inference(superposition,[],[f35,f55])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 0.21/0.48    inference(definition_unfolding,[],[f24,f27])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X0)) )),
% 0.21/0.48    inference(superposition,[],[f35,f25])).
% 0.21/0.48  fof(f82,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k3_xboole_0(X1,X0) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 0.21/0.48    inference(superposition,[],[f30,f25])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f3980,plain,(
% 0.21/0.48    ~r1_xboole_0(sK0,sK2)),
% 0.21/0.48    inference(resolution,[],[f3941,f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ~r1_tarski(sK0,sK1) | ~r1_xboole_0(sK0,sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f3941,plain,(
% 0.21/0.48    r1_tarski(sK0,sK1)),
% 0.21/0.48    inference(superposition,[],[f954,f55])).
% 0.21/0.48  fof(f954,plain,(
% 0.21/0.48    ( ! [X39,X41,X40] : (r1_tarski(k3_xboole_0(X39,k5_xboole_0(X40,k3_xboole_0(X40,X41))),X40)) )),
% 0.21/0.48    inference(forward_demodulation,[],[f936,f36])).
% 0.21/0.48  fof(f936,plain,(
% 0.21/0.48    ( ! [X39,X41,X40] : (r1_tarski(k5_xboole_0(k3_xboole_0(X39,X40),k3_xboole_0(k3_xboole_0(X39,X40),X41)),X40)) )),
% 0.21/0.48    inference(resolution,[],[f889,f35])).
% 0.21/0.48  fof(f889,plain,(
% 0.21/0.48    ( ! [X19,X17,X18] : (~r1_tarski(X19,k3_xboole_0(X18,X17)) | r1_tarski(X19,X17)) )),
% 0.21/0.48    inference(superposition,[],[f33,f470])).
% 0.21/0.48  fof(f470,plain,(
% 0.21/0.48    ( ! [X4,X3] : (k3_xboole_0(X3,X4) = k3_xboole_0(X4,k3_xboole_0(X3,X4))) )),
% 0.21/0.48    inference(superposition,[],[f256,f25])).
% 0.21/0.48  fof(f256,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(k3_xboole_0(X0,X1),X1)) )),
% 0.21/0.48    inference(resolution,[],[f245,f28])).
% 0.21/0.48  fof(f245,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) )),
% 0.21/0.48    inference(superposition,[],[f198,f25])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (22619)------------------------------
% 0.21/0.48  % (22619)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (22619)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (22619)Memory used [KB]: 3198
% 0.21/0.48  % (22619)Time elapsed: 0.063 s
% 0.21/0.48  % (22619)------------------------------
% 0.21/0.48  % (22619)------------------------------
% 0.21/0.48  % (22606)Success in time 0.12 s
%------------------------------------------------------------------------------
