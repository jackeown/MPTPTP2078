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
% DateTime   : Thu Dec  3 12:31:37 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   36 (  68 expanded)
%              Number of leaves         :    8 (  19 expanded)
%              Depth                    :   11
%              Number of atoms          :   67 ( 144 expanded)
%              Number of equality atoms :   36 (  76 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (2607)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
fof(f143,plain,(
    $false ),
    inference(resolution,[],[f136,f28])).

fof(f28,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f27])).

fof(f27,plain,
    ( r1_xboole_0(sK0,sK1)
    | r1_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f19,f16])).

fof(f16,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ( sK0 != k4_xboole_0(sK0,sK1)
      | ~ r1_xboole_0(sK0,sK1) )
    & ( sK0 = k4_xboole_0(sK0,sK1)
      | r1_xboole_0(sK0,sK1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f13])).

fof(f13,plain,
    ( ? [X0,X1] :
        ( ( k4_xboole_0(X0,X1) != X0
          | ~ r1_xboole_0(X0,X1) )
        & ( k4_xboole_0(X0,X1) = X0
          | r1_xboole_0(X0,X1) ) )
   => ( ( sK0 != k4_xboole_0(sK0,sK1)
        | ~ r1_xboole_0(sK0,sK1) )
      & ( sK0 = k4_xboole_0(sK0,sK1)
        | r1_xboole_0(sK0,sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ( k4_xboole_0(X0,X1) != X0
        | ~ r1_xboole_0(X0,X1) )
      & ( k4_xboole_0(X0,X1) = X0
        | r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <~> k4_xboole_0(X0,X1) = X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_xboole_0(X0,X1)
      <=> k4_xboole_0(X0,X1) = X0 ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f19,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f136,plain,(
    ! [X0] : ~ r1_xboole_0(sK0,X0) ),
    inference(subsumption_resolution,[],[f135,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(forward_demodulation,[],[f87,f18])).

fof(f18,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f87,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(superposition,[],[f48,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f48,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = X0 ),
    inference(forward_demodulation,[],[f46,f33])).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k3_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f31,f21])).

fof(f21,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[],[f20,f20])).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,k4_xboole_0(X0,X1)),k3_xboole_0(X0,X1)) = X0 ),
    inference(superposition,[],[f22,f20])).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f135,plain,(
    ! [X0] :
      ( sK0 != k4_xboole_0(sK0,X0)
      | ~ r1_xboole_0(sK0,X0) ) ),
    inference(superposition,[],[f132,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k4_xboole_0(X0,k1_xboole_0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(superposition,[],[f21,f24])).

fof(f132,plain,(
    sK0 != k4_xboole_0(sK0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f131,f28])).

fof(f131,plain,
    ( sK0 != k4_xboole_0(sK0,k1_xboole_0)
    | ~ r1_xboole_0(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f107])).

fof(f107,plain,
    ( sK0 != k4_xboole_0(sK0,k1_xboole_0)
    | ~ r1_xboole_0(sK0,sK1)
    | ~ r1_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f17,f34])).

fof(f17,plain,
    ( sK0 != k4_xboole_0(sK0,sK1)
    | ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.36  % Computer   : n008.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 10:51:30 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.23/0.47  % (2609)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.23/0.48  % (2606)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.23/0.48  % (2604)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.23/0.48  % (2604)Refutation found. Thanks to Tanya!
% 0.23/0.48  % SZS status Theorem for theBenchmark
% 0.23/0.48  % SZS output start Proof for theBenchmark
% 0.23/0.48  % (2607)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.23/0.48  fof(f143,plain,(
% 0.23/0.48    $false),
% 0.23/0.48    inference(resolution,[],[f136,f28])).
% 0.23/0.48  fof(f28,plain,(
% 0.23/0.48    r1_xboole_0(sK0,sK1)),
% 0.23/0.48    inference(duplicate_literal_removal,[],[f27])).
% 0.23/0.48  fof(f27,plain,(
% 0.23/0.48    r1_xboole_0(sK0,sK1) | r1_xboole_0(sK0,sK1)),
% 0.23/0.48    inference(superposition,[],[f19,f16])).
% 0.23/0.48  fof(f16,plain,(
% 0.23/0.48    sK0 = k4_xboole_0(sK0,sK1) | r1_xboole_0(sK0,sK1)),
% 0.23/0.48    inference(cnf_transformation,[],[f14])).
% 0.23/0.48  fof(f14,plain,(
% 0.23/0.48    (sK0 != k4_xboole_0(sK0,sK1) | ~r1_xboole_0(sK0,sK1)) & (sK0 = k4_xboole_0(sK0,sK1) | r1_xboole_0(sK0,sK1))),
% 0.23/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f13])).
% 0.23/0.48  fof(f13,plain,(
% 0.23/0.48    ? [X0,X1] : ((k4_xboole_0(X0,X1) != X0 | ~r1_xboole_0(X0,X1)) & (k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1))) => ((sK0 != k4_xboole_0(sK0,sK1) | ~r1_xboole_0(sK0,sK1)) & (sK0 = k4_xboole_0(sK0,sK1) | r1_xboole_0(sK0,sK1)))),
% 0.23/0.48    introduced(choice_axiom,[])).
% 0.23/0.48  fof(f12,plain,(
% 0.23/0.48    ? [X0,X1] : ((k4_xboole_0(X0,X1) != X0 | ~r1_xboole_0(X0,X1)) & (k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1)))),
% 0.23/0.48    inference(nnf_transformation,[],[f10])).
% 0.23/0.48  fof(f10,plain,(
% 0.23/0.48    ? [X0,X1] : (r1_xboole_0(X0,X1) <~> k4_xboole_0(X0,X1) = X0)),
% 0.23/0.48    inference(ennf_transformation,[],[f9])).
% 0.23/0.48  fof(f9,negated_conjecture,(
% 0.23/0.48    ~! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.23/0.48    inference(negated_conjecture,[],[f8])).
% 0.23/0.48  fof(f8,conjecture,(
% 0.23/0.48    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.23/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.23/0.48  fof(f19,plain,(
% 0.23/0.48    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.23/0.48    inference(cnf_transformation,[],[f7])).
% 0.23/0.48  fof(f7,axiom,(
% 0.23/0.48    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.23/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.23/0.48  fof(f136,plain,(
% 0.23/0.48    ( ! [X0] : (~r1_xboole_0(sK0,X0)) )),
% 0.23/0.48    inference(subsumption_resolution,[],[f135,f92])).
% 0.23/0.48  fof(f92,plain,(
% 0.23/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.23/0.48    inference(forward_demodulation,[],[f87,f18])).
% 0.23/0.48  fof(f18,plain,(
% 0.23/0.48    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.23/0.48    inference(cnf_transformation,[],[f3])).
% 0.23/0.48  fof(f3,axiom,(
% 0.23/0.48    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.23/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.23/0.48  fof(f87,plain,(
% 0.23/0.48    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.23/0.48    inference(superposition,[],[f48,f24])).
% 0.23/0.48  fof(f24,plain,(
% 0.23/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.23/0.48    inference(cnf_transformation,[],[f15])).
% 0.23/0.48  fof(f15,plain,(
% 0.23/0.48    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.23/0.48    inference(nnf_transformation,[],[f1])).
% 0.23/0.48  fof(f1,axiom,(
% 0.23/0.48    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.23/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.23/0.48  fof(f48,plain,(
% 0.23/0.48    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = X0) )),
% 0.23/0.48    inference(forward_demodulation,[],[f46,f33])).
% 0.23/0.48  fof(f33,plain,(
% 0.23/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.23/0.48    inference(forward_demodulation,[],[f31,f21])).
% 0.23/0.48  fof(f21,plain,(
% 0.23/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 0.23/0.48    inference(cnf_transformation,[],[f4])).
% 0.23/0.48  fof(f4,axiom,(
% 0.23/0.48    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 0.23/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.23/0.48  fof(f31,plain,(
% 0.23/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.23/0.48    inference(superposition,[],[f20,f20])).
% 0.23/0.48  fof(f20,plain,(
% 0.23/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.23/0.48    inference(cnf_transformation,[],[f5])).
% 0.23/0.48  fof(f5,axiom,(
% 0.23/0.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.23/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.23/0.48  fof(f46,plain,(
% 0.23/0.48    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,k4_xboole_0(X0,X1)),k3_xboole_0(X0,X1)) = X0) )),
% 0.23/0.48    inference(superposition,[],[f22,f20])).
% 0.23/0.48  fof(f22,plain,(
% 0.23/0.48    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 0.23/0.48    inference(cnf_transformation,[],[f6])).
% 0.23/0.48  fof(f6,axiom,(
% 0.23/0.48    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.23/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.23/0.48  fof(f135,plain,(
% 0.23/0.48    ( ! [X0] : (sK0 != k4_xboole_0(sK0,X0) | ~r1_xboole_0(sK0,X0)) )),
% 0.23/0.48    inference(superposition,[],[f132,f34])).
% 0.23/0.48  fof(f34,plain,(
% 0.23/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k1_xboole_0) | ~r1_xboole_0(X0,X1)) )),
% 0.23/0.48    inference(superposition,[],[f21,f24])).
% 0.23/0.48  fof(f132,plain,(
% 0.23/0.48    sK0 != k4_xboole_0(sK0,k1_xboole_0)),
% 0.23/0.48    inference(subsumption_resolution,[],[f131,f28])).
% 0.23/0.48  fof(f131,plain,(
% 0.23/0.48    sK0 != k4_xboole_0(sK0,k1_xboole_0) | ~r1_xboole_0(sK0,sK1)),
% 0.23/0.48    inference(duplicate_literal_removal,[],[f107])).
% 0.23/0.48  fof(f107,plain,(
% 0.23/0.48    sK0 != k4_xboole_0(sK0,k1_xboole_0) | ~r1_xboole_0(sK0,sK1) | ~r1_xboole_0(sK0,sK1)),
% 0.23/0.48    inference(superposition,[],[f17,f34])).
% 0.23/0.48  fof(f17,plain,(
% 0.23/0.48    sK0 != k4_xboole_0(sK0,sK1) | ~r1_xboole_0(sK0,sK1)),
% 0.23/0.48    inference(cnf_transformation,[],[f14])).
% 0.23/0.48  % SZS output end Proof for theBenchmark
% 0.23/0.48  % (2604)------------------------------
% 0.23/0.48  % (2604)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.48  % (2604)Termination reason: Refutation
% 0.23/0.48  
% 0.23/0.48  % (2604)Memory used [KB]: 1663
% 0.23/0.48  % (2604)Time elapsed: 0.052 s
% 0.23/0.48  % (2604)------------------------------
% 0.23/0.48  % (2604)------------------------------
% 0.23/0.48  % (2616)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.23/0.48  % (2600)Success in time 0.111 s
%------------------------------------------------------------------------------
