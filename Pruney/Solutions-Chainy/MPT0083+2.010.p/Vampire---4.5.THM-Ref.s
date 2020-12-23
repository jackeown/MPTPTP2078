%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:12 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 251 expanded)
%              Number of leaves         :    9 (  88 expanded)
%              Depth                    :   19
%              Number of atoms          :   76 ( 277 expanded)
%              Number of equality atoms :   51 ( 237 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f670,plain,(
    $false ),
    inference(subsumption_resolution,[],[f669,f313])).

fof(f313,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f30,f120])).

fof(f120,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X3),X2) ),
    inference(forward_demodulation,[],[f119,f31])).

fof(f31,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f25,f17])).

fof(f17,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f25,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f16,f19])).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f16,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f119,plain,(
    ! [X2,X3] : k4_xboole_0(k4_xboole_0(X2,X3),X2) = k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,X3)) ),
    inference(forward_demodulation,[],[f104,f66])).

fof(f66,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f27,f26])).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f18,f19,f19])).

fof(f18,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f20,f19])).

fof(f20,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f104,plain,(
    ! [X2,X3] : k4_xboole_0(k4_xboole_0(X2,X3),X2) = k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2)))) ),
    inference(superposition,[],[f66,f26])).

fof(f30,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f23,f19,f19])).

fof(f23,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f669,plain,(
    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK2,sK0))) ),
    inference(forward_demodulation,[],[f667,f66])).

fof(f667,plain,(
    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))))) ),
    inference(backward_demodulation,[],[f325,f653])).

fof(f653,plain,(
    ! [X1] : k4_xboole_0(sK0,k4_xboole_0(sK0,X1)) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X1,sK1))) ),
    inference(superposition,[],[f508,f30])).

fof(f508,plain,(
    ! [X6] : k4_xboole_0(sK0,X6) = k4_xboole_0(k4_xboole_0(sK0,X6),sK1) ),
    inference(forward_demodulation,[],[f489,f17])).

fof(f489,plain,(
    ! [X6] : k4_xboole_0(k4_xboole_0(sK0,X6),sK1) = k4_xboole_0(k4_xboole_0(sK0,X6),k1_xboole_0) ),
    inference(superposition,[],[f66,f371])).

fof(f371,plain,(
    ! [X32] : k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,X32))) ),
    inference(forward_demodulation,[],[f370,f80])).

fof(f80,plain,(
    ! [X6] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X6) ),
    inference(forward_demodulation,[],[f69,f17])).

fof(f69,plain,(
    ! [X6] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,X6) ),
    inference(superposition,[],[f27,f40])).

fof(f40,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(forward_demodulation,[],[f38,f31])).

fof(f38,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f26,f17])).

fof(f370,plain,(
    ! [X32] : k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,X32))) = k4_xboole_0(k1_xboole_0,X32) ),
    inference(forward_demodulation,[],[f306,f31])).

fof(f306,plain,(
    ! [X32] : k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,X32))) = k4_xboole_0(k4_xboole_0(sK1,sK1),X32) ),
    inference(superposition,[],[f30,f129])).

fof(f129,plain,(
    sK1 = k4_xboole_0(sK1,sK0) ),
    inference(forward_demodulation,[],[f128,f17])).

fof(f128,plain,(
    k4_xboole_0(sK1,sK0) = k4_xboole_0(sK1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f108,f31])).

fof(f108,plain,(
    k4_xboole_0(sK1,sK0) = k4_xboole_0(sK1,k4_xboole_0(sK0,sK0)) ),
    inference(superposition,[],[f66,f78])).

fof(f78,plain,(
    sK0 = k4_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f68,f17])).

fof(f68,plain,(
    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f27,f36])).

fof(f36,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f29,f14])).

fof(f14,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1))
    & r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1))
        & r1_xboole_0(X0,X1) )
   => ( ~ r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1))
      & r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1))
      & r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,X1)
       => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_xboole_1)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f21,f19])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f325,plain,(
    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK2,sK1)))))) ),
    inference(superposition,[],[f77,f30])).

fof(f77,plain,(
    k1_xboole_0 != k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK2,sK1)))) ),
    inference(backward_demodulation,[],[f35,f66])).

fof(f35,plain,(
    k1_xboole_0 != k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))))) ),
    inference(forward_demodulation,[],[f34,f30])).

fof(f34,plain,(
    k1_xboole_0 != k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) ),
    inference(resolution,[],[f28,f33])).

fof(f33,plain,(
    ~ r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(forward_demodulation,[],[f32,f26])).

fof(f32,plain,(
    ~ r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(backward_demodulation,[],[f24,f26])).

fof(f24,plain,(
    ~ r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))) ),
    inference(definition_unfolding,[],[f15,f19,f19])).

fof(f15,plain,(
    ~ r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f22,f19])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:08:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.47  % (18988)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.47  % (18978)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (18976)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (18977)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (18981)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.47  % (18982)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.48  % (18974)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.48  % (18985)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (18984)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  % (18989)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.49  % (18988)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f670,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(subsumption_resolution,[],[f669,f313])).
% 0.21/0.49  fof(f313,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 0.21/0.49    inference(superposition,[],[f30,f120])).
% 0.21/0.49  fof(f120,plain,(
% 0.21/0.49    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X3),X2)) )),
% 0.21/0.49    inference(forward_demodulation,[],[f119,f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.21/0.49    inference(backward_demodulation,[],[f25,f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.21/0.49    inference(definition_unfolding,[],[f16,f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.49  fof(f119,plain,(
% 0.21/0.49    ( ! [X2,X3] : (k4_xboole_0(k4_xboole_0(X2,X3),X2) = k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,X3))) )),
% 0.21/0.49    inference(forward_demodulation,[],[f104,f66])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 0.21/0.49    inference(superposition,[],[f27,f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.21/0.49    inference(definition_unfolding,[],[f18,f19,f19])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.21/0.49    inference(definition_unfolding,[],[f20,f19])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.21/0.49  fof(f104,plain,(
% 0.21/0.49    ( ! [X2,X3] : (k4_xboole_0(k4_xboole_0(X2,X3),X2) = k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2))))) )),
% 0.21/0.49    inference(superposition,[],[f66,f26])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 0.21/0.49    inference(definition_unfolding,[],[f23,f19,f19])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 0.21/0.49  fof(f669,plain,(
% 0.21/0.49    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK2,sK0)))),
% 0.21/0.49    inference(forward_demodulation,[],[f667,f66])).
% 0.21/0.49  fof(f667,plain,(
% 0.21/0.49    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))))),
% 0.21/0.49    inference(backward_demodulation,[],[f325,f653])).
% 0.21/0.49  fof(f653,plain,(
% 0.21/0.49    ( ! [X1] : (k4_xboole_0(sK0,k4_xboole_0(sK0,X1)) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X1,sK1)))) )),
% 0.21/0.49    inference(superposition,[],[f508,f30])).
% 0.21/0.49  fof(f508,plain,(
% 0.21/0.49    ( ! [X6] : (k4_xboole_0(sK0,X6) = k4_xboole_0(k4_xboole_0(sK0,X6),sK1)) )),
% 0.21/0.49    inference(forward_demodulation,[],[f489,f17])).
% 0.21/0.49  fof(f489,plain,(
% 0.21/0.49    ( ! [X6] : (k4_xboole_0(k4_xboole_0(sK0,X6),sK1) = k4_xboole_0(k4_xboole_0(sK0,X6),k1_xboole_0)) )),
% 0.21/0.49    inference(superposition,[],[f66,f371])).
% 0.21/0.49  fof(f371,plain,(
% 0.21/0.49    ( ! [X32] : (k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,X32)))) )),
% 0.21/0.49    inference(forward_demodulation,[],[f370,f80])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    ( ! [X6] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X6)) )),
% 0.21/0.49    inference(forward_demodulation,[],[f69,f17])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    ( ! [X6] : (k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,X6)) )),
% 0.21/0.49    inference(superposition,[],[f27,f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) )),
% 0.21/0.49    inference(forward_demodulation,[],[f38,f31])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ( ! [X0] : (k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) )),
% 0.21/0.49    inference(superposition,[],[f26,f17])).
% 0.21/0.49  fof(f370,plain,(
% 0.21/0.49    ( ! [X32] : (k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,X32))) = k4_xboole_0(k1_xboole_0,X32)) )),
% 0.21/0.49    inference(forward_demodulation,[],[f306,f31])).
% 0.21/0.49  fof(f306,plain,(
% 0.21/0.49    ( ! [X32] : (k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,X32))) = k4_xboole_0(k4_xboole_0(sK1,sK1),X32)) )),
% 0.21/0.49    inference(superposition,[],[f30,f129])).
% 0.21/0.49  fof(f129,plain,(
% 0.21/0.49    sK1 = k4_xboole_0(sK1,sK0)),
% 0.21/0.49    inference(forward_demodulation,[],[f128,f17])).
% 0.21/0.49  fof(f128,plain,(
% 0.21/0.49    k4_xboole_0(sK1,sK0) = k4_xboole_0(sK1,k1_xboole_0)),
% 0.21/0.49    inference(forward_demodulation,[],[f108,f31])).
% 0.21/0.49  fof(f108,plain,(
% 0.21/0.49    k4_xboole_0(sK1,sK0) = k4_xboole_0(sK1,k4_xboole_0(sK0,sK0))),
% 0.21/0.49    inference(superposition,[],[f66,f78])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    sK0 = k4_xboole_0(sK0,sK1)),
% 0.21/0.49    inference(forward_demodulation,[],[f68,f17])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k1_xboole_0)),
% 0.21/0.49    inference(superposition,[],[f27,f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.21/0.49    inference(resolution,[],[f29,f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    r1_xboole_0(sK0,sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ~r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1)) & r1_xboole_0(sK0,sK1)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ? [X0,X1,X2] : (~r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) & r1_xboole_0(X0,X1)) => (~r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1)) & r1_xboole_0(sK0,sK1))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ? [X0,X1,X2] : (~r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) & r1_xboole_0(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1,X2] : (r1_xboole_0(X0,X1) => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)))),
% 0.21/0.49    inference(negated_conjecture,[],[f8])).
% 0.21/0.49  fof(f8,conjecture,(
% 0.21/0.49    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_xboole_1)).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.49    inference(definition_unfolding,[],[f21,f19])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.49    inference(nnf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.49  fof(f325,plain,(
% 0.21/0.49    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK2,sK1))))))),
% 0.21/0.49    inference(superposition,[],[f77,f30])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    k1_xboole_0 != k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK2,sK1))))),
% 0.21/0.49    inference(backward_demodulation,[],[f35,f66])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    k1_xboole_0 != k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))))),
% 0.21/0.49    inference(forward_demodulation,[],[f34,f30])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    k1_xboole_0 != k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))),
% 0.21/0.49    inference(resolution,[],[f28,f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ~r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),
% 0.21/0.49    inference(forward_demodulation,[],[f32,f26])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ~r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),
% 0.21/0.49    inference(backward_demodulation,[],[f24,f26])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ~r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)))),
% 0.21/0.49    inference(definition_unfolding,[],[f15,f19,f19])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ~r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1))),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.49    inference(definition_unfolding,[],[f22,f19])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (18988)------------------------------
% 0.21/0.49  % (18988)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (18988)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (18988)Memory used [KB]: 6524
% 0.21/0.49  % (18988)Time elapsed: 0.024 s
% 0.21/0.49  % (18988)------------------------------
% 0.21/0.49  % (18988)------------------------------
% 0.21/0.49  % (18975)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.49  % (18973)Success in time 0.133 s
%------------------------------------------------------------------------------
