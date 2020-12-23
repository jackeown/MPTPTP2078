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
% DateTime   : Thu Dec  3 12:31:43 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   58 (1697 expanded)
%              Number of leaves         :    8 ( 540 expanded)
%              Depth                    :   25
%              Number of atoms          :   83 (2849 expanded)
%              Number of equality atoms :   49 (1340 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f401,plain,(
    $false ),
    inference(subsumption_resolution,[],[f400,f212])).

fof(f212,plain,(
    k1_xboole_0 != k4_xboole_0(k1_xboole_0,sK2) ),
    inference(superposition,[],[f29,f183])).

fof(f183,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(k1_xboole_0,sK2) ),
    inference(superposition,[],[f158,f28])).

fof(f28,plain,(
    sK0 = k4_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f22,f17])).

fof(f17,plain,(
    r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ~ r1_tarski(sK0,k4_xboole_0(sK1,sK2))
    & r1_xboole_0(sK0,sK2)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
        & r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(sK0,k4_xboole_0(sK1,sK2))
      & r1_xboole_0(sK0,sK2)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) )
       => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(X0,X1) = X0 ) ),
    inference(unused_predicate_definition_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f158,plain,(
    ! [X7] : k4_xboole_0(k4_xboole_0(sK0,X7),k4_xboole_0(sK1,X7)) = k4_xboole_0(k1_xboole_0,X7) ),
    inference(backward_demodulation,[],[f138,f157])).

fof(f157,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(k1_xboole_0,X0))) ),
    inference(forward_demodulation,[],[f139,f30])).

fof(f30,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f24,f16])).

fof(f16,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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

fof(f139,plain,(
    ! [X0] : k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(k4_xboole_0(sK0,sK1),X0) ),
    inference(superposition,[],[f132,f19])).

fof(f19,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f132,plain,(
    ! [X0,X1] : k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK1,X0)),X1) = k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(X0,X1))) ),
    inference(forward_demodulation,[],[f120,f66])).

fof(f66,plain,(
    ! [X17] : k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,X17))) = k4_xboole_0(sK0,X17) ),
    inference(forward_demodulation,[],[f47,f19])).

fof(f47,plain,(
    ! [X17] : k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,X17))) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),X17) ),
    inference(superposition,[],[f27,f30])).

fof(f27,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f25,f21,f21])).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f25,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f120,plain,(
    ! [X0,X1] : k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK1,X0)),X1) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X0,X1))))) ),
    inference(superposition,[],[f78,f27])).

fof(f78,plain,(
    ! [X0,X1] : k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,X0),X1))) = k4_xboole_0(k4_xboole_0(sK0,X0),X1) ),
    inference(superposition,[],[f27,f66])).

fof(f138,plain,(
    ! [X7] : k4_xboole_0(k4_xboole_0(sK0,X7),k4_xboole_0(sK1,X7)) = k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(k1_xboole_0,X7))) ),
    inference(forward_demodulation,[],[f124,f133])).

fof(f133,plain,(
    ! [X0,X1] : k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,X1))))) = k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(X0,X1))) ),
    inference(backward_demodulation,[],[f106,f132])).

fof(f106,plain,(
    ! [X0,X1] : k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK1,X0)),X1) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,X1))))) ),
    inference(forward_demodulation,[],[f97,f27])).

fof(f97,plain,(
    ! [X0,X1] : k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK1,X0)),X1) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK1)),X1))) ),
    inference(superposition,[],[f27,f76])).

fof(f76,plain,(
    ! [X0] : k4_xboole_0(sK0,k4_xboole_0(sK1,X0)) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,sK1)))) ),
    inference(superposition,[],[f66,f26])).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f20,f21,f21])).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f124,plain,(
    ! [X7] : k4_xboole_0(k4_xboole_0(sK0,X7),k4_xboole_0(sK1,X7)) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(sK1,X7))))) ),
    inference(superposition,[],[f78,f32])).

fof(f32,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f26,f19])).

fof(f29,plain,(
    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f23,f18])).

fof(f18,plain,(
    ~ r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f14])).

% (28857)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f400,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK2) ),
    inference(forward_demodulation,[],[f385,f30])).

fof(f385,plain,(
    k4_xboole_0(sK0,sK1) = k4_xboole_0(k1_xboole_0,sK2) ),
    inference(superposition,[],[f360,f183])).

fof(f360,plain,(
    ! [X1] : k4_xboole_0(sK0,X1) = k4_xboole_0(sK0,k4_xboole_0(X1,sK2)) ),
    inference(superposition,[],[f343,f66])).

fof(f343,plain,(
    ! [X1] : k4_xboole_0(sK0,X1) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(X1,sK2)))) ),
    inference(backward_demodulation,[],[f218,f342])).

fof(f342,plain,(
    ! [X0] : k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),X0)) = k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(X0,sK2))) ),
    inference(forward_demodulation,[],[f330,f133])).

fof(f330,plain,(
    ! [X0] : k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),X0)) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,sK2))))) ),
    inference(superposition,[],[f218,f26])).

fof(f218,plain,(
    ! [X1] : k4_xboole_0(sK0,X1) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),X1))) ),
    inference(forward_demodulation,[],[f216,f217])).

fof(f217,plain,(
    sK0 = k4_xboole_0(sK0,k4_xboole_0(k1_xboole_0,sK2)) ),
    inference(forward_demodulation,[],[f214,f28])).

fof(f214,plain,(
    k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k4_xboole_0(k1_xboole_0,sK2)) ),
    inference(superposition,[],[f66,f183])).

fof(f216,plain,(
    ! [X1] : k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),X1))) = k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(k1_xboole_0,sK2)),X1) ),
    inference(superposition,[],[f27,f183])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:44:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.45  % (28860)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.46  % (28871)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.46  % (28859)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (28861)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (28862)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (28864)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.48  % (28868)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.48  % (28870)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  % (28867)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.49  % (28871)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f401,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(subsumption_resolution,[],[f400,f212])).
% 0.21/0.49  fof(f212,plain,(
% 0.21/0.49    k1_xboole_0 != k4_xboole_0(k1_xboole_0,sK2)),
% 0.21/0.49    inference(superposition,[],[f29,f183])).
% 0.21/0.49  fof(f183,plain,(
% 0.21/0.49    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(k1_xboole_0,sK2)),
% 0.21/0.49    inference(superposition,[],[f158,f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    sK0 = k4_xboole_0(sK0,sK2)),
% 0.21/0.49    inference(resolution,[],[f22,f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    r1_xboole_0(sK0,sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ~r1_tarski(sK0,k4_xboole_0(sK1,sK2)) & r1_xboole_0(sK0,sK2) & r1_tarski(sK0,sK1)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ? [X0,X1,X2] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) & r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => (~r1_tarski(sK0,k4_xboole_0(sK1,sK2)) & r1_xboole_0(sK0,sK2) & r1_tarski(sK0,sK1))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ? [X0,X1,X2] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) & r1_xboole_0(X0,X2) & r1_tarski(X0,X1))),
% 0.21/0.49    inference(flattening,[],[f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ? [X0,X1,X2] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) & (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.21/0.49    inference(negated_conjecture,[],[f7])).
% 0.21/0.49  fof(f7,conjecture,(
% 0.21/0.49    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(X0,X1) = X0)),
% 0.21/0.49    inference(unused_predicate_definition_removal,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.21/0.49  fof(f158,plain,(
% 0.21/0.49    ( ! [X7] : (k4_xboole_0(k4_xboole_0(sK0,X7),k4_xboole_0(sK1,X7)) = k4_xboole_0(k1_xboole_0,X7)) )),
% 0.21/0.49    inference(backward_demodulation,[],[f138,f157])).
% 0.21/0.49  fof(f157,plain,(
% 0.21/0.49    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(k1_xboole_0,X0)))) )),
% 0.21/0.49    inference(forward_demodulation,[],[f139,f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 0.21/0.49    inference(resolution,[],[f24,f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    r1_tarski(sK0,sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.21/0.49    inference(nnf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.49  fof(f139,plain,(
% 0.21/0.49    ( ! [X0] : (k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(k4_xboole_0(sK0,sK1),X0)) )),
% 0.21/0.49    inference(superposition,[],[f132,f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.49  fof(f132,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK1,X0)),X1) = k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(X0,X1)))) )),
% 0.21/0.49    inference(forward_demodulation,[],[f120,f66])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    ( ! [X17] : (k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,X17))) = k4_xboole_0(sK0,X17)) )),
% 0.21/0.49    inference(forward_demodulation,[],[f47,f19])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ( ! [X17] : (k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,X17))) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),X17)) )),
% 0.21/0.49    inference(superposition,[],[f27,f30])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 0.21/0.49    inference(definition_unfolding,[],[f25,f21,f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 0.21/0.49  fof(f120,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK1,X0)),X1) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X0,X1)))))) )),
% 0.21/0.49    inference(superposition,[],[f78,f27])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,X0),X1))) = k4_xboole_0(k4_xboole_0(sK0,X0),X1)) )),
% 0.21/0.49    inference(superposition,[],[f27,f66])).
% 0.21/0.49  fof(f138,plain,(
% 0.21/0.49    ( ! [X7] : (k4_xboole_0(k4_xboole_0(sK0,X7),k4_xboole_0(sK1,X7)) = k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(k1_xboole_0,X7)))) )),
% 0.21/0.49    inference(forward_demodulation,[],[f124,f133])).
% 0.21/0.49  fof(f133,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,X1))))) = k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(X0,X1)))) )),
% 0.21/0.49    inference(backward_demodulation,[],[f106,f132])).
% 0.21/0.49  fof(f106,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK1,X0)),X1) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,X1)))))) )),
% 0.21/0.49    inference(forward_demodulation,[],[f97,f27])).
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK1,X0)),X1) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK1)),X1)))) )),
% 0.21/0.49    inference(superposition,[],[f27,f76])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    ( ! [X0] : (k4_xboole_0(sK0,k4_xboole_0(sK1,X0)) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,sK1))))) )),
% 0.21/0.49    inference(superposition,[],[f66,f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.21/0.49    inference(definition_unfolding,[],[f20,f21,f21])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.49  fof(f124,plain,(
% 0.21/0.49    ( ! [X7] : (k4_xboole_0(k4_xboole_0(sK0,X7),k4_xboole_0(sK1,X7)) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(sK1,X7)))))) )),
% 0.21/0.49    inference(superposition,[],[f78,f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ( ! [X0] : (k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0)) )),
% 0.21/0.49    inference(superposition,[],[f26,f19])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.21/0.49    inference(resolution,[],[f23,f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ~r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  % (28857)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f400,plain,(
% 0.21/0.49    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK2)),
% 0.21/0.49    inference(forward_demodulation,[],[f385,f30])).
% 0.21/0.49  fof(f385,plain,(
% 0.21/0.49    k4_xboole_0(sK0,sK1) = k4_xboole_0(k1_xboole_0,sK2)),
% 0.21/0.49    inference(superposition,[],[f360,f183])).
% 0.21/0.49  fof(f360,plain,(
% 0.21/0.49    ( ! [X1] : (k4_xboole_0(sK0,X1) = k4_xboole_0(sK0,k4_xboole_0(X1,sK2))) )),
% 0.21/0.49    inference(superposition,[],[f343,f66])).
% 0.21/0.49  fof(f343,plain,(
% 0.21/0.49    ( ! [X1] : (k4_xboole_0(sK0,X1) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(X1,sK2))))) )),
% 0.21/0.49    inference(backward_demodulation,[],[f218,f342])).
% 0.21/0.49  fof(f342,plain,(
% 0.21/0.49    ( ! [X0] : (k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),X0)) = k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(X0,sK2)))) )),
% 0.21/0.49    inference(forward_demodulation,[],[f330,f133])).
% 0.21/0.49  fof(f330,plain,(
% 0.21/0.49    ( ! [X0] : (k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),X0)) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,sK2)))))) )),
% 0.21/0.49    inference(superposition,[],[f218,f26])).
% 0.21/0.49  fof(f218,plain,(
% 0.21/0.49    ( ! [X1] : (k4_xboole_0(sK0,X1) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),X1)))) )),
% 0.21/0.49    inference(forward_demodulation,[],[f216,f217])).
% 0.21/0.49  fof(f217,plain,(
% 0.21/0.49    sK0 = k4_xboole_0(sK0,k4_xboole_0(k1_xboole_0,sK2))),
% 0.21/0.49    inference(forward_demodulation,[],[f214,f28])).
% 0.21/0.49  fof(f214,plain,(
% 0.21/0.49    k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k4_xboole_0(k1_xboole_0,sK2))),
% 0.21/0.49    inference(superposition,[],[f66,f183])).
% 0.21/0.49  fof(f216,plain,(
% 0.21/0.49    ( ! [X1] : (k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),X1))) = k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(k1_xboole_0,sK2)),X1)) )),
% 0.21/0.49    inference(superposition,[],[f27,f183])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (28871)------------------------------
% 0.21/0.49  % (28871)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (28871)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (28871)Memory used [KB]: 6524
% 0.21/0.49  % (28871)Time elapsed: 0.036 s
% 0.21/0.49  % (28871)------------------------------
% 0.21/0.49  % (28871)------------------------------
% 0.21/0.50  % (28852)Success in time 0.14 s
%------------------------------------------------------------------------------
