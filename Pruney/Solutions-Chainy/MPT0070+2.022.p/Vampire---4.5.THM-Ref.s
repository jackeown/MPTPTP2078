%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:29 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 185 expanded)
%              Number of leaves         :   10 (  52 expanded)
%              Depth                    :   18
%              Number of atoms          :   87 ( 367 expanded)
%              Number of equality atoms :   41 ( 114 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f885,plain,(
    $false ),
    inference(resolution,[],[f883,f25])).

fof(f25,plain,(
    ~ r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    & r1_xboole_0(sK1,sK2)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X0,X2)
        & r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
   => ( ~ r1_xboole_0(sK0,sK2)
      & r1_xboole_0(sK1,sK2)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X2)
      & r1_xboole_0(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X2)
      & r1_xboole_0(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X1,X2)
          & r1_tarski(X0,X1) )
       => r1_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f883,plain,(
    r1_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f880,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f880,plain,(
    r1_xboole_0(sK2,sK0) ),
    inference(trivial_inequality_removal,[],[f879])).

fof(f879,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK2,sK0) ),
    inference(forward_demodulation,[],[f874,f255])).

fof(f255,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,sK2) ),
    inference(forward_demodulation,[],[f254,f120])).

fof(f120,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f114,f53])).

% (4829)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
fof(f53,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f41,f24])).

fof(f24,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f34,f28])).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f34,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f114,plain,(
    k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f101,f26])).

fof(f26,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

% (4825)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f101,plain,(
    ! [X0] : k4_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK1,sK2),X0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f36,f53])).

fof(f36,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f254,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(sK2,sK2) ),
    inference(forward_demodulation,[],[f244,f54])).

fof(f54,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) ),
    inference(resolution,[],[f41,f42])).

fof(f42,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(resolution,[],[f33,f24])).

fof(f244,plain,(
    k4_xboole_0(k1_xboole_0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))) = k4_xboole_0(sK2,sK2) ),
    inference(superposition,[],[f132,f37])).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f29,f28])).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f132,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK2,k2_xboole_0(X0,k4_xboole_0(sK2,sK1))) ),
    inference(superposition,[],[f102,f27])).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f102,plain,(
    ! [X1] : k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK2,sK1),X1)) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f36,f54])).

fof(f874,plain,
    ( k1_xboole_0 != k4_xboole_0(sK2,sK2)
    | r1_xboole_0(sK2,sK0) ),
    inference(superposition,[],[f40,f866])).

fof(f866,plain,(
    sK2 = k4_xboole_0(sK2,sK0) ),
    inference(forward_demodulation,[],[f856,f309])).

fof(f309,plain,(
    sK2 = k4_xboole_0(sK2,sK1) ),
    inference(superposition,[],[f226,f44])).

fof(f44,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f27,f26])).

fof(f226,plain,(
    sK2 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK1)) ),
    inference(superposition,[],[f37,f54])).

fof(f856,plain,(
    k4_xboole_0(sK2,sK1) = k4_xboole_0(sK2,sK0) ),
    inference(superposition,[],[f813,f52])).

fof(f52,plain,(
    sK1 = k2_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f32,f23])).

fof(f23,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f813,plain,(
    ! [X0] : k4_xboole_0(sK2,X0) = k4_xboole_0(sK2,k2_xboole_0(X0,sK1)) ),
    inference(superposition,[],[f324,f27])).

fof(f324,plain,(
    ! [X0] : k4_xboole_0(sK2,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK2,X0) ),
    inference(superposition,[],[f36,f309])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f35,f28])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:56:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (4827)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.48  % (4828)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.48  % (4824)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.49  % (4823)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.50  % (4835)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.50  % (4836)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.50  % (4826)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.50  % (4824)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f885,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(resolution,[],[f883,f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ~r1_xboole_0(sK0,sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ~r1_xboole_0(sK0,sK2) & r1_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ? [X0,X1,X2] : (~r1_xboole_0(X0,X2) & r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => (~r1_xboole_0(sK0,sK2) & r1_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ? [X0,X1,X2] : (~r1_xboole_0(X0,X2) & r1_xboole_0(X1,X2) & r1_tarski(X0,X1))),
% 0.22/0.50    inference(flattening,[],[f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ? [X0,X1,X2] : (~r1_xboole_0(X0,X2) & (r1_xboole_0(X1,X2) & r1_tarski(X0,X1)))),
% 0.22/0.50    inference(ennf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,negated_conjecture,(
% 0.22/0.50    ~! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.22/0.50    inference(negated_conjecture,[],[f10])).
% 0.22/0.50  fof(f10,conjecture,(
% 0.22/0.50    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.22/0.50  fof(f883,plain,(
% 0.22/0.50    r1_xboole_0(sK0,sK2)),
% 0.22/0.50    inference(resolution,[],[f880,f33])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.22/0.50  fof(f880,plain,(
% 0.22/0.50    r1_xboole_0(sK2,sK0)),
% 0.22/0.50    inference(trivial_inequality_removal,[],[f879])).
% 0.22/0.50  fof(f879,plain,(
% 0.22/0.50    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK2,sK0)),
% 0.22/0.50    inference(forward_demodulation,[],[f874,f255])).
% 0.22/0.50  fof(f255,plain,(
% 0.22/0.50    k1_xboole_0 = k4_xboole_0(sK2,sK2)),
% 0.22/0.50    inference(forward_demodulation,[],[f254,f120])).
% 0.22/0.50  fof(f120,plain,(
% 0.22/0.50    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.22/0.50    inference(forward_demodulation,[],[f114,f53])).
% 0.22/0.50  % (4829)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),
% 0.22/0.50    inference(resolution,[],[f41,f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    r1_xboole_0(sK1,sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.50    inference(definition_unfolding,[],[f34,f28])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.22/0.50    inference(nnf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.22/0.50  fof(f114,plain,(
% 0.22/0.50    k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.22/0.50    inference(superposition,[],[f101,f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f6])).
% 0.22/0.50  % (4825)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.22/0.50  fof(f101,plain,(
% 0.22/0.50    ( ! [X0] : (k4_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK1,sK2),X0)) = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.22/0.50    inference(superposition,[],[f36,f53])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.22/0.50  fof(f254,plain,(
% 0.22/0.50    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(sK2,sK2)),
% 0.22/0.50    inference(forward_demodulation,[],[f244,f54])).
% 0.22/0.50  fof(f54,plain,(
% 0.22/0.50    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))),
% 0.22/0.50    inference(resolution,[],[f41,f42])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    r1_xboole_0(sK2,sK1)),
% 0.22/0.50    inference(resolution,[],[f33,f24])).
% 0.22/0.50  fof(f244,plain,(
% 0.22/0.50    k4_xboole_0(k1_xboole_0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))) = k4_xboole_0(sK2,sK2)),
% 0.22/0.50    inference(superposition,[],[f132,f37])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 0.22/0.50    inference(definition_unfolding,[],[f29,f28])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,axiom,(
% 0.22/0.50    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.22/0.50  fof(f132,plain,(
% 0.22/0.50    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK2,k2_xboole_0(X0,k4_xboole_0(sK2,sK1)))) )),
% 0.22/0.50    inference(superposition,[],[f102,f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.22/0.50  fof(f102,plain,(
% 0.22/0.50    ( ! [X1] : (k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK2,sK1),X1)) = k4_xboole_0(k1_xboole_0,X1)) )),
% 0.22/0.50    inference(superposition,[],[f36,f54])).
% 0.22/0.50  fof(f874,plain,(
% 0.22/0.50    k1_xboole_0 != k4_xboole_0(sK2,sK2) | r1_xboole_0(sK2,sK0)),
% 0.22/0.50    inference(superposition,[],[f40,f866])).
% 0.22/0.50  fof(f866,plain,(
% 0.22/0.50    sK2 = k4_xboole_0(sK2,sK0)),
% 0.22/0.50    inference(forward_demodulation,[],[f856,f309])).
% 0.22/0.50  fof(f309,plain,(
% 0.22/0.50    sK2 = k4_xboole_0(sK2,sK1)),
% 0.22/0.50    inference(superposition,[],[f226,f44])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.22/0.50    inference(superposition,[],[f27,f26])).
% 0.22/0.50  fof(f226,plain,(
% 0.22/0.50    sK2 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK1))),
% 0.22/0.50    inference(superposition,[],[f37,f54])).
% 0.22/0.50  fof(f856,plain,(
% 0.22/0.50    k4_xboole_0(sK2,sK1) = k4_xboole_0(sK2,sK0)),
% 0.22/0.50    inference(superposition,[],[f813,f52])).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    sK1 = k2_xboole_0(sK0,sK1)),
% 0.22/0.50    inference(resolution,[],[f32,f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    r1_tarski(sK0,sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.22/0.50    inference(cnf_transformation,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.22/0.50  fof(f813,plain,(
% 0.22/0.50    ( ! [X0] : (k4_xboole_0(sK2,X0) = k4_xboole_0(sK2,k2_xboole_0(X0,sK1))) )),
% 0.22/0.50    inference(superposition,[],[f324,f27])).
% 0.22/0.50  fof(f324,plain,(
% 0.22/0.50    ( ! [X0] : (k4_xboole_0(sK2,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK2,X0)) )),
% 0.22/0.50    inference(superposition,[],[f36,f309])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.22/0.50    inference(definition_unfolding,[],[f35,f28])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f22])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (4824)------------------------------
% 0.22/0.50  % (4824)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (4824)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (4824)Memory used [KB]: 6396
% 0.22/0.50  % (4824)Time elapsed: 0.062 s
% 0.22/0.50  % (4824)------------------------------
% 0.22/0.50  % (4824)------------------------------
% 0.22/0.50  % (4821)Success in time 0.135 s
%------------------------------------------------------------------------------
