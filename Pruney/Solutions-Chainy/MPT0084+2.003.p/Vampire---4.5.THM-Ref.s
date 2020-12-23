%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:14 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 104 expanded)
%              Number of leaves         :   13 (  34 expanded)
%              Depth                    :   15
%              Number of atoms          :   83 ( 165 expanded)
%              Number of equality atoms :   44 (  83 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f895,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f866])).

fof(f866,plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(superposition,[],[f93,f844])).

fof(f844,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f843,f241])).

fof(f241,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0,sK2))) ),
    inference(superposition,[],[f40,f173])).

fof(f173,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,X0),sK2) ),
    inference(resolution,[],[f165,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f165,plain,(
    ! [X9] : r1_tarski(k4_xboole_0(sK0,X9),sK2) ),
    inference(superposition,[],[f71,f36])).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f26,f27])).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f71,plain,(
    ! [X13] : r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,X13)),sK2) ),
    inference(superposition,[],[f39,f59])).

% (2550)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
fof(f59,plain,(
    sK2 = k2_xboole_0(sK0,sK2) ),
    inference(superposition,[],[f56,f24])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f56,plain,(
    sK2 = k2_xboole_0(sK2,sK0) ),
    inference(forward_demodulation,[],[f53,f22])).

fof(f22,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f53,plain,(
    k2_xboole_0(sK2,sK0) = k2_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[],[f25,f51])).

fof(f51,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f31,f20])).

fof(f20,plain,(
    r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    & r1_tarski(sK0,sK2)
    & ~ r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) )
   => ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
      & r1_tarski(sK0,sK2)
      & ~ r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
      & r1_tarski(X0,X2)
      & ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,X2)
          & ~ r1_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f39,plain,(
    ! [X2,X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(X0,X2)) ),
    inference(definition_unfolding,[],[f32,f27])).

fof(f32,plain,(
    ! [X2,X0,X1] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_xboole_1)).

fof(f40,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f33,f27,f27])).

fof(f33,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f843,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) ),
    inference(forward_demodulation,[],[f842,f36])).

fof(f842,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))) ),
    inference(forward_demodulation,[],[f819,f23])).

fof(f23,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f819,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))) = k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k1_xboole_0) ),
    inference(superposition,[],[f42,f115])).

fof(f115,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) ),
    inference(resolution,[],[f38,f35])).

fof(f35,plain,(
    r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(definition_unfolding,[],[f21,f27])).

fof(f21,plain,(
    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f28,f27])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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

fof(f42,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) ),
    inference(forward_demodulation,[],[f41,f40])).

fof(f41,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(definition_unfolding,[],[f34,f27,f27,f27,f27])).

fof(f34,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f93,plain,(
    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f37,f19])).

fof(f19,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f29,f27])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:09:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.43  % (2547)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.46  % (2551)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.46  % (2555)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.46  % (2554)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.47  % (2546)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (2543)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.47  % (2545)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (2542)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.48  % (2552)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.49  % (2548)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.49  % (2544)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.49  % (2558)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.50  % (2543)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f895,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(trivial_inequality_removal,[],[f866])).
% 0.21/0.50  fof(f866,plain,(
% 0.21/0.50    k1_xboole_0 != k1_xboole_0),
% 0.21/0.50    inference(superposition,[],[f93,f844])).
% 0.21/0.50  fof(f844,plain,(
% 0.21/0.50    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.21/0.50    inference(forward_demodulation,[],[f843,f241])).
% 0.21/0.50  fof(f241,plain,(
% 0.21/0.50    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0,sK2)))) )),
% 0.21/0.50    inference(superposition,[],[f40,f173])).
% 0.21/0.50  fof(f173,plain,(
% 0.21/0.50    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,X0),sK2)) )),
% 0.21/0.50    inference(resolution,[],[f165,f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 0.21/0.50    inference(nnf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.50  fof(f165,plain,(
% 0.21/0.50    ( ! [X9] : (r1_tarski(k4_xboole_0(sK0,X9),sK2)) )),
% 0.21/0.50    inference(superposition,[],[f71,f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.21/0.50    inference(definition_unfolding,[],[f26,f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,axiom,(
% 0.21/0.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.21/0.50  fof(f71,plain,(
% 0.21/0.50    ( ! [X13] : (r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,X13)),sK2)) )),
% 0.21/0.50    inference(superposition,[],[f39,f59])).
% 0.21/0.50  % (2550)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    sK2 = k2_xboole_0(sK0,sK2)),
% 0.21/0.50    inference(superposition,[],[f56,f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    sK2 = k2_xboole_0(sK2,sK0)),
% 0.21/0.50    inference(forward_demodulation,[],[f53,f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    k2_xboole_0(sK2,sK0) = k2_xboole_0(sK2,k1_xboole_0)),
% 0.21/0.50    inference(superposition,[],[f25,f51])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    k1_xboole_0 = k4_xboole_0(sK0,sK2)),
% 0.21/0.50    inference(resolution,[],[f31,f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    r1_tarski(sK0,sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,sK2) & ~r1_xboole_0(sK0,sK1)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1)) => (r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,sK2) & ~r1_xboole_0(sK0,sK1))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.21/0.50    inference(negated_conjecture,[],[f12])).
% 0.21/0.50  fof(f12,conjecture,(
% 0.21/0.50    ! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(X0,X2))) )),
% 0.21/0.50    inference(definition_unfolding,[],[f32,f27])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_xboole_1)).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 0.21/0.50    inference(definition_unfolding,[],[f33,f27,f27])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 0.21/0.50  fof(f843,plain,(
% 0.21/0.50    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 0.21/0.50    inference(forward_demodulation,[],[f842,f36])).
% 0.21/0.50  fof(f842,plain,(
% 0.21/0.50    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))))),
% 0.21/0.50    inference(forward_demodulation,[],[f819,f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.50  fof(f819,plain,(
% 0.21/0.50    k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))) = k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k1_xboole_0)),
% 0.21/0.50    inference(superposition,[],[f42,f115])).
% 0.21/0.50  fof(f115,plain,(
% 0.21/0.50    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))),
% 0.21/0.50    inference(resolution,[],[f38,f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),
% 0.21/0.50    inference(definition_unfolding,[],[f21,f27])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.50    inference(definition_unfolding,[],[f28,f27])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.50    inference(nnf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))))) )),
% 0.21/0.50    inference(forward_demodulation,[],[f41,f40])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) )),
% 0.21/0.50    inference(definition_unfolding,[],[f34,f27,f27,f27,f27])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).
% 0.21/0.50  fof(f93,plain,(
% 0.21/0.50    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.21/0.50    inference(resolution,[],[f37,f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ~r1_xboole_0(sK0,sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.50    inference(definition_unfolding,[],[f29,f27])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (2543)------------------------------
% 0.21/0.50  % (2543)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (2543)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (2543)Memory used [KB]: 2046
% 0.21/0.50  % (2543)Time elapsed: 0.062 s
% 0.21/0.50  % (2543)------------------------------
% 0.21/0.50  % (2543)------------------------------
% 0.21/0.50  % (2539)Success in time 0.138 s
%------------------------------------------------------------------------------
