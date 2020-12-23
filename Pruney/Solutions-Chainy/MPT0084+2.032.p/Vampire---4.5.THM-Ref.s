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
% DateTime   : Thu Dec  3 12:31:18 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 205 expanded)
%              Number of leaves         :   11 (  67 expanded)
%              Depth                    :   18
%              Number of atoms          :   97 ( 277 expanded)
%              Number of equality atoms :   42 ( 168 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f602,plain,(
    $false ),
    inference(resolution,[],[f545,f19])).

fof(f19,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    & r1_tarski(sK0,sK2)
    & ~ r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) )
   => ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
      & r1_tarski(sK0,sK2)
      & ~ r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
      & r1_tarski(X0,X2)
      & ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,X2)
          & ~ r1_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).

fof(f545,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f540,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f27,f26])).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f17])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f540,plain,(
    ! [X0] : ~ r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(backward_demodulation,[],[f39,f537])).

fof(f537,plain,(
    ! [X8,X7] : k4_xboole_0(sK0,k4_xboole_0(X8,k4_xboole_0(X7,sK2))) = k4_xboole_0(sK0,X8) ),
    inference(forward_demodulation,[],[f536,f120])).

fof(f120,plain,(
    ! [X2,X3] : k4_xboole_0(X2,X3) = k2_xboole_0(k4_xboole_0(X2,X3),k1_xboole_0) ),
    inference(forward_demodulation,[],[f119,f23])).

fof(f23,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f119,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k4_xboole_0(X3,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(X2,X3),k1_xboole_0) ),
    inference(forward_demodulation,[],[f104,f37])).

fof(f37,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f32,f23])).

fof(f32,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f22,f26])).

fof(f22,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f104,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k4_xboole_0(X3,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,X2)) ),
    inference(superposition,[],[f36,f23])).

fof(f36,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f30,f26])).

fof(f30,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f536,plain,(
    ! [X8,X7] : k4_xboole_0(sK0,k4_xboole_0(X8,k4_xboole_0(X7,sK2))) = k2_xboole_0(k4_xboole_0(sK0,X8),k1_xboole_0) ),
    inference(forward_demodulation,[],[f522,f37])).

fof(f522,plain,(
    ! [X8,X7] : k4_xboole_0(sK0,k4_xboole_0(X8,k4_xboole_0(X7,sK2))) = k2_xboole_0(k4_xboole_0(sK0,X8),k4_xboole_0(sK0,sK0)) ),
    inference(superposition,[],[f36,f496])).

fof(f496,plain,(
    ! [X13] : sK0 = k4_xboole_0(sK0,k4_xboole_0(X13,sK2)) ),
    inference(backward_demodulation,[],[f124,f492])).

fof(f492,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(backward_demodulation,[],[f118,f491])).

fof(f491,plain,(
    ! [X14,X15] : k2_xboole_0(k4_xboole_0(X14,X15),X14) = X14 ),
    inference(forward_demodulation,[],[f467,f23])).

fof(f467,plain,(
    ! [X14,X15] : k2_xboole_0(k4_xboole_0(k4_xboole_0(X14,X15),k1_xboole_0),X14) = X14 ),
    inference(superposition,[],[f334,f169])).

fof(f169,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,X0),X1) ),
    inference(forward_demodulation,[],[f149,f23])).

fof(f149,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X1,k1_xboole_0)) ),
    inference(superposition,[],[f113,f37])).

fof(f113,plain,(
    ! [X2,X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(superposition,[],[f24,f36])).

fof(f24,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f334,plain,(
    ! [X2,X3] : k2_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X2)),X2) = X2 ),
    inference(forward_demodulation,[],[f333,f23])).

fof(f333,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k1_xboole_0) = k2_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X2)),X2) ),
    inference(forward_demodulation,[],[f317,f169])).

fof(f317,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X2,X3),X2)) = k2_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X2)),X2) ),
    inference(superposition,[],[f118,f33])).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f25,f26,f26])).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f118,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(forward_demodulation,[],[f103,f23])).

fof(f103,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f36,f37])).

fof(f124,plain,(
    ! [X13] : k4_xboole_0(sK0,k4_xboole_0(X13,sK2)) = k4_xboole_0(sK0,k4_xboole_0(X13,sK0)) ),
    inference(forward_demodulation,[],[f123,f118])).

fof(f123,plain,(
    ! [X13] : k4_xboole_0(sK0,k4_xboole_0(X13,sK2)) = k2_xboole_0(k4_xboole_0(sK0,X13),sK0) ),
    inference(forward_demodulation,[],[f108,f23])).

fof(f108,plain,(
    ! [X13] : k4_xboole_0(sK0,k4_xboole_0(X13,sK2)) = k2_xboole_0(k4_xboole_0(sK0,X13),k4_xboole_0(sK0,k1_xboole_0)) ),
    inference(superposition,[],[f36,f40])).

fof(f40,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK2) ),
    inference(superposition,[],[f24,f38])).

fof(f38,plain,(
    sK2 = k2_xboole_0(sK0,k4_xboole_0(sK2,sK0)) ),
    inference(resolution,[],[f29,f20])).

fof(f20,plain,(
    r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

fof(f39,plain,(
    ! [X0] : ~ r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))) ),
    inference(resolution,[],[f34,f31])).

fof(f31,plain,(
    r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(definition_unfolding,[],[f21,f26])).

fof(f21,plain,(
    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f28,f26])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n005.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:03:47 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (6558)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.46  % (6559)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.46  % (6570)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.48  % (6566)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.48  % (6569)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.48  % (6557)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.48  % (6561)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.48  % (6560)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.49  % (6567)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.49  % (6555)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.49  % (6564)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.49  % (6563)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.49  % (6562)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.49  % (6556)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.49  % (6571)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.49  % (6568)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.50  % (6565)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.50  % (6556)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f602,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(resolution,[],[f545,f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ~r1_xboole_0(sK0,sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,sK2) & ~r1_xboole_0(sK0,sK1)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1)) => (r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,sK2) & ~r1_xboole_0(sK0,sK1))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f10])).
% 0.22/0.50  fof(f10,negated_conjecture,(
% 0.22/0.50    ~! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.22/0.50    inference(negated_conjecture,[],[f9])).
% 0.22/0.50  fof(f9,conjecture,(
% 0.22/0.50    ! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).
% 0.22/0.50  fof(f545,plain,(
% 0.22/0.50    r1_xboole_0(sK0,sK1)),
% 0.22/0.50    inference(resolution,[],[f540,f35])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r1_xboole_0(X0,X1)) )),
% 0.22/0.50    inference(definition_unfolding,[],[f27,f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.22/0.50    inference(ennf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,plain,(
% 0.22/0.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.50    inference(rectify,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.22/0.50  fof(f540,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) )),
% 0.22/0.50    inference(backward_demodulation,[],[f39,f537])).
% 0.22/0.50  fof(f537,plain,(
% 0.22/0.50    ( ! [X8,X7] : (k4_xboole_0(sK0,k4_xboole_0(X8,k4_xboole_0(X7,sK2))) = k4_xboole_0(sK0,X8)) )),
% 0.22/0.50    inference(forward_demodulation,[],[f536,f120])).
% 0.22/0.50  fof(f120,plain,(
% 0.22/0.50    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k2_xboole_0(k4_xboole_0(X2,X3),k1_xboole_0)) )),
% 0.22/0.50    inference(forward_demodulation,[],[f119,f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.22/0.50  fof(f119,plain,(
% 0.22/0.50    ( ! [X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X3,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(X2,X3),k1_xboole_0)) )),
% 0.22/0.50    inference(forward_demodulation,[],[f104,f37])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.22/0.50    inference(backward_demodulation,[],[f32,f23])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.22/0.50    inference(definition_unfolding,[],[f22,f26])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.22/0.50  fof(f104,plain,(
% 0.22/0.50    ( ! [X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X3,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,X2))) )),
% 0.22/0.50    inference(superposition,[],[f36,f23])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) )),
% 0.22/0.50    inference(definition_unfolding,[],[f30,f26])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).
% 0.22/0.50  fof(f536,plain,(
% 0.22/0.50    ( ! [X8,X7] : (k4_xboole_0(sK0,k4_xboole_0(X8,k4_xboole_0(X7,sK2))) = k2_xboole_0(k4_xboole_0(sK0,X8),k1_xboole_0)) )),
% 0.22/0.50    inference(forward_demodulation,[],[f522,f37])).
% 0.22/0.50  fof(f522,plain,(
% 0.22/0.50    ( ! [X8,X7] : (k4_xboole_0(sK0,k4_xboole_0(X8,k4_xboole_0(X7,sK2))) = k2_xboole_0(k4_xboole_0(sK0,X8),k4_xboole_0(sK0,sK0))) )),
% 0.22/0.50    inference(superposition,[],[f36,f496])).
% 0.22/0.50  fof(f496,plain,(
% 0.22/0.50    ( ! [X13] : (sK0 = k4_xboole_0(sK0,k4_xboole_0(X13,sK2))) )),
% 0.22/0.50    inference(backward_demodulation,[],[f124,f492])).
% 0.22/0.50  fof(f492,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0) )),
% 0.22/0.50    inference(backward_demodulation,[],[f118,f491])).
% 0.22/0.50  fof(f491,plain,(
% 0.22/0.50    ( ! [X14,X15] : (k2_xboole_0(k4_xboole_0(X14,X15),X14) = X14) )),
% 0.22/0.50    inference(forward_demodulation,[],[f467,f23])).
% 0.22/0.50  fof(f467,plain,(
% 0.22/0.50    ( ! [X14,X15] : (k2_xboole_0(k4_xboole_0(k4_xboole_0(X14,X15),k1_xboole_0),X14) = X14) )),
% 0.22/0.50    inference(superposition,[],[f334,f169])).
% 0.22/0.50  fof(f169,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,X0),X1)) )),
% 0.22/0.50    inference(forward_demodulation,[],[f149,f23])).
% 0.22/0.50  fof(f149,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X1,k1_xboole_0))) )),
% 0.22/0.50    inference(superposition,[],[f113,f37])).
% 0.22/0.50  fof(f113,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,X2)))) )),
% 0.22/0.50    inference(superposition,[],[f24,f36])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.22/0.50  fof(f334,plain,(
% 0.22/0.50    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X2)),X2) = X2) )),
% 0.22/0.50    inference(forward_demodulation,[],[f333,f23])).
% 0.22/0.50  fof(f333,plain,(
% 0.22/0.50    ( ! [X2,X3] : (k4_xboole_0(X2,k1_xboole_0) = k2_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X2)),X2)) )),
% 0.22/0.50    inference(forward_demodulation,[],[f317,f169])).
% 0.22/0.50  fof(f317,plain,(
% 0.22/0.50    ( ! [X2,X3] : (k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X2,X3),X2)) = k2_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X2)),X2)) )),
% 0.22/0.50    inference(superposition,[],[f118,f33])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.22/0.50    inference(definition_unfolding,[],[f25,f26,f26])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.50  fof(f118,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X0,X1),X0)) )),
% 0.22/0.50    inference(forward_demodulation,[],[f103,f23])).
% 0.22/0.50  fof(f103,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k1_xboole_0))) )),
% 0.22/0.50    inference(superposition,[],[f36,f37])).
% 0.22/0.50  fof(f124,plain,(
% 0.22/0.50    ( ! [X13] : (k4_xboole_0(sK0,k4_xboole_0(X13,sK2)) = k4_xboole_0(sK0,k4_xboole_0(X13,sK0))) )),
% 0.22/0.50    inference(forward_demodulation,[],[f123,f118])).
% 0.22/0.50  fof(f123,plain,(
% 0.22/0.50    ( ! [X13] : (k4_xboole_0(sK0,k4_xboole_0(X13,sK2)) = k2_xboole_0(k4_xboole_0(sK0,X13),sK0)) )),
% 0.22/0.50    inference(forward_demodulation,[],[f108,f23])).
% 0.22/0.50  fof(f108,plain,(
% 0.22/0.50    ( ! [X13] : (k4_xboole_0(sK0,k4_xboole_0(X13,sK2)) = k2_xboole_0(k4_xboole_0(sK0,X13),k4_xboole_0(sK0,k1_xboole_0))) )),
% 0.22/0.50    inference(superposition,[],[f36,f40])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    k1_xboole_0 = k4_xboole_0(sK0,sK2)),
% 0.22/0.50    inference(superposition,[],[f24,f38])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    sK2 = k2_xboole_0(sK0,k4_xboole_0(sK2,sK0))),
% 0.22/0.50    inference(resolution,[],[f29,f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    r1_tarski(sK0,sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f16])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1) )),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))))) )),
% 0.22/0.50    inference(resolution,[],[f34,f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),
% 0.22/0.50    inference(definition_unfolding,[],[f21,f26])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 0.22/0.50    inference(cnf_transformation,[],[f16])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.22/0.50    inference(definition_unfolding,[],[f28,f26])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f18])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (6556)------------------------------
% 0.22/0.50  % (6556)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (6556)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (6556)Memory used [KB]: 1918
% 0.22/0.50  % (6556)Time elapsed: 0.080 s
% 0.22/0.50  % (6556)------------------------------
% 0.22/0.50  % (6556)------------------------------
% 0.22/0.50  % (6554)Success in time 0.142 s
%------------------------------------------------------------------------------
