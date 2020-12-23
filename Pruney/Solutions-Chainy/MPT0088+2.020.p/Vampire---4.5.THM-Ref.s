%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:33 EST 2020

% Result     : Theorem 2.59s
% Output     : Refutation 2.59s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 130 expanded)
%              Number of leaves         :   11 (  44 expanded)
%              Depth                    :   19
%              Number of atoms          :   76 ( 162 expanded)
%              Number of equality atoms :   46 ( 117 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8936,plain,(
    $false ),
    inference(subsumption_resolution,[],[f8933,f18])).

fof(f18,plain,(
    ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X1,k4_xboole_0(X0,X2))
        & r1_xboole_0(X0,k4_xboole_0(X1,X2)) )
   => ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
      & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X1,k4_xboole_0(X0,X2))
      & r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
       => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
     => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_xboole_1)).

fof(f8933,plain,(
    r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(trivial_inequality_removal,[],[f8848])).

fof(f8848,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(superposition,[],[f32,f8749])).

fof(f8749,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))) ),
    inference(forward_demodulation,[],[f8748,f37])).

fof(f37,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f30,f20])).

fof(f20,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f30,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f19,f22])).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f19,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f8748,plain,(
    k4_xboole_0(sK1,sK1) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))) ),
    inference(forward_demodulation,[],[f8353,f507])).

fof(f507,plain,(
    ! [X10,X11] : k4_xboole_0(X10,k4_xboole_0(X11,X10)) = X10 ),
    inference(forward_demodulation,[],[f478,f20])).

fof(f478,plain,(
    ! [X10,X11] : k4_xboole_0(X10,k4_xboole_0(X11,X10)) = k4_xboole_0(X10,k1_xboole_0) ),
    inference(superposition,[],[f31,f128])).

fof(f128,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f34,f43])).

fof(f43,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(resolution,[],[f27,f21])).

fof(f21,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f34,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f28,f22,f22])).

fof(f28,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f23,f22])).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f8353,plain,(
    k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK1))) ),
    inference(superposition,[],[f220,f2945])).

fof(f2945,plain,(
    ! [X7] : k4_xboole_0(sK0,X7) = k4_xboole_0(sK0,k4_xboole_0(X7,k4_xboole_0(sK1,sK2))) ),
    inference(forward_demodulation,[],[f2876,f31])).

fof(f2876,plain,(
    ! [X7] : k4_xboole_0(sK0,k4_xboole_0(X7,k4_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X7))) ),
    inference(superposition,[],[f31,f283])).

fof(f283,plain,(
    ! [X20] : k4_xboole_0(sK0,k4_xboole_0(sK0,X20)) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X20,k4_xboole_0(sK1,sK2)))) ),
    inference(forward_demodulation,[],[f282,f20])).

fof(f282,plain,(
    ! [X20] : k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X20,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X20,k1_xboole_0))) ),
    inference(forward_demodulation,[],[f281,f37])).

fof(f281,plain,(
    ! [X20] : k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X20,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X20,k4_xboole_0(sK0,sK0)))) ),
    inference(forward_demodulation,[],[f214,f34])).

fof(f214,plain,(
    ! [X20] : k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X20,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,X20)),k4_xboole_0(sK0,sK0)) ),
    inference(superposition,[],[f35,f104])).

fof(f104,plain,(
    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f91,f20])).

fof(f91,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f31,f70])).

fof(f70,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) ),
    inference(resolution,[],[f33,f17])).

fof(f17,plain,(
    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f24,f22])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f35,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f29,f22,f22,f22])).

fof(f29,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_xboole_1)).

fof(f220,plain,(
    ! [X4,X5,X3] : k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,k4_xboole_0(X3,k4_xboole_0(X3,X5))))) = k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,X5))) ),
    inference(superposition,[],[f35,f34])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f25,f22])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:13:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (20815)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.46  % (20814)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (20827)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.47  % (20823)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.47  % (20822)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.47  % (20821)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.47  % (20813)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (20819)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.48  % (20824)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  % (20811)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.48  % (20825)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.49  % (20816)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.49  % (20817)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.49  % (20812)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.50  % (20826)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.50  % (20818)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.50  % (20820)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.51  % (20828)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 2.59/0.70  % (20823)Refutation found. Thanks to Tanya!
% 2.59/0.70  % SZS status Theorem for theBenchmark
% 2.59/0.70  % SZS output start Proof for theBenchmark
% 2.59/0.70  fof(f8936,plain,(
% 2.59/0.70    $false),
% 2.59/0.70    inference(subsumption_resolution,[],[f8933,f18])).
% 2.59/0.70  fof(f18,plain,(
% 2.59/0.70    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 2.59/0.70    inference(cnf_transformation,[],[f14])).
% 2.59/0.70  fof(f14,plain,(
% 2.59/0.70    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 2.59/0.70    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f13])).
% 2.59/0.70  fof(f13,plain,(
% 2.59/0.70    ? [X0,X1,X2] : (~r1_xboole_0(X1,k4_xboole_0(X0,X2)) & r1_xboole_0(X0,k4_xboole_0(X1,X2))) => (~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 2.59/0.70    introduced(choice_axiom,[])).
% 2.59/0.71  fof(f12,plain,(
% 2.59/0.71    ? [X0,X1,X2] : (~r1_xboole_0(X1,k4_xboole_0(X0,X2)) & r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 2.59/0.71    inference(ennf_transformation,[],[f11])).
% 2.59/0.72  fof(f11,negated_conjecture,(
% 2.59/0.72    ~! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 2.59/0.72    inference(negated_conjecture,[],[f10])).
% 2.59/0.72  fof(f10,conjecture,(
% 2.59/0.72    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 2.59/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_xboole_1)).
% 2.59/0.72  fof(f8933,plain,(
% 2.59/0.72    r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 2.59/0.72    inference(trivial_inequality_removal,[],[f8848])).
% 2.59/0.72  fof(f8848,plain,(
% 2.59/0.72    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 2.59/0.72    inference(superposition,[],[f32,f8749])).
% 2.59/0.72  fof(f8749,plain,(
% 2.59/0.72    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2)))),
% 2.59/0.72    inference(forward_demodulation,[],[f8748,f37])).
% 2.59/0.72  fof(f37,plain,(
% 2.59/0.72    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 2.59/0.72    inference(forward_demodulation,[],[f30,f20])).
% 2.59/0.72  fof(f20,plain,(
% 2.59/0.72    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.59/0.72    inference(cnf_transformation,[],[f5])).
% 2.59/0.72  fof(f5,axiom,(
% 2.59/0.72    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.59/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 2.59/0.72  fof(f30,plain,(
% 2.59/0.72    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 2.59/0.72    inference(definition_unfolding,[],[f19,f22])).
% 2.59/0.72  fof(f22,plain,(
% 2.59/0.72    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.59/0.72    inference(cnf_transformation,[],[f7])).
% 2.59/0.72  fof(f7,axiom,(
% 2.59/0.72    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.59/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.59/0.72  fof(f19,plain,(
% 2.59/0.72    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 2.59/0.72    inference(cnf_transformation,[],[f3])).
% 2.59/0.72  fof(f3,axiom,(
% 2.59/0.72    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 2.59/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 2.59/0.72  fof(f8748,plain,(
% 2.59/0.72    k4_xboole_0(sK1,sK1) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2)))),
% 2.59/0.72    inference(forward_demodulation,[],[f8353,f507])).
% 2.59/0.72  fof(f507,plain,(
% 2.59/0.72    ( ! [X10,X11] : (k4_xboole_0(X10,k4_xboole_0(X11,X10)) = X10) )),
% 2.59/0.72    inference(forward_demodulation,[],[f478,f20])).
% 2.59/0.72  fof(f478,plain,(
% 2.59/0.72    ( ! [X10,X11] : (k4_xboole_0(X10,k4_xboole_0(X11,X10)) = k4_xboole_0(X10,k1_xboole_0)) )),
% 2.59/0.72    inference(superposition,[],[f31,f128])).
% 2.59/0.72  fof(f128,plain,(
% 2.59/0.72    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 2.59/0.72    inference(superposition,[],[f34,f43])).
% 2.59/0.72  fof(f43,plain,(
% 2.59/0.72    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)) )),
% 2.59/0.72    inference(resolution,[],[f27,f21])).
% 2.59/0.72  fof(f21,plain,(
% 2.59/0.72    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.59/0.72    inference(cnf_transformation,[],[f4])).
% 2.59/0.72  fof(f4,axiom,(
% 2.59/0.72    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.59/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.59/0.72  fof(f27,plain,(
% 2.59/0.72    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 2.59/0.72    inference(cnf_transformation,[],[f16])).
% 2.59/0.72  fof(f16,plain,(
% 2.59/0.72    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 2.59/0.72    inference(nnf_transformation,[],[f2])).
% 2.59/0.72  fof(f2,axiom,(
% 2.59/0.72    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 2.59/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 2.59/0.72  fof(f34,plain,(
% 2.59/0.72    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 2.59/0.72    inference(definition_unfolding,[],[f28,f22,f22])).
% 2.59/0.72  fof(f28,plain,(
% 2.59/0.72    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 2.59/0.72    inference(cnf_transformation,[],[f8])).
% 2.59/0.72  fof(f8,axiom,(
% 2.59/0.72    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 2.59/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 2.59/0.72  fof(f31,plain,(
% 2.59/0.72    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 2.59/0.72    inference(definition_unfolding,[],[f23,f22])).
% 2.59/0.72  fof(f23,plain,(
% 2.59/0.72    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.59/0.72    inference(cnf_transformation,[],[f6])).
% 2.59/0.72  fof(f6,axiom,(
% 2.59/0.72    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.59/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 2.59/0.72  fof(f8353,plain,(
% 2.59/0.72    k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)))),
% 2.59/0.72    inference(superposition,[],[f220,f2945])).
% 2.59/0.72  fof(f2945,plain,(
% 2.59/0.72    ( ! [X7] : (k4_xboole_0(sK0,X7) = k4_xboole_0(sK0,k4_xboole_0(X7,k4_xboole_0(sK1,sK2)))) )),
% 2.59/0.72    inference(forward_demodulation,[],[f2876,f31])).
% 2.59/0.72  fof(f2876,plain,(
% 2.59/0.72    ( ! [X7] : (k4_xboole_0(sK0,k4_xboole_0(X7,k4_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X7)))) )),
% 2.59/0.72    inference(superposition,[],[f31,f283])).
% 2.59/0.72  fof(f283,plain,(
% 2.59/0.72    ( ! [X20] : (k4_xboole_0(sK0,k4_xboole_0(sK0,X20)) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X20,k4_xboole_0(sK1,sK2))))) )),
% 2.59/0.72    inference(forward_demodulation,[],[f282,f20])).
% 2.59/0.72  fof(f282,plain,(
% 2.59/0.72    ( ! [X20] : (k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X20,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X20,k1_xboole_0)))) )),
% 2.59/0.72    inference(forward_demodulation,[],[f281,f37])).
% 2.59/0.72  fof(f281,plain,(
% 2.59/0.72    ( ! [X20] : (k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X20,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X20,k4_xboole_0(sK0,sK0))))) )),
% 2.59/0.72    inference(forward_demodulation,[],[f214,f34])).
% 2.59/0.72  fof(f214,plain,(
% 2.59/0.72    ( ! [X20] : (k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X20,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,X20)),k4_xboole_0(sK0,sK0))) )),
% 2.59/0.72    inference(superposition,[],[f35,f104])).
% 2.59/0.72  fof(f104,plain,(
% 2.59/0.72    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 2.59/0.72    inference(forward_demodulation,[],[f91,f20])).
% 2.59/0.72  fof(f91,plain,(
% 2.59/0.72    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k1_xboole_0)),
% 2.59/0.72    inference(superposition,[],[f31,f70])).
% 2.59/0.72  fof(f70,plain,(
% 2.59/0.72    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 2.59/0.72    inference(resolution,[],[f33,f17])).
% 2.59/0.72  fof(f17,plain,(
% 2.59/0.72    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 2.59/0.72    inference(cnf_transformation,[],[f14])).
% 2.59/0.72  fof(f33,plain,(
% 2.59/0.72    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.59/0.72    inference(definition_unfolding,[],[f24,f22])).
% 2.59/0.72  fof(f24,plain,(
% 2.59/0.72    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 2.59/0.72    inference(cnf_transformation,[],[f15])).
% 2.59/0.72  fof(f15,plain,(
% 2.59/0.72    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 2.59/0.72    inference(nnf_transformation,[],[f1])).
% 2.59/0.72  fof(f1,axiom,(
% 2.59/0.72    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.59/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 2.59/0.72  fof(f35,plain,(
% 2.59/0.72    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) )),
% 2.59/0.72    inference(definition_unfolding,[],[f29,f22,f22,f22])).
% 2.59/0.72  fof(f29,plain,(
% 2.59/0.72    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 2.59/0.72    inference(cnf_transformation,[],[f9])).
% 2.59/0.72  fof(f9,axiom,(
% 2.59/0.72    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 2.59/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_xboole_1)).
% 2.59/0.72  fof(f220,plain,(
% 2.59/0.72    ( ! [X4,X5,X3] : (k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,k4_xboole_0(X3,k4_xboole_0(X3,X5))))) = k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,X5)))) )),
% 2.59/0.72    inference(superposition,[],[f35,f34])).
% 2.59/0.72  fof(f32,plain,(
% 2.59/0.72    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 2.59/0.72    inference(definition_unfolding,[],[f25,f22])).
% 2.59/0.72  fof(f25,plain,(
% 2.59/0.72    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 2.59/0.72    inference(cnf_transformation,[],[f15])).
% 2.59/0.72  % SZS output end Proof for theBenchmark
% 2.59/0.72  % (20823)------------------------------
% 2.59/0.72  % (20823)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.59/0.72  % (20823)Termination reason: Refutation
% 2.59/0.72  
% 2.59/0.72  % (20823)Memory used [KB]: 5500
% 2.59/0.72  % (20823)Time elapsed: 0.270 s
% 2.59/0.72  % (20823)------------------------------
% 2.59/0.72  % (20823)------------------------------
% 2.59/0.72  % (20810)Success in time 0.358 s
%------------------------------------------------------------------------------
