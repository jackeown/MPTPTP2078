%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:31 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 142 expanded)
%              Number of leaves         :   11 (  47 expanded)
%              Depth                    :   17
%              Number of atoms          :   74 ( 168 expanded)
%              Number of equality atoms :   52 ( 131 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2699,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f2698])).

fof(f2698,plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(superposition,[],[f2457,f95])).

fof(f95,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(X3,k2_xboole_0(X3,X2)) ),
    inference(superposition,[],[f62,f20])).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f62,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,X5)) ),
    inference(forward_demodulation,[],[f56,f21])).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f56,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,X6))) ),
    inference(superposition,[],[f27,f33])).

fof(f33,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f28,f19])).

fof(f19,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f28,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f18,f22])).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f18,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f27,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f2457,plain,(
    k1_xboole_0 != k4_xboole_0(sK1,k2_xboole_0(sK1,sK2)) ),
    inference(backward_demodulation,[],[f204,f2456])).

fof(f2456,plain,(
    k2_xboole_0(sK2,k4_xboole_0(sK1,sK0)) = k2_xboole_0(sK1,sK2) ),
    inference(forward_demodulation,[],[f2455,f20])).

fof(f2455,plain,(
    k2_xboole_0(sK2,k4_xboole_0(sK1,sK0)) = k2_xboole_0(sK2,sK1) ),
    inference(forward_demodulation,[],[f2439,f21])).

fof(f2439,plain,(
    k2_xboole_0(sK2,k4_xboole_0(sK1,sK0)) = k2_xboole_0(sK2,k4_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f58,f2393])).

fof(f2393,plain,(
    k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k2_xboole_0(sK0,sK2)) ),
    inference(forward_demodulation,[],[f2377,f20])).

fof(f2377,plain,(
    k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k2_xboole_0(sK2,sK0)) ),
    inference(superposition,[],[f2301,f27])).

fof(f2301,plain,(
    k4_xboole_0(sK1,sK2) = k4_xboole_0(k4_xboole_0(sK1,sK2),sK0) ),
    inference(superposition,[],[f2224,f79])).

fof(f79,plain,(
    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f69,f19])).

fof(f69,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f29,f47])).

fof(f47,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) ),
    inference(resolution,[],[f31,f16])).

fof(f16,plain,(
    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
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

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f23,f22])).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f2224,plain,(
    ! [X4,X3] : k4_xboole_0(X3,k4_xboole_0(X4,X3)) = X3 ),
    inference(forward_demodulation,[],[f2105,f19])).

fof(f2105,plain,(
    ! [X4,X3] : k4_xboole_0(X3,k1_xboole_0) = k4_xboole_0(X3,k4_xboole_0(X4,X3)) ),
    inference(superposition,[],[f189,f62])).

fof(f189,plain,(
    ! [X4,X2,X3] : k4_xboole_0(X2,k4_xboole_0(X3,X4)) = k4_xboole_0(X2,k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X2,X3),X4))) ),
    inference(forward_demodulation,[],[f188,f51])).

fof(f51,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[],[f27,f19])).

fof(f188,plain,(
    ! [X4,X2,X3] : k4_xboole_0(X2,k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X2,X3),X4))) = k4_xboole_0(X2,k2_xboole_0(k1_xboole_0,k4_xboole_0(X3,X4))) ),
    inference(forward_demodulation,[],[f155,f33])).

fof(f155,plain,(
    ! [X4,X2,X3] : k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X2,X2),k4_xboole_0(X3,X4))) = k4_xboole_0(X2,k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X2,X3),X4))) ),
    inference(superposition,[],[f34,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) ),
    inference(backward_demodulation,[],[f32,f27])).

fof(f32,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f26,f22,f22])).

fof(f26,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f58,plain,(
    ! [X4,X2,X3] : k2_xboole_0(X4,k4_xboole_0(X2,X3)) = k2_xboole_0(X4,k4_xboole_0(X2,k2_xboole_0(X3,X4))) ),
    inference(superposition,[],[f21,f27])).

fof(f204,plain,(
    k1_xboole_0 != k4_xboole_0(sK1,k2_xboole_0(sK2,k4_xboole_0(sK1,sK0))) ),
    inference(forward_demodulation,[],[f163,f20])).

fof(f163,plain,(
    k1_xboole_0 != k4_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK1,sK0),sK2)) ),
    inference(superposition,[],[f40,f34])).

fof(f40,plain,(
    k1_xboole_0 != k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))) ),
    inference(resolution,[],[f30,f17])).

fof(f17,plain,(
    ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f25,f22])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:29:20 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.44  % (12166)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.47  % (12156)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.47  % (12155)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.47  % (12162)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.48  % (12163)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.48  % (12164)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.48  % (12150)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.48  % (12151)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.48  % (12149)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.49  % (12154)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.49  % (12167)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.49  % (12161)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.49  % (12158)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.50  % (12165)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.50  % (12152)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.51  % (12159)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.51  % (12157)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.52  % (12160)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.57  % (12150)Refutation found. Thanks to Tanya!
% 0.22/0.57  % SZS status Theorem for theBenchmark
% 0.22/0.57  % SZS output start Proof for theBenchmark
% 0.22/0.57  fof(f2699,plain,(
% 0.22/0.57    $false),
% 0.22/0.57    inference(trivial_inequality_removal,[],[f2698])).
% 0.22/0.57  fof(f2698,plain,(
% 0.22/0.57    k1_xboole_0 != k1_xboole_0),
% 0.22/0.57    inference(superposition,[],[f2457,f95])).
% 0.22/0.57  fof(f95,plain,(
% 0.22/0.57    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(X3,k2_xboole_0(X3,X2))) )),
% 0.22/0.57    inference(superposition,[],[f62,f20])).
% 0.22/0.57  fof(f20,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f1])).
% 0.22/0.57  fof(f1,axiom,(
% 0.22/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.22/0.57  fof(f62,plain,(
% 0.22/0.57    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,X5))) )),
% 0.22/0.57    inference(forward_demodulation,[],[f56,f21])).
% 0.22/0.57  fof(f21,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f4])).
% 0.22/0.57  fof(f4,axiom,(
% 0.22/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.22/0.57  fof(f56,plain,(
% 0.22/0.57    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,X6)))) )),
% 0.22/0.57    inference(superposition,[],[f27,f33])).
% 0.22/0.57  fof(f33,plain,(
% 0.22/0.57    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.22/0.57    inference(backward_demodulation,[],[f28,f19])).
% 0.22/0.57  fof(f19,plain,(
% 0.22/0.57    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.57    inference(cnf_transformation,[],[f5])).
% 0.22/0.57  fof(f5,axiom,(
% 0.22/0.57    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.22/0.57  fof(f28,plain,(
% 0.22/0.57    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.22/0.57    inference(definition_unfolding,[],[f18,f22])).
% 0.22/0.57  fof(f22,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f8])).
% 0.22/0.57  fof(f8,axiom,(
% 0.22/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.57  fof(f18,plain,(
% 0.22/0.57    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f3])).
% 0.22/0.57  fof(f3,axiom,(
% 0.22/0.57    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.22/0.57  fof(f27,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f6])).
% 0.22/0.57  fof(f6,axiom,(
% 0.22/0.57    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.22/0.57  fof(f2457,plain,(
% 0.22/0.57    k1_xboole_0 != k4_xboole_0(sK1,k2_xboole_0(sK1,sK2))),
% 0.22/0.57    inference(backward_demodulation,[],[f204,f2456])).
% 0.22/0.57  fof(f2456,plain,(
% 0.22/0.57    k2_xboole_0(sK2,k4_xboole_0(sK1,sK0)) = k2_xboole_0(sK1,sK2)),
% 0.22/0.57    inference(forward_demodulation,[],[f2455,f20])).
% 0.22/0.57  fof(f2455,plain,(
% 0.22/0.57    k2_xboole_0(sK2,k4_xboole_0(sK1,sK0)) = k2_xboole_0(sK2,sK1)),
% 0.22/0.57    inference(forward_demodulation,[],[f2439,f21])).
% 0.22/0.57  fof(f2439,plain,(
% 0.22/0.57    k2_xboole_0(sK2,k4_xboole_0(sK1,sK0)) = k2_xboole_0(sK2,k4_xboole_0(sK1,sK2))),
% 0.22/0.57    inference(superposition,[],[f58,f2393])).
% 0.22/0.57  fof(f2393,plain,(
% 0.22/0.57    k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k2_xboole_0(sK0,sK2))),
% 0.22/0.57    inference(forward_demodulation,[],[f2377,f20])).
% 0.22/0.57  fof(f2377,plain,(
% 0.22/0.57    k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k2_xboole_0(sK2,sK0))),
% 0.22/0.57    inference(superposition,[],[f2301,f27])).
% 0.22/0.57  fof(f2301,plain,(
% 0.22/0.57    k4_xboole_0(sK1,sK2) = k4_xboole_0(k4_xboole_0(sK1,sK2),sK0)),
% 0.22/0.57    inference(superposition,[],[f2224,f79])).
% 0.22/0.57  fof(f79,plain,(
% 0.22/0.57    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.22/0.57    inference(forward_demodulation,[],[f69,f19])).
% 0.22/0.57  fof(f69,plain,(
% 0.22/0.57    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k1_xboole_0)),
% 0.22/0.57    inference(superposition,[],[f29,f47])).
% 0.22/0.57  fof(f47,plain,(
% 0.22/0.57    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 0.22/0.57    inference(resolution,[],[f31,f16])).
% 0.22/0.57  fof(f16,plain,(
% 0.22/0.57    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.22/0.57    inference(cnf_transformation,[],[f14])).
% 0.22/0.57  fof(f14,plain,(
% 0.22/0.57    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.22/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f13])).
% 0.22/0.57  fof(f13,plain,(
% 0.22/0.57    ? [X0,X1,X2] : (~r1_xboole_0(X1,k4_xboole_0(X0,X2)) & r1_xboole_0(X0,k4_xboole_0(X1,X2))) => (~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f12,plain,(
% 0.22/0.57    ? [X0,X1,X2] : (~r1_xboole_0(X1,k4_xboole_0(X0,X2)) & r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 0.22/0.57    inference(ennf_transformation,[],[f11])).
% 0.22/0.57  fof(f11,negated_conjecture,(
% 0.22/0.57    ~! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 0.22/0.57    inference(negated_conjecture,[],[f10])).
% 0.22/0.57  fof(f10,conjecture,(
% 0.22/0.57    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_xboole_1)).
% 0.22/0.57  fof(f31,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.57    inference(definition_unfolding,[],[f24,f22])).
% 0.22/0.57  fof(f24,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f15])).
% 0.22/0.57  fof(f15,plain,(
% 0.22/0.57    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.22/0.57    inference(nnf_transformation,[],[f2])).
% 0.22/0.57  fof(f2,axiom,(
% 0.22/0.57    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.22/0.57  fof(f29,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.22/0.57    inference(definition_unfolding,[],[f23,f22])).
% 0.22/0.57  fof(f23,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f7])).
% 0.22/0.57  fof(f7,axiom,(
% 0.22/0.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.22/0.57  fof(f2224,plain,(
% 0.22/0.57    ( ! [X4,X3] : (k4_xboole_0(X3,k4_xboole_0(X4,X3)) = X3) )),
% 0.22/0.57    inference(forward_demodulation,[],[f2105,f19])).
% 0.22/0.57  fof(f2105,plain,(
% 0.22/0.57    ( ! [X4,X3] : (k4_xboole_0(X3,k1_xboole_0) = k4_xboole_0(X3,k4_xboole_0(X4,X3))) )),
% 0.22/0.57    inference(superposition,[],[f189,f62])).
% 0.22/0.57  fof(f189,plain,(
% 0.22/0.57    ( ! [X4,X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X3,X4)) = k4_xboole_0(X2,k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X2,X3),X4)))) )),
% 0.22/0.57    inference(forward_demodulation,[],[f188,f51])).
% 0.22/0.57  fof(f51,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1))) )),
% 0.22/0.57    inference(superposition,[],[f27,f19])).
% 0.22/0.57  fof(f188,plain,(
% 0.22/0.57    ( ! [X4,X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X2,X3),X4))) = k4_xboole_0(X2,k2_xboole_0(k1_xboole_0,k4_xboole_0(X3,X4)))) )),
% 0.22/0.57    inference(forward_demodulation,[],[f155,f33])).
% 0.22/0.57  fof(f155,plain,(
% 0.22/0.57    ( ! [X4,X2,X3] : (k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X2,X2),k4_xboole_0(X3,X4))) = k4_xboole_0(X2,k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X2,X3),X4)))) )),
% 0.22/0.57    inference(superposition,[],[f34,f34])).
% 0.22/0.57  fof(f34,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))) )),
% 0.22/0.57    inference(backward_demodulation,[],[f32,f27])).
% 0.22/0.57  fof(f32,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 0.22/0.57    inference(definition_unfolding,[],[f26,f22,f22])).
% 0.22/0.57  fof(f26,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f9])).
% 0.22/0.57  fof(f9,axiom,(
% 0.22/0.57    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 0.22/0.57  fof(f58,plain,(
% 0.22/0.57    ( ! [X4,X2,X3] : (k2_xboole_0(X4,k4_xboole_0(X2,X3)) = k2_xboole_0(X4,k4_xboole_0(X2,k2_xboole_0(X3,X4)))) )),
% 0.22/0.57    inference(superposition,[],[f21,f27])).
% 0.22/0.57  fof(f204,plain,(
% 0.22/0.57    k1_xboole_0 != k4_xboole_0(sK1,k2_xboole_0(sK2,k4_xboole_0(sK1,sK0)))),
% 0.22/0.57    inference(forward_demodulation,[],[f163,f20])).
% 0.22/0.57  fof(f163,plain,(
% 0.22/0.57    k1_xboole_0 != k4_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK1,sK0),sK2))),
% 0.22/0.57    inference(superposition,[],[f40,f34])).
% 0.22/0.57  fof(f40,plain,(
% 0.22/0.57    k1_xboole_0 != k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2)))),
% 0.22/0.57    inference(resolution,[],[f30,f17])).
% 0.22/0.57  fof(f17,plain,(
% 0.22/0.57    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 0.22/0.57    inference(cnf_transformation,[],[f14])).
% 0.22/0.57  fof(f30,plain,(
% 0.22/0.57    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.57    inference(definition_unfolding,[],[f25,f22])).
% 0.22/0.57  fof(f25,plain,(
% 0.22/0.57    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.22/0.57    inference(cnf_transformation,[],[f15])).
% 0.22/0.57  % SZS output end Proof for theBenchmark
% 0.22/0.57  % (12150)------------------------------
% 0.22/0.57  % (12150)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (12150)Termination reason: Refutation
% 0.22/0.57  
% 0.22/0.57  % (12150)Memory used [KB]: 3582
% 0.22/0.57  % (12150)Time elapsed: 0.148 s
% 0.22/0.57  % (12150)------------------------------
% 0.22/0.57  % (12150)------------------------------
% 0.22/0.57  % (12146)Success in time 0.213 s
%------------------------------------------------------------------------------
