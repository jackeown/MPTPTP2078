%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:31 EST 2020

% Result     : Theorem 1.47s
% Output     : Refutation 1.47s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 127 expanded)
%              Number of leaves         :   11 (  40 expanded)
%              Depth                    :   21
%              Number of atoms          :   85 ( 182 expanded)
%              Number of equality atoms :   48 ( 111 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3246,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3215,f18])).

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

fof(f3215,plain,(
    r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(superposition,[],[f3087,f2382])).

fof(f2382,plain,(
    k4_xboole_0(sK0,sK2) = k4_xboole_0(k4_xboole_0(sK0,sK2),sK1) ),
    inference(superposition,[],[f2252,f81])).

fof(f81,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[],[f29,f19])).

fof(f19,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f29,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f2252,plain,(
    k4_xboole_0(sK0,sK2) = k4_xboole_0(k4_xboole_0(sK0,sK2),k2_xboole_0(k1_xboole_0,sK1)) ),
    inference(forward_demodulation,[],[f2251,f21])).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f2251,plain,(
    k4_xboole_0(sK0,sK2) = k4_xboole_0(k4_xboole_0(sK0,sK2),k2_xboole_0(sK1,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f2250,f37])).

fof(f37,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(resolution,[],[f27,f20])).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f2250,plain,(
    k4_xboole_0(sK0,sK2) = k4_xboole_0(k4_xboole_0(sK0,sK2),k2_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK0,sK2),sK0))) ),
    inference(forward_demodulation,[],[f2249,f21])).

fof(f2249,plain,(
    k4_xboole_0(sK0,sK2) = k4_xboole_0(k4_xboole_0(sK0,sK2),k2_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK2),sK0),sK1)) ),
    inference(forward_demodulation,[],[f2238,f19])).

fof(f2238,plain,(
    k4_xboole_0(k4_xboole_0(sK0,sK2),k2_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK2),sK0),sK1)) = k4_xboole_0(k4_xboole_0(sK0,sK2),k1_xboole_0) ),
    inference(superposition,[],[f267,f2236])).

fof(f2236,plain,(
    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f2171,f27])).

fof(f2171,plain,(
    r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) ),
    inference(trivial_inequality_removal,[],[f2170])).

fof(f2170,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f94,f504])).

fof(f504,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK2,k4_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f503,f38])).

fof(f38,plain,(
    ! [X2] : k1_xboole_0 = k4_xboole_0(X2,X2) ),
    inference(resolution,[],[f27,f34])).

fof(f34,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(superposition,[],[f20,f19])).

fof(f503,plain,(
    k4_xboole_0(sK0,sK0) = k4_xboole_0(sK0,k2_xboole_0(sK2,k4_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f444,f21])).

fof(f444,plain,(
    k4_xboole_0(sK0,sK0) = k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK2)) ),
    inference(superposition,[],[f267,f153])).

fof(f153,plain,(
    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f134,f19])).

fof(f134,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f30,f67])).

fof(f67,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) ),
    inference(resolution,[],[f32,f17])).

fof(f17,plain,(
    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f24,f22])).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

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

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f23,f22])).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f94,plain,(
    ! [X12,X10,X11] :
      ( k1_xboole_0 != k4_xboole_0(X10,k2_xboole_0(X11,X12))
      | r1_tarski(k4_xboole_0(X10,X11),X12) ) ),
    inference(superposition,[],[f26,f29])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f267,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) ),
    inference(forward_demodulation,[],[f33,f29])).

fof(f33,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f28,f22,f22])).

fof(f28,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f3087,plain,(
    ! [X2,X1] : r1_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(trivial_inequality_removal,[],[f3067])).

fof(f3067,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_xboole_0(X1,k4_xboole_0(X2,X1)) ) ),
    inference(superposition,[],[f450,f87])).

fof(f87,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f29,f37])).

fof(f450,plain,(
    ! [X6,X7,X5] :
      ( k1_xboole_0 != k4_xboole_0(X5,k2_xboole_0(k4_xboole_0(X5,X6),X7))
      | r1_xboole_0(X5,k4_xboole_0(X6,X7)) ) ),
    inference(superposition,[],[f31,f267])).

fof(f31,plain,(
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
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:41:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.43  % (6923)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.46  % (6909)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.46  % (6921)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.47  % (6922)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.47  % (6913)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.47  % (6916)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.48  % (6912)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.48  % (6915)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.48  % (6925)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.49  % (6920)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.49  % (6917)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.50  % (6924)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.50  % (6927)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.50  % (6911)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.50  % (6910)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.51  % (6919)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.51  % (6918)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.52  % (6926)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 1.47/0.55  % (6922)Refutation found. Thanks to Tanya!
% 1.47/0.55  % SZS status Theorem for theBenchmark
% 1.47/0.55  % SZS output start Proof for theBenchmark
% 1.47/0.55  fof(f3246,plain,(
% 1.47/0.55    $false),
% 1.47/0.55    inference(subsumption_resolution,[],[f3215,f18])).
% 1.47/0.55  fof(f18,plain,(
% 1.47/0.55    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 1.47/0.55    inference(cnf_transformation,[],[f14])).
% 1.47/0.55  fof(f14,plain,(
% 1.47/0.55    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 1.47/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f13])).
% 1.47/0.55  fof(f13,plain,(
% 1.47/0.55    ? [X0,X1,X2] : (~r1_xboole_0(X1,k4_xboole_0(X0,X2)) & r1_xboole_0(X0,k4_xboole_0(X1,X2))) => (~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 1.47/0.55    introduced(choice_axiom,[])).
% 1.47/0.55  fof(f12,plain,(
% 1.47/0.55    ? [X0,X1,X2] : (~r1_xboole_0(X1,k4_xboole_0(X0,X2)) & r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 1.47/0.55    inference(ennf_transformation,[],[f11])).
% 1.47/0.55  fof(f11,negated_conjecture,(
% 1.47/0.55    ~! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 1.47/0.55    inference(negated_conjecture,[],[f10])).
% 1.47/0.55  fof(f10,conjecture,(
% 1.47/0.55    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 1.47/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_xboole_1)).
% 1.47/0.55  fof(f3215,plain,(
% 1.47/0.55    r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 1.47/0.55    inference(superposition,[],[f3087,f2382])).
% 1.47/0.55  fof(f2382,plain,(
% 1.47/0.55    k4_xboole_0(sK0,sK2) = k4_xboole_0(k4_xboole_0(sK0,sK2),sK1)),
% 1.47/0.55    inference(superposition,[],[f2252,f81])).
% 1.47/0.55  fof(f81,plain,(
% 1.47/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1))) )),
% 1.47/0.55    inference(superposition,[],[f29,f19])).
% 1.47/0.55  fof(f19,plain,(
% 1.47/0.55    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.47/0.55    inference(cnf_transformation,[],[f5])).
% 1.47/0.55  fof(f5,axiom,(
% 1.47/0.55    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.47/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.47/0.55  fof(f29,plain,(
% 1.47/0.55    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.47/0.55    inference(cnf_transformation,[],[f6])).
% 1.47/0.55  fof(f6,axiom,(
% 1.47/0.55    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.47/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 1.47/0.55  fof(f2252,plain,(
% 1.47/0.55    k4_xboole_0(sK0,sK2) = k4_xboole_0(k4_xboole_0(sK0,sK2),k2_xboole_0(k1_xboole_0,sK1))),
% 1.47/0.55    inference(forward_demodulation,[],[f2251,f21])).
% 1.47/0.55  fof(f21,plain,(
% 1.47/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f1])).
% 1.47/0.55  fof(f1,axiom,(
% 1.47/0.55    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.47/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.47/0.55  fof(f2251,plain,(
% 1.47/0.55    k4_xboole_0(sK0,sK2) = k4_xboole_0(k4_xboole_0(sK0,sK2),k2_xboole_0(sK1,k1_xboole_0))),
% 1.47/0.55    inference(forward_demodulation,[],[f2250,f37])).
% 1.47/0.55  fof(f37,plain,(
% 1.47/0.55    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)) )),
% 1.47/0.55    inference(resolution,[],[f27,f20])).
% 1.47/0.55  fof(f20,plain,(
% 1.47/0.55    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f4])).
% 1.47/0.55  fof(f4,axiom,(
% 1.47/0.55    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.47/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.47/0.55  fof(f27,plain,(
% 1.47/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f16])).
% 1.47/0.55  fof(f16,plain,(
% 1.47/0.55    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 1.47/0.55    inference(nnf_transformation,[],[f3])).
% 1.47/0.55  fof(f3,axiom,(
% 1.47/0.55    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 1.47/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.47/0.55  fof(f2250,plain,(
% 1.47/0.55    k4_xboole_0(sK0,sK2) = k4_xboole_0(k4_xboole_0(sK0,sK2),k2_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK0,sK2),sK0)))),
% 1.47/0.55    inference(forward_demodulation,[],[f2249,f21])).
% 1.47/0.55  fof(f2249,plain,(
% 1.47/0.55    k4_xboole_0(sK0,sK2) = k4_xboole_0(k4_xboole_0(sK0,sK2),k2_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK2),sK0),sK1))),
% 1.47/0.55    inference(forward_demodulation,[],[f2238,f19])).
% 1.47/0.55  fof(f2238,plain,(
% 1.47/0.55    k4_xboole_0(k4_xboole_0(sK0,sK2),k2_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK2),sK0),sK1)) = k4_xboole_0(k4_xboole_0(sK0,sK2),k1_xboole_0)),
% 1.47/0.55    inference(superposition,[],[f267,f2236])).
% 1.47/0.55  fof(f2236,plain,(
% 1.47/0.55    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))),
% 1.47/0.55    inference(resolution,[],[f2171,f27])).
% 1.47/0.55  fof(f2171,plain,(
% 1.47/0.55    r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))),
% 1.47/0.55    inference(trivial_inequality_removal,[],[f2170])).
% 1.47/0.55  fof(f2170,plain,(
% 1.47/0.55    k1_xboole_0 != k1_xboole_0 | r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))),
% 1.47/0.55    inference(superposition,[],[f94,f504])).
% 1.47/0.55  fof(f504,plain,(
% 1.47/0.55    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)))),
% 1.47/0.55    inference(forward_demodulation,[],[f503,f38])).
% 1.47/0.55  fof(f38,plain,(
% 1.47/0.55    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(X2,X2)) )),
% 1.47/0.55    inference(resolution,[],[f27,f34])).
% 1.47/0.55  fof(f34,plain,(
% 1.47/0.55    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 1.47/0.55    inference(superposition,[],[f20,f19])).
% 1.47/0.55  fof(f503,plain,(
% 1.47/0.55    k4_xboole_0(sK0,sK0) = k4_xboole_0(sK0,k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)))),
% 1.47/0.55    inference(forward_demodulation,[],[f444,f21])).
% 1.47/0.55  fof(f444,plain,(
% 1.47/0.55    k4_xboole_0(sK0,sK0) = k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK2))),
% 1.47/0.55    inference(superposition,[],[f267,f153])).
% 1.47/0.55  fof(f153,plain,(
% 1.47/0.55    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 1.47/0.55    inference(forward_demodulation,[],[f134,f19])).
% 1.47/0.55  fof(f134,plain,(
% 1.47/0.55    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k1_xboole_0)),
% 1.47/0.55    inference(superposition,[],[f30,f67])).
% 1.47/0.55  fof(f67,plain,(
% 1.47/0.55    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 1.47/0.55    inference(resolution,[],[f32,f17])).
% 1.47/0.55  fof(f17,plain,(
% 1.47/0.55    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 1.47/0.55    inference(cnf_transformation,[],[f14])).
% 1.47/0.55  fof(f32,plain,(
% 1.47/0.55    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.47/0.55    inference(definition_unfolding,[],[f24,f22])).
% 1.47/0.55  fof(f22,plain,(
% 1.47/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.47/0.55    inference(cnf_transformation,[],[f8])).
% 1.47/0.55  fof(f8,axiom,(
% 1.47/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.47/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.47/0.55  fof(f24,plain,(
% 1.47/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f15])).
% 1.47/0.55  fof(f15,plain,(
% 1.47/0.55    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.47/0.55    inference(nnf_transformation,[],[f2])).
% 1.47/0.55  fof(f2,axiom,(
% 1.47/0.55    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.47/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.47/0.55  fof(f30,plain,(
% 1.47/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.47/0.55    inference(definition_unfolding,[],[f23,f22])).
% 1.47/0.55  fof(f23,plain,(
% 1.47/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.47/0.55    inference(cnf_transformation,[],[f7])).
% 1.47/0.55  fof(f7,axiom,(
% 1.47/0.55    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.47/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 1.47/0.55  fof(f94,plain,(
% 1.47/0.55    ( ! [X12,X10,X11] : (k1_xboole_0 != k4_xboole_0(X10,k2_xboole_0(X11,X12)) | r1_tarski(k4_xboole_0(X10,X11),X12)) )),
% 1.47/0.55    inference(superposition,[],[f26,f29])).
% 1.47/0.55  fof(f26,plain,(
% 1.47/0.55    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,X1) | r1_tarski(X0,X1)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f16])).
% 1.47/0.55  fof(f267,plain,(
% 1.47/0.55    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))) )),
% 1.47/0.55    inference(forward_demodulation,[],[f33,f29])).
% 1.47/0.55  fof(f33,plain,(
% 1.47/0.55    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 1.47/0.55    inference(definition_unfolding,[],[f28,f22,f22])).
% 1.47/0.55  fof(f28,plain,(
% 1.47/0.55    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f9])).
% 1.47/0.55  fof(f9,axiom,(
% 1.47/0.55    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 1.47/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 1.47/0.55  fof(f3087,plain,(
% 1.47/0.55    ( ! [X2,X1] : (r1_xboole_0(X1,k4_xboole_0(X2,X1))) )),
% 1.47/0.55    inference(trivial_inequality_removal,[],[f3067])).
% 1.47/0.55  fof(f3067,plain,(
% 1.47/0.55    ( ! [X2,X1] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(X1,k4_xboole_0(X2,X1))) )),
% 1.47/0.55    inference(superposition,[],[f450,f87])).
% 1.47/0.55  fof(f87,plain,(
% 1.47/0.55    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X1,X0))) )),
% 1.47/0.55    inference(superposition,[],[f29,f37])).
% 1.47/0.55  fof(f450,plain,(
% 1.47/0.55    ( ! [X6,X7,X5] : (k1_xboole_0 != k4_xboole_0(X5,k2_xboole_0(k4_xboole_0(X5,X6),X7)) | r1_xboole_0(X5,k4_xboole_0(X6,X7))) )),
% 1.47/0.55    inference(superposition,[],[f31,f267])).
% 1.47/0.55  fof(f31,plain,(
% 1.47/0.55    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 1.47/0.55    inference(definition_unfolding,[],[f25,f22])).
% 1.47/0.55  fof(f25,plain,(
% 1.47/0.55    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.47/0.55    inference(cnf_transformation,[],[f15])).
% 1.47/0.55  % SZS output end Proof for theBenchmark
% 1.47/0.55  % (6922)------------------------------
% 1.47/0.55  % (6922)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.55  % (6922)Termination reason: Refutation
% 1.47/0.55  
% 1.47/0.55  % (6922)Memory used [KB]: 3326
% 1.47/0.55  % (6922)Time elapsed: 0.124 s
% 1.47/0.55  % (6922)------------------------------
% 1.47/0.55  % (6922)------------------------------
% 1.47/0.55  % (6906)Success in time 0.194 s
%------------------------------------------------------------------------------
