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
% DateTime   : Thu Dec  3 12:30:26 EST 2020

% Result     : Theorem 1.47s
% Output     : Refutation 1.47s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 115 expanded)
%              Number of leaves         :   11 (  35 expanded)
%              Depth                    :   16
%              Number of atoms          :   81 ( 179 expanded)
%              Number of equality atoms :   46 (  91 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4814,plain,(
    $false ),
    inference(subsumption_resolution,[],[f41,f4813])).

fof(f4813,plain,(
    k1_xboole_0 = k3_xboole_0(sK0,sK2) ),
    inference(forward_demodulation,[],[f4806,f62])).

fof(f62,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(X1,X1) ),
    inference(backward_demodulation,[],[f44,f57])).

fof(f57,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f49,f28])).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f49,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f43,f23])).

fof(f23,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f43,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f29,f23])).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f44,plain,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k4_xboole_0(X1,X1) ),
    inference(superposition,[],[f29,f24])).

fof(f24,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f4806,plain,(
    k3_xboole_0(sK0,sK2) = k4_xboole_0(sK0,sK0) ),
    inference(superposition,[],[f29,f4774])).

fof(f4774,plain,(
    sK0 = k4_xboole_0(sK0,sK2) ),
    inference(superposition,[],[f4660,f371])).

fof(f371,plain,(
    sK0 = k3_xboole_0(sK1,sK0) ),
    inference(superposition,[],[f235,f39])).

fof(f39,plain,(
    sK0 = k3_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f30,f20])).

fof(f20,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    & r1_xboole_0(sK1,sK2)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X0,X2)
        & r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
   => ( ~ r1_xboole_0(sK0,sK2)
      & r1_xboole_0(sK1,sK2)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X2)
      & r1_xboole_0(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X2)
      & r1_xboole_0(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X1,X2)
          & r1_tarski(X0,X1) )
       => r1_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f235,plain,(
    ! [X2,X1] : k3_xboole_0(X2,X1) = k3_xboole_0(X1,k3_xboole_0(X2,X1)) ),
    inference(superposition,[],[f108,f28])).

fof(f108,plain,(
    ! [X4,X3] : k3_xboole_0(X3,X4) = k3_xboole_0(X3,k3_xboole_0(X3,X4)) ),
    inference(forward_demodulation,[],[f102,f29])).

fof(f102,plain,(
    ! [X4,X3] : k3_xboole_0(X3,k3_xboole_0(X3,X4)) = k4_xboole_0(X3,k4_xboole_0(X3,X4)) ),
    inference(superposition,[],[f29,f92])).

fof(f92,plain,(
    ! [X2,X3] : k4_xboole_0(X2,X3) = k4_xboole_0(X2,k3_xboole_0(X2,X3)) ),
    inference(backward_demodulation,[],[f45,f84])).

fof(f84,plain,(
    ! [X2,X3] : k4_xboole_0(X2,X3) = k3_xboole_0(X2,k4_xboole_0(X2,X3)) ),
    inference(superposition,[],[f38,f28])).

fof(f38,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k3_xboole_0(k4_xboole_0(X1,X2),X1) ),
    inference(resolution,[],[f30,f26])).

fof(f26,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f45,plain,(
    ! [X2,X3] : k3_xboole_0(X2,k4_xboole_0(X2,X3)) = k4_xboole_0(X2,k3_xboole_0(X2,X3)) ),
    inference(superposition,[],[f29,f29])).

fof(f4660,plain,(
    ! [X19] : k3_xboole_0(sK1,X19) = k4_xboole_0(k3_xboole_0(sK1,X19),sK2) ),
    inference(forward_demodulation,[],[f4561,f29])).

fof(f4561,plain,(
    ! [X19] : k4_xboole_0(sK1,k4_xboole_0(sK1,X19)) = k4_xboole_0(k3_xboole_0(sK1,X19),sK2) ),
    inference(superposition,[],[f473,f667])).

fof(f667,plain,(
    ! [X0] : k4_xboole_0(sK1,X0) = k4_xboole_0(sK1,k2_xboole_0(X0,sK2)) ),
    inference(superposition,[],[f481,f27])).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f481,plain,(
    ! [X32] : k4_xboole_0(sK1,k2_xboole_0(sK2,X32)) = k4_xboole_0(sK1,X32) ),
    inference(superposition,[],[f33,f107])).

fof(f107,plain,(
    sK1 = k4_xboole_0(sK1,sK2) ),
    inference(forward_demodulation,[],[f98,f24])).

fof(f98,plain,(
    k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f92,f40])).

fof(f40,plain,(
    k1_xboole_0 = k3_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f31,f21])).

fof(f21,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f31,plain,(
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

fof(f33,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f473,plain,(
    ! [X12,X10,X11] : k4_xboole_0(X10,k2_xboole_0(k4_xboole_0(X10,X11),X12)) = k4_xboole_0(k3_xboole_0(X10,X11),X12) ),
    inference(superposition,[],[f33,f29])).

fof(f41,plain,(
    k1_xboole_0 != k3_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f32,f22])).

fof(f22,plain,(
    ~ r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 13:05:11 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.42  % (2725)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.42  % (2725)Refutation not found, incomplete strategy% (2725)------------------------------
% 0.22/0.42  % (2725)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.42  % (2725)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.42  
% 0.22/0.42  % (2725)Memory used [KB]: 10618
% 0.22/0.42  % (2725)Time elapsed: 0.004 s
% 0.22/0.42  % (2725)------------------------------
% 0.22/0.42  % (2725)------------------------------
% 0.22/0.46  % (2722)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.50  % (2719)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.51  % (2717)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.51  % (2715)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.52  % (2726)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.52  % (2716)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.52  % (2718)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.52  % (2727)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.52  % (2730)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 1.34/0.52  % (2729)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 1.34/0.53  % (2728)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 1.34/0.53  % (2721)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 1.34/0.53  % (2731)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 1.34/0.53  % (2723)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 1.34/0.53  % (2724)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 1.34/0.53  % (2720)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 1.34/0.53  % (2714)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 1.47/0.62  % (2730)Refutation found. Thanks to Tanya!
% 1.47/0.62  % SZS status Theorem for theBenchmark
% 1.47/0.62  % SZS output start Proof for theBenchmark
% 1.47/0.62  fof(f4814,plain,(
% 1.47/0.62    $false),
% 1.47/0.62    inference(subsumption_resolution,[],[f41,f4813])).
% 1.47/0.62  fof(f4813,plain,(
% 1.47/0.62    k1_xboole_0 = k3_xboole_0(sK0,sK2)),
% 1.47/0.62    inference(forward_demodulation,[],[f4806,f62])).
% 1.47/0.62  fof(f62,plain,(
% 1.47/0.62    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(X1,X1)) )),
% 1.47/0.62    inference(backward_demodulation,[],[f44,f57])).
% 1.47/0.62  fof(f57,plain,(
% 1.47/0.62    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)) )),
% 1.47/0.62    inference(superposition,[],[f49,f28])).
% 1.47/0.62  fof(f28,plain,(
% 1.47/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.47/0.62    inference(cnf_transformation,[],[f2])).
% 1.47/0.62  fof(f2,axiom,(
% 1.47/0.62    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.47/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.47/0.62  fof(f49,plain,(
% 1.47/0.62    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 1.47/0.62    inference(forward_demodulation,[],[f43,f23])).
% 1.47/0.62  fof(f23,plain,(
% 1.47/0.62    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.47/0.62    inference(cnf_transformation,[],[f10])).
% 1.47/0.62  fof(f10,axiom,(
% 1.47/0.62    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 1.47/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 1.47/0.62  fof(f43,plain,(
% 1.47/0.62    ( ! [X0] : (k4_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,X0)) )),
% 1.47/0.62    inference(superposition,[],[f29,f23])).
% 1.47/0.62  fof(f29,plain,(
% 1.47/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.47/0.62    inference(cnf_transformation,[],[f9])).
% 1.47/0.62  fof(f9,axiom,(
% 1.47/0.62    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.47/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.47/0.62  fof(f44,plain,(
% 1.47/0.62    ( ! [X1] : (k3_xboole_0(X1,k1_xboole_0) = k4_xboole_0(X1,X1)) )),
% 1.47/0.62    inference(superposition,[],[f29,f24])).
% 1.47/0.62  fof(f24,plain,(
% 1.47/0.62    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.47/0.62    inference(cnf_transformation,[],[f7])).
% 1.47/0.62  fof(f7,axiom,(
% 1.47/0.62    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.47/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.47/0.62  fof(f4806,plain,(
% 1.47/0.62    k3_xboole_0(sK0,sK2) = k4_xboole_0(sK0,sK0)),
% 1.47/0.62    inference(superposition,[],[f29,f4774])).
% 1.47/0.62  fof(f4774,plain,(
% 1.47/0.62    sK0 = k4_xboole_0(sK0,sK2)),
% 1.47/0.62    inference(superposition,[],[f4660,f371])).
% 1.47/0.62  fof(f371,plain,(
% 1.47/0.62    sK0 = k3_xboole_0(sK1,sK0)),
% 1.47/0.62    inference(superposition,[],[f235,f39])).
% 1.47/0.62  fof(f39,plain,(
% 1.47/0.62    sK0 = k3_xboole_0(sK0,sK1)),
% 1.47/0.62    inference(resolution,[],[f30,f20])).
% 1.47/0.62  fof(f20,plain,(
% 1.47/0.62    r1_tarski(sK0,sK1)),
% 1.47/0.62    inference(cnf_transformation,[],[f18])).
% 1.47/0.62  fof(f18,plain,(
% 1.47/0.62    ~r1_xboole_0(sK0,sK2) & r1_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1)),
% 1.47/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f17])).
% 1.47/0.62  fof(f17,plain,(
% 1.47/0.62    ? [X0,X1,X2] : (~r1_xboole_0(X0,X2) & r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => (~r1_xboole_0(sK0,sK2) & r1_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1))),
% 1.47/0.62    introduced(choice_axiom,[])).
% 1.47/0.62  fof(f15,plain,(
% 1.47/0.62    ? [X0,X1,X2] : (~r1_xboole_0(X0,X2) & r1_xboole_0(X1,X2) & r1_tarski(X0,X1))),
% 1.47/0.62    inference(flattening,[],[f14])).
% 1.47/0.62  fof(f14,plain,(
% 1.47/0.62    ? [X0,X1,X2] : (~r1_xboole_0(X0,X2) & (r1_xboole_0(X1,X2) & r1_tarski(X0,X1)))),
% 1.47/0.62    inference(ennf_transformation,[],[f12])).
% 1.47/0.62  fof(f12,negated_conjecture,(
% 1.47/0.62    ~! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 1.47/0.62    inference(negated_conjecture,[],[f11])).
% 1.47/0.62  fof(f11,conjecture,(
% 1.47/0.62    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 1.47/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).
% 1.47/0.62  fof(f30,plain,(
% 1.47/0.62    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.47/0.62    inference(cnf_transformation,[],[f16])).
% 1.47/0.62  fof(f16,plain,(
% 1.47/0.62    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.47/0.62    inference(ennf_transformation,[],[f5])).
% 1.47/0.62  fof(f5,axiom,(
% 1.47/0.62    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.47/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.47/0.62  fof(f235,plain,(
% 1.47/0.62    ( ! [X2,X1] : (k3_xboole_0(X2,X1) = k3_xboole_0(X1,k3_xboole_0(X2,X1))) )),
% 1.47/0.62    inference(superposition,[],[f108,f28])).
% 1.47/0.62  fof(f108,plain,(
% 1.47/0.62    ( ! [X4,X3] : (k3_xboole_0(X3,X4) = k3_xboole_0(X3,k3_xboole_0(X3,X4))) )),
% 1.47/0.62    inference(forward_demodulation,[],[f102,f29])).
% 1.47/0.62  fof(f102,plain,(
% 1.47/0.62    ( ! [X4,X3] : (k3_xboole_0(X3,k3_xboole_0(X3,X4)) = k4_xboole_0(X3,k4_xboole_0(X3,X4))) )),
% 1.47/0.62    inference(superposition,[],[f29,f92])).
% 1.47/0.62  fof(f92,plain,(
% 1.47/0.62    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k4_xboole_0(X2,k3_xboole_0(X2,X3))) )),
% 1.47/0.62    inference(backward_demodulation,[],[f45,f84])).
% 1.47/0.62  fof(f84,plain,(
% 1.47/0.62    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k3_xboole_0(X2,k4_xboole_0(X2,X3))) )),
% 1.47/0.62    inference(superposition,[],[f38,f28])).
% 1.47/0.62  fof(f38,plain,(
% 1.47/0.62    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k3_xboole_0(k4_xboole_0(X1,X2),X1)) )),
% 1.47/0.62    inference(resolution,[],[f30,f26])).
% 1.47/0.62  fof(f26,plain,(
% 1.47/0.62    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.47/0.62    inference(cnf_transformation,[],[f6])).
% 1.47/0.62  fof(f6,axiom,(
% 1.47/0.62    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.47/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.47/0.62  fof(f45,plain,(
% 1.47/0.62    ( ! [X2,X3] : (k3_xboole_0(X2,k4_xboole_0(X2,X3)) = k4_xboole_0(X2,k3_xboole_0(X2,X3))) )),
% 1.47/0.62    inference(superposition,[],[f29,f29])).
% 1.47/0.62  fof(f4660,plain,(
% 1.47/0.62    ( ! [X19] : (k3_xboole_0(sK1,X19) = k4_xboole_0(k3_xboole_0(sK1,X19),sK2)) )),
% 1.47/0.62    inference(forward_demodulation,[],[f4561,f29])).
% 1.47/0.62  fof(f4561,plain,(
% 1.47/0.62    ( ! [X19] : (k4_xboole_0(sK1,k4_xboole_0(sK1,X19)) = k4_xboole_0(k3_xboole_0(sK1,X19),sK2)) )),
% 1.47/0.62    inference(superposition,[],[f473,f667])).
% 1.47/0.62  fof(f667,plain,(
% 1.47/0.62    ( ! [X0] : (k4_xboole_0(sK1,X0) = k4_xboole_0(sK1,k2_xboole_0(X0,sK2))) )),
% 1.47/0.62    inference(superposition,[],[f481,f27])).
% 1.47/0.62  fof(f27,plain,(
% 1.47/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.47/0.62    inference(cnf_transformation,[],[f1])).
% 1.47/0.62  fof(f1,axiom,(
% 1.47/0.62    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.47/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.47/0.62  fof(f481,plain,(
% 1.47/0.62    ( ! [X32] : (k4_xboole_0(sK1,k2_xboole_0(sK2,X32)) = k4_xboole_0(sK1,X32)) )),
% 1.47/0.62    inference(superposition,[],[f33,f107])).
% 1.47/0.62  fof(f107,plain,(
% 1.47/0.62    sK1 = k4_xboole_0(sK1,sK2)),
% 1.47/0.62    inference(forward_demodulation,[],[f98,f24])).
% 1.47/0.62  fof(f98,plain,(
% 1.47/0.62    k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k1_xboole_0)),
% 1.47/0.62    inference(superposition,[],[f92,f40])).
% 1.47/0.62  fof(f40,plain,(
% 1.47/0.62    k1_xboole_0 = k3_xboole_0(sK1,sK2)),
% 1.47/0.62    inference(resolution,[],[f31,f21])).
% 1.47/0.62  fof(f21,plain,(
% 1.47/0.62    r1_xboole_0(sK1,sK2)),
% 1.47/0.62    inference(cnf_transformation,[],[f18])).
% 1.47/0.62  fof(f31,plain,(
% 1.47/0.62    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.47/0.62    inference(cnf_transformation,[],[f19])).
% 1.47/0.62  fof(f19,plain,(
% 1.47/0.62    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.47/0.62    inference(nnf_transformation,[],[f3])).
% 1.47/0.62  fof(f3,axiom,(
% 1.47/0.62    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.47/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.47/0.62  fof(f33,plain,(
% 1.47/0.62    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.47/0.62    inference(cnf_transformation,[],[f8])).
% 1.47/0.62  fof(f8,axiom,(
% 1.47/0.62    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.47/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 1.47/0.62  fof(f473,plain,(
% 1.47/0.62    ( ! [X12,X10,X11] : (k4_xboole_0(X10,k2_xboole_0(k4_xboole_0(X10,X11),X12)) = k4_xboole_0(k3_xboole_0(X10,X11),X12)) )),
% 1.47/0.62    inference(superposition,[],[f33,f29])).
% 1.47/0.62  fof(f41,plain,(
% 1.47/0.62    k1_xboole_0 != k3_xboole_0(sK0,sK2)),
% 1.47/0.62    inference(resolution,[],[f32,f22])).
% 1.47/0.62  fof(f22,plain,(
% 1.47/0.62    ~r1_xboole_0(sK0,sK2)),
% 1.47/0.62    inference(cnf_transformation,[],[f18])).
% 1.47/0.62  fof(f32,plain,(
% 1.47/0.62    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.47/0.62    inference(cnf_transformation,[],[f19])).
% 1.47/0.62  % SZS output end Proof for theBenchmark
% 1.47/0.62  % (2730)------------------------------
% 1.47/0.62  % (2730)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.62  % (2730)Termination reason: Refutation
% 1.47/0.62  
% 1.47/0.62  % (2730)Memory used [KB]: 8315
% 1.47/0.62  % (2730)Time elapsed: 0.196 s
% 1.47/0.62  % (2730)------------------------------
% 1.47/0.62  % (2730)------------------------------
% 1.47/0.62  % (2713)Success in time 0.261 s
%------------------------------------------------------------------------------
