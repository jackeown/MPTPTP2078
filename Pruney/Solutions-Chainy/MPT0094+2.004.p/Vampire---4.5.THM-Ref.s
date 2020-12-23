%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:45 EST 2020

% Result     : Theorem 1.95s
% Output     : Refutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :   49 (  94 expanded)
%              Number of leaves         :   11 (  29 expanded)
%              Depth                    :   13
%              Number of atoms          :   64 ( 128 expanded)
%              Number of equality atoms :   47 (  85 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2803,plain,(
    $false ),
    inference(subsumption_resolution,[],[f33,f2744])).

fof(f2744,plain,(
    ! [X28] : k4_xboole_0(k2_xboole_0(sK1,X28),sK0) = k2_xboole_0(sK1,k4_xboole_0(X28,sK0)) ),
    inference(superposition,[],[f30,f1796])).

fof(f1796,plain,(
    sK1 = k4_xboole_0(sK1,sK0) ),
    inference(forward_demodulation,[],[f1795,f34])).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(resolution,[],[f26,f21])).

fof(f21,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f1795,plain,(
    k4_xboole_0(sK1,sK0) = k2_xboole_0(k4_xboole_0(sK1,sK1),sK1) ),
    inference(forward_demodulation,[],[f1773,f219])).

fof(f219,plain,(
    ! [X6,X7] : k4_xboole_0(X6,X7) = k2_xboole_0(k4_xboole_0(X6,X6),k4_xboole_0(X6,X7)) ),
    inference(superposition,[],[f34,f50])).

fof(f50,plain,(
    ! [X10,X9] : k4_xboole_0(k4_xboole_0(X9,X10),X9) = k4_xboole_0(X9,X9) ),
    inference(superposition,[],[f24,f34])).

fof(f24,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f1773,plain,(
    k2_xboole_0(k4_xboole_0(sK1,sK1),sK1) = k2_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK0)) ),
    inference(superposition,[],[f55,f1761])).

fof(f1761,plain,(
    sK1 = k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK1,sK1)) ),
    inference(superposition,[],[f127,f1730])).

fof(f1730,plain,(
    k4_xboole_0(sK1,sK1) = k3_xboole_0(sK1,sK0) ),
    inference(superposition,[],[f1705,f138])).

fof(f138,plain,(
    ! [X4,X5] : k4_xboole_0(X4,X4) = k4_xboole_0(k3_xboole_0(X4,X5),X4) ),
    inference(superposition,[],[f24,f122])).

fof(f122,plain,(
    ! [X4,X5] : k2_xboole_0(k3_xboole_0(X4,X5),X4) = X4 ),
    inference(superposition,[],[f34,f25])).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f1705,plain,(
    ! [X24] : k3_xboole_0(X24,sK0) = k4_xboole_0(k3_xboole_0(X24,sK0),sK1) ),
    inference(superposition,[],[f29,f39])).

fof(f39,plain,(
    sK0 = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f27,f19])).

fof(f19,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,sK0),sK1) != k4_xboole_0(k2_xboole_0(sK2,sK1),sK0)
    & r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2] :
        ( k2_xboole_0(k4_xboole_0(X2,X0),X1) != k4_xboole_0(k2_xboole_0(X2,X1),X0)
        & r1_xboole_0(X0,X1) )
   => ( k2_xboole_0(k4_xboole_0(sK2,sK0),sK1) != k4_xboole_0(k2_xboole_0(sK2,sK1),sK0)
      & r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(k4_xboole_0(X2,X0),X1) != k4_xboole_0(k2_xboole_0(X2,X1),X0)
      & r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,X1)
       => k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_xboole_1)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f29,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f127,plain,(
    ! [X2,X3] : k2_xboole_0(k4_xboole_0(X2,X3),k3_xboole_0(X2,X3)) = X2 ),
    inference(forward_demodulation,[],[f126,f35])).

fof(f35,plain,(
    ! [X2,X3] : k2_xboole_0(X2,k4_xboole_0(X2,X3)) = X2 ),
    inference(superposition,[],[f34,f22])).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f126,plain,(
    ! [X2,X3] : k2_xboole_0(X2,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X2,X3),k3_xboole_0(X2,X3)) ),
    inference(forward_demodulation,[],[f121,f22])).

fof(f121,plain,(
    ! [X2,X3] : k2_xboole_0(k4_xboole_0(X2,X3),X2) = k2_xboole_0(k4_xboole_0(X2,X3),k3_xboole_0(X2,X3)) ),
    inference(superposition,[],[f23,f25])).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f55,plain,(
    ! [X0,X1] : k2_xboole_0(X1,X0) = k2_xboole_0(X1,k2_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f51,f23])).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(X1,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(superposition,[],[f23,f24])).

fof(f30,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_xboole_1)).

fof(f33,plain,(
    k4_xboole_0(k2_xboole_0(sK1,sK2),sK0) != k2_xboole_0(sK1,k4_xboole_0(sK2,sK0)) ),
    inference(forward_demodulation,[],[f32,f22])).

fof(f32,plain,(
    k2_xboole_0(k4_xboole_0(sK2,sK0),sK1) != k4_xboole_0(k2_xboole_0(sK1,sK2),sK0) ),
    inference(backward_demodulation,[],[f20,f22])).

fof(f20,plain,(
    k2_xboole_0(k4_xboole_0(sK2,sK0),sK1) != k4_xboole_0(k2_xboole_0(sK2,sK1),sK0) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:43:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (11912)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.47  % (11911)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.47  % (11909)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.48  % (11913)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.49  % (11922)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.49  % (11916)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.50  % (11910)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.50  % (11908)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.50  % (11919)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.50  % (11914)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.50  % (11923)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.50  % (11924)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.51  % (11920)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.51  % (11907)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.51  % (11915)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.52  % (11917)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.52  % (11921)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.56  % (11918)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 1.95/0.62  % (11923)Refutation found. Thanks to Tanya!
% 1.95/0.62  % SZS status Theorem for theBenchmark
% 1.95/0.62  % SZS output start Proof for theBenchmark
% 1.95/0.62  fof(f2803,plain,(
% 1.95/0.62    $false),
% 1.95/0.62    inference(subsumption_resolution,[],[f33,f2744])).
% 1.95/0.62  fof(f2744,plain,(
% 1.95/0.62    ( ! [X28] : (k4_xboole_0(k2_xboole_0(sK1,X28),sK0) = k2_xboole_0(sK1,k4_xboole_0(X28,sK0))) )),
% 1.95/0.62    inference(superposition,[],[f30,f1796])).
% 1.95/0.62  fof(f1796,plain,(
% 1.95/0.62    sK1 = k4_xboole_0(sK1,sK0)),
% 1.95/0.62    inference(forward_demodulation,[],[f1795,f34])).
% 1.95/0.62  fof(f34,plain,(
% 1.95/0.62    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0) )),
% 1.95/0.62    inference(resolution,[],[f26,f21])).
% 1.95/0.62  fof(f21,plain,(
% 1.95/0.62    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.95/0.62    inference(cnf_transformation,[],[f3])).
% 1.95/0.62  fof(f3,axiom,(
% 1.95/0.62    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.95/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.95/0.62  fof(f26,plain,(
% 1.95/0.62    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.95/0.62    inference(cnf_transformation,[],[f14])).
% 1.95/0.62  fof(f14,plain,(
% 1.95/0.62    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.95/0.62    inference(ennf_transformation,[],[f2])).
% 1.95/0.62  fof(f2,axiom,(
% 1.95/0.62    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.95/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.95/0.62  fof(f1795,plain,(
% 1.95/0.62    k4_xboole_0(sK1,sK0) = k2_xboole_0(k4_xboole_0(sK1,sK1),sK1)),
% 1.95/0.62    inference(forward_demodulation,[],[f1773,f219])).
% 1.95/0.62  fof(f219,plain,(
% 1.95/0.62    ( ! [X6,X7] : (k4_xboole_0(X6,X7) = k2_xboole_0(k4_xboole_0(X6,X6),k4_xboole_0(X6,X7))) )),
% 1.95/0.62    inference(superposition,[],[f34,f50])).
% 1.95/0.62  fof(f50,plain,(
% 1.95/0.62    ( ! [X10,X9] : (k4_xboole_0(k4_xboole_0(X9,X10),X9) = k4_xboole_0(X9,X9)) )),
% 1.95/0.62    inference(superposition,[],[f24,f34])).
% 1.95/0.62  fof(f24,plain,(
% 1.95/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 1.95/0.62    inference(cnf_transformation,[],[f5])).
% 1.95/0.62  fof(f5,axiom,(
% 1.95/0.62    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 1.95/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 1.95/0.62  fof(f1773,plain,(
% 1.95/0.62    k2_xboole_0(k4_xboole_0(sK1,sK1),sK1) = k2_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK0))),
% 1.95/0.62    inference(superposition,[],[f55,f1761])).
% 1.95/0.62  fof(f1761,plain,(
% 1.95/0.62    sK1 = k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK1,sK1))),
% 1.95/0.62    inference(superposition,[],[f127,f1730])).
% 1.95/0.62  fof(f1730,plain,(
% 1.95/0.62    k4_xboole_0(sK1,sK1) = k3_xboole_0(sK1,sK0)),
% 1.95/0.62    inference(superposition,[],[f1705,f138])).
% 1.95/0.62  fof(f138,plain,(
% 1.95/0.62    ( ! [X4,X5] : (k4_xboole_0(X4,X4) = k4_xboole_0(k3_xboole_0(X4,X5),X4)) )),
% 1.95/0.62    inference(superposition,[],[f24,f122])).
% 1.95/0.62  fof(f122,plain,(
% 1.95/0.62    ( ! [X4,X5] : (k2_xboole_0(k3_xboole_0(X4,X5),X4) = X4) )),
% 1.95/0.62    inference(superposition,[],[f34,f25])).
% 1.95/0.62  fof(f25,plain,(
% 1.95/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.95/0.62    inference(cnf_transformation,[],[f8])).
% 1.95/0.62  fof(f8,axiom,(
% 1.95/0.62    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.95/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.95/0.62  fof(f1705,plain,(
% 1.95/0.62    ( ! [X24] : (k3_xboole_0(X24,sK0) = k4_xboole_0(k3_xboole_0(X24,sK0),sK1)) )),
% 1.95/0.62    inference(superposition,[],[f29,f39])).
% 1.95/0.62  fof(f39,plain,(
% 1.95/0.62    sK0 = k4_xboole_0(sK0,sK1)),
% 1.95/0.62    inference(resolution,[],[f27,f19])).
% 1.95/0.62  fof(f19,plain,(
% 1.95/0.62    r1_xboole_0(sK0,sK1)),
% 1.95/0.62    inference(cnf_transformation,[],[f17])).
% 1.95/0.62  fof(f17,plain,(
% 1.95/0.62    k2_xboole_0(k4_xboole_0(sK2,sK0),sK1) != k4_xboole_0(k2_xboole_0(sK2,sK1),sK0) & r1_xboole_0(sK0,sK1)),
% 1.95/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f16])).
% 1.95/0.62  fof(f16,plain,(
% 1.95/0.62    ? [X0,X1,X2] : (k2_xboole_0(k4_xboole_0(X2,X0),X1) != k4_xboole_0(k2_xboole_0(X2,X1),X0) & r1_xboole_0(X0,X1)) => (k2_xboole_0(k4_xboole_0(sK2,sK0),sK1) != k4_xboole_0(k2_xboole_0(sK2,sK1),sK0) & r1_xboole_0(sK0,sK1))),
% 1.95/0.62    introduced(choice_axiom,[])).
% 1.95/0.62  fof(f13,plain,(
% 1.95/0.62    ? [X0,X1,X2] : (k2_xboole_0(k4_xboole_0(X2,X0),X1) != k4_xboole_0(k2_xboole_0(X2,X1),X0) & r1_xboole_0(X0,X1))),
% 1.95/0.62    inference(ennf_transformation,[],[f12])).
% 1.95/0.62  fof(f12,negated_conjecture,(
% 1.95/0.62    ~! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0))),
% 1.95/0.62    inference(negated_conjecture,[],[f11])).
% 1.95/0.62  fof(f11,conjecture,(
% 1.95/0.62    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0))),
% 1.95/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_xboole_1)).
% 1.95/0.62  fof(f27,plain,(
% 1.95/0.62    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 1.95/0.62    inference(cnf_transformation,[],[f18])).
% 1.95/0.62  fof(f18,plain,(
% 1.95/0.62    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 1.95/0.62    inference(nnf_transformation,[],[f10])).
% 1.95/0.62  fof(f10,axiom,(
% 1.95/0.62    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.95/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.95/0.62  fof(f29,plain,(
% 1.95/0.62    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 1.95/0.62    inference(cnf_transformation,[],[f9])).
% 1.95/0.62  fof(f9,axiom,(
% 1.95/0.62    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 1.95/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 1.95/0.62  fof(f127,plain,(
% 1.95/0.62    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X2,X3),k3_xboole_0(X2,X3)) = X2) )),
% 1.95/0.62    inference(forward_demodulation,[],[f126,f35])).
% 1.95/0.62  fof(f35,plain,(
% 1.95/0.62    ( ! [X2,X3] : (k2_xboole_0(X2,k4_xboole_0(X2,X3)) = X2) )),
% 1.95/0.62    inference(superposition,[],[f34,f22])).
% 1.95/0.62  fof(f22,plain,(
% 1.95/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.95/0.62    inference(cnf_transformation,[],[f1])).
% 1.95/0.62  fof(f1,axiom,(
% 1.95/0.62    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.95/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.95/0.62  fof(f126,plain,(
% 1.95/0.62    ( ! [X2,X3] : (k2_xboole_0(X2,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X2,X3),k3_xboole_0(X2,X3))) )),
% 1.95/0.62    inference(forward_demodulation,[],[f121,f22])).
% 1.95/0.62  fof(f121,plain,(
% 1.95/0.62    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X2,X3),X2) = k2_xboole_0(k4_xboole_0(X2,X3),k3_xboole_0(X2,X3))) )),
% 1.95/0.62    inference(superposition,[],[f23,f25])).
% 1.95/0.62  fof(f23,plain,(
% 1.95/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.95/0.62    inference(cnf_transformation,[],[f4])).
% 1.95/0.62  fof(f4,axiom,(
% 1.95/0.62    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.95/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.95/0.62  fof(f55,plain,(
% 1.95/0.62    ( ! [X0,X1] : (k2_xboole_0(X1,X0) = k2_xboole_0(X1,k2_xboole_0(X0,X1))) )),
% 1.95/0.62    inference(forward_demodulation,[],[f51,f23])).
% 1.95/0.62  fof(f51,plain,(
% 1.95/0.62    ( ! [X0,X1] : (k2_xboole_0(X1,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,k4_xboole_0(X0,X1))) )),
% 1.95/0.62    inference(superposition,[],[f23,f24])).
% 1.95/0.62  fof(f30,plain,(
% 1.95/0.62    ( ! [X2,X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))) )),
% 1.95/0.62    inference(cnf_transformation,[],[f6])).
% 1.95/0.62  fof(f6,axiom,(
% 1.95/0.62    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))),
% 1.95/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_xboole_1)).
% 1.95/0.62  fof(f33,plain,(
% 1.95/0.62    k4_xboole_0(k2_xboole_0(sK1,sK2),sK0) != k2_xboole_0(sK1,k4_xboole_0(sK2,sK0))),
% 1.95/0.62    inference(forward_demodulation,[],[f32,f22])).
% 1.95/0.62  fof(f32,plain,(
% 1.95/0.62    k2_xboole_0(k4_xboole_0(sK2,sK0),sK1) != k4_xboole_0(k2_xboole_0(sK1,sK2),sK0)),
% 1.95/0.62    inference(backward_demodulation,[],[f20,f22])).
% 1.95/0.62  fof(f20,plain,(
% 1.95/0.62    k2_xboole_0(k4_xboole_0(sK2,sK0),sK1) != k4_xboole_0(k2_xboole_0(sK2,sK1),sK0)),
% 1.95/0.62    inference(cnf_transformation,[],[f17])).
% 1.95/0.62  % SZS output end Proof for theBenchmark
% 1.95/0.62  % (11923)------------------------------
% 1.95/0.62  % (11923)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.95/0.62  % (11923)Termination reason: Refutation
% 1.95/0.62  
% 1.95/0.62  % (11923)Memory used [KB]: 7291
% 1.95/0.62  % (11923)Time elapsed: 0.181 s
% 1.95/0.62  % (11923)------------------------------
% 1.95/0.62  % (11923)------------------------------
% 1.95/0.62  % (11906)Success in time 0.253 s
%------------------------------------------------------------------------------
