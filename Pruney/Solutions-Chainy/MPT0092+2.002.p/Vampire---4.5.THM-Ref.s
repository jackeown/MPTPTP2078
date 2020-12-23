%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:40 EST 2020

% Result     : Theorem 1.56s
% Output     : Refutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :   48 (  92 expanded)
%              Number of leaves         :   11 (  29 expanded)
%              Depth                    :   13
%              Number of atoms          :   66 ( 132 expanded)
%              Number of equality atoms :   37 (  74 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3365,plain,(
    $false ),
    inference(resolution,[],[f3357,f19])).

fof(f19,plain,(
    ~ r1_xboole_0(sK0,k4_xboole_0(sK2,sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ~ r1_xboole_0(sK0,k4_xboole_0(sK2,sK1))
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X0,k4_xboole_0(X2,X1))
        & r1_tarski(X0,X1) )
   => ( ~ r1_xboole_0(sK0,k4_xboole_0(sK2,sK1))
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,k4_xboole_0(X2,X1))
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,X1)
       => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f3357,plain,(
    ! [X10] : r1_xboole_0(sK0,k4_xboole_0(X10,sK1)) ),
    inference(trivial_inequality_removal,[],[f3345])).

fof(f3345,plain,(
    ! [X10] :
      ( sK0 != sK0
      | r1_xboole_0(sK0,k4_xboole_0(X10,sK1)) ) ),
    inference(superposition,[],[f27,f3040])).

fof(f3040,plain,(
    ! [X16] : sK0 = k4_xboole_0(sK0,k4_xboole_0(X16,sK1)) ),
    inference(forward_demodulation,[],[f2920,f20])).

fof(f20,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f2920,plain,(
    ! [X16] : k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK0,k4_xboole_0(X16,sK1)) ),
    inference(superposition,[],[f186,f117])).

fof(f117,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(X0,sK1)) ),
    inference(superposition,[],[f106,f22])).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f106,plain,(
    ! [X12] : k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,X12)) ),
    inference(forward_demodulation,[],[f93,f54])).

fof(f54,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f53,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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

fof(f53,plain,(
    ! [X2] : r1_tarski(k1_xboole_0,X2) ),
    inference(superposition,[],[f21,f40])).

fof(f40,plain,(
    ! [X2] : k1_xboole_0 = k4_xboole_0(X2,X2) ),
    inference(resolution,[],[f29,f34])).

fof(f34,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(superposition,[],[f21,f20])).

fof(f21,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f93,plain,(
    ! [X12] : k4_xboole_0(sK0,k2_xboole_0(sK1,X12)) = k4_xboole_0(k1_xboole_0,X12) ),
    inference(superposition,[],[f31,f38])).

fof(f38,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f29,f18])).

fof(f18,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f31,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f186,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))) ),
    inference(forward_demodulation,[],[f185,f67])).

fof(f67,plain,(
    ! [X1] : k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f63,f22])).

fof(f63,plain,(
    ! [X2] : k2_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(forward_demodulation,[],[f58,f20])).

fof(f58,plain,(
    ! [X2] : k2_xboole_0(X2,k1_xboole_0) = k4_xboole_0(X2,k1_xboole_0) ),
    inference(superposition,[],[f24,f20])).

fof(f24,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f185,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))) ),
    inference(forward_demodulation,[],[f151,f40])).

fof(f151,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X1,X2))) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))) ),
    inference(superposition,[],[f33,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) ),
    inference(backward_demodulation,[],[f32,f31])).

fof(f32,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f30,f25,f25])).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f30,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:55:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (18223)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.47  % (18234)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.47  % (18222)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.47  % (18228)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.48  % (18224)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.48  % (18230)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.48  % (18238)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.49  % (18227)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.49  % (18226)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.49  % (18232)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.49  % (18233)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.50  % (18231)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.50  % (18239)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.50  % (18235)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.51  % (18237)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.51  % (18225)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.52  % (18229)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.53  % (18236)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 1.56/0.57  % (18223)Refutation found. Thanks to Tanya!
% 1.56/0.57  % SZS status Theorem for theBenchmark
% 1.56/0.57  % SZS output start Proof for theBenchmark
% 1.56/0.57  fof(f3365,plain,(
% 1.56/0.57    $false),
% 1.56/0.57    inference(resolution,[],[f3357,f19])).
% 1.56/0.57  fof(f19,plain,(
% 1.56/0.57    ~r1_xboole_0(sK0,k4_xboole_0(sK2,sK1))),
% 1.56/0.57    inference(cnf_transformation,[],[f15])).
% 1.56/0.57  fof(f15,plain,(
% 1.56/0.57    ~r1_xboole_0(sK0,k4_xboole_0(sK2,sK1)) & r1_tarski(sK0,sK1)),
% 1.56/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f14])).
% 1.56/0.57  fof(f14,plain,(
% 1.56/0.57    ? [X0,X1,X2] : (~r1_xboole_0(X0,k4_xboole_0(X2,X1)) & r1_tarski(X0,X1)) => (~r1_xboole_0(sK0,k4_xboole_0(sK2,sK1)) & r1_tarski(sK0,sK1))),
% 1.56/0.57    introduced(choice_axiom,[])).
% 1.56/0.57  fof(f13,plain,(
% 1.56/0.57    ? [X0,X1,X2] : (~r1_xboole_0(X0,k4_xboole_0(X2,X1)) & r1_tarski(X0,X1))),
% 1.56/0.57    inference(ennf_transformation,[],[f12])).
% 1.56/0.57  fof(f12,negated_conjecture,(
% 1.56/0.57    ~! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 1.56/0.57    inference(negated_conjecture,[],[f11])).
% 1.56/0.57  fof(f11,conjecture,(
% 1.56/0.57    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 1.56/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).
% 1.56/0.57  fof(f3357,plain,(
% 1.56/0.57    ( ! [X10] : (r1_xboole_0(sK0,k4_xboole_0(X10,sK1))) )),
% 1.56/0.57    inference(trivial_inequality_removal,[],[f3345])).
% 1.56/0.57  fof(f3345,plain,(
% 1.56/0.57    ( ! [X10] : (sK0 != sK0 | r1_xboole_0(sK0,k4_xboole_0(X10,sK1))) )),
% 1.56/0.57    inference(superposition,[],[f27,f3040])).
% 1.56/0.57  fof(f3040,plain,(
% 1.56/0.57    ( ! [X16] : (sK0 = k4_xboole_0(sK0,k4_xboole_0(X16,sK1))) )),
% 1.56/0.57    inference(forward_demodulation,[],[f2920,f20])).
% 1.56/0.57  fof(f20,plain,(
% 1.56/0.57    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.56/0.57    inference(cnf_transformation,[],[f5])).
% 1.56/0.57  fof(f5,axiom,(
% 1.56/0.57    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.56/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.56/0.57  fof(f2920,plain,(
% 1.56/0.57    ( ! [X16] : (k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK0,k4_xboole_0(X16,sK1))) )),
% 1.56/0.57    inference(superposition,[],[f186,f117])).
% 1.56/0.57  fof(f117,plain,(
% 1.56/0.57    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(X0,sK1))) )),
% 1.56/0.57    inference(superposition,[],[f106,f22])).
% 1.56/0.57  fof(f22,plain,(
% 1.56/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f1])).
% 1.56/0.57  fof(f1,axiom,(
% 1.56/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.56/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.56/0.57  fof(f106,plain,(
% 1.56/0.57    ( ! [X12] : (k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,X12))) )),
% 1.56/0.57    inference(forward_demodulation,[],[f93,f54])).
% 1.56/0.57  fof(f54,plain,(
% 1.56/0.57    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.56/0.57    inference(resolution,[],[f53,f29])).
% 1.56/0.57  fof(f29,plain,(
% 1.56/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.56/0.57    inference(cnf_transformation,[],[f17])).
% 1.56/0.57  fof(f17,plain,(
% 1.56/0.57    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.56/0.57    inference(nnf_transformation,[],[f2])).
% 1.56/0.57  fof(f2,axiom,(
% 1.56/0.57    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.56/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.56/0.57  fof(f53,plain,(
% 1.56/0.57    ( ! [X2] : (r1_tarski(k1_xboole_0,X2)) )),
% 1.56/0.57    inference(superposition,[],[f21,f40])).
% 1.56/0.57  fof(f40,plain,(
% 1.56/0.57    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(X2,X2)) )),
% 1.56/0.57    inference(resolution,[],[f29,f34])).
% 1.56/0.57  fof(f34,plain,(
% 1.56/0.57    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 1.56/0.57    inference(superposition,[],[f21,f20])).
% 1.56/0.57  fof(f21,plain,(
% 1.56/0.57    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f3])).
% 1.56/0.57  fof(f3,axiom,(
% 1.56/0.57    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.56/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.56/0.57  fof(f93,plain,(
% 1.56/0.57    ( ! [X12] : (k4_xboole_0(sK0,k2_xboole_0(sK1,X12)) = k4_xboole_0(k1_xboole_0,X12)) )),
% 1.56/0.57    inference(superposition,[],[f31,f38])).
% 1.56/0.57  fof(f38,plain,(
% 1.56/0.57    k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 1.56/0.57    inference(resolution,[],[f29,f18])).
% 1.56/0.57  fof(f18,plain,(
% 1.56/0.57    r1_tarski(sK0,sK1)),
% 1.56/0.57    inference(cnf_transformation,[],[f15])).
% 1.56/0.57  fof(f31,plain,(
% 1.56/0.57    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.56/0.57    inference(cnf_transformation,[],[f7])).
% 1.56/0.57  fof(f7,axiom,(
% 1.56/0.57    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.56/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 1.56/0.57  fof(f186,plain,(
% 1.56/0.57    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)))) )),
% 1.56/0.57    inference(forward_demodulation,[],[f185,f67])).
% 1.56/0.57  fof(f67,plain,(
% 1.56/0.57    ( ! [X1] : (k2_xboole_0(k1_xboole_0,X1) = X1) )),
% 1.56/0.57    inference(superposition,[],[f63,f22])).
% 1.56/0.57  fof(f63,plain,(
% 1.56/0.57    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = X2) )),
% 1.56/0.57    inference(forward_demodulation,[],[f58,f20])).
% 1.56/0.57  fof(f58,plain,(
% 1.56/0.57    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = k4_xboole_0(X2,k1_xboole_0)) )),
% 1.56/0.57    inference(superposition,[],[f24,f20])).
% 1.56/0.57  fof(f24,plain,(
% 1.56/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f6])).
% 1.56/0.57  fof(f6,axiom,(
% 1.56/0.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 1.56/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 1.56/0.57  fof(f185,plain,(
% 1.56/0.57    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2)))) )),
% 1.56/0.57    inference(forward_demodulation,[],[f151,f40])).
% 1.56/0.57  fof(f151,plain,(
% 1.56/0.57    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X1,X2))) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)))) )),
% 1.56/0.57    inference(superposition,[],[f33,f33])).
% 1.56/0.57  fof(f33,plain,(
% 1.56/0.57    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))) )),
% 1.56/0.57    inference(backward_demodulation,[],[f32,f31])).
% 1.56/0.57  fof(f32,plain,(
% 1.56/0.57    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 1.56/0.57    inference(definition_unfolding,[],[f30,f25,f25])).
% 1.56/0.57  fof(f25,plain,(
% 1.56/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f8])).
% 1.56/0.57  fof(f8,axiom,(
% 1.56/0.57    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.56/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.56/0.57  fof(f30,plain,(
% 1.56/0.57    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f9])).
% 1.56/0.57  fof(f9,axiom,(
% 1.56/0.57    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 1.56/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 1.56/0.57  fof(f27,plain,(
% 1.56/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f16])).
% 1.56/0.57  fof(f16,plain,(
% 1.56/0.57    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 1.56/0.57    inference(nnf_transformation,[],[f10])).
% 1.56/0.57  fof(f10,axiom,(
% 1.56/0.57    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.56/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.56/0.57  % SZS output end Proof for theBenchmark
% 1.56/0.57  % (18223)------------------------------
% 1.56/0.57  % (18223)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.57  % (18223)Termination reason: Refutation
% 1.56/0.57  
% 1.56/0.57  % (18223)Memory used [KB]: 3582
% 1.56/0.57  % (18223)Time elapsed: 0.133 s
% 1.56/0.57  % (18223)------------------------------
% 1.56/0.57  % (18223)------------------------------
% 1.56/0.59  % (18221)Success in time 0.225 s
%------------------------------------------------------------------------------
