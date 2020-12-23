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
% DateTime   : Thu Dec  3 12:31:30 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 101 expanded)
%              Number of leaves         :   10 (  30 expanded)
%              Depth                    :   21
%              Number of atoms          :   80 ( 172 expanded)
%              Number of equality atoms :   10 (  26 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1519,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1518,f22])).

fof(f22,plain,(
    ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X1,k4_xboole_0(X0,X2))
        & r1_xboole_0(X0,k4_xboole_0(X1,X2)) )
   => ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
      & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X1,k4_xboole_0(X0,X2))
      & r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
       => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
     => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_xboole_1)).

fof(f1518,plain,(
    r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f1515,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f1515,plain,(
    r1_xboole_0(k4_xboole_0(sK0,sK2),sK1) ),
    inference(resolution,[],[f1505,f23])).

fof(f23,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f1505,plain,(
    ! [X0] :
      ( ~ r1_tarski(k4_xboole_0(sK0,sK2),X0)
      | r1_xboole_0(k4_xboole_0(sK0,sK2),sK1) ) ),
    inference(resolution,[],[f1500,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
      | ~ r1_tarski(X0,X2)
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f31,f26])).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_xboole_1)).

fof(f1500,plain,(
    ! [X5] : r1_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,X5)) ),
    inference(resolution,[],[f1493,f27])).

fof(f1493,plain,(
    ! [X0] : r1_xboole_0(k4_xboole_0(sK1,X0),k4_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f1224,f23])).

fof(f1224,plain,(
    ! [X50,X51] :
      ( ~ r1_tarski(k4_xboole_0(sK1,X50),X51)
      | r1_xboole_0(k4_xboole_0(sK1,X50),k4_xboole_0(sK0,sK2)) ) ),
    inference(resolution,[],[f255,f1092])).

fof(f1092,plain,(
    ! [X12,X13] : r1_xboole_0(k4_xboole_0(sK1,X12),k4_xboole_0(sK0,k2_xboole_0(sK2,X13))) ),
    inference(resolution,[],[f1061,f27])).

fof(f1061,plain,(
    ! [X4,X3] : r1_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK2,X3)),k4_xboole_0(sK1,X4)) ),
    inference(resolution,[],[f1056,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_xboole_1)).

fof(f1056,plain,(
    ! [X0] : r1_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK2,X0)),sK1) ),
    inference(resolution,[],[f998,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] : r1_tarski(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X0,X1)) ),
    inference(superposition,[],[f23,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f998,plain,(
    ! [X41,X42] :
      ( ~ r1_tarski(k4_xboole_0(sK0,X41),k4_xboole_0(X42,sK2))
      | r1_xboole_0(k4_xboole_0(sK0,X41),sK1) ) ),
    inference(resolution,[],[f414,f154])).

fof(f154,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(sK0,X1),k4_xboole_0(sK1,k2_xboole_0(X0,sK2))) ),
    inference(superposition,[],[f79,f25])).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f79,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK1,k2_xboole_0(sK2,X1))) ),
    inference(backward_demodulation,[],[f49,f29])).

fof(f49,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(k4_xboole_0(sK1,sK2),X1)) ),
    inference(resolution,[],[f46,f30])).

fof(f46,plain,(
    ! [X2] : r1_xboole_0(k4_xboole_0(sK0,X2),k4_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f41,f27])).

fof(f41,plain,(
    ! [X4] : r1_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,X4)) ),
    inference(resolution,[],[f30,f35])).

fof(f35,plain,(
    r1_xboole_0(k4_xboole_0(sK1,sK2),sK0) ),
    inference(resolution,[],[f27,f21])).

fof(f21,plain,(
    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f20])).

fof(f414,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_xboole_0(X3,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)))
      | ~ r1_tarski(X3,k4_xboole_0(X1,X2))
      | r1_xboole_0(X3,X0) ) ),
    inference(superposition,[],[f34,f330])).

fof(f330,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) ),
    inference(forward_demodulation,[],[f33,f29])).

fof(f33,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f28,f26,f26])).

fof(f28,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f255,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_xboole_0(X3,k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))))
      | ~ r1_tarski(X3,X2)
      | r1_xboole_0(X3,k4_xboole_0(X0,X1)) ) ),
    inference(forward_demodulation,[],[f251,f29])).

fof(f251,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_xboole_0(X3,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))))
      | ~ r1_tarski(X3,X2)
      | r1_xboole_0(X3,k4_xboole_0(X0,X1)) ) ),
    inference(superposition,[],[f34,f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:56:17 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (10419)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (10421)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (10423)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.48  % (10430)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.48  % (10415)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.49  % (10418)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.49  % (10416)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.49  % (10432)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.49  % (10420)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.49  % (10429)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.49  % (10424)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.50  % (10422)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.51  % (10427)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.51  % (10428)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.53  % (10417)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.54  % (10425)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.55  % (10426)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.55  % (10426)Refutation not found, incomplete strategy% (10426)------------------------------
% 0.21/0.55  % (10426)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (10426)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (10426)Memory used [KB]: 10618
% 0.21/0.55  % (10426)Time elapsed: 0.123 s
% 0.21/0.55  % (10426)------------------------------
% 0.21/0.55  % (10426)------------------------------
% 0.21/0.55  % (10431)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.57  % (10427)Refutation found. Thanks to Tanya!
% 0.21/0.57  % SZS status Theorem for theBenchmark
% 0.21/0.57  % SZS output start Proof for theBenchmark
% 0.21/0.57  fof(f1519,plain,(
% 0.21/0.57    $false),
% 0.21/0.57    inference(subsumption_resolution,[],[f1518,f22])).
% 0.21/0.57  fof(f22,plain,(
% 0.21/0.57    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 0.21/0.57    inference(cnf_transformation,[],[f20])).
% 0.21/0.57  fof(f20,plain,(
% 0.21/0.57    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f19])).
% 0.21/0.57  fof(f19,plain,(
% 0.21/0.57    ? [X0,X1,X2] : (~r1_xboole_0(X1,k4_xboole_0(X0,X2)) & r1_xboole_0(X0,k4_xboole_0(X1,X2))) => (~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f13,plain,(
% 0.21/0.57    ? [X0,X1,X2] : (~r1_xboole_0(X1,k4_xboole_0(X0,X2)) & r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 0.21/0.57    inference(ennf_transformation,[],[f12])).
% 0.21/0.57  fof(f12,negated_conjecture,(
% 0.21/0.57    ~! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 0.21/0.57    inference(negated_conjecture,[],[f11])).
% 0.21/0.57  fof(f11,conjecture,(
% 0.21/0.57    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_xboole_1)).
% 0.21/0.57  fof(f1518,plain,(
% 0.21/0.57    r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 0.21/0.57    inference(resolution,[],[f1515,f27])).
% 0.21/0.57  fof(f27,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f14])).
% 0.21/0.57  fof(f14,plain,(
% 0.21/0.57    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f2])).
% 0.21/0.57  fof(f2,axiom,(
% 0.21/0.57    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.21/0.57  fof(f1515,plain,(
% 0.21/0.57    r1_xboole_0(k4_xboole_0(sK0,sK2),sK1)),
% 0.21/0.57    inference(resolution,[],[f1505,f23])).
% 0.21/0.57  fof(f23,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f3])).
% 0.21/0.57  fof(f3,axiom,(
% 0.21/0.57    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.21/0.57  fof(f1505,plain,(
% 0.21/0.57    ( ! [X0] : (~r1_tarski(k4_xboole_0(sK0,sK2),X0) | r1_xboole_0(k4_xboole_0(sK0,sK2),sK1)) )),
% 0.21/0.57    inference(resolution,[],[f1500,f34])).
% 0.21/0.57  fof(f34,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) | ~r1_tarski(X0,X2) | r1_xboole_0(X0,X1)) )),
% 0.21/0.57    inference(definition_unfolding,[],[f31,f26])).
% 0.21/0.57  fof(f26,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f5])).
% 0.21/0.57  fof(f5,axiom,(
% 0.21/0.57    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.57  fof(f31,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | r1_xboole_0(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f16])).
% 0.21/0.57  fof(f16,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | r1_xboole_0(X0,X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f8])).
% 0.21/0.57  fof(f8,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_xboole_1)).
% 0.21/0.57  fof(f1500,plain,(
% 0.21/0.57    ( ! [X5] : (r1_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,X5))) )),
% 0.21/0.57    inference(resolution,[],[f1493,f27])).
% 0.21/0.57  fof(f1493,plain,(
% 0.21/0.57    ( ! [X0] : (r1_xboole_0(k4_xboole_0(sK1,X0),k4_xboole_0(sK0,sK2))) )),
% 0.21/0.57    inference(resolution,[],[f1224,f23])).
% 0.21/0.57  fof(f1224,plain,(
% 0.21/0.57    ( ! [X50,X51] : (~r1_tarski(k4_xboole_0(sK1,X50),X51) | r1_xboole_0(k4_xboole_0(sK1,X50),k4_xboole_0(sK0,sK2))) )),
% 0.21/0.57    inference(resolution,[],[f255,f1092])).
% 0.21/0.57  fof(f1092,plain,(
% 0.21/0.57    ( ! [X12,X13] : (r1_xboole_0(k4_xboole_0(sK1,X12),k4_xboole_0(sK0,k2_xboole_0(sK2,X13)))) )),
% 0.21/0.57    inference(resolution,[],[f1061,f27])).
% 0.21/0.57  fof(f1061,plain,(
% 0.21/0.57    ( ! [X4,X3] : (r1_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK2,X3)),k4_xboole_0(sK1,X4))) )),
% 0.21/0.57    inference(resolution,[],[f1056,f30])).
% 0.21/0.57  fof(f30,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k4_xboole_0(X1,X2))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f15])).
% 0.21/0.57  fof(f15,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f10])).
% 0.21/0.57  fof(f10,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_xboole_1)).
% 0.21/0.57  fof(f1056,plain,(
% 0.21/0.57    ( ! [X0] : (r1_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK2,X0)),sK1)) )),
% 0.21/0.57    inference(resolution,[],[f998,f88])).
% 0.21/0.57  fof(f88,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X0,X1))) )),
% 0.21/0.57    inference(superposition,[],[f23,f29])).
% 0.21/0.57  fof(f29,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f4])).
% 0.21/0.57  fof(f4,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.21/0.57  fof(f998,plain,(
% 0.21/0.57    ( ! [X41,X42] : (~r1_tarski(k4_xboole_0(sK0,X41),k4_xboole_0(X42,sK2)) | r1_xboole_0(k4_xboole_0(sK0,X41),sK1)) )),
% 0.21/0.57    inference(resolution,[],[f414,f154])).
% 0.21/0.57  fof(f154,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(sK0,X1),k4_xboole_0(sK1,k2_xboole_0(X0,sK2)))) )),
% 0.21/0.57    inference(superposition,[],[f79,f25])).
% 0.21/0.57  fof(f25,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f1])).
% 0.21/0.57  fof(f1,axiom,(
% 0.21/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.57  fof(f79,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK1,k2_xboole_0(sK2,X1)))) )),
% 0.21/0.57    inference(backward_demodulation,[],[f49,f29])).
% 0.21/0.57  fof(f49,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(k4_xboole_0(sK1,sK2),X1))) )),
% 0.21/0.57    inference(resolution,[],[f46,f30])).
% 0.21/0.57  fof(f46,plain,(
% 0.21/0.57    ( ! [X2] : (r1_xboole_0(k4_xboole_0(sK0,X2),k4_xboole_0(sK1,sK2))) )),
% 0.21/0.57    inference(resolution,[],[f41,f27])).
% 0.21/0.57  fof(f41,plain,(
% 0.21/0.57    ( ! [X4] : (r1_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,X4))) )),
% 0.21/0.57    inference(resolution,[],[f30,f35])).
% 0.21/0.57  fof(f35,plain,(
% 0.21/0.57    r1_xboole_0(k4_xboole_0(sK1,sK2),sK0)),
% 0.21/0.57    inference(resolution,[],[f27,f21])).
% 0.21/0.57  fof(f21,plain,(
% 0.21/0.57    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.21/0.57    inference(cnf_transformation,[],[f20])).
% 0.21/0.57  fof(f414,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (~r1_xboole_0(X3,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))) | ~r1_tarski(X3,k4_xboole_0(X1,X2)) | r1_xboole_0(X3,X0)) )),
% 0.21/0.57    inference(superposition,[],[f34,f330])).
% 0.21/0.57  fof(f330,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))) )),
% 0.21/0.57    inference(forward_demodulation,[],[f33,f29])).
% 0.21/0.57  fof(f33,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 0.21/0.57    inference(definition_unfolding,[],[f28,f26,f26])).
% 0.21/0.57  fof(f28,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f6])).
% 0.21/0.57  fof(f6,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 0.21/0.57  fof(f255,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (~r1_xboole_0(X3,k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2))))) | ~r1_tarski(X3,X2) | r1_xboole_0(X3,k4_xboole_0(X0,X1))) )),
% 0.21/0.57    inference(forward_demodulation,[],[f251,f29])).
% 0.21/0.57  fof(f251,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (~r1_xboole_0(X3,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2)))) | ~r1_tarski(X3,X2) | r1_xboole_0(X3,k4_xboole_0(X0,X1))) )),
% 0.21/0.57    inference(superposition,[],[f34,f29])).
% 0.21/0.57  % SZS output end Proof for theBenchmark
% 0.21/0.57  % (10427)------------------------------
% 0.21/0.57  % (10427)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (10427)Termination reason: Refutation
% 0.21/0.57  
% 0.21/0.57  % (10427)Memory used [KB]: 2558
% 0.21/0.57  % (10427)Time elapsed: 0.135 s
% 0.21/0.57  % (10427)------------------------------
% 0.21/0.57  % (10427)------------------------------
% 0.21/0.58  % (10414)Success in time 0.221 s
%------------------------------------------------------------------------------
