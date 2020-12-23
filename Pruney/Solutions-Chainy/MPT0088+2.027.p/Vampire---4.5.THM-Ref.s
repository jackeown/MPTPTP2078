%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:34 EST 2020

% Result     : Theorem 1.51s
% Output     : Refutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 338 expanded)
%              Number of leaves         :   10 ( 112 expanded)
%              Depth                    :   17
%              Number of atoms          :   73 ( 358 expanded)
%              Number of equality atoms :   48 ( 321 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8101,plain,(
    $false ),
    inference(subsumption_resolution,[],[f8030,f16])).

fof(f16,plain,(
    ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X1,k4_xboole_0(X0,X2))
        & r1_xboole_0(X0,k4_xboole_0(X1,X2)) )
   => ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
      & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X1,k4_xboole_0(X0,X2))
      & r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
       => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
     => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_xboole_1)).

fof(f8030,plain,(
    r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(superposition,[],[f4506,f7646])).

fof(f7646,plain,(
    k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k2_xboole_0(sK2,sK1)) ),
    inference(superposition,[],[f6859,f21])).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f6859,plain,(
    ! [X1] : k4_xboole_0(sK0,X1) = k4_xboole_0(sK0,k2_xboole_0(X1,k4_xboole_0(sK1,sK2))) ),
    inference(superposition,[],[f6199,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f6199,plain,(
    ! [X20] : k4_xboole_0(sK0,X20) = k4_xboole_0(k4_xboole_0(sK0,X20),k4_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f4372,f4593])).

fof(f4593,plain,(
    ! [X25] : k4_xboole_0(sK1,sK2) = k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,X25)) ),
    inference(forward_demodulation,[],[f4574,f761])).

fof(f761,plain,(
    ! [X2,X3] : k2_xboole_0(X2,k4_xboole_0(X2,X3)) = X2 ),
    inference(forward_demodulation,[],[f738,f218])).

fof(f218,plain,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(backward_demodulation,[],[f33,f201])).

fof(f201,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(superposition,[],[f189,f18])).

fof(f18,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f189,plain,(
    ! [X4,X3] : k2_xboole_0(k4_xboole_0(X3,X4),X3) = X3 ),
    inference(forward_demodulation,[],[f188,f18])).

fof(f188,plain,(
    ! [X4,X3] : k2_xboole_0(k4_xboole_0(X3,X4),X3) = k4_xboole_0(X3,k1_xboole_0) ),
    inference(forward_demodulation,[],[f158,f31])).

fof(f31,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f26,f18])).

fof(f26,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f17,f20])).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f17,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f158,plain,(
    ! [X4,X3] : k2_xboole_0(k4_xboole_0(X3,X4),X3) = k4_xboole_0(X3,k4_xboole_0(X4,X4)) ),
    inference(superposition,[],[f29,f21])).

fof(f29,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f25,f20])).

fof(f25,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f33,plain,(
    ! [X1] : k2_xboole_0(X1,X1) = k2_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f21,f31])).

fof(f738,plain,(
    ! [X2,X3] : k2_xboole_0(X2,k1_xboole_0) = k2_xboole_0(X2,k4_xboole_0(X2,X3)) ),
    inference(superposition,[],[f21,f684])).

fof(f684,plain,(
    ! [X8,X9] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X8,X9),X8) ),
    inference(superposition,[],[f676,f189])).

fof(f676,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X3)) ),
    inference(forward_demodulation,[],[f58,f217])).

fof(f217,plain,(
    ! [X3] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X3) ),
    inference(backward_demodulation,[],[f86,f201])).

fof(f86,plain,(
    ! [X3] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k2_xboole_0(X3,X3)) ),
    inference(superposition,[],[f72,f33])).

fof(f72,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,X5)) ),
    inference(forward_demodulation,[],[f63,f21])).

fof(f63,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,X6))) ),
    inference(superposition,[],[f24,f31])).

fof(f58,plain,(
    ! [X2,X3] : k4_xboole_0(k1_xboole_0,X3) = k4_xboole_0(X2,k2_xboole_0(X2,X3)) ),
    inference(superposition,[],[f24,f31])).

fof(f4574,plain,(
    ! [X25] : k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,X25)) = k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),X25))) ),
    inference(superposition,[],[f29,f4383])).

fof(f4383,plain,(
    k4_xboole_0(sK1,sK2) = k4_xboole_0(k4_xboole_0(sK1,sK2),sK0) ),
    inference(superposition,[],[f4372,f260])).

fof(f260,plain,(
    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f200,f218])).

fof(f200,plain,(
    sK0 = k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k1_xboole_0) ),
    inference(backward_demodulation,[],[f45,f189])).

fof(f45,plain,(
    k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)),sK0) = k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k1_xboole_0) ),
    inference(superposition,[],[f21,f41])).

fof(f41,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) ),
    inference(resolution,[],[f28,f15])).

fof(f15,plain,(
    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f22,f20])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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

fof(f4372,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k4_xboole_0(X3,X2)) = X2 ),
    inference(forward_demodulation,[],[f175,f189])).

fof(f175,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k4_xboole_0(X3,X2)) = k2_xboole_0(k4_xboole_0(X2,X3),X2) ),
    inference(forward_demodulation,[],[f147,f18])).

fof(f147,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k4_xboole_0(X3,X2)) = k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k1_xboole_0)) ),
    inference(superposition,[],[f29,f31])).

fof(f4506,plain,(
    ! [X12,X13,X11] : r1_xboole_0(X13,k4_xboole_0(X11,k2_xboole_0(X12,X13))) ),
    inference(superposition,[],[f4455,f24])).

fof(f4455,plain,(
    ! [X72,X71] : r1_xboole_0(X71,k4_xboole_0(X72,X71)) ),
    inference(superposition,[],[f19,f4372])).

fof(f19,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:37:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.42  % (14364)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.45  % (14363)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.46  % (14366)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.50  % (14354)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.51  % (14362)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.52  % (14357)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (14365)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.52  % (14369)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.53  % (14353)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 1.34/0.53  % (14367)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 1.34/0.53  % (14351)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 1.34/0.54  % (14356)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 1.34/0.54  % (14359)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 1.34/0.54  % (14352)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 1.51/0.55  % (14355)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 1.51/0.55  % (14364)Refutation found. Thanks to Tanya!
% 1.51/0.55  % SZS status Theorem for theBenchmark
% 1.51/0.55  % SZS output start Proof for theBenchmark
% 1.51/0.55  fof(f8101,plain,(
% 1.51/0.55    $false),
% 1.51/0.55    inference(subsumption_resolution,[],[f8030,f16])).
% 1.51/0.55  fof(f16,plain,(
% 1.51/0.55    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 1.51/0.55    inference(cnf_transformation,[],[f13])).
% 1.51/0.55  fof(f13,plain,(
% 1.51/0.55    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 1.51/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f12])).
% 1.51/0.55  fof(f12,plain,(
% 1.51/0.55    ? [X0,X1,X2] : (~r1_xboole_0(X1,k4_xboole_0(X0,X2)) & r1_xboole_0(X0,k4_xboole_0(X1,X2))) => (~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 1.51/0.55    introduced(choice_axiom,[])).
% 1.51/0.55  fof(f11,plain,(
% 1.51/0.55    ? [X0,X1,X2] : (~r1_xboole_0(X1,k4_xboole_0(X0,X2)) & r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 1.51/0.55    inference(ennf_transformation,[],[f10])).
% 1.51/0.55  fof(f10,negated_conjecture,(
% 1.51/0.55    ~! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 1.51/0.55    inference(negated_conjecture,[],[f9])).
% 1.51/0.55  fof(f9,conjecture,(
% 1.51/0.55    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 1.51/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_xboole_1)).
% 1.51/0.55  fof(f8030,plain,(
% 1.51/0.55    r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 1.51/0.55    inference(superposition,[],[f4506,f7646])).
% 1.51/0.55  fof(f7646,plain,(
% 1.51/0.55    k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k2_xboole_0(sK2,sK1))),
% 1.51/0.55    inference(superposition,[],[f6859,f21])).
% 1.51/0.55  fof(f21,plain,(
% 1.51/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 1.51/0.55    inference(cnf_transformation,[],[f3])).
% 1.51/0.55  fof(f3,axiom,(
% 1.51/0.55    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 1.51/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.51/0.55  fof(f6859,plain,(
% 1.51/0.55    ( ! [X1] : (k4_xboole_0(sK0,X1) = k4_xboole_0(sK0,k2_xboole_0(X1,k4_xboole_0(sK1,sK2)))) )),
% 1.51/0.55    inference(superposition,[],[f6199,f24])).
% 1.51/0.55  fof(f24,plain,(
% 1.51/0.55    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.51/0.55    inference(cnf_transformation,[],[f5])).
% 1.51/0.55  fof(f5,axiom,(
% 1.51/0.55    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.51/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 1.51/0.55  fof(f6199,plain,(
% 1.51/0.55    ( ! [X20] : (k4_xboole_0(sK0,X20) = k4_xboole_0(k4_xboole_0(sK0,X20),k4_xboole_0(sK1,sK2))) )),
% 1.51/0.55    inference(superposition,[],[f4372,f4593])).
% 1.51/0.55  fof(f4593,plain,(
% 1.51/0.55    ( ! [X25] : (k4_xboole_0(sK1,sK2) = k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,X25))) )),
% 1.51/0.55    inference(forward_demodulation,[],[f4574,f761])).
% 1.51/0.55  fof(f761,plain,(
% 1.51/0.55    ( ! [X2,X3] : (k2_xboole_0(X2,k4_xboole_0(X2,X3)) = X2) )),
% 1.51/0.55    inference(forward_demodulation,[],[f738,f218])).
% 1.51/0.55  fof(f218,plain,(
% 1.51/0.55    ( ! [X1] : (k2_xboole_0(X1,k1_xboole_0) = X1) )),
% 1.51/0.55    inference(backward_demodulation,[],[f33,f201])).
% 1.51/0.55  fof(f201,plain,(
% 1.51/0.55    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 1.51/0.55    inference(superposition,[],[f189,f18])).
% 1.51/0.55  fof(f18,plain,(
% 1.51/0.55    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.51/0.55    inference(cnf_transformation,[],[f4])).
% 1.51/0.55  fof(f4,axiom,(
% 1.51/0.55    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.51/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.51/0.55  fof(f189,plain,(
% 1.51/0.55    ( ! [X4,X3] : (k2_xboole_0(k4_xboole_0(X3,X4),X3) = X3) )),
% 1.51/0.55    inference(forward_demodulation,[],[f188,f18])).
% 1.51/0.55  fof(f188,plain,(
% 1.51/0.55    ( ! [X4,X3] : (k2_xboole_0(k4_xboole_0(X3,X4),X3) = k4_xboole_0(X3,k1_xboole_0)) )),
% 1.51/0.55    inference(forward_demodulation,[],[f158,f31])).
% 1.51/0.55  fof(f31,plain,(
% 1.51/0.55    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.51/0.55    inference(forward_demodulation,[],[f26,f18])).
% 1.51/0.55  fof(f26,plain,(
% 1.51/0.55    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 1.51/0.55    inference(definition_unfolding,[],[f17,f20])).
% 1.51/0.55  fof(f20,plain,(
% 1.51/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.51/0.55    inference(cnf_transformation,[],[f6])).
% 1.51/0.55  fof(f6,axiom,(
% 1.51/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.51/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.51/0.55  fof(f17,plain,(
% 1.51/0.55    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.51/0.55    inference(cnf_transformation,[],[f2])).
% 1.51/0.55  fof(f2,axiom,(
% 1.51/0.55    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.51/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 1.51/0.55  fof(f158,plain,(
% 1.51/0.55    ( ! [X4,X3] : (k2_xboole_0(k4_xboole_0(X3,X4),X3) = k4_xboole_0(X3,k4_xboole_0(X4,X4))) )),
% 1.51/0.55    inference(superposition,[],[f29,f21])).
% 1.51/0.55  fof(f29,plain,(
% 1.51/0.55    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) )),
% 1.51/0.55    inference(definition_unfolding,[],[f25,f20])).
% 1.51/0.55  fof(f25,plain,(
% 1.51/0.55    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 1.51/0.55    inference(cnf_transformation,[],[f7])).
% 1.51/0.55  fof(f7,axiom,(
% 1.51/0.55    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 1.51/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).
% 1.51/0.55  fof(f33,plain,(
% 1.51/0.55    ( ! [X1] : (k2_xboole_0(X1,X1) = k2_xboole_0(X1,k1_xboole_0)) )),
% 1.51/0.55    inference(superposition,[],[f21,f31])).
% 1.51/0.55  fof(f738,plain,(
% 1.51/0.55    ( ! [X2,X3] : (k2_xboole_0(X2,k1_xboole_0) = k2_xboole_0(X2,k4_xboole_0(X2,X3))) )),
% 1.51/0.55    inference(superposition,[],[f21,f684])).
% 1.51/0.55  fof(f684,plain,(
% 1.51/0.55    ( ! [X8,X9] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X8,X9),X8)) )),
% 1.51/0.55    inference(superposition,[],[f676,f189])).
% 1.51/0.55  fof(f676,plain,(
% 1.51/0.55    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X3))) )),
% 1.51/0.55    inference(forward_demodulation,[],[f58,f217])).
% 1.51/0.55  fof(f217,plain,(
% 1.51/0.55    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X3)) )),
% 1.51/0.55    inference(backward_demodulation,[],[f86,f201])).
% 1.51/0.55  fof(f86,plain,(
% 1.51/0.55    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k2_xboole_0(X3,X3))) )),
% 1.51/0.55    inference(superposition,[],[f72,f33])).
% 1.51/0.55  fof(f72,plain,(
% 1.51/0.55    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,X5))) )),
% 1.51/0.55    inference(forward_demodulation,[],[f63,f21])).
% 1.51/0.55  fof(f63,plain,(
% 1.51/0.55    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,X6)))) )),
% 1.51/0.55    inference(superposition,[],[f24,f31])).
% 1.51/0.55  fof(f58,plain,(
% 1.51/0.55    ( ! [X2,X3] : (k4_xboole_0(k1_xboole_0,X3) = k4_xboole_0(X2,k2_xboole_0(X2,X3))) )),
% 1.51/0.55    inference(superposition,[],[f24,f31])).
% 1.51/0.55  fof(f4574,plain,(
% 1.51/0.55    ( ! [X25] : (k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,X25)) = k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),X25)))) )),
% 1.51/0.55    inference(superposition,[],[f29,f4383])).
% 1.51/0.55  fof(f4383,plain,(
% 1.51/0.55    k4_xboole_0(sK1,sK2) = k4_xboole_0(k4_xboole_0(sK1,sK2),sK0)),
% 1.51/0.55    inference(superposition,[],[f4372,f260])).
% 1.51/0.55  fof(f260,plain,(
% 1.51/0.55    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 1.51/0.55    inference(superposition,[],[f200,f218])).
% 1.51/0.55  fof(f200,plain,(
% 1.51/0.55    sK0 = k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k1_xboole_0)),
% 1.51/0.55    inference(backward_demodulation,[],[f45,f189])).
% 1.51/0.55  fof(f45,plain,(
% 1.51/0.55    k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)),sK0) = k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k1_xboole_0)),
% 1.51/0.55    inference(superposition,[],[f21,f41])).
% 1.51/0.55  fof(f41,plain,(
% 1.51/0.55    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 1.51/0.55    inference(resolution,[],[f28,f15])).
% 1.51/0.55  fof(f15,plain,(
% 1.51/0.55    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 1.51/0.55    inference(cnf_transformation,[],[f13])).
% 1.51/0.55  fof(f28,plain,(
% 1.51/0.55    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.51/0.55    inference(definition_unfolding,[],[f22,f20])).
% 1.51/0.55  fof(f22,plain,(
% 1.51/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.51/0.55    inference(cnf_transformation,[],[f14])).
% 1.51/0.55  fof(f14,plain,(
% 1.51/0.55    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.51/0.55    inference(nnf_transformation,[],[f1])).
% 1.51/0.55  fof(f1,axiom,(
% 1.51/0.55    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.51/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.51/0.55  fof(f4372,plain,(
% 1.51/0.55    ( ! [X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X3,X2)) = X2) )),
% 1.51/0.55    inference(forward_demodulation,[],[f175,f189])).
% 1.51/0.55  fof(f175,plain,(
% 1.51/0.55    ( ! [X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X3,X2)) = k2_xboole_0(k4_xboole_0(X2,X3),X2)) )),
% 1.51/0.55    inference(forward_demodulation,[],[f147,f18])).
% 1.51/0.55  fof(f147,plain,(
% 1.51/0.55    ( ! [X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X3,X2)) = k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k1_xboole_0))) )),
% 1.51/0.55    inference(superposition,[],[f29,f31])).
% 1.51/0.55  fof(f4506,plain,(
% 1.51/0.55    ( ! [X12,X13,X11] : (r1_xboole_0(X13,k4_xboole_0(X11,k2_xboole_0(X12,X13)))) )),
% 1.51/0.55    inference(superposition,[],[f4455,f24])).
% 1.51/0.55  fof(f4455,plain,(
% 1.51/0.55    ( ! [X72,X71] : (r1_xboole_0(X71,k4_xboole_0(X72,X71))) )),
% 1.51/0.55    inference(superposition,[],[f19,f4372])).
% 1.51/0.55  fof(f19,plain,(
% 1.51/0.55    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.51/0.55    inference(cnf_transformation,[],[f8])).
% 1.51/0.55  fof(f8,axiom,(
% 1.51/0.55    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 1.51/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 1.51/0.55  % SZS output end Proof for theBenchmark
% 1.51/0.55  % (14364)------------------------------
% 1.51/0.55  % (14364)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.55  % (14364)Termination reason: Refutation
% 1.51/0.55  
% 1.51/0.55  % (14364)Memory used [KB]: 5500
% 1.51/0.55  % (14364)Time elapsed: 0.140 s
% 1.51/0.55  % (14364)------------------------------
% 1.51/0.55  % (14364)------------------------------
% 1.51/0.56  % (14350)Success in time 0.191 s
%------------------------------------------------------------------------------
