%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:59 EST 2020

% Result     : Theorem 44.12s
% Output     : Refutation 44.12s
% Verified   : 
% Statistics : Number of formulae       :   49 (  81 expanded)
%              Number of leaves         :   11 (  25 expanded)
%              Depth                    :   13
%              Number of atoms          :   71 ( 117 expanded)
%              Number of equality atoms :   43 (  74 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f65530,plain,(
    $false ),
    inference(subsumption_resolution,[],[f65529,f22])).

fof(f22,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
    & r1_tarski(sK2,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2] :
        ( k4_xboole_0(X0,X2) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2)))
        & r1_tarski(X2,X1) )
   => ( k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
      & r1_tarski(sK2,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(X0,X2) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2)))
      & r1_tarski(X2,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X2,X1)
       => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X2,X1)
     => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_xboole_1)).

fof(f65529,plain,(
    ~ r1_tarski(sK2,sK1) ),
    inference(trivial_inequality_removal,[],[f65506])).

fof(f65506,plain,
    ( k4_xboole_0(sK0,sK2) != k4_xboole_0(sK0,sK2)
    | ~ r1_tarski(sK2,sK1) ),
    inference(superposition,[],[f65500,f37])).

fof(f37,plain,(
    ! [X4,X3] :
      ( k3_xboole_0(X4,X3) = X3
      | ~ r1_tarski(X3,X4) ) ),
    inference(superposition,[],[f31,f27])).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f65500,plain,(
    k4_xboole_0(sK0,sK2) != k4_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f65499,f26])).

fof(f26,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f65499,plain,
    ( k4_xboole_0(sK0,sK2) != k4_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ~ r1_tarski(k4_xboole_0(sK1,sK2),sK1) ),
    inference(subsumption_resolution,[],[f65470,f122])).

fof(f122,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(superposition,[],[f66,f25])).

fof(f25,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f66,plain,(
    ! [X6,X7] : r1_tarski(k3_xboole_0(X6,X7),X6) ),
    inference(superposition,[],[f26,f30])).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f65470,plain,
    ( k4_xboole_0(sK0,sK2) != k4_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ~ r1_tarski(sK1,sK1)
    | ~ r1_tarski(k4_xboole_0(sK1,sK2),sK1) ),
    inference(superposition,[],[f53128,f30])).

fof(f53128,plain,(
    ! [X783] :
      ( k4_xboole_0(sK0,sK2) != k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(X783,sK2)))
      | ~ r1_tarski(X783,sK1)
      | ~ r1_tarski(k4_xboole_0(sK1,sK2),X783) ) ),
    inference(forward_demodulation,[],[f52893,f15010])).

fof(f15010,plain,(
    ! [X26,X27,X25] : k4_xboole_0(X25,k4_xboole_0(X26,X27)) = k2_xboole_0(k4_xboole_0(X25,X26),k3_xboole_0(X25,X27)) ),
    inference(forward_demodulation,[],[f14948,f1089])).

fof(f1089,plain,(
    ! [X6,X7,X5] : k5_xboole_0(k4_xboole_0(X5,X6),k3_xboole_0(X7,k3_xboole_0(X5,X6))) = k4_xboole_0(X5,k4_xboole_0(X6,X7)) ),
    inference(forward_demodulation,[],[f1088,f29])).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f1088,plain,(
    ! [X6,X7,X5] : k5_xboole_0(k4_xboole_0(X5,X6),k3_xboole_0(X7,k3_xboole_0(X5,X6))) = k5_xboole_0(X5,k3_xboole_0(X5,k4_xboole_0(X6,X7))) ),
    inference(forward_demodulation,[],[f1066,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f1066,plain,(
    ! [X6,X7,X5] : k5_xboole_0(k4_xboole_0(X5,X6),k3_xboole_0(X7,k3_xboole_0(X5,X6))) = k5_xboole_0(X5,k4_xboole_0(k3_xboole_0(X5,X6),X7)) ),
    inference(superposition,[],[f71,f56])).

fof(f56,plain,(
    ! [X4,X3] : k4_xboole_0(X3,X4) = k5_xboole_0(X3,k3_xboole_0(X4,X3)) ),
    inference(superposition,[],[f29,f27])).

fof(f71,plain,(
    ! [X4,X5,X3] : k5_xboole_0(X3,k5_xboole_0(k3_xboole_0(X3,X4),X5)) = k5_xboole_0(k4_xboole_0(X3,X4),X5) ),
    inference(superposition,[],[f34,f29])).

fof(f34,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f14948,plain,(
    ! [X26,X27,X25] : k2_xboole_0(k4_xboole_0(X25,X26),k3_xboole_0(X25,X27)) = k5_xboole_0(k4_xboole_0(X25,X26),k3_xboole_0(X27,k3_xboole_0(X25,X26))) ),
    inference(superposition,[],[f540,f30])).

fof(f540,plain,(
    ! [X10,X11,X9] : k2_xboole_0(X11,k3_xboole_0(X9,X10)) = k5_xboole_0(X11,k3_xboole_0(X10,k4_xboole_0(X9,X11))) ),
    inference(superposition,[],[f28,f83])).

fof(f83,plain,(
    ! [X6,X7,X5] : k3_xboole_0(X5,k4_xboole_0(X6,X7)) = k4_xboole_0(k3_xboole_0(X6,X5),X7) ),
    inference(superposition,[],[f35,f27])).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f52893,plain,(
    ! [X783] :
      ( k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(X783,sK2)))
      | ~ r1_tarski(X783,sK1)
      | ~ r1_tarski(k4_xboole_0(sK1,sK2),X783) ) ),
    inference(superposition,[],[f23,f778])).

fof(f778,plain,(
    ! [X8,X7,X9] :
      ( k4_xboole_0(X8,X9) = k4_xboole_0(X7,X9)
      | ~ r1_tarski(X7,X8)
      | ~ r1_tarski(k4_xboole_0(X8,X9),X7) ) ),
    inference(superposition,[],[f82,f37])).

fof(f82,plain,(
    ! [X4,X2,X3] :
      ( k3_xboole_0(X2,k4_xboole_0(X3,X4)) = k4_xboole_0(X2,X4)
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f35,f31])).

fof(f23,plain,(
    k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:29:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (24405)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.46  % (24397)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (24398)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (24400)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (24410)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.47  % (24396)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (24394)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.47  % (24399)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (24401)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.48  % (24407)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.49  % (24411)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.49  % (24402)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.49  % (24395)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.49  % (24409)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.49  % (24408)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.50  % (24404)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.51  % (24403)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.51  % (24412)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 4.83/1.03  % (24398)Time limit reached!
% 4.83/1.03  % (24398)------------------------------
% 4.83/1.03  % (24398)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.83/1.03  % (24398)Termination reason: Time limit
% 4.83/1.03  
% 4.83/1.03  % (24398)Memory used [KB]: 17910
% 5.39/1.03  % (24398)Time elapsed: 0.622 s
% 5.39/1.03  % (24398)------------------------------
% 5.39/1.03  % (24398)------------------------------
% 12.49/1.93  % (24400)Time limit reached!
% 12.49/1.93  % (24400)------------------------------
% 12.49/1.93  % (24400)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.49/1.95  % (24400)Termination reason: Time limit
% 12.49/1.95  
% 12.49/1.95  % (24400)Memory used [KB]: 42344
% 12.49/1.95  % (24400)Time elapsed: 1.525 s
% 12.49/1.95  % (24400)------------------------------
% 12.49/1.95  % (24400)------------------------------
% 12.49/1.96  % (24399)Time limit reached!
% 12.49/1.96  % (24399)------------------------------
% 12.49/1.96  % (24399)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.49/1.96  % (24399)Termination reason: Time limit
% 12.49/1.96  % (24399)Termination phase: Saturation
% 12.49/1.96  
% 12.49/1.96  % (24399)Memory used [KB]: 25713
% 12.49/1.96  % (24399)Time elapsed: 1.500 s
% 12.49/1.96  % (24399)------------------------------
% 12.49/1.96  % (24399)------------------------------
% 14.30/2.22  % (24396)Time limit reached!
% 14.30/2.22  % (24396)------------------------------
% 14.30/2.22  % (24396)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.30/2.23  % (24396)Termination reason: Time limit
% 14.30/2.23  % (24396)Termination phase: Saturation
% 14.30/2.23  
% 14.30/2.23  % (24396)Memory used [KB]: 43240
% 14.30/2.23  % (24396)Time elapsed: 1.800 s
% 14.30/2.23  % (24396)------------------------------
% 14.30/2.23  % (24396)------------------------------
% 17.79/2.61  % (24407)Time limit reached!
% 17.79/2.61  % (24407)------------------------------
% 17.79/2.61  % (24407)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.79/2.61  % (24407)Termination reason: Time limit
% 17.79/2.61  % (24407)Termination phase: Saturation
% 17.79/2.61  
% 17.79/2.61  % (24407)Memory used [KB]: 72791
% 17.79/2.61  % (24407)Time elapsed: 2.200 s
% 17.79/2.61  % (24407)------------------------------
% 17.79/2.61  % (24407)------------------------------
% 44.12/5.93  % (24397)Refutation found. Thanks to Tanya!
% 44.12/5.93  % SZS status Theorem for theBenchmark
% 44.12/5.93  % SZS output start Proof for theBenchmark
% 44.12/5.93  fof(f65530,plain,(
% 44.12/5.93    $false),
% 44.12/5.93    inference(subsumption_resolution,[],[f65529,f22])).
% 44.12/5.93  fof(f22,plain,(
% 44.12/5.93    r1_tarski(sK2,sK1)),
% 44.12/5.93    inference(cnf_transformation,[],[f20])).
% 44.12/5.93  fof(f20,plain,(
% 44.12/5.93    k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) & r1_tarski(sK2,sK1)),
% 44.12/5.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f19])).
% 44.12/5.93  fof(f19,plain,(
% 44.12/5.93    ? [X0,X1,X2] : (k4_xboole_0(X0,X2) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) & r1_tarski(X2,X1)) => (k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) & r1_tarski(sK2,sK1))),
% 44.12/5.93    introduced(choice_axiom,[])).
% 44.12/5.93  fof(f17,plain,(
% 44.12/5.93    ? [X0,X1,X2] : (k4_xboole_0(X0,X2) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) & r1_tarski(X2,X1))),
% 44.12/5.93    inference(ennf_transformation,[],[f14])).
% 44.12/5.93  fof(f14,negated_conjecture,(
% 44.12/5.93    ~! [X0,X1,X2] : (r1_tarski(X2,X1) => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))))),
% 44.12/5.93    inference(negated_conjecture,[],[f13])).
% 44.12/5.93  fof(f13,conjecture,(
% 44.12/5.93    ! [X0,X1,X2] : (r1_tarski(X2,X1) => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))))),
% 44.12/5.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_xboole_1)).
% 44.12/5.93  fof(f65529,plain,(
% 44.12/5.93    ~r1_tarski(sK2,sK1)),
% 44.12/5.93    inference(trivial_inequality_removal,[],[f65506])).
% 44.12/5.93  fof(f65506,plain,(
% 44.12/5.93    k4_xboole_0(sK0,sK2) != k4_xboole_0(sK0,sK2) | ~r1_tarski(sK2,sK1)),
% 44.12/5.93    inference(superposition,[],[f65500,f37])).
% 44.12/5.93  fof(f37,plain,(
% 44.12/5.93    ( ! [X4,X3] : (k3_xboole_0(X4,X3) = X3 | ~r1_tarski(X3,X4)) )),
% 44.12/5.93    inference(superposition,[],[f31,f27])).
% 44.12/5.93  fof(f27,plain,(
% 44.12/5.93    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 44.12/5.93    inference(cnf_transformation,[],[f1])).
% 44.12/5.93  fof(f1,axiom,(
% 44.12/5.93    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 44.12/5.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 44.12/5.93  fof(f31,plain,(
% 44.12/5.93    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 44.12/5.93    inference(cnf_transformation,[],[f18])).
% 44.12/5.93  fof(f18,plain,(
% 44.12/5.93    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 44.12/5.93    inference(ennf_transformation,[],[f7])).
% 44.12/5.93  fof(f7,axiom,(
% 44.12/5.93    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 44.12/5.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 44.12/5.93  fof(f65500,plain,(
% 44.12/5.93    k4_xboole_0(sK0,sK2) != k4_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 44.12/5.93    inference(subsumption_resolution,[],[f65499,f26])).
% 44.12/5.93  fof(f26,plain,(
% 44.12/5.93    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 44.12/5.93    inference(cnf_transformation,[],[f8])).
% 44.12/5.93  fof(f8,axiom,(
% 44.12/5.93    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 44.12/5.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 44.12/5.93  fof(f65499,plain,(
% 44.12/5.93    k4_xboole_0(sK0,sK2) != k4_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | ~r1_tarski(k4_xboole_0(sK1,sK2),sK1)),
% 44.12/5.93    inference(subsumption_resolution,[],[f65470,f122])).
% 44.12/5.93  fof(f122,plain,(
% 44.12/5.93    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 44.12/5.93    inference(superposition,[],[f66,f25])).
% 44.12/5.93  fof(f25,plain,(
% 44.12/5.93    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 44.12/5.93    inference(cnf_transformation,[],[f16])).
% 44.12/5.93  fof(f16,plain,(
% 44.12/5.93    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 44.12/5.93    inference(rectify,[],[f3])).
% 44.12/5.93  fof(f3,axiom,(
% 44.12/5.93    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 44.12/5.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 44.12/5.93  fof(f66,plain,(
% 44.12/5.93    ( ! [X6,X7] : (r1_tarski(k3_xboole_0(X6,X7),X6)) )),
% 44.12/5.93    inference(superposition,[],[f26,f30])).
% 44.12/5.93  fof(f30,plain,(
% 44.12/5.93    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 44.12/5.93    inference(cnf_transformation,[],[f9])).
% 44.12/5.93  fof(f9,axiom,(
% 44.12/5.93    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 44.12/5.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 44.12/5.93  fof(f65470,plain,(
% 44.12/5.93    k4_xboole_0(sK0,sK2) != k4_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | ~r1_tarski(sK1,sK1) | ~r1_tarski(k4_xboole_0(sK1,sK2),sK1)),
% 44.12/5.93    inference(superposition,[],[f53128,f30])).
% 44.12/5.93  fof(f53128,plain,(
% 44.12/5.93    ( ! [X783] : (k4_xboole_0(sK0,sK2) != k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(X783,sK2))) | ~r1_tarski(X783,sK1) | ~r1_tarski(k4_xboole_0(sK1,sK2),X783)) )),
% 44.12/5.93    inference(forward_demodulation,[],[f52893,f15010])).
% 44.12/5.93  fof(f15010,plain,(
% 44.12/5.93    ( ! [X26,X27,X25] : (k4_xboole_0(X25,k4_xboole_0(X26,X27)) = k2_xboole_0(k4_xboole_0(X25,X26),k3_xboole_0(X25,X27))) )),
% 44.12/5.93    inference(forward_demodulation,[],[f14948,f1089])).
% 44.12/5.93  fof(f1089,plain,(
% 44.12/5.93    ( ! [X6,X7,X5] : (k5_xboole_0(k4_xboole_0(X5,X6),k3_xboole_0(X7,k3_xboole_0(X5,X6))) = k4_xboole_0(X5,k4_xboole_0(X6,X7))) )),
% 44.12/5.93    inference(forward_demodulation,[],[f1088,f29])).
% 44.12/5.93  fof(f29,plain,(
% 44.12/5.93    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 44.12/5.93    inference(cnf_transformation,[],[f5])).
% 44.12/5.93  fof(f5,axiom,(
% 44.12/5.93    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 44.12/5.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 44.12/5.93  fof(f1088,plain,(
% 44.12/5.93    ( ! [X6,X7,X5] : (k5_xboole_0(k4_xboole_0(X5,X6),k3_xboole_0(X7,k3_xboole_0(X5,X6))) = k5_xboole_0(X5,k3_xboole_0(X5,k4_xboole_0(X6,X7)))) )),
% 44.12/5.93    inference(forward_demodulation,[],[f1066,f35])).
% 44.12/5.93  fof(f35,plain,(
% 44.12/5.93    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 44.12/5.93    inference(cnf_transformation,[],[f10])).
% 44.12/5.93  fof(f10,axiom,(
% 44.12/5.93    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 44.12/5.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 44.12/5.93  fof(f1066,plain,(
% 44.12/5.93    ( ! [X6,X7,X5] : (k5_xboole_0(k4_xboole_0(X5,X6),k3_xboole_0(X7,k3_xboole_0(X5,X6))) = k5_xboole_0(X5,k4_xboole_0(k3_xboole_0(X5,X6),X7))) )),
% 44.12/5.93    inference(superposition,[],[f71,f56])).
% 44.12/5.93  fof(f56,plain,(
% 44.12/5.93    ( ! [X4,X3] : (k4_xboole_0(X3,X4) = k5_xboole_0(X3,k3_xboole_0(X4,X3))) )),
% 44.12/5.93    inference(superposition,[],[f29,f27])).
% 44.12/5.93  fof(f71,plain,(
% 44.12/5.93    ( ! [X4,X5,X3] : (k5_xboole_0(X3,k5_xboole_0(k3_xboole_0(X3,X4),X5)) = k5_xboole_0(k4_xboole_0(X3,X4),X5)) )),
% 44.12/5.93    inference(superposition,[],[f34,f29])).
% 44.12/5.93  fof(f34,plain,(
% 44.12/5.93    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 44.12/5.93    inference(cnf_transformation,[],[f11])).
% 44.12/5.93  fof(f11,axiom,(
% 44.12/5.93    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 44.12/5.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 44.12/5.93  fof(f14948,plain,(
% 44.12/5.93    ( ! [X26,X27,X25] : (k2_xboole_0(k4_xboole_0(X25,X26),k3_xboole_0(X25,X27)) = k5_xboole_0(k4_xboole_0(X25,X26),k3_xboole_0(X27,k3_xboole_0(X25,X26)))) )),
% 44.12/5.93    inference(superposition,[],[f540,f30])).
% 44.12/5.93  fof(f540,plain,(
% 44.12/5.93    ( ! [X10,X11,X9] : (k2_xboole_0(X11,k3_xboole_0(X9,X10)) = k5_xboole_0(X11,k3_xboole_0(X10,k4_xboole_0(X9,X11)))) )),
% 44.12/5.93    inference(superposition,[],[f28,f83])).
% 44.12/5.93  fof(f83,plain,(
% 44.12/5.93    ( ! [X6,X7,X5] : (k3_xboole_0(X5,k4_xboole_0(X6,X7)) = k4_xboole_0(k3_xboole_0(X6,X5),X7)) )),
% 44.12/5.93    inference(superposition,[],[f35,f27])).
% 44.12/5.93  fof(f28,plain,(
% 44.12/5.93    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 44.12/5.93    inference(cnf_transformation,[],[f12])).
% 44.12/5.93  fof(f12,axiom,(
% 44.12/5.93    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 44.12/5.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 44.12/5.93  fof(f52893,plain,(
% 44.12/5.93    ( ! [X783] : (k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(X783,sK2))) | ~r1_tarski(X783,sK1) | ~r1_tarski(k4_xboole_0(sK1,sK2),X783)) )),
% 44.12/5.93    inference(superposition,[],[f23,f778])).
% 44.12/5.93  fof(f778,plain,(
% 44.12/5.93    ( ! [X8,X7,X9] : (k4_xboole_0(X8,X9) = k4_xboole_0(X7,X9) | ~r1_tarski(X7,X8) | ~r1_tarski(k4_xboole_0(X8,X9),X7)) )),
% 44.12/5.93    inference(superposition,[],[f82,f37])).
% 44.12/5.93  fof(f82,plain,(
% 44.12/5.93    ( ! [X4,X2,X3] : (k3_xboole_0(X2,k4_xboole_0(X3,X4)) = k4_xboole_0(X2,X4) | ~r1_tarski(X2,X3)) )),
% 44.12/5.93    inference(superposition,[],[f35,f31])).
% 44.12/5.93  fof(f23,plain,(
% 44.12/5.93    k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 44.12/5.93    inference(cnf_transformation,[],[f20])).
% 44.12/5.93  % SZS output end Proof for theBenchmark
% 44.12/5.93  % (24397)------------------------------
% 44.12/5.93  % (24397)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 44.12/5.93  % (24397)Termination reason: Refutation
% 44.12/5.93  
% 44.12/5.93  % (24397)Memory used [KB]: 47206
% 44.12/5.93  % (24397)Time elapsed: 5.508 s
% 44.12/5.93  % (24397)------------------------------
% 44.12/5.93  % (24397)------------------------------
% 44.12/5.93  % (24391)Success in time 5.574 s
%------------------------------------------------------------------------------
