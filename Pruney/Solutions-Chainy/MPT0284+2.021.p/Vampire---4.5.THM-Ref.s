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
% DateTime   : Thu Dec  3 12:41:41 EST 2020

% Result     : Theorem 1.28s
% Output     : Refutation 1.28s
% Verified   : 
% Statistics : Number of formulae       :   46 (  59 expanded)
%              Number of leaves         :   12 (  17 expanded)
%              Depth                    :   12
%              Number of atoms          :   74 (  98 expanded)
%              Number of equality atoms :   11 (  15 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1651,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1648,f34])).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_xboole_1)).

fof(f1648,plain,(
    ~ r1_tarski(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f1638,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

fof(f1638,plain,(
    ~ r1_tarski(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f1635,f54])).

fof(f54,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X1,X0)) ),
    inference(superposition,[],[f34,f33])).

fof(f33,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f1635,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
    | ~ r1_tarski(k4_xboole_0(sK1,sK0),k5_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f1614,f41])).

fof(f1614,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k4_xboole_0(sK1,sK0)),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
    | ~ r1_tarski(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f1610,f237])).

fof(f237,plain,(
    ! [X14,X12,X13] :
      ( r1_tarski(k1_zfmisc_1(k3_xboole_0(X12,X13)),X14)
      | ~ r1_tarski(k1_zfmisc_1(X13),X14) ) ),
    inference(superposition,[],[f161,f38])).

fof(f38,plain,(
    ! [X0,X1] : k1_zfmisc_1(k3_xboole_0(X0,X1)) = k3_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] : k1_zfmisc_1(k3_xboole_0(X0,X1)) = k3_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_zfmisc_1)).

fof(f161,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X2,X0),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f99,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f99,plain,(
    ! [X4,X5,X3] : r1_tarski(k3_xboole_0(X5,k3_xboole_0(X4,X3)),X3) ),
    inference(superposition,[],[f66,f32])).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f66,plain,(
    ! [X6,X8,X7] : r1_tarski(k3_xboole_0(X6,k3_xboole_0(X7,X8)),X7) ),
    inference(resolution,[],[f44,f50])).

fof(f50,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0) ),
    inference(superposition,[],[f31,f32])).

fof(f31,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_xboole_0(X1,X2))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).

fof(f1610,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
    | ~ r1_tarski(k1_zfmisc_1(k4_xboole_0(sK1,sK0)),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
    | ~ r1_tarski(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    inference(resolution,[],[f1235,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k5_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k5_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k5_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_xboole_1)).

fof(f1235,plain,
    ( ~ r1_tarski(k5_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
    | ~ r1_tarski(k1_zfmisc_1(k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f1217,f38])).

fof(f1217,plain,
    ( ~ r1_tarski(k3_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
    | ~ r1_tarski(k5_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    inference(resolution,[],[f157,f30])).

fof(f30,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f28])).

fof(f28,plain,
    ( ? [X0,X1] : ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1)))
   => ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] : ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1))) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1))) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_zfmisc_1)).

fof(f157,plain,(
    ! [X10,X11,X9] :
      ( r1_tarski(k2_xboole_0(X9,X10),X11)
      | ~ r1_tarski(k3_xboole_0(X9,X10),X11)
      | ~ r1_tarski(k5_xboole_0(X9,X10),X11) ) ),
    inference(superposition,[],[f45,f39])).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:35:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (20797)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.47  % (20796)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.47  % (20802)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.47  % (20802)Refutation not found, incomplete strategy% (20802)------------------------------
% 0.22/0.47  % (20802)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (20806)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.47  % (20794)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.48  % (20805)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.48  % (20804)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.48  % (20800)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.49  % (20802)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (20802)Memory used [KB]: 10618
% 0.22/0.49  % (20802)Time elapsed: 0.061 s
% 0.22/0.49  % (20802)------------------------------
% 0.22/0.49  % (20802)------------------------------
% 0.22/0.49  % (20808)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.49  % (20803)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.49  % (20801)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.49  % (20793)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.50  % (20795)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.50  % (20807)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.50  % (20791)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.51  % (20792)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.51  % (20798)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.52  % (20799)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 1.28/0.53  % (20794)Refutation found. Thanks to Tanya!
% 1.28/0.53  % SZS status Theorem for theBenchmark
% 1.28/0.53  % SZS output start Proof for theBenchmark
% 1.28/0.53  fof(f1651,plain,(
% 1.28/0.53    $false),
% 1.28/0.53    inference(subsumption_resolution,[],[f1648,f34])).
% 1.28/0.53  fof(f34,plain,(
% 1.28/0.53    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 1.28/0.53    inference(cnf_transformation,[],[f10])).
% 1.28/0.53  fof(f10,axiom,(
% 1.28/0.53    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 1.28/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_xboole_1)).
% 1.28/0.53  fof(f1648,plain,(
% 1.28/0.53    ~r1_tarski(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1))),
% 1.28/0.53    inference(resolution,[],[f1638,f41])).
% 1.28/0.53  fof(f41,plain,(
% 1.28/0.53    ( ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f24])).
% 1.28/0.53  fof(f24,plain,(
% 1.28/0.53    ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 1.28/0.53    inference(ennf_transformation,[],[f18])).
% 1.28/0.53  fof(f18,axiom,(
% 1.28/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)))),
% 1.28/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).
% 1.28/0.53  fof(f1638,plain,(
% 1.28/0.53    ~r1_tarski(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 1.28/0.53    inference(subsumption_resolution,[],[f1635,f54])).
% 1.28/0.53  fof(f54,plain,(
% 1.28/0.53    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X1,X0))) )),
% 1.28/0.53    inference(superposition,[],[f34,f33])).
% 1.28/0.53  fof(f33,plain,(
% 1.28/0.53    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f2])).
% 1.28/0.53  fof(f2,axiom,(
% 1.28/0.53    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.28/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.28/0.53  fof(f1635,plain,(
% 1.28/0.53    ~r1_tarski(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) | ~r1_tarski(k4_xboole_0(sK1,sK0),k5_xboole_0(sK0,sK1))),
% 1.28/0.53    inference(resolution,[],[f1614,f41])).
% 1.28/0.53  fof(f1614,plain,(
% 1.28/0.53    ~r1_tarski(k1_zfmisc_1(k4_xboole_0(sK1,sK0)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) | ~r1_tarski(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 1.28/0.53    inference(subsumption_resolution,[],[f1610,f237])).
% 1.28/0.53  fof(f237,plain,(
% 1.28/0.53    ( ! [X14,X12,X13] : (r1_tarski(k1_zfmisc_1(k3_xboole_0(X12,X13)),X14) | ~r1_tarski(k1_zfmisc_1(X13),X14)) )),
% 1.28/0.53    inference(superposition,[],[f161,f38])).
% 1.28/0.53  fof(f38,plain,(
% 1.28/0.53    ( ! [X0,X1] : (k1_zfmisc_1(k3_xboole_0(X0,X1)) = k3_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1))) )),
% 1.28/0.53    inference(cnf_transformation,[],[f19])).
% 1.28/0.53  fof(f19,axiom,(
% 1.28/0.53    ! [X0,X1] : k1_zfmisc_1(k3_xboole_0(X0,X1)) = k3_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1))),
% 1.28/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_zfmisc_1)).
% 1.28/0.53  fof(f161,plain,(
% 1.28/0.53    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X2,X0),X1) | ~r1_tarski(X0,X1)) )),
% 1.28/0.53    inference(superposition,[],[f99,f40])).
% 1.28/0.53  fof(f40,plain,(
% 1.28/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f23])).
% 1.28/0.53  fof(f23,plain,(
% 1.28/0.53    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.28/0.53    inference(ennf_transformation,[],[f7])).
% 1.28/0.53  fof(f7,axiom,(
% 1.28/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.28/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.28/0.53  fof(f99,plain,(
% 1.28/0.53    ( ! [X4,X5,X3] : (r1_tarski(k3_xboole_0(X5,k3_xboole_0(X4,X3)),X3)) )),
% 1.28/0.53    inference(superposition,[],[f66,f32])).
% 1.28/0.53  fof(f32,plain,(
% 1.28/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f1])).
% 1.28/0.53  fof(f1,axiom,(
% 1.28/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.28/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.28/0.53  fof(f66,plain,(
% 1.28/0.53    ( ! [X6,X8,X7] : (r1_tarski(k3_xboole_0(X6,k3_xboole_0(X7,X8)),X7)) )),
% 1.28/0.53    inference(resolution,[],[f44,f50])).
% 1.28/0.53  fof(f50,plain,(
% 1.28/0.53    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) )),
% 1.28/0.53    inference(superposition,[],[f31,f32])).
% 1.28/0.53  fof(f31,plain,(
% 1.28/0.53    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f5])).
% 1.28/0.53  fof(f5,axiom,(
% 1.28/0.53    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.28/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.28/0.53  fof(f44,plain,(
% 1.28/0.53    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_xboole_0(X1,X2)) | r1_tarski(X0,X1)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f25])).
% 1.28/0.53  fof(f25,plain,(
% 1.28/0.53    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 1.28/0.53    inference(ennf_transformation,[],[f6])).
% 1.28/0.53  fof(f6,axiom,(
% 1.28/0.53    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 1.28/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).
% 1.28/0.53  fof(f1610,plain,(
% 1.28/0.53    ~r1_tarski(k1_zfmisc_1(k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) | ~r1_tarski(k1_zfmisc_1(k4_xboole_0(sK1,sK0)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) | ~r1_tarski(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 1.28/0.53    inference(resolution,[],[f1235,f45])).
% 1.28/0.53  fof(f45,plain,(
% 1.28/0.53    ( ! [X2,X0,X1] : (r1_tarski(k5_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f27])).
% 1.28/0.53  fof(f27,plain,(
% 1.28/0.53    ! [X0,X1,X2] : (r1_tarski(k5_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 1.28/0.53    inference(flattening,[],[f26])).
% 1.28/0.53  fof(f26,plain,(
% 1.28/0.53    ! [X0,X1,X2] : (r1_tarski(k5_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 1.28/0.53    inference(ennf_transformation,[],[f4])).
% 1.28/0.53  fof(f4,axiom,(
% 1.28/0.53    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k5_xboole_0(X0,X2),X1))),
% 1.28/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_xboole_1)).
% 1.28/0.53  fof(f1235,plain,(
% 1.28/0.53    ~r1_tarski(k5_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) | ~r1_tarski(k1_zfmisc_1(k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 1.28/0.53    inference(forward_demodulation,[],[f1217,f38])).
% 1.28/0.53  fof(f1217,plain,(
% 1.28/0.53    ~r1_tarski(k3_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) | ~r1_tarski(k5_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 1.28/0.53    inference(resolution,[],[f157,f30])).
% 1.28/0.53  fof(f30,plain,(
% 1.28/0.53    ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 1.28/0.53    inference(cnf_transformation,[],[f29])).
% 1.28/0.53  fof(f29,plain,(
% 1.28/0.53    ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 1.28/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f28])).
% 1.28/0.53  fof(f28,plain,(
% 1.28/0.53    ? [X0,X1] : ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1))) => ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 1.28/0.53    introduced(choice_axiom,[])).
% 1.28/0.53  fof(f22,plain,(
% 1.28/0.53    ? [X0,X1] : ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1)))),
% 1.28/0.53    inference(ennf_transformation,[],[f21])).
% 1.28/0.53  fof(f21,negated_conjecture,(
% 1.28/0.53    ~! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1)))),
% 1.28/0.53    inference(negated_conjecture,[],[f20])).
% 1.28/0.53  fof(f20,conjecture,(
% 1.28/0.53    ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1)))),
% 1.28/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_zfmisc_1)).
% 1.28/0.53  fof(f157,plain,(
% 1.28/0.53    ( ! [X10,X11,X9] : (r1_tarski(k2_xboole_0(X9,X10),X11) | ~r1_tarski(k3_xboole_0(X9,X10),X11) | ~r1_tarski(k5_xboole_0(X9,X10),X11)) )),
% 1.28/0.53    inference(superposition,[],[f45,f39])).
% 1.28/0.53  fof(f39,plain,(
% 1.28/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 1.28/0.53    inference(cnf_transformation,[],[f9])).
% 1.28/0.53  fof(f9,axiom,(
% 1.28/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.28/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
% 1.28/0.53  % SZS output end Proof for theBenchmark
% 1.28/0.53  % (20794)------------------------------
% 1.28/0.53  % (20794)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.53  % (20794)Termination reason: Refutation
% 1.28/0.53  
% 1.28/0.53  % (20794)Memory used [KB]: 4477
% 1.28/0.53  % (20794)Time elapsed: 0.118 s
% 1.28/0.53  % (20794)------------------------------
% 1.28/0.53  % (20794)------------------------------
% 1.28/0.54  % (20790)Success in time 0.174 s
%------------------------------------------------------------------------------
