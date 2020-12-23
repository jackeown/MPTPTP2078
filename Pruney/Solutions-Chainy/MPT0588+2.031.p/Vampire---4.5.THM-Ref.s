%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:59 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   54 (  71 expanded)
%              Number of leaves         :   14 (  21 expanded)
%              Depth                    :   16
%              Number of atoms          :   86 ( 117 expanded)
%              Number of equality atoms :   44 (  62 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f257,plain,(
    $false ),
    inference(subsumption_resolution,[],[f255,f27])).

fof(f27,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f25])).

fof(f25,plain,
    ( ? [X0,X1] :
        ( k7_relat_1(X1,X0) != k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
        & v1_relat_1(X1) )
   => ( k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1] :
      ( k7_relat_1(X1,X0) != k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_relat_1)).

fof(f255,plain,(
    ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f254,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_relat_1)).

fof(f254,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f253,f27])).

fof(f253,plain,
    ( ~ v1_relat_1(sK1)
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),k1_relat_1(sK1)) ),
    inference(trivial_inequality_removal,[],[f250])).

fof(f250,plain,
    ( k7_relat_1(sK1,sK0) != k7_relat_1(sK1,sK0)
    | ~ v1_relat_1(sK1)
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),k1_relat_1(sK1)) ),
    inference(superposition,[],[f249,f73])).

fof(f73,plain,(
    ! [X4,X5,X3] :
      ( k7_relat_1(X3,X4) = k7_relat_1(X3,k3_xboole_0(X4,X5))
      | ~ v1_relat_1(X3)
      | ~ r1_tarski(k1_relat_1(k7_relat_1(X3,X4)),X5) ) ),
    inference(subsumption_resolution,[],[f67,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f67,plain,(
    ! [X4,X5,X3] :
      ( k7_relat_1(X3,X4) = k7_relat_1(X3,k3_xboole_0(X4,X5))
      | ~ v1_relat_1(X3)
      | ~ r1_tarski(k1_relat_1(k7_relat_1(X3,X4)),X5)
      | ~ v1_relat_1(k7_relat_1(X3,X4)) ) ),
    inference(superposition,[],[f38,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

fof(f249,plain,(
    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(sK0,k1_relat_1(sK1))) ),
    inference(backward_demodulation,[],[f28,f246])).

fof(f246,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2) ),
    inference(superposition,[],[f124,f31])).

fof(f31,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f124,plain,(
    ! [X2,X1] : k3_xboole_0(X1,X2) = k1_setfam_1(k2_tarski(X2,X1)) ),
    inference(superposition,[],[f31,f112])).

fof(f112,plain,(
    ! [X2,X3] : k2_tarski(X2,X3) = k2_tarski(X3,X2) ),
    inference(superposition,[],[f107,f30])).

fof(f30,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f107,plain,(
    ! [X8,X9] : k1_enumset1(X9,X9,X8) = k2_tarski(X8,X9) ),
    inference(forward_demodulation,[],[f106,f33])).

fof(f33,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f106,plain,(
    ! [X8,X9] : k1_enumset1(X9,X9,X8) = k2_xboole_0(k1_tarski(X8),k1_tarski(X9)) ),
    inference(forward_demodulation,[],[f99,f29])).

fof(f29,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f99,plain,(
    ! [X8,X9] : k1_enumset1(X9,X9,X8) = k2_xboole_0(k1_tarski(X8),k2_tarski(X9,X9)) ),
    inference(superposition,[],[f95,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X2,X0,X1,X0) ),
    inference(superposition,[],[f39,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f39,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X1,X2,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X1,X2,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_enumset1)).

fof(f95,plain,(
    ! [X2,X0,X1] : k2_enumset1(X2,X0,X0,X1) = k2_xboole_0(k1_tarski(X2),k2_tarski(X0,X1)) ),
    inference(superposition,[],[f94,f30])).

fof(f94,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(forward_demodulation,[],[f92,f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f92,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(superposition,[],[f42,f29])).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).

fof(f28,plain,(
    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0)) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.14  % Command    : run_vampire %s %d
% 0.15/0.36  % Computer   : n023.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 09:28:36 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.21/0.48  % (32273)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (32272)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  % (32279)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.48  % (32265)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.48  % (32274)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.49  % (32271)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.49  % (32277)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.49  % (32265)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % (32262)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.49  % (32264)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.50  % (32268)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f257,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(subsumption_resolution,[],[f255,f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    v1_relat_1(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0)) & v1_relat_1(sK1)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ? [X0,X1] : (k7_relat_1(X1,X0) != k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1)) => (k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0)) & v1_relat_1(sK1))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ? [X0,X1] : (k7_relat_1(X1,X0) != k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 0.21/0.51    inference(negated_conjecture,[],[f17])).
% 0.21/0.51  fof(f17,conjecture,(
% 0.21/0.51    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_relat_1)).
% 0.21/0.51  fof(f255,plain,(
% 0.21/0.51    ~v1_relat_1(sK1)),
% 0.21/0.51    inference(resolution,[],[f254,f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,axiom,(
% 0.21/0.51    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_relat_1)).
% 0.21/0.51  fof(f254,plain,(
% 0.21/0.51    ~r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),k1_relat_1(sK1))),
% 0.21/0.51    inference(subsumption_resolution,[],[f253,f27])).
% 0.21/0.51  fof(f253,plain,(
% 0.21/0.51    ~v1_relat_1(sK1) | ~r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),k1_relat_1(sK1))),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f250])).
% 0.21/0.51  fof(f250,plain,(
% 0.21/0.51    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,sK0) | ~v1_relat_1(sK1) | ~r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),k1_relat_1(sK1))),
% 0.21/0.51    inference(superposition,[],[f249,f73])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    ( ! [X4,X5,X3] : (k7_relat_1(X3,X4) = k7_relat_1(X3,k3_xboole_0(X4,X5)) | ~v1_relat_1(X3) | ~r1_tarski(k1_relat_1(k7_relat_1(X3,X4)),X5)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f67,f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,axiom,(
% 0.21/0.51    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    ( ! [X4,X5,X3] : (k7_relat_1(X3,X4) = k7_relat_1(X3,k3_xboole_0(X4,X5)) | ~v1_relat_1(X3) | ~r1_tarski(k1_relat_1(k7_relat_1(X3,X4)),X5) | ~v1_relat_1(k7_relat_1(X3,X4))) )),
% 0.21/0.51    inference(superposition,[],[f38,f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(flattening,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,axiom,(
% 0.21/0.51    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.21/0.51    inference(ennf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).
% 0.21/0.51  fof(f249,plain,(
% 0.21/0.51    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(sK0,k1_relat_1(sK1)))),
% 0.21/0.51    inference(backward_demodulation,[],[f28,f246])).
% 0.21/0.51  fof(f246,plain,(
% 0.21/0.51    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)) )),
% 0.21/0.51    inference(superposition,[],[f124,f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,axiom,(
% 0.21/0.51    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.51  fof(f124,plain,(
% 0.21/0.51    ( ! [X2,X1] : (k3_xboole_0(X1,X2) = k1_setfam_1(k2_tarski(X2,X1))) )),
% 0.21/0.51    inference(superposition,[],[f31,f112])).
% 0.21/0.51  fof(f112,plain,(
% 0.21/0.51    ( ! [X2,X3] : (k2_tarski(X2,X3) = k2_tarski(X3,X2)) )),
% 0.21/0.51    inference(superposition,[],[f107,f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.51  fof(f107,plain,(
% 0.21/0.51    ( ! [X8,X9] : (k1_enumset1(X9,X9,X8) = k2_tarski(X8,X9)) )),
% 0.21/0.51    inference(forward_demodulation,[],[f106,f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 0.21/0.51  fof(f106,plain,(
% 0.21/0.51    ( ! [X8,X9] : (k1_enumset1(X9,X9,X8) = k2_xboole_0(k1_tarski(X8),k1_tarski(X9))) )),
% 0.21/0.51    inference(forward_demodulation,[],[f99,f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.51  fof(f99,plain,(
% 0.21/0.51    ( ! [X8,X9] : (k1_enumset1(X9,X9,X8) = k2_xboole_0(k1_tarski(X8),k2_tarski(X9,X9))) )),
% 0.21/0.51    inference(superposition,[],[f95,f57])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X2,X0,X1,X0)) )),
% 0.21/0.51    inference(superposition,[],[f39,f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X1,X2,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X1,X2,X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_enumset1)).
% 0.21/0.51  fof(f95,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k2_enumset1(X2,X0,X0,X1) = k2_xboole_0(k1_tarski(X2),k2_tarski(X0,X1))) )),
% 0.21/0.51    inference(superposition,[],[f94,f30])).
% 0.21/0.51  fof(f94,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 0.21/0.51    inference(forward_demodulation,[],[f92,f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.51  fof(f92,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 0.21/0.51    inference(superposition,[],[f42,f29])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0))),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (32265)------------------------------
% 0.21/0.51  % (32265)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (32265)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (32267)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.51  % (32265)Memory used [KB]: 1791
% 0.21/0.51  % (32265)Time elapsed: 0.071 s
% 0.21/0.51  % (32265)------------------------------
% 0.21/0.51  % (32265)------------------------------
% 0.21/0.51  % (32253)Success in time 0.138 s
%------------------------------------------------------------------------------
