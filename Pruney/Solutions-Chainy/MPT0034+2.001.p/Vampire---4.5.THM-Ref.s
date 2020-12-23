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
% DateTime   : Thu Dec  3 12:29:42 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 201 expanded)
%              Number of leaves         :   10 (  60 expanded)
%              Depth                    :   12
%              Number of atoms          :   88 ( 289 expanded)
%              Number of equality atoms :   35 ( 136 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2958,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2941,f1449])).

fof(f1449,plain,(
    ! [X16] : r1_tarski(k3_xboole_0(sK0,X16),k3_xboole_0(sK1,X16)) ),
    inference(superposition,[],[f1178,f465])).

fof(f465,plain,(
    ! [X2] : k3_xboole_0(sK0,X2) = k3_xboole_0(sK0,k3_xboole_0(sK1,X2)) ),
    inference(superposition,[],[f27,f379])).

fof(f379,plain,(
    sK0 = k3_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f331,f33])).

fof(f33,plain,(
    sK1 = k2_xboole_0(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f19,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f19,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3))
    & r1_tarski(sK2,sK3)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3))
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3))
      & r1_tarski(sK2,sK3)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_tarski(X2,X3)
          & r1_tarski(X0,X1) )
       => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_xboole_1)).

fof(f331,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(forward_demodulation,[],[f297,f48])).

fof(f48,plain,(
    ! [X2,X3] : k2_xboole_0(X2,k3_xboole_0(X2,X3)) = X2 ),
    inference(superposition,[],[f31,f25])).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0 ),
    inference(unit_resulting_resolution,[],[f24,f26])).

fof(f24,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f297,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[],[f28,f23])).

fof(f23,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f28,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_xboole_1)).

fof(f27,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f1178,plain,(
    ! [X8,X7] : r1_tarski(k3_xboole_0(X8,X7),X7) ),
    inference(superposition,[],[f972,f344])).

fof(f344,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X1,X0)) = X0 ),
    inference(backward_demodulation,[],[f310,f343])).

fof(f343,plain,(
    ! [X12,X11] : k3_xboole_0(k2_xboole_0(X11,X12),X11) = X11 ),
    inference(forward_demodulation,[],[f342,f39])).

fof(f39,plain,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(superposition,[],[f32,f25])).

fof(f32,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(unit_resulting_resolution,[],[f30,f26])).

fof(f30,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(superposition,[],[f24,f22])).

fof(f22,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

% (32550)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f342,plain,(
    ! [X12,X11] : k2_xboole_0(X11,k1_xboole_0) = k3_xboole_0(k2_xboole_0(X11,X12),X11) ),
    inference(forward_demodulation,[],[f314,f22])).

fof(f314,plain,(
    ! [X12,X11] : k2_xboole_0(X11,k3_xboole_0(X12,k1_xboole_0)) = k3_xboole_0(k2_xboole_0(X11,X12),X11) ),
    inference(superposition,[],[f28,f39])).

fof(f310,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(k2_xboole_0(X0,X1),X0) ),
    inference(superposition,[],[f28,f23])).

fof(f972,plain,(
    ! [X2,X1] : r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f912,f25])).

fof(f912,plain,(
    ! [X0,X1] : r1_tarski(X1,k2_xboole_0(X1,X0)) ),
    inference(forward_demodulation,[],[f855,f39])).

fof(f855,plain,(
    ! [X0,X1] : r1_tarski(k2_xboole_0(X1,k1_xboole_0),k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f323,f22])).

fof(f323,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_xboole_0(X0,k3_xboole_0(X1,X2)),k2_xboole_0(X0,X1)) ),
    inference(superposition,[],[f24,f28])).

fof(f2941,plain,(
    ~ r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f71,f2892])).

fof(f2892,plain,(
    sK2 = k3_xboole_0(sK3,sK2) ),
    inference(superposition,[],[f1299,f402])).

fof(f402,plain,(
    sK3 = k2_xboole_0(sK3,sK2) ),
    inference(superposition,[],[f142,f331])).

fof(f142,plain,(
    ! [X1] : sK3 = k2_xboole_0(sK3,k3_xboole_0(sK2,X1)) ),
    inference(superposition,[],[f93,f25])).

fof(f93,plain,(
    ! [X0] : sK3 = k2_xboole_0(k3_xboole_0(sK2,X0),sK3) ),
    inference(unit_resulting_resolution,[],[f63,f26])).

fof(f63,plain,(
    ! [X0] : r1_tarski(k3_xboole_0(sK2,X0),sK3) ),
    inference(unit_resulting_resolution,[],[f24,f20,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f20,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f1299,plain,(
    ! [X0,X1] : k3_xboole_0(k2_xboole_0(X1,X0),X0) = X0 ),
    inference(forward_demodulation,[],[f1251,f344])).

fof(f1251,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(k2_xboole_0(X1,X0),X0) ),
    inference(superposition,[],[f298,f23])).

fof(f298,plain,(
    ! [X4,X2,X3] : k2_xboole_0(X2,k3_xboole_0(X3,X4)) = k3_xboole_0(k2_xboole_0(X3,X2),k2_xboole_0(X2,X4)) ),
    inference(superposition,[],[f28,f25])).

fof(f71,plain,(
    ! [X0] : ~ r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,k3_xboole_0(sK3,X0))) ),
    inference(forward_demodulation,[],[f55,f27])).

fof(f55,plain,(
    ! [X0] : ~ r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(k3_xboole_0(sK1,sK3),X0)) ),
    inference(unit_resulting_resolution,[],[f21,f24,f29])).

fof(f21,plain,(
    ~ r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3)) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:27:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.42  % (32548)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.21/0.42  % (32543)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.21/0.44  % (32549)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.21/0.45  % (32545)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.21/0.46  % (32541)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.21/0.46  % (32547)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.47  % (32551)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.21/0.47  % (32544)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.21/0.47  % (32542)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.21/0.47  % (32546)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.48  % (32552)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.21/0.48  % (32543)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f2958,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(subsumption_resolution,[],[f2941,f1449])).
% 0.21/0.48  fof(f1449,plain,(
% 0.21/0.48    ( ! [X16] : (r1_tarski(k3_xboole_0(sK0,X16),k3_xboole_0(sK1,X16))) )),
% 0.21/0.48    inference(superposition,[],[f1178,f465])).
% 0.21/0.48  fof(f465,plain,(
% 0.21/0.48    ( ! [X2] : (k3_xboole_0(sK0,X2) = k3_xboole_0(sK0,k3_xboole_0(sK1,X2))) )),
% 0.21/0.48    inference(superposition,[],[f27,f379])).
% 0.21/0.48  fof(f379,plain,(
% 0.21/0.48    sK0 = k3_xboole_0(sK0,sK1)),
% 0.21/0.48    inference(superposition,[],[f331,f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    sK1 = k2_xboole_0(sK0,sK1)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f19,f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    r1_tarski(sK0,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ~r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3)) & r1_tarski(sK2,sK3) & r1_tarski(sK0,sK1)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3] : (~r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) & r1_tarski(X2,X3) & r1_tarski(X0,X1)) => (~r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3)) & r1_tarski(sK2,sK3) & r1_tarski(sK0,sK1))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3] : (~r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) & r1_tarski(X2,X3) & r1_tarski(X0,X1))),
% 0.21/0.49    inference(flattening,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3] : (~r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) & (r1_tarski(X2,X3) & r1_tarski(X0,X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)))),
% 0.21/0.49    inference(negated_conjecture,[],[f9])).
% 0.21/0.49  fof(f9,conjecture,(
% 0.21/0.49    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_xboole_1)).
% 0.21/0.49  fof(f331,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 0.21/0.49    inference(forward_demodulation,[],[f297,f48])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ( ! [X2,X3] : (k2_xboole_0(X2,k3_xboole_0(X2,X3)) = X2) )),
% 0.21/0.49    inference(superposition,[],[f31,f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0) )),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f24,f26])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.21/0.49  fof(f297,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.49    inference(superposition,[],[f28,f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.21/0.49    inference(rectify,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_xboole_1)).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).
% 0.21/0.49  fof(f1178,plain,(
% 0.21/0.49    ( ! [X8,X7] : (r1_tarski(k3_xboole_0(X8,X7),X7)) )),
% 0.21/0.49    inference(superposition,[],[f972,f344])).
% 0.21/0.49  fof(f344,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X1,X0)) = X0) )),
% 0.21/0.49    inference(backward_demodulation,[],[f310,f343])).
% 0.21/0.49  fof(f343,plain,(
% 0.21/0.49    ( ! [X12,X11] : (k3_xboole_0(k2_xboole_0(X11,X12),X11) = X11) )),
% 0.21/0.49    inference(forward_demodulation,[],[f342,f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ( ! [X1] : (k2_xboole_0(X1,k1_xboole_0) = X1) )),
% 0.21/0.49    inference(superposition,[],[f32,f25])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f30,f26])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.49    inference(superposition,[],[f24,f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f8])).
% 0.21/0.49  % (32550)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.49  fof(f342,plain,(
% 0.21/0.49    ( ! [X12,X11] : (k2_xboole_0(X11,k1_xboole_0) = k3_xboole_0(k2_xboole_0(X11,X12),X11)) )),
% 0.21/0.49    inference(forward_demodulation,[],[f314,f22])).
% 0.21/0.49  fof(f314,plain,(
% 0.21/0.49    ( ! [X12,X11] : (k2_xboole_0(X11,k3_xboole_0(X12,k1_xboole_0)) = k3_xboole_0(k2_xboole_0(X11,X12),X11)) )),
% 0.21/0.49    inference(superposition,[],[f28,f39])).
% 0.21/0.49  fof(f310,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(k2_xboole_0(X0,X1),X0)) )),
% 0.21/0.49    inference(superposition,[],[f28,f23])).
% 0.21/0.49  fof(f972,plain,(
% 0.21/0.49    ( ! [X2,X1] : (r1_tarski(X1,k2_xboole_0(X2,X1))) )),
% 0.21/0.49    inference(superposition,[],[f912,f25])).
% 0.21/0.49  fof(f912,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(X1,k2_xboole_0(X1,X0))) )),
% 0.21/0.49    inference(forward_demodulation,[],[f855,f39])).
% 0.21/0.49  fof(f855,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k2_xboole_0(X1,k1_xboole_0),k2_xboole_0(X1,X0))) )),
% 0.21/0.49    inference(superposition,[],[f323,f22])).
% 0.21/0.49  fof(f323,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,k3_xboole_0(X1,X2)),k2_xboole_0(X0,X1))) )),
% 0.21/0.49    inference(superposition,[],[f24,f28])).
% 0.21/0.49  fof(f2941,plain,(
% 0.21/0.49    ~r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK2))),
% 0.21/0.49    inference(superposition,[],[f71,f2892])).
% 0.21/0.49  fof(f2892,plain,(
% 0.21/0.49    sK2 = k3_xboole_0(sK3,sK2)),
% 0.21/0.49    inference(superposition,[],[f1299,f402])).
% 0.21/0.49  fof(f402,plain,(
% 0.21/0.49    sK3 = k2_xboole_0(sK3,sK2)),
% 0.21/0.49    inference(superposition,[],[f142,f331])).
% 0.21/0.49  fof(f142,plain,(
% 0.21/0.49    ( ! [X1] : (sK3 = k2_xboole_0(sK3,k3_xboole_0(sK2,X1))) )),
% 0.21/0.49    inference(superposition,[],[f93,f25])).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    ( ! [X0] : (sK3 = k2_xboole_0(k3_xboole_0(sK2,X0),sK3)) )),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f63,f26])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    ( ! [X0] : (r1_tarski(k3_xboole_0(sK2,X0),sK3)) )),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f24,f20,f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.49    inference(flattening,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    r1_tarski(sK2,sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f1299,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k3_xboole_0(k2_xboole_0(X1,X0),X0) = X0) )),
% 0.21/0.49    inference(forward_demodulation,[],[f1251,f344])).
% 0.21/0.49  fof(f1251,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(k2_xboole_0(X1,X0),X0)) )),
% 0.21/0.49    inference(superposition,[],[f298,f23])).
% 0.21/0.49  fof(f298,plain,(
% 0.21/0.49    ( ! [X4,X2,X3] : (k2_xboole_0(X2,k3_xboole_0(X3,X4)) = k3_xboole_0(k2_xboole_0(X3,X2),k2_xboole_0(X2,X4))) )),
% 0.21/0.49    inference(superposition,[],[f28,f25])).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,k3_xboole_0(sK3,X0)))) )),
% 0.21/0.49    inference(forward_demodulation,[],[f55,f27])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(k3_xboole_0(sK1,sK3),X0))) )),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f21,f24,f29])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ~r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3))),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (32543)------------------------------
% 0.21/0.49  % (32543)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (32543)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (32543)Memory used [KB]: 7547
% 0.21/0.49  % (32543)Time elapsed: 0.066 s
% 0.21/0.49  % (32543)------------------------------
% 0.21/0.49  % (32543)------------------------------
% 0.21/0.49  % (32540)Success in time 0.127 s
%------------------------------------------------------------------------------
