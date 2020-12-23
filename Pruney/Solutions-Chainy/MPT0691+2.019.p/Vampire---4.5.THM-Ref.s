%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:47 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 165 expanded)
%              Number of leaves         :   11 (  42 expanded)
%              Depth                    :   13
%              Number of atoms          :  101 ( 401 expanded)
%              Number of equality atoms :   24 (  48 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1314,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1311,f26])).

fof(f26,plain,(
    ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f22])).

fof(f22,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k1_relat_1(X1))
         => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(f1311,plain,(
    r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(superposition,[],[f1262,f110])).

fof(f110,plain,(
    sK0 = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(subsumption_resolution,[],[f105,f24])).

fof(f24,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f105,plain,
    ( sK0 = k1_relat_1(k7_relat_1(sK1,sK0))
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f33,f25])).

fof(f25,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(f1262,plain,(
    ! [X2] : r1_tarski(k1_relat_1(k7_relat_1(sK1,X2)),k10_relat_1(sK1,k9_relat_1(sK1,X2))) ),
    inference(resolution,[],[f573,f104])).

fof(f104,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(k7_relat_1(sK1,X0))) ),
    inference(superposition,[],[f88,f69])).

fof(f69,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k10_relat_1(k7_relat_1(sK1,X0),k9_relat_1(sK1,X0)) ),
    inference(backward_demodulation,[],[f47,f60])).

fof(f60,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0) ),
    inference(resolution,[],[f31,f24])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f47,plain,(
    ! [X0] : k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(k7_relat_1(sK1,X0))) = k1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(resolution,[],[f27,f38])).

fof(f38,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(resolution,[],[f30,f24])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k7_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

% (13603)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
fof(f88,plain,(
    ! [X2,X1] : r1_tarski(k10_relat_1(k7_relat_1(sK1,X1),X2),k1_relat_1(k7_relat_1(sK1,X1))) ),
    inference(forward_demodulation,[],[f87,f69])).

fof(f87,plain,(
    ! [X2,X1] : r1_tarski(k10_relat_1(k7_relat_1(sK1,X1),X2),k10_relat_1(k7_relat_1(sK1,X1),k9_relat_1(sK1,X1))) ),
    inference(forward_demodulation,[],[f78,f60])).

fof(f78,plain,(
    ! [X2,X1] : r1_tarski(k10_relat_1(k7_relat_1(sK1,X1),X2),k10_relat_1(k7_relat_1(sK1,X1),k2_relat_1(k7_relat_1(sK1,X1)))) ),
    inference(resolution,[],[f32,f38])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t170_relat_1)).

fof(f573,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X3,k1_relat_1(k7_relat_1(sK1,X2)))
      | r1_tarski(X3,k10_relat_1(sK1,k9_relat_1(sK1,X2))) ) ),
    inference(superposition,[],[f227,f69])).

fof(f227,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k10_relat_1(k7_relat_1(sK1,X0),X1))
      | r1_tarski(X2,k10_relat_1(sK1,X1)) ) ),
    inference(superposition,[],[f54,f215])).

fof(f215,plain,(
    ! [X0,X1] : k10_relat_1(k7_relat_1(sK1,X0),X1) = k1_setfam_1(k2_tarski(X0,k10_relat_1(sK1,X1))) ),
    inference(resolution,[],[f36,f24])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k2_tarski(X0,k10_relat_1(X2,X1))) ) ),
    inference(definition_unfolding,[],[f34,f29])).

fof(f29,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k1_setfam_1(k2_tarski(X1,X0)))
      | r1_tarski(X2,X0) ) ),
    inference(superposition,[],[f37,f28])).

fof(f28,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k1_setfam_1(k2_tarski(X1,X2)))
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f35,f29])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:54:31 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.42  % (13606)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.47  % (13598)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.48  % (13607)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.48  % (13610)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.48  % (13612)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.48  % (13599)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.49  % (13606)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f1314,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(subsumption_resolution,[],[f1311,f26])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 0.22/0.49    inference(cnf_transformation,[],[f23])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1)),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1)) => (~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 0.22/0.49    inference(flattening,[],[f12])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    ? [X0,X1] : ((~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f11])).
% 0.22/0.49  fof(f11,negated_conjecture,(
% 0.22/0.49    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 0.22/0.49    inference(negated_conjecture,[],[f10])).
% 0.22/0.49  fof(f10,conjecture,(
% 0.22/0.49    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).
% 0.22/0.49  fof(f1311,plain,(
% 0.22/0.49    r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 0.22/0.49    inference(superposition,[],[f1262,f110])).
% 0.22/0.49  fof(f110,plain,(
% 0.22/0.49    sK0 = k1_relat_1(k7_relat_1(sK1,sK0))),
% 0.22/0.49    inference(subsumption_resolution,[],[f105,f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    v1_relat_1(sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f23])).
% 0.22/0.49  fof(f105,plain,(
% 0.22/0.49    sK0 = k1_relat_1(k7_relat_1(sK1,sK0)) | ~v1_relat_1(sK1)),
% 0.22/0.49    inference(resolution,[],[f33,f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    r1_tarski(sK0,k1_relat_1(sK1))),
% 0.22/0.49    inference(cnf_transformation,[],[f23])).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~v1_relat_1(X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(flattening,[],[f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,axiom,(
% 0.22/0.49    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).
% 0.22/0.49  fof(f1262,plain,(
% 0.22/0.49    ( ! [X2] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X2)),k10_relat_1(sK1,k9_relat_1(sK1,X2)))) )),
% 0.22/0.49    inference(resolution,[],[f573,f104])).
% 0.22/0.49  fof(f104,plain,(
% 0.22/0.49    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(k7_relat_1(sK1,X0)))) )),
% 0.22/0.49    inference(superposition,[],[f88,f69])).
% 0.22/0.49  fof(f69,plain,(
% 0.22/0.49    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k10_relat_1(k7_relat_1(sK1,X0),k9_relat_1(sK1,X0))) )),
% 0.22/0.49    inference(backward_demodulation,[],[f47,f60])).
% 0.22/0.49  fof(f60,plain,(
% 0.22/0.49    ( ! [X0] : (k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0)) )),
% 0.22/0.49    inference(resolution,[],[f31,f24])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.22/0.49  fof(f47,plain,(
% 0.22/0.49    ( ! [X0] : (k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(k7_relat_1(sK1,X0))) = k1_relat_1(k7_relat_1(sK1,X0))) )),
% 0.22/0.49    inference(resolution,[],[f27,f38])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    ( ! [X0] : (v1_relat_1(k7_relat_1(sK1,X0))) )),
% 0.22/0.49    inference(resolution,[],[f30,f24])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 0.22/0.49  % (13603)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.49  fof(f88,plain,(
% 0.22/0.49    ( ! [X2,X1] : (r1_tarski(k10_relat_1(k7_relat_1(sK1,X1),X2),k1_relat_1(k7_relat_1(sK1,X1)))) )),
% 0.22/0.49    inference(forward_demodulation,[],[f87,f69])).
% 0.22/0.49  fof(f87,plain,(
% 0.22/0.49    ( ! [X2,X1] : (r1_tarski(k10_relat_1(k7_relat_1(sK1,X1),X2),k10_relat_1(k7_relat_1(sK1,X1),k9_relat_1(sK1,X1)))) )),
% 0.22/0.49    inference(forward_demodulation,[],[f78,f60])).
% 0.22/0.49  fof(f78,plain,(
% 0.22/0.49    ( ! [X2,X1] : (r1_tarski(k10_relat_1(k7_relat_1(sK1,X1),X2),k10_relat_1(k7_relat_1(sK1,X1),k2_relat_1(k7_relat_1(sK1,X1))))) )),
% 0.22/0.49    inference(resolution,[],[f32,f38])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1)))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t170_relat_1)).
% 0.22/0.49  fof(f573,plain,(
% 0.22/0.49    ( ! [X2,X3] : (~r1_tarski(X3,k1_relat_1(k7_relat_1(sK1,X2))) | r1_tarski(X3,k10_relat_1(sK1,k9_relat_1(sK1,X2)))) )),
% 0.22/0.49    inference(superposition,[],[f227,f69])).
% 0.22/0.49  fof(f227,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~r1_tarski(X2,k10_relat_1(k7_relat_1(sK1,X0),X1)) | r1_tarski(X2,k10_relat_1(sK1,X1))) )),
% 0.22/0.49    inference(superposition,[],[f54,f215])).
% 0.22/0.49  fof(f215,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK1,X0),X1) = k1_setfam_1(k2_tarski(X0,k10_relat_1(sK1,X1)))) )),
% 0.22/0.49    inference(resolution,[],[f36,f24])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k2_tarski(X0,k10_relat_1(X2,X1)))) )),
% 0.22/0.49    inference(definition_unfolding,[],[f34,f29])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 0.22/0.49    inference(ennf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).
% 0.22/0.49  fof(f54,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~r1_tarski(X2,k1_setfam_1(k2_tarski(X1,X0))) | r1_tarski(X2,X0)) )),
% 0.22/0.49    inference(superposition,[],[f37,f28])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~r1_tarski(X0,k1_setfam_1(k2_tarski(X1,X2))) | r1_tarski(X0,X1)) )),
% 0.22/0.49    inference(definition_unfolding,[],[f35,f29])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.22/0.49    inference(ennf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (13606)------------------------------
% 0.22/0.49  % (13606)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (13606)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (13606)Memory used [KB]: 3326
% 0.22/0.49  % (13606)Time elapsed: 0.069 s
% 0.22/0.49  % (13606)------------------------------
% 0.22/0.49  % (13606)------------------------------
% 0.22/0.49  % (13591)Success in time 0.127 s
%------------------------------------------------------------------------------
