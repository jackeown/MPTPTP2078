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
% DateTime   : Thu Dec  3 12:49:15 EST 2020

% Result     : Theorem 1.36s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :   47 (  88 expanded)
%              Number of leaves         :   12 (  25 expanded)
%              Depth                    :   12
%              Number of atoms          :   78 ( 137 expanded)
%              Number of equality atoms :   34 (  64 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f53,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f52])).

fof(f52,plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(superposition,[],[f22,f50])).

fof(f50,plain,(
    ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f49,f46])).

fof(f46,plain,(
    k1_xboole_0 = k8_relat_1(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f45,f24])).

fof(f24,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f45,plain,(
    k1_xboole_0 = k8_relat_1(k2_relat_1(k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[],[f44,f28])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k8_relat_1(k2_relat_1(X0),X0) = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k8_relat_1(k2_relat_1(X0),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k8_relat_1(k2_relat_1(X0),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_relat_1)).

fof(f44,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f43,f29])).

fof(f29,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) )
     => v1_relat_1(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

fof(f43,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f42,f39])).

fof(f39,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_enumset1(X0,X0,X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f27,f38])).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f31,f37])).

fof(f37,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f32,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f32,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f27,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f42,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,k1_xboole_0))) ),
    inference(resolution,[],[f41,f26])).

fof(f26,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f33,f38])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

% (30687)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f49,plain,(
    ! [X0] : k8_relat_1(k1_xboole_0,k1_xboole_0) = k8_relat_1(X0,k8_relat_1(k1_xboole_0,k1_xboole_0)) ),
    inference(resolution,[],[f48,f25])).

fof(f25,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k8_relat_1(X0,k1_xboole_0) = k8_relat_1(X1,k8_relat_1(X0,k1_xboole_0)) ) ),
    inference(resolution,[],[f36,f44])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1)
      | k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_relat_1)).

fof(f22,plain,(
    k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] : k1_xboole_0 != k8_relat_1(X0,k1_xboole_0) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:20:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 1.36/0.54  % (30692)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.36/0.54  % (30692)Refutation found. Thanks to Tanya!
% 1.36/0.54  % SZS status Theorem for theBenchmark
% 1.36/0.54  % (30708)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.36/0.55  % (30705)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.36/0.55  % (30700)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.36/0.55  % SZS output start Proof for theBenchmark
% 1.36/0.55  fof(f53,plain,(
% 1.36/0.55    $false),
% 1.36/0.55    inference(trivial_inequality_removal,[],[f52])).
% 1.36/0.55  fof(f52,plain,(
% 1.36/0.55    k1_xboole_0 != k1_xboole_0),
% 1.36/0.55    inference(superposition,[],[f22,f50])).
% 1.36/0.55  fof(f50,plain,(
% 1.36/0.55    ( ! [X0] : (k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)) )),
% 1.36/0.55    inference(forward_demodulation,[],[f49,f46])).
% 1.36/0.55  fof(f46,plain,(
% 1.36/0.55    k1_xboole_0 = k8_relat_1(k1_xboole_0,k1_xboole_0)),
% 1.36/0.55    inference(forward_demodulation,[],[f45,f24])).
% 1.36/0.55  fof(f24,plain,(
% 1.36/0.55    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.36/0.55    inference(cnf_transformation,[],[f11])).
% 1.36/0.55  fof(f11,axiom,(
% 1.36/0.55    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 1.36/0.55  fof(f45,plain,(
% 1.36/0.55    k1_xboole_0 = k8_relat_1(k2_relat_1(k1_xboole_0),k1_xboole_0)),
% 1.36/0.55    inference(resolution,[],[f44,f28])).
% 1.36/0.55  fof(f28,plain,(
% 1.36/0.55    ( ! [X0] : (~v1_relat_1(X0) | k8_relat_1(k2_relat_1(X0),X0) = X0) )),
% 1.36/0.55    inference(cnf_transformation,[],[f17])).
% 1.36/0.55  fof(f17,plain,(
% 1.36/0.55    ! [X0] : (k8_relat_1(k2_relat_1(X0),X0) = X0 | ~v1_relat_1(X0))),
% 1.36/0.55    inference(ennf_transformation,[],[f9])).
% 1.36/0.55  fof(f9,axiom,(
% 1.36/0.55    ! [X0] : (v1_relat_1(X0) => k8_relat_1(k2_relat_1(X0),X0) = X0)),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_relat_1)).
% 1.36/0.55  fof(f44,plain,(
% 1.36/0.55    v1_relat_1(k1_xboole_0)),
% 1.36/0.55    inference(resolution,[],[f43,f29])).
% 1.36/0.55  fof(f29,plain,(
% 1.36/0.55    ( ! [X0] : (r2_hidden(sK1(X0),X0) | v1_relat_1(X0)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f18])).
% 1.36/0.55  fof(f18,plain,(
% 1.36/0.55    ! [X0] : (v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 1.36/0.55    inference(ennf_transformation,[],[f15])).
% 1.36/0.55  fof(f15,plain,(
% 1.36/0.55    ! [X0] : (! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => v1_relat_1(X0))),
% 1.36/0.55    inference(unused_predicate_definition_removal,[],[f8])).
% 1.36/0.55  fof(f8,axiom,(
% 1.36/0.55    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).
% 1.36/0.55  fof(f43,plain,(
% 1.36/0.55    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.36/0.55    inference(forward_demodulation,[],[f42,f39])).
% 1.36/0.55  fof(f39,plain,(
% 1.36/0.55    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_enumset1(X0,X0,X0,k1_xboole_0))) )),
% 1.36/0.55    inference(definition_unfolding,[],[f27,f38])).
% 1.36/0.55  fof(f38,plain,(
% 1.36/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 1.36/0.55    inference(definition_unfolding,[],[f31,f37])).
% 1.36/0.55  fof(f37,plain,(
% 1.36/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.36/0.55    inference(definition_unfolding,[],[f32,f35])).
% 1.36/0.55  fof(f35,plain,(
% 1.36/0.55    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f6])).
% 1.36/0.55  fof(f6,axiom,(
% 1.36/0.55    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.36/0.55  fof(f32,plain,(
% 1.36/0.55    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f5])).
% 1.36/0.55  fof(f5,axiom,(
% 1.36/0.55    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.36/0.55  fof(f31,plain,(
% 1.36/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.36/0.55    inference(cnf_transformation,[],[f7])).
% 1.36/0.55  fof(f7,axiom,(
% 1.36/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.36/0.55  fof(f27,plain,(
% 1.36/0.55    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f2])).
% 1.36/0.55  fof(f2,axiom,(
% 1.36/0.55    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 1.36/0.55  fof(f42,plain,(
% 1.36/0.55    ( ! [X0,X1] : (~r2_hidden(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,k1_xboole_0)))) )),
% 1.36/0.55    inference(resolution,[],[f41,f26])).
% 1.36/0.55  fof(f26,plain,(
% 1.36/0.55    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f4])).
% 1.36/0.55  fof(f4,axiom,(
% 1.36/0.55    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.36/0.55  fof(f41,plain,(
% 1.36/0.55    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) )),
% 1.36/0.55    inference(definition_unfolding,[],[f33,f38])).
% 1.36/0.55  fof(f33,plain,(
% 1.36/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f19])).
% 1.36/0.55  fof(f19,plain,(
% 1.36/0.55    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.36/0.55    inference(ennf_transformation,[],[f14])).
% 1.36/0.55  fof(f14,plain,(
% 1.36/0.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.36/0.55    inference(rectify,[],[f1])).
% 1.36/0.55  % (30687)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.36/0.55  fof(f1,axiom,(
% 1.36/0.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.36/0.55  fof(f49,plain,(
% 1.36/0.55    ( ! [X0] : (k8_relat_1(k1_xboole_0,k1_xboole_0) = k8_relat_1(X0,k8_relat_1(k1_xboole_0,k1_xboole_0))) )),
% 1.36/0.55    inference(resolution,[],[f48,f25])).
% 1.36/0.55  fof(f25,plain,(
% 1.36/0.55    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f3])).
% 1.36/0.55  fof(f3,axiom,(
% 1.36/0.55    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.36/0.55  fof(f48,plain,(
% 1.36/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k8_relat_1(X0,k1_xboole_0) = k8_relat_1(X1,k8_relat_1(X0,k1_xboole_0))) )),
% 1.36/0.55    inference(resolution,[],[f36,f44])).
% 1.36/0.55  fof(f36,plain,(
% 1.36/0.55    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(X0,X1) | k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))) )),
% 1.36/0.55    inference(cnf_transformation,[],[f21])).
% 1.36/0.55  fof(f21,plain,(
% 1.36/0.55    ! [X0,X1,X2] : (k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 1.36/0.55    inference(flattening,[],[f20])).
% 1.36/0.55  fof(f20,plain,(
% 1.36/0.55    ! [X0,X1,X2] : ((k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 1.36/0.55    inference(ennf_transformation,[],[f10])).
% 1.36/0.55  fof(f10,axiom,(
% 1.36/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_relat_1)).
% 1.36/0.55  fof(f22,plain,(
% 1.36/0.55    k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0)),
% 1.36/0.55    inference(cnf_transformation,[],[f16])).
% 1.36/0.55  fof(f16,plain,(
% 1.36/0.55    ? [X0] : k1_xboole_0 != k8_relat_1(X0,k1_xboole_0)),
% 1.36/0.55    inference(ennf_transformation,[],[f13])).
% 1.36/0.55  fof(f13,negated_conjecture,(
% 1.36/0.55    ~! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)),
% 1.36/0.55    inference(negated_conjecture,[],[f12])).
% 1.36/0.55  fof(f12,conjecture,(
% 1.36/0.55    ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_relat_1)).
% 1.36/0.55  % SZS output end Proof for theBenchmark
% 1.36/0.55  % (30692)------------------------------
% 1.36/0.55  % (30692)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.55  % (30692)Termination reason: Refutation
% 1.36/0.55  
% 1.36/0.55  % (30692)Memory used [KB]: 6140
% 1.36/0.55  % (30692)Time elapsed: 0.114 s
% 1.36/0.55  % (30692)------------------------------
% 1.36/0.55  % (30692)------------------------------
% 1.36/0.56  % (30685)Success in time 0.191 s
%------------------------------------------------------------------------------
