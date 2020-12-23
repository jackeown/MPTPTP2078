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
% DateTime   : Thu Dec  3 12:49:51 EST 2020

% Result     : Theorem 1.61s
% Output     : Refutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   55 (  87 expanded)
%              Number of leaves         :   11 (  24 expanded)
%              Depth                    :   13
%              Number of atoms          :  108 ( 182 expanded)
%              Number of equality atoms :   22 (  41 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f300,plain,(
    $false ),
    inference(subsumption_resolution,[],[f298,f26])).

fof(f26,plain,(
    ~ r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f20])).

fof(f20,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).

fof(f298,plain,(
    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(superposition,[],[f284,f156])).

fof(f156,plain,(
    sK1 = k3_tarski(k2_tarski(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f155,f46])).

fof(f46,plain,(
    ! [X2,X1] : r1_tarski(X1,k3_tarski(k2_tarski(X2,X1))) ),
    inference(superposition,[],[f39,f29])).

fof(f29,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f39,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f28,f30])).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f28,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f155,plain,
    ( sK1 = k3_tarski(k2_tarski(sK0,sK1))
    | ~ r1_tarski(sK1,k3_tarski(k2_tarski(sK0,sK1))) ),
    inference(resolution,[],[f153,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f153,plain,(
    r1_tarski(k3_tarski(k2_tarski(sK0,sK1)),sK1) ),
    inference(forward_demodulation,[],[f147,f29])).

fof(f147,plain,(
    r1_tarski(k3_tarski(k2_tarski(sK1,sK0)),sK1) ),
    inference(resolution,[],[f88,f111])).

fof(f111,plain,(
    ! [X13] : r1_tarski(k4_xboole_0(k3_tarski(k2_tarski(X13,sK0)),X13),sK1) ),
    inference(resolution,[],[f70,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | r1_tarski(X0,sK1) ) ),
    inference(resolution,[],[f37,f25])).

fof(f25,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f70,plain,(
    ! [X4,X5] : r1_tarski(k4_xboole_0(k3_tarski(k2_tarski(X4,X5)),X4),X5) ),
    inference(resolution,[],[f41,f43])).

fof(f43,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))
      | r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f35,f30])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X1,X0),X0)
      | r1_tarski(X1,X0) ) ),
    inference(superposition,[],[f42,f38])).

fof(f38,plain,(
    ! [X0] : k3_tarski(k2_tarski(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f27,f30])).

fof(f27,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f36,f30])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f284,plain,(
    ! [X2,X1] : r1_tarski(k9_relat_1(sK2,X1),k9_relat_1(sK2,k3_tarski(k2_tarski(X1,X2)))) ),
    inference(superposition,[],[f39,f96])).

fof(f96,plain,(
    ! [X0,X1] : k9_relat_1(sK2,k3_tarski(k2_tarski(X0,X1))) = k3_tarski(k2_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) ),
    inference(resolution,[],[f40,f24])).

fof(f24,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k9_relat_1(X2,k3_tarski(k2_tarski(X0,X1))) = k3_tarski(k2_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) ) ),
    inference(definition_unfolding,[],[f34,f30,f30])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t153_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n005.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:14:17 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.54  % (28756)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.27/0.55  % (28770)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.27/0.57  % (28762)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.27/0.57  % (28755)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.61/0.58  % (28751)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.61/0.58  % (28759)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.61/0.58  % (28754)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.61/0.58  % (28756)Refutation found. Thanks to Tanya!
% 1.61/0.58  % SZS status Theorem for theBenchmark
% 1.61/0.58  % SZS output start Proof for theBenchmark
% 1.61/0.58  fof(f300,plain,(
% 1.61/0.58    $false),
% 1.61/0.58    inference(subsumption_resolution,[],[f298,f26])).
% 1.61/0.58  fof(f26,plain,(
% 1.61/0.58    ~r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 1.61/0.58    inference(cnf_transformation,[],[f21])).
% 1.61/0.58  fof(f21,plain,(
% 1.61/0.58    ~r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK2)),
% 1.61/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f20])).
% 1.61/0.58  fof(f20,plain,(
% 1.61/0.58    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (~r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK2))),
% 1.61/0.58    introduced(choice_axiom,[])).
% 1.61/0.59  fof(f14,plain,(
% 1.61/0.59    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 1.61/0.59    inference(flattening,[],[f13])).
% 1.61/0.59  fof(f13,plain,(
% 1.61/0.59    ? [X0,X1,X2] : ((~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 1.61/0.59    inference(ennf_transformation,[],[f11])).
% 1.61/0.59  fof(f11,negated_conjecture,(
% 1.61/0.59    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 1.61/0.59    inference(negated_conjecture,[],[f10])).
% 1.61/0.59  fof(f10,conjecture,(
% 1.61/0.59    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 1.61/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).
% 1.61/0.59  fof(f298,plain,(
% 1.61/0.59    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 1.61/0.59    inference(superposition,[],[f284,f156])).
% 1.61/0.59  fof(f156,plain,(
% 1.61/0.59    sK1 = k3_tarski(k2_tarski(sK0,sK1))),
% 1.61/0.59    inference(subsumption_resolution,[],[f155,f46])).
% 1.61/0.59  fof(f46,plain,(
% 1.61/0.59    ( ! [X2,X1] : (r1_tarski(X1,k3_tarski(k2_tarski(X2,X1)))) )),
% 1.61/0.59    inference(superposition,[],[f39,f29])).
% 1.61/0.59  fof(f29,plain,(
% 1.61/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.61/0.59    inference(cnf_transformation,[],[f7])).
% 1.61/0.59  fof(f7,axiom,(
% 1.61/0.59    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.61/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.61/0.59  fof(f39,plain,(
% 1.61/0.59    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) )),
% 1.61/0.59    inference(definition_unfolding,[],[f28,f30])).
% 1.61/0.59  fof(f30,plain,(
% 1.61/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.61/0.59    inference(cnf_transformation,[],[f8])).
% 1.61/0.59  fof(f8,axiom,(
% 1.61/0.59    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.61/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.61/0.59  fof(f28,plain,(
% 1.61/0.59    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.61/0.59    inference(cnf_transformation,[],[f6])).
% 1.61/0.59  fof(f6,axiom,(
% 1.61/0.59    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.61/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.61/0.59  fof(f155,plain,(
% 1.61/0.59    sK1 = k3_tarski(k2_tarski(sK0,sK1)) | ~r1_tarski(sK1,k3_tarski(k2_tarski(sK0,sK1)))),
% 1.61/0.59    inference(resolution,[],[f153,f33])).
% 1.61/0.59  fof(f33,plain,(
% 1.61/0.59    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.61/0.59    inference(cnf_transformation,[],[f23])).
% 1.61/0.59  fof(f23,plain,(
% 1.61/0.59    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.61/0.59    inference(flattening,[],[f22])).
% 1.61/0.59  fof(f22,plain,(
% 1.61/0.59    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.61/0.59    inference(nnf_transformation,[],[f2])).
% 1.61/0.59  fof(f2,axiom,(
% 1.61/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.61/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.61/0.59  fof(f153,plain,(
% 1.61/0.59    r1_tarski(k3_tarski(k2_tarski(sK0,sK1)),sK1)),
% 1.61/0.59    inference(forward_demodulation,[],[f147,f29])).
% 1.61/0.59  fof(f147,plain,(
% 1.61/0.59    r1_tarski(k3_tarski(k2_tarski(sK1,sK0)),sK1)),
% 1.61/0.59    inference(resolution,[],[f88,f111])).
% 1.61/0.59  fof(f111,plain,(
% 1.61/0.59    ( ! [X13] : (r1_tarski(k4_xboole_0(k3_tarski(k2_tarski(X13,sK0)),X13),sK1)) )),
% 1.61/0.59    inference(resolution,[],[f70,f64])).
% 1.61/0.59  fof(f64,plain,(
% 1.61/0.59    ( ! [X0] : (~r1_tarski(X0,sK0) | r1_tarski(X0,sK1)) )),
% 1.61/0.59    inference(resolution,[],[f37,f25])).
% 1.61/0.59  fof(f25,plain,(
% 1.61/0.59    r1_tarski(sK0,sK1)),
% 1.61/0.59    inference(cnf_transformation,[],[f21])).
% 1.61/0.59  fof(f37,plain,(
% 1.61/0.59    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.61/0.59    inference(cnf_transformation,[],[f19])).
% 1.61/0.59  fof(f19,plain,(
% 1.61/0.59    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.61/0.59    inference(flattening,[],[f18])).
% 1.61/0.59  fof(f18,plain,(
% 1.61/0.59    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.61/0.59    inference(ennf_transformation,[],[f3])).
% 1.61/0.59  fof(f3,axiom,(
% 1.61/0.59    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.61/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.61/0.59  fof(f70,plain,(
% 1.61/0.59    ( ! [X4,X5] : (r1_tarski(k4_xboole_0(k3_tarski(k2_tarski(X4,X5)),X4),X5)) )),
% 1.61/0.59    inference(resolution,[],[f41,f43])).
% 1.61/0.59  fof(f43,plain,(
% 1.61/0.59    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.61/0.59    inference(equality_resolution,[],[f32])).
% 1.61/0.59  fof(f32,plain,(
% 1.61/0.59    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.61/0.59    inference(cnf_transformation,[],[f23])).
% 1.61/0.59  fof(f41,plain,(
% 1.61/0.59    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) | r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 1.61/0.59    inference(definition_unfolding,[],[f35,f30])).
% 1.61/0.59  fof(f35,plain,(
% 1.61/0.59    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 1.61/0.59    inference(cnf_transformation,[],[f16])).
% 1.61/0.59  fof(f16,plain,(
% 1.61/0.59    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 1.61/0.59    inference(ennf_transformation,[],[f4])).
% 1.61/0.59  fof(f4,axiom,(
% 1.61/0.59    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 1.61/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 1.61/0.59  fof(f88,plain,(
% 1.61/0.59    ( ! [X0,X1] : (~r1_tarski(k4_xboole_0(X1,X0),X0) | r1_tarski(X1,X0)) )),
% 1.61/0.59    inference(superposition,[],[f42,f38])).
% 1.61/0.59  fof(f38,plain,(
% 1.61/0.59    ( ! [X0] : (k3_tarski(k2_tarski(X0,X0)) = X0) )),
% 1.61/0.59    inference(definition_unfolding,[],[f27,f30])).
% 1.61/0.59  fof(f27,plain,(
% 1.61/0.59    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 1.61/0.59    inference(cnf_transformation,[],[f12])).
% 1.61/0.59  fof(f12,plain,(
% 1.61/0.59    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 1.61/0.59    inference(rectify,[],[f1])).
% 1.61/0.59  fof(f1,axiom,(
% 1.61/0.59    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 1.61/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 1.61/0.59  fof(f42,plain,(
% 1.61/0.59    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 1.61/0.59    inference(definition_unfolding,[],[f36,f30])).
% 1.61/0.59  fof(f36,plain,(
% 1.61/0.59    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 1.61/0.59    inference(cnf_transformation,[],[f17])).
% 1.61/0.59  fof(f17,plain,(
% 1.61/0.59    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 1.61/0.59    inference(ennf_transformation,[],[f5])).
% 1.61/0.59  fof(f5,axiom,(
% 1.61/0.59    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 1.61/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
% 1.61/0.59  fof(f284,plain,(
% 1.61/0.59    ( ! [X2,X1] : (r1_tarski(k9_relat_1(sK2,X1),k9_relat_1(sK2,k3_tarski(k2_tarski(X1,X2))))) )),
% 1.61/0.59    inference(superposition,[],[f39,f96])).
% 1.61/0.59  fof(f96,plain,(
% 1.61/0.59    ( ! [X0,X1] : (k9_relat_1(sK2,k3_tarski(k2_tarski(X0,X1))) = k3_tarski(k2_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)))) )),
% 1.61/0.59    inference(resolution,[],[f40,f24])).
% 1.61/0.59  fof(f24,plain,(
% 1.61/0.59    v1_relat_1(sK2)),
% 1.61/0.59    inference(cnf_transformation,[],[f21])).
% 1.61/0.59  fof(f40,plain,(
% 1.61/0.59    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k9_relat_1(X2,k3_tarski(k2_tarski(X0,X1))) = k3_tarski(k2_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))) )),
% 1.61/0.59    inference(definition_unfolding,[],[f34,f30,f30])).
% 1.61/0.59  fof(f34,plain,(
% 1.61/0.59    ( ! [X2,X0,X1] : (k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.61/0.59    inference(cnf_transformation,[],[f15])).
% 1.61/0.59  fof(f15,plain,(
% 1.61/0.59    ! [X0,X1,X2] : (k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 1.61/0.59    inference(ennf_transformation,[],[f9])).
% 1.61/0.59  fof(f9,axiom,(
% 1.61/0.59    ! [X0,X1,X2] : (v1_relat_1(X2) => k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))),
% 1.61/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t153_relat_1)).
% 1.61/0.59  % SZS output end Proof for theBenchmark
% 1.61/0.59  % (28756)------------------------------
% 1.61/0.59  % (28756)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.59  % (28756)Termination reason: Refutation
% 1.61/0.59  
% 1.61/0.59  % (28756)Memory used [KB]: 10874
% 1.61/0.59  % (28756)Time elapsed: 0.153 s
% 1.61/0.59  % (28756)------------------------------
% 1.61/0.59  % (28756)------------------------------
% 1.61/0.59  % (28749)Success in time 0.225 s
%------------------------------------------------------------------------------
