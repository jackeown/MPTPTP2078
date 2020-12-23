%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:36 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   30 (  44 expanded)
%              Number of leaves         :    8 (  14 expanded)
%              Depth                    :    7
%              Number of atoms          :   45 (  66 expanded)
%              Number of equality atoms :   26 (  47 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f42,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f35,f28,f29])).

fof(f29,plain,(
    ! [X0] :
      ( r1_tarski(X0,k1_tarski(sK0))
      | ~ r1_tarski(X0,k1_tarski(sK1)) ) ),
    inference(superposition,[],[f26,f24])).

fof(f24,plain,(
    k1_tarski(sK0) = k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) ),
    inference(definition_unfolding,[],[f14,f19])).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f14,plain,(
    k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( sK0 != sK1
    & k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f12])).

fof(f12,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) )
   => ( sK0 != sK1
      & k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k5_xboole_0(k5_xboole_0(X2,X1),k3_xboole_0(X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f21,f19])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f28,plain,(
    ~ r1_tarski(k1_tarski(sK1),k1_tarski(sK0)) ),
    inference(unit_resulting_resolution,[],[f15,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

fof(f15,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f13])).

fof(f35,plain,(
    ! [X0] : r1_tarski(k1_tarski(X0),k1_tarski(X0)) ),
    inference(superposition,[],[f25,f23])).

fof(f23,plain,(
    ! [X0] : k1_tarski(X0) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X0)),k3_xboole_0(k1_tarski(X0),k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f16,f22])).

fof(f22,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))) ),
    inference(definition_unfolding,[],[f18,f19])).

fof(f18,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f16,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f25,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1)))) ),
    inference(definition_unfolding,[],[f17,f22])).

fof(f17,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n012.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:42:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.49  % (3591)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.49  % (3584)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.50  % (3607)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.50  % (3608)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.51  % (3600)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.51  % (3584)Refutation not found, incomplete strategy% (3584)------------------------------
% 0.20/0.51  % (3584)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (3584)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (3584)Memory used [KB]: 1663
% 0.20/0.51  % (3584)Time elapsed: 0.095 s
% 0.20/0.51  % (3584)------------------------------
% 0.20/0.51  % (3584)------------------------------
% 0.20/0.51  % (3587)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.51  % (3585)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.51  % (3592)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.51  % (3588)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.51  % (3587)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f35,f28,f29])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ( ! [X0] : (r1_tarski(X0,k1_tarski(sK0)) | ~r1_tarski(X0,k1_tarski(sK1))) )),
% 0.20/0.51    inference(superposition,[],[f26,f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    k1_tarski(sK0) = k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),
% 0.20/0.51    inference(definition_unfolding,[],[f14,f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 0.20/0.51    inference(cnf_transformation,[],[f13])).
% 0.20/0.51  fof(f13,plain,(
% 0.20/0.51    sK0 != sK1 & k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f12])).
% 0.20/0.51  fof(f12,plain,(
% 0.20/0.51    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) => (sK0 != sK1 & k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f9,plain,(
% 0.20/0.51    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.20/0.51    inference(ennf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,negated_conjecture,(
% 0.20/0.51    ~! [X0,X1] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.20/0.51    inference(negated_conjecture,[],[f7])).
% 0.20/0.51  fof(f7,conjecture,(
% 0.20/0.51    ! [X0,X1] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (r1_tarski(X0,k5_xboole_0(k5_xboole_0(X2,X1),k3_xboole_0(X2,X1))) | ~r1_tarski(X0,X1)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f21,f19])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ~r1_tarski(k1_tarski(sK1),k1_tarski(sK0))),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f15,f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 0.20/0.51    inference(cnf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,plain,(
% 0.20/0.51    ! [X0,X1] : (X0 = X1 | ~r1_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 0.20/0.51    inference(ennf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    sK0 != sK1),
% 0.20/0.51    inference(cnf_transformation,[],[f13])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    ( ! [X0] : (r1_tarski(k1_tarski(X0),k1_tarski(X0))) )),
% 0.20/0.51    inference(superposition,[],[f25,f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ( ! [X0] : (k1_tarski(X0) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X0)),k3_xboole_0(k1_tarski(X0),k1_tarski(X0)))) )),
% 0.20/0.51    inference(definition_unfolding,[],[f16,f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1)))) )),
% 0.20/0.51    inference(definition_unfolding,[],[f18,f19])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))))) )),
% 0.20/0.51    inference(definition_unfolding,[],[f17,f22])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (3587)------------------------------
% 0.20/0.51  % (3587)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (3587)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (3587)Memory used [KB]: 1663
% 0.20/0.51  % (3587)Time elapsed: 0.100 s
% 0.20/0.51  % (3587)------------------------------
% 0.20/0.51  % (3587)------------------------------
% 0.20/0.51  % (3600)Refutation not found, incomplete strategy% (3600)------------------------------
% 0.20/0.51  % (3600)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (3600)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (3600)Memory used [KB]: 1663
% 0.20/0.51  % (3600)Time elapsed: 0.093 s
% 0.20/0.51  % (3600)------------------------------
% 0.20/0.51  % (3600)------------------------------
% 0.20/0.51  % (3607)Refutation not found, incomplete strategy% (3607)------------------------------
% 0.20/0.51  % (3607)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (3582)Success in time 0.151 s
%------------------------------------------------------------------------------
