%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:01 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 373 expanded)
%              Number of leaves         :   12 ( 121 expanded)
%              Depth                    :   18
%              Number of atoms          :   84 ( 447 expanded)
%              Number of equality atoms :   70 ( 422 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f180,plain,(
    $false ),
    inference(subsumption_resolution,[],[f159,f154])).

fof(f154,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f153])).

fof(f153,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f26,f149])).

fof(f149,plain,(
    k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(duplicate_literal_removal,[],[f145])).

fof(f145,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f41,f107])).

fof(f107,plain,
    ( k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f41,f98])).

fof(f98,plain,
    ( k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(trivial_inequality_removal,[],[f68])).

fof(f68,plain,
    ( k3_xboole_0(sK0,sK1) != k3_xboole_0(sK0,sK1)
    | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(superposition,[],[f39,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))
      | k1_xboole_0 = k2_enumset1(X1,X1,X1,X1)
      | k1_xboole_0 = k2_enumset1(X0,X0,X0,X0) ) ),
    inference(superposition,[],[f48,f40])).

fof(f40,plain,(
    ! [X0] : k1_setfam_1(k2_enumset1(X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f21,f35])).

fof(f35,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f22,f33])).

fof(f33,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f24,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f24,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f22,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f21,plain,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_setfam_1(k2_enumset1(X0,X1,X2,X3)) = k3_xboole_0(k1_setfam_1(k2_enumset1(X0,X0,X1,X2)),X3)
      | k1_xboole_0 = k2_enumset1(X3,X3,X3,X3)
      | k1_xboole_0 = k2_enumset1(X0,X0,X1,X2) ) ),
    inference(forward_demodulation,[],[f47,f40])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_xboole_0(k1_setfam_1(k2_enumset1(X0,X0,X1,X2)),k1_setfam_1(k2_enumset1(X3,X3,X3,X3))) = k1_setfam_1(k2_enumset1(X0,X1,X2,X3))
      | k1_xboole_0 = k2_enumset1(X3,X3,X3,X3)
      | k1_xboole_0 = k2_enumset1(X0,X0,X1,X2) ) ),
    inference(superposition,[],[f42,f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X1,X2),k2_enumset1(X0,X0,X1,X2),k2_enumset1(X0,X0,X1,X2),k2_enumset1(X3,X3,X3,X3))) ),
    inference(definition_unfolding,[],[f30,f36])).

fof(f36,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k3_tarski(k2_enumset1(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X0,X1,X2,X3),k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X4,X4,X4))) ),
    inference(definition_unfolding,[],[f31,f34,f35])).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f23,f33])).

fof(f23,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f31,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

fof(f30,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) = k1_setfam_1(k3_tarski(k2_enumset1(X0,X0,X0,X1)))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f27,f34])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( k1_setfam_1(k2_xboole_0(X0,X1)) != k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_setfam_1)).

fof(f39,plain,(
    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)) ),
    inference(definition_unfolding,[],[f20,f33])).

fof(f20,plain,(
    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f41,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X0) = k3_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f25,f35,f35,f33])).

fof(f25,plain,(
    ! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_zfmisc_1)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
     => r1_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f159,plain,(
    ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f44,f155])).

fof(f155,plain,(
    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(resolution,[],[f154,f103])).

fof(f103,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(superposition,[],[f44,f98])).

% (11911)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
fof(f44,plain,(
    ! [X1] : ~ r1_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1)) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))
      | X0 != X1 ) ),
    inference(definition_unfolding,[],[f28,f35,f35])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( X0 = X1
        & r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:35:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.56  % (11901)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.56  % (11897)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.57  % (11894)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.58  % (11897)Refutation found. Thanks to Tanya!
% 0.21/0.58  % SZS status Theorem for theBenchmark
% 0.21/0.58  % (11901)Refutation not found, incomplete strategy% (11901)------------------------------
% 0.21/0.58  % (11901)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (11901)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (11901)Memory used [KB]: 10618
% 0.21/0.58  % (11901)Time elapsed: 0.158 s
% 0.21/0.58  % (11901)------------------------------
% 0.21/0.58  % (11901)------------------------------
% 1.61/0.59  % (11893)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.61/0.59  % SZS output start Proof for theBenchmark
% 1.61/0.59  fof(f180,plain,(
% 1.61/0.59    $false),
% 1.61/0.59    inference(subsumption_resolution,[],[f159,f154])).
% 1.61/0.59  fof(f154,plain,(
% 1.61/0.59    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.61/0.59    inference(trivial_inequality_removal,[],[f153])).
% 1.61/0.59  fof(f153,plain,(
% 1.61/0.59    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.61/0.59    inference(superposition,[],[f26,f149])).
% 1.61/0.59  fof(f149,plain,(
% 1.61/0.59    k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.61/0.59    inference(duplicate_literal_removal,[],[f145])).
% 1.61/0.59  fof(f145,plain,(
% 1.61/0.59    k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.61/0.59    inference(superposition,[],[f41,f107])).
% 1.61/0.59  fof(f107,plain,(
% 1.61/0.59    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.61/0.59    inference(superposition,[],[f41,f98])).
% 1.61/0.59  fof(f98,plain,(
% 1.61/0.59    k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 1.61/0.59    inference(trivial_inequality_removal,[],[f68])).
% 1.61/0.59  fof(f68,plain,(
% 1.61/0.59    k3_xboole_0(sK0,sK1) != k3_xboole_0(sK0,sK1) | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 1.61/0.59    inference(superposition,[],[f39,f50])).
% 1.61/0.59  fof(f50,plain,(
% 1.61/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) | k1_xboole_0 = k2_enumset1(X1,X1,X1,X1) | k1_xboole_0 = k2_enumset1(X0,X0,X0,X0)) )),
% 1.61/0.59    inference(superposition,[],[f48,f40])).
% 1.61/0.59  fof(f40,plain,(
% 1.61/0.59    ( ! [X0] : (k1_setfam_1(k2_enumset1(X0,X0,X0,X0)) = X0) )),
% 1.61/0.59    inference(definition_unfolding,[],[f21,f35])).
% 1.61/0.59  fof(f35,plain,(
% 1.61/0.59    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.61/0.59    inference(definition_unfolding,[],[f22,f33])).
% 1.61/0.59  fof(f33,plain,(
% 1.61/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.61/0.59    inference(definition_unfolding,[],[f24,f29])).
% 1.61/0.59  fof(f29,plain,(
% 1.61/0.59    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.61/0.59    inference(cnf_transformation,[],[f6])).
% 1.61/0.59  fof(f6,axiom,(
% 1.61/0.59    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.61/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.61/0.59  fof(f24,plain,(
% 1.61/0.59    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.61/0.59    inference(cnf_transformation,[],[f5])).
% 1.61/0.59  fof(f5,axiom,(
% 1.61/0.59    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.61/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.61/0.59  fof(f22,plain,(
% 1.61/0.59    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.61/0.59    inference(cnf_transformation,[],[f4])).
% 1.61/0.59  fof(f4,axiom,(
% 1.61/0.59    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.61/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.61/0.59  fof(f21,plain,(
% 1.61/0.59    ( ! [X0] : (k1_setfam_1(k1_tarski(X0)) = X0) )),
% 1.61/0.59    inference(cnf_transformation,[],[f12])).
% 1.61/0.59  fof(f12,axiom,(
% 1.61/0.59    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 1.61/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).
% 1.61/0.59  fof(f48,plain,(
% 1.61/0.59    ( ! [X2,X0,X3,X1] : (k1_setfam_1(k2_enumset1(X0,X1,X2,X3)) = k3_xboole_0(k1_setfam_1(k2_enumset1(X0,X0,X1,X2)),X3) | k1_xboole_0 = k2_enumset1(X3,X3,X3,X3) | k1_xboole_0 = k2_enumset1(X0,X0,X1,X2)) )),
% 1.61/0.59    inference(forward_demodulation,[],[f47,f40])).
% 1.61/0.59  fof(f47,plain,(
% 1.61/0.59    ( ! [X2,X0,X3,X1] : (k3_xboole_0(k1_setfam_1(k2_enumset1(X0,X0,X1,X2)),k1_setfam_1(k2_enumset1(X3,X3,X3,X3))) = k1_setfam_1(k2_enumset1(X0,X1,X2,X3)) | k1_xboole_0 = k2_enumset1(X3,X3,X3,X3) | k1_xboole_0 = k2_enumset1(X0,X0,X1,X2)) )),
% 1.61/0.59    inference(superposition,[],[f42,f38])).
% 1.61/0.59  fof(f38,plain,(
% 1.61/0.59    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X1,X2),k2_enumset1(X0,X0,X1,X2),k2_enumset1(X0,X0,X1,X2),k2_enumset1(X3,X3,X3,X3)))) )),
% 1.61/0.59    inference(definition_unfolding,[],[f30,f36])).
% 1.61/0.59  fof(f36,plain,(
% 1.61/0.59    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k3_tarski(k2_enumset1(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X0,X1,X2,X3),k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X4,X4,X4)))) )),
% 1.61/0.59    inference(definition_unfolding,[],[f31,f34,f35])).
% 1.61/0.59  fof(f34,plain,(
% 1.61/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 1.61/0.59    inference(definition_unfolding,[],[f23,f33])).
% 1.61/0.59  fof(f23,plain,(
% 1.61/0.59    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 1.61/0.59    inference(cnf_transformation,[],[f8])).
% 1.61/0.59  fof(f8,axiom,(
% 1.61/0.59    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 1.61/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.61/0.59  fof(f31,plain,(
% 1.61/0.59    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) )),
% 1.61/0.59    inference(cnf_transformation,[],[f2])).
% 1.61/0.59  fof(f2,axiom,(
% 1.61/0.59    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))),
% 1.61/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).
% 1.61/0.59  fof(f30,plain,(
% 1.61/0.59    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 1.61/0.59    inference(cnf_transformation,[],[f7])).
% 1.61/0.59  fof(f7,axiom,(
% 1.61/0.59    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 1.61/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.61/0.59  fof(f42,plain,(
% 1.61/0.59    ( ! [X0,X1] : (k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) = k1_setfam_1(k3_tarski(k2_enumset1(X0,X0,X0,X1))) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.61/0.59    inference(definition_unfolding,[],[f27,f34])).
% 1.61/0.59  fof(f27,plain,(
% 1.61/0.59    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))) )),
% 1.61/0.59    inference(cnf_transformation,[],[f18])).
% 1.61/0.59  fof(f18,plain,(
% 1.61/0.59    ! [X0,X1] : (k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.61/0.59    inference(ennf_transformation,[],[f11])).
% 1.61/0.59  fof(f11,axiom,(
% 1.61/0.59    ! [X0,X1] : ~(k1_setfam_1(k2_xboole_0(X0,X1)) != k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.61/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_setfam_1)).
% 1.61/0.59  fof(f39,plain,(
% 1.61/0.59    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),
% 1.61/0.59    inference(definition_unfolding,[],[f20,f33])).
% 1.61/0.59  fof(f20,plain,(
% 1.61/0.59    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1))),
% 1.61/0.59    inference(cnf_transformation,[],[f16])).
% 1.61/0.59  fof(f16,plain,(
% 1.61/0.59    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1))),
% 1.61/0.59    inference(ennf_transformation,[],[f14])).
% 1.61/0.59  fof(f14,negated_conjecture,(
% 1.61/0.59    ~! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.61/0.59    inference(negated_conjecture,[],[f13])).
% 1.61/0.59  fof(f13,conjecture,(
% 1.61/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.61/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.61/0.59  fof(f41,plain,(
% 1.61/0.59    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X0) = k3_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X1))) )),
% 1.61/0.59    inference(definition_unfolding,[],[f25,f35,f35,f33])).
% 1.61/0.59  fof(f25,plain,(
% 1.61/0.59    ( ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 1.61/0.59    inference(cnf_transformation,[],[f10])).
% 1.61/0.59  fof(f10,axiom,(
% 1.61/0.59    ! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 1.61/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_zfmisc_1)).
% 1.61/0.59  fof(f26,plain,(
% 1.61/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 1.61/0.59    inference(cnf_transformation,[],[f17])).
% 1.61/0.59  fof(f17,plain,(
% 1.61/0.59    ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0)),
% 1.61/0.59    inference(ennf_transformation,[],[f15])).
% 1.61/0.59  fof(f15,plain,(
% 1.61/0.59    ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 => r1_xboole_0(X0,X1))),
% 1.61/0.59    inference(unused_predicate_definition_removal,[],[f1])).
% 1.61/0.59  fof(f1,axiom,(
% 1.61/0.59    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.61/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.61/0.59  fof(f159,plain,(
% 1.61/0.59    ~r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.61/0.59    inference(superposition,[],[f44,f155])).
% 1.61/0.59  fof(f155,plain,(
% 1.61/0.59    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 1.61/0.59    inference(resolution,[],[f154,f103])).
% 1.61/0.59  fof(f103,plain,(
% 1.61/0.59    ~r1_xboole_0(k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 1.61/0.59    inference(superposition,[],[f44,f98])).
% 1.61/0.59  % (11911)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.61/0.59  fof(f44,plain,(
% 1.61/0.59    ( ! [X1] : (~r1_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1))) )),
% 1.61/0.59    inference(equality_resolution,[],[f43])).
% 1.61/0.59  fof(f43,plain,(
% 1.61/0.59    ( ! [X0,X1] : (~r1_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) | X0 != X1) )),
% 1.61/0.59    inference(definition_unfolding,[],[f28,f35,f35])).
% 1.61/0.59  fof(f28,plain,(
% 1.61/0.59    ( ! [X0,X1] : (~r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 != X1) )),
% 1.61/0.59    inference(cnf_transformation,[],[f19])).
% 1.61/0.59  fof(f19,plain,(
% 1.61/0.59    ! [X0,X1] : (X0 != X1 | ~r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 1.61/0.59    inference(ennf_transformation,[],[f9])).
% 1.61/0.59  fof(f9,axiom,(
% 1.61/0.59    ! [X0,X1] : ~(X0 = X1 & r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 1.61/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_zfmisc_1)).
% 1.61/0.59  % SZS output end Proof for theBenchmark
% 1.61/0.59  % (11897)------------------------------
% 1.61/0.59  % (11897)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.59  % (11897)Termination reason: Refutation
% 1.61/0.59  
% 1.61/0.59  % (11897)Memory used [KB]: 6268
% 1.61/0.59  % (11897)Time elapsed: 0.141 s
% 1.61/0.59  % (11897)------------------------------
% 1.61/0.59  % (11897)------------------------------
% 1.61/0.59  % (11890)Success in time 0.222 s
%------------------------------------------------------------------------------
