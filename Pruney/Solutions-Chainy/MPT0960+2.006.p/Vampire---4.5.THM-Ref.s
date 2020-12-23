%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:07 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   30 (  32 expanded)
%              Number of leaves         :    9 (  10 expanded)
%              Depth                    :    7
%              Number of atoms          :   38 (  40 expanded)
%              Number of equality atoms :   13 (  15 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f42,plain,(
    $false ),
    inference(resolution,[],[f41,f15])).

fof(f15,plain,(
    ~ r1_tarski(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ~ r1_tarski(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f13])).

fof(f13,plain,
    ( ? [X0] : ~ r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))
   => ~ r1_tarski(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0)) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] : ~ r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_wellord2)).

fof(f41,plain,(
    ! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) ),
    inference(superposition,[],[f35,f29])).

fof(f29,plain,(
    ! [X0] : k1_wellord2(X0) = k2_wellord1(k1_wellord2(k1_zfmisc_1(k3_tarski(X0))),X0) ),
    inference(resolution,[],[f22,f17])).

fof(f17,plain,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_zfmisc_1)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_wellord2)).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(k2_wellord1(k1_wellord2(X0),X1),k2_zfmisc_1(X1,X1)) ),
    inference(superposition,[],[f25,f32])).

fof(f32,plain,(
    ! [X0,X1] : k2_wellord1(k1_wellord2(X0),X1) = k1_setfam_1(k2_tarski(k1_wellord2(X0),k2_zfmisc_1(X1,X1))) ),
    inference(resolution,[],[f23,f16])).

fof(f16,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k2_wellord1(X0,X1) = k1_setfam_1(k2_tarski(X0,k2_zfmisc_1(X1,X1))) ) ),
    inference(definition_unfolding,[],[f18,f21])).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] : k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_wellord1)).

fof(f25,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X1,X0)),X0) ),
    inference(superposition,[],[f24,f20])).

fof(f20,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f24,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f19,f21])).

fof(f19,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:11:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (13941)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.46  % (13941)Refutation found. Thanks to Tanya!
% 0.22/0.46  % SZS status Theorem for theBenchmark
% 0.22/0.46  % SZS output start Proof for theBenchmark
% 0.22/0.46  fof(f42,plain,(
% 0.22/0.46    $false),
% 0.22/0.46    inference(resolution,[],[f41,f15])).
% 0.22/0.46  fof(f15,plain,(
% 0.22/0.46    ~r1_tarski(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0))),
% 0.22/0.46    inference(cnf_transformation,[],[f14])).
% 0.22/0.46  fof(f14,plain,(
% 0.22/0.46    ~r1_tarski(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0))),
% 0.22/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f13])).
% 0.22/0.46  fof(f13,plain,(
% 0.22/0.46    ? [X0] : ~r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) => ~r1_tarski(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0))),
% 0.22/0.46    introduced(choice_axiom,[])).
% 0.22/0.46  fof(f10,plain,(
% 0.22/0.46    ? [X0] : ~r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))),
% 0.22/0.46    inference(ennf_transformation,[],[f9])).
% 0.22/0.46  fof(f9,negated_conjecture,(
% 0.22/0.46    ~! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))),
% 0.22/0.46    inference(negated_conjecture,[],[f8])).
% 0.22/0.46  fof(f8,conjecture,(
% 0.22/0.46    ! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_wellord2)).
% 0.22/0.46  fof(f41,plain,(
% 0.22/0.46    ( ! [X0] : (r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))) )),
% 0.22/0.46    inference(superposition,[],[f35,f29])).
% 0.22/0.46  fof(f29,plain,(
% 0.22/0.46    ( ! [X0] : (k1_wellord2(X0) = k2_wellord1(k1_wellord2(k1_zfmisc_1(k3_tarski(X0))),X0)) )),
% 0.22/0.46    inference(resolution,[],[f22,f17])).
% 0.22/0.46  fof(f17,plain,(
% 0.22/0.46    ( ! [X0] : (r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))) )),
% 0.22/0.46    inference(cnf_transformation,[],[f3])).
% 0.22/0.46  fof(f3,axiom,(
% 0.22/0.46    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_zfmisc_1)).
% 0.22/0.46  fof(f22,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f12])).
% 0.22/0.46  fof(f12,plain,(
% 0.22/0.46    ! [X0,X1] : (k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) | ~r1_tarski(X0,X1))),
% 0.22/0.46    inference(ennf_transformation,[],[f7])).
% 0.22/0.46  fof(f7,axiom,(
% 0.22/0.46    ! [X0,X1] : (r1_tarski(X0,X1) => k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_wellord2)).
% 0.22/0.46  fof(f35,plain,(
% 0.22/0.46    ( ! [X0,X1] : (r1_tarski(k2_wellord1(k1_wellord2(X0),X1),k2_zfmisc_1(X1,X1))) )),
% 0.22/0.46    inference(superposition,[],[f25,f32])).
% 0.22/0.46  fof(f32,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k2_wellord1(k1_wellord2(X0),X1) = k1_setfam_1(k2_tarski(k1_wellord2(X0),k2_zfmisc_1(X1,X1)))) )),
% 0.22/0.46    inference(resolution,[],[f23,f16])).
% 0.22/0.46  fof(f16,plain,(
% 0.22/0.46    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 0.22/0.46    inference(cnf_transformation,[],[f6])).
% 0.22/0.46  fof(f6,axiom,(
% 0.22/0.46    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).
% 0.22/0.46  fof(f23,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~v1_relat_1(X0) | k2_wellord1(X0,X1) = k1_setfam_1(k2_tarski(X0,k2_zfmisc_1(X1,X1)))) )),
% 0.22/0.46    inference(definition_unfolding,[],[f18,f21])).
% 0.22/0.46  fof(f21,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.22/0.46    inference(cnf_transformation,[],[f4])).
% 0.22/0.46  fof(f4,axiom,(
% 0.22/0.46    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.22/0.46  fof(f18,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f11])).
% 0.22/0.46  fof(f11,plain,(
% 0.22/0.46    ! [X0] : (! [X1] : k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) | ~v1_relat_1(X0))),
% 0.22/0.46    inference(ennf_transformation,[],[f5])).
% 0.22/0.46  fof(f5,axiom,(
% 0.22/0.46    ! [X0] : (v1_relat_1(X0) => ! [X1] : k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1)))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_wellord1)).
% 0.22/0.46  fof(f25,plain,(
% 0.22/0.46    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X1,X0)),X0)) )),
% 0.22/0.46    inference(superposition,[],[f24,f20])).
% 0.22/0.46  fof(f20,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f2])).
% 0.22/0.46  fof(f2,axiom,(
% 0.22/0.46    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.22/0.46  fof(f24,plain,(
% 0.22/0.46    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) )),
% 0.22/0.46    inference(definition_unfolding,[],[f19,f21])).
% 0.22/0.46  fof(f19,plain,(
% 0.22/0.46    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f1])).
% 0.22/0.46  fof(f1,axiom,(
% 0.22/0.46    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.22/0.46  % SZS output end Proof for theBenchmark
% 0.22/0.46  % (13941)------------------------------
% 0.22/0.46  % (13941)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.46  % (13941)Termination reason: Refutation
% 0.22/0.46  
% 0.22/0.46  % (13941)Memory used [KB]: 6140
% 0.22/0.46  % (13941)Time elapsed: 0.044 s
% 0.22/0.46  % (13941)------------------------------
% 0.22/0.46  % (13941)------------------------------
% 0.22/0.46  % (13926)Success in time 0.099 s
%------------------------------------------------------------------------------
