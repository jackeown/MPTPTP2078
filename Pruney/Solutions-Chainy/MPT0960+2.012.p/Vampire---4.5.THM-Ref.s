%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:07 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   26 (  26 expanded)
%              Number of leaves         :    8 (   8 expanded)
%              Depth                    :    6
%              Number of atoms          :   33 (  33 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f44,plain,(
    $false ),
    inference(subsumption_resolution,[],[f14,f42])).

fof(f42,plain,(
    ! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) ),
    inference(superposition,[],[f34,f23])).

fof(f23,plain,(
    ! [X0,X1] : k1_wellord2(X0) = k2_wellord1(k1_wellord2(k2_xboole_0(X0,X1)),X0) ),
    inference(resolution,[],[f20,f17])).

fof(f17,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_wellord2)).

fof(f34,plain,(
    ! [X2,X3] : r1_tarski(k2_wellord1(k1_wellord2(X2),X3),k2_zfmisc_1(X3,X3)) ),
    inference(superposition,[],[f21,f25])).

fof(f25,plain,(
    ! [X0,X1] : k2_wellord1(k1_wellord2(X0),X1) = k3_xboole_0(k1_wellord2(X0),k2_zfmisc_1(X1,X1)) ),
    inference(resolution,[],[f16,f15])).

fof(f15,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] : k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_wellord1)).

fof(f21,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0) ),
    inference(superposition,[],[f18,f19])).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f18,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f14,plain,(
    ~ r1_tarski(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ~ r1_tarski(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f12])).

fof(f12,plain,
    ( ? [X0] : ~ r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))
   => ~ r1_tarski(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0)) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] : ~ r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_wellord2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:54:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.40  % (11808)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.13/0.41  % (11801)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.13/0.41  % (11802)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.13/0.41  % (11808)Refutation found. Thanks to Tanya!
% 0.13/0.41  % SZS status Theorem for theBenchmark
% 0.13/0.41  % SZS output start Proof for theBenchmark
% 0.13/0.41  fof(f44,plain,(
% 0.13/0.41    $false),
% 0.13/0.41    inference(subsumption_resolution,[],[f14,f42])).
% 0.13/0.41  fof(f42,plain,(
% 0.13/0.41    ( ! [X0] : (r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))) )),
% 0.13/0.41    inference(superposition,[],[f34,f23])).
% 0.13/0.41  fof(f23,plain,(
% 0.13/0.41    ( ! [X0,X1] : (k1_wellord2(X0) = k2_wellord1(k1_wellord2(k2_xboole_0(X0,X1)),X0)) )),
% 0.13/0.41    inference(resolution,[],[f20,f17])).
% 0.13/0.41  fof(f17,plain,(
% 0.13/0.41    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.13/0.41    inference(cnf_transformation,[],[f3])).
% 0.13/0.41  fof(f3,axiom,(
% 0.13/0.41    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.13/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.13/0.41  fof(f20,plain,(
% 0.13/0.41    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0)) )),
% 0.13/0.41    inference(cnf_transformation,[],[f11])).
% 0.13/0.41  fof(f11,plain,(
% 0.13/0.41    ! [X0,X1] : (k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) | ~r1_tarski(X0,X1))),
% 0.13/0.41    inference(ennf_transformation,[],[f6])).
% 0.13/0.41  fof(f6,axiom,(
% 0.13/0.41    ! [X0,X1] : (r1_tarski(X0,X1) => k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0))),
% 0.13/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_wellord2)).
% 0.13/0.41  fof(f34,plain,(
% 0.13/0.41    ( ! [X2,X3] : (r1_tarski(k2_wellord1(k1_wellord2(X2),X3),k2_zfmisc_1(X3,X3))) )),
% 0.13/0.41    inference(superposition,[],[f21,f25])).
% 0.13/0.41  fof(f25,plain,(
% 0.13/0.41    ( ! [X0,X1] : (k2_wellord1(k1_wellord2(X0),X1) = k3_xboole_0(k1_wellord2(X0),k2_zfmisc_1(X1,X1))) )),
% 0.13/0.41    inference(resolution,[],[f16,f15])).
% 0.13/0.41  fof(f15,plain,(
% 0.13/0.41    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 0.13/0.41    inference(cnf_transformation,[],[f5])).
% 0.13/0.41  fof(f5,axiom,(
% 0.13/0.41    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 0.13/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).
% 0.13/0.41  fof(f16,plain,(
% 0.13/0.41    ( ! [X0,X1] : (~v1_relat_1(X0) | k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1))) )),
% 0.13/0.41    inference(cnf_transformation,[],[f10])).
% 0.13/0.41  fof(f10,plain,(
% 0.13/0.41    ! [X0] : (! [X1] : k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) | ~v1_relat_1(X0))),
% 0.13/0.41    inference(ennf_transformation,[],[f4])).
% 0.13/0.41  fof(f4,axiom,(
% 0.13/0.41    ! [X0] : (v1_relat_1(X0) => ! [X1] : k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1)))),
% 0.13/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_wellord1)).
% 0.13/0.41  fof(f21,plain,(
% 0.13/0.41    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) )),
% 0.13/0.41    inference(superposition,[],[f18,f19])).
% 0.13/0.41  fof(f19,plain,(
% 0.13/0.41    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.13/0.41    inference(cnf_transformation,[],[f1])).
% 0.13/0.41  fof(f1,axiom,(
% 0.13/0.41    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.13/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.13/0.41  fof(f18,plain,(
% 0.13/0.41    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.13/0.41    inference(cnf_transformation,[],[f2])).
% 0.13/0.41  fof(f2,axiom,(
% 0.13/0.41    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.13/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.13/0.41  fof(f14,plain,(
% 0.13/0.41    ~r1_tarski(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0))),
% 0.13/0.41    inference(cnf_transformation,[],[f13])).
% 0.13/0.41  fof(f13,plain,(
% 0.13/0.41    ~r1_tarski(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0))),
% 0.13/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f12])).
% 0.13/0.41  fof(f12,plain,(
% 0.13/0.41    ? [X0] : ~r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) => ~r1_tarski(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0))),
% 0.13/0.41    introduced(choice_axiom,[])).
% 0.13/0.41  fof(f9,plain,(
% 0.13/0.41    ? [X0] : ~r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))),
% 0.13/0.41    inference(ennf_transformation,[],[f8])).
% 0.13/0.41  fof(f8,negated_conjecture,(
% 0.13/0.41    ~! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))),
% 0.13/0.41    inference(negated_conjecture,[],[f7])).
% 0.13/0.41  fof(f7,conjecture,(
% 0.13/0.41    ! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))),
% 0.13/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_wellord2)).
% 0.13/0.41  % SZS output end Proof for theBenchmark
% 0.13/0.41  % (11808)------------------------------
% 0.13/0.41  % (11808)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.13/0.41  % (11808)Termination reason: Refutation
% 0.13/0.41  
% 0.13/0.41  % (11808)Memory used [KB]: 10618
% 0.13/0.41  % (11808)Time elapsed: 0.005 s
% 0.13/0.41  % (11808)------------------------------
% 0.13/0.41  % (11808)------------------------------
% 0.13/0.41  % (11796)Success in time 0.06 s
%------------------------------------------------------------------------------
