%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:59 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   30 (  48 expanded)
%              Number of leaves         :    6 (  11 expanded)
%              Depth                    :   10
%              Number of atoms          :   60 (  93 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f39,plain,(
    $false ),
    inference(subsumption_resolution,[],[f38,f14])).

fof(f14,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(k7_relat_1(X2,X0),X1),k9_relat_1(X2,X1))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => r1_tarski(k9_relat_1(k7_relat_1(X2,X0),X1),k9_relat_1(X2,X1)) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k9_relat_1(k7_relat_1(X2,X0),X1),k9_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t161_relat_1)).

fof(f38,plain,(
    ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f37,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

fof(f37,plain,(
    ~ r1_tarski(k7_relat_1(sK2,sK0),sK2) ),
    inference(subsumption_resolution,[],[f36,f32])).

fof(f32,plain,(
    ! [X3] : v1_relat_1(k7_relat_1(sK2,X3)) ),
    inference(subsumption_resolution,[],[f31,f14])).

fof(f31,plain,(
    ! [X3] :
      ( v1_relat_1(k7_relat_1(sK2,X3))
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f17,f27])).

fof(f27,plain,(
    ! [X0] : k7_relat_1(sK2,X0) = k3_xboole_0(sK2,k7_relat_1(sK2,X0)) ),
    inference(resolution,[],[f26,f14])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(X0,X1) = k3_xboole_0(X0,k7_relat_1(X0,X1)) ) ),
    inference(forward_demodulation,[],[f25,f16])).

fof(f16,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X0,X1) = k3_xboole_0(k7_relat_1(X0,X1),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f20,f18])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f17,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

fof(f36,plain,
    ( ~ r1_tarski(k7_relat_1(sK2,sK0),sK2)
    | ~ v1_relat_1(k7_relat_1(sK2,sK0)) ),
    inference(subsumption_resolution,[],[f34,f14])).

fof(f34,plain,
    ( ~ v1_relat_1(sK2)
    | ~ r1_tarski(k7_relat_1(sK2,sK0),sK2)
    | ~ v1_relat_1(k7_relat_1(sK2,sK0)) ),
    inference(resolution,[],[f19,f15])).

fof(f15,plain,(
    ~ r1_tarski(k9_relat_1(k7_relat_1(sK2,sK0),sK1),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:20:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.41  % (9343)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.21/0.44  % (9336)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.21/0.44  % (9336)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f39,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(subsumption_resolution,[],[f38,f14])).
% 0.21/0.44  fof(f14,plain,(
% 0.21/0.44    v1_relat_1(sK2)),
% 0.21/0.44    inference(cnf_transformation,[],[f8])).
% 0.21/0.44  fof(f8,plain,(
% 0.21/0.44    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(k7_relat_1(X2,X0),X1),k9_relat_1(X2,X1)) & v1_relat_1(X2))),
% 0.21/0.44    inference(ennf_transformation,[],[f7])).
% 0.21/0.44  fof(f7,negated_conjecture,(
% 0.21/0.44    ~! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k9_relat_1(k7_relat_1(X2,X0),X1),k9_relat_1(X2,X1)))),
% 0.21/0.44    inference(negated_conjecture,[],[f6])).
% 0.21/0.44  fof(f6,conjecture,(
% 0.21/0.44    ! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k9_relat_1(k7_relat_1(X2,X0),X1),k9_relat_1(X2,X1)))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t161_relat_1)).
% 0.21/0.44  fof(f38,plain,(
% 0.21/0.44    ~v1_relat_1(sK2)),
% 0.21/0.44    inference(resolution,[],[f37,f18])).
% 0.21/0.44  fof(f18,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f10])).
% 0.21/0.44  fof(f10,plain,(
% 0.21/0.44    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f5])).
% 0.21/0.44  fof(f5,axiom,(
% 0.21/0.44    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).
% 0.21/0.44  fof(f37,plain,(
% 0.21/0.44    ~r1_tarski(k7_relat_1(sK2,sK0),sK2)),
% 0.21/0.44    inference(subsumption_resolution,[],[f36,f32])).
% 0.21/0.44  fof(f32,plain,(
% 0.21/0.44    ( ! [X3] : (v1_relat_1(k7_relat_1(sK2,X3))) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f31,f14])).
% 0.21/0.44  fof(f31,plain,(
% 0.21/0.44    ( ! [X3] : (v1_relat_1(k7_relat_1(sK2,X3)) | ~v1_relat_1(sK2)) )),
% 0.21/0.44    inference(superposition,[],[f17,f27])).
% 0.21/0.44  fof(f27,plain,(
% 0.21/0.44    ( ! [X0] : (k7_relat_1(sK2,X0) = k3_xboole_0(sK2,k7_relat_1(sK2,X0))) )),
% 0.21/0.44    inference(resolution,[],[f26,f14])).
% 0.21/0.44  fof(f26,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~v1_relat_1(X0) | k7_relat_1(X0,X1) = k3_xboole_0(X0,k7_relat_1(X0,X1))) )),
% 0.21/0.44    inference(forward_demodulation,[],[f25,f16])).
% 0.21/0.44  fof(f16,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.44  fof(f25,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k7_relat_1(X0,X1) = k3_xboole_0(k7_relat_1(X0,X1),X0) | ~v1_relat_1(X0)) )),
% 0.21/0.44    inference(resolution,[],[f20,f18])).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  fof(f13,plain,(
% 0.21/0.44    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.44  fof(f17,plain,(
% 0.21/0.44    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f9])).
% 0.21/0.44  fof(f9,plain,(
% 0.21/0.44    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).
% 0.21/0.44  fof(f36,plain,(
% 0.21/0.44    ~r1_tarski(k7_relat_1(sK2,sK0),sK2) | ~v1_relat_1(k7_relat_1(sK2,sK0))),
% 0.21/0.44    inference(subsumption_resolution,[],[f34,f14])).
% 0.21/0.44  fof(f34,plain,(
% 0.21/0.44    ~v1_relat_1(sK2) | ~r1_tarski(k7_relat_1(sK2,sK0),sK2) | ~v1_relat_1(k7_relat_1(sK2,sK0))),
% 0.21/0.44    inference(resolution,[],[f19,f15])).
% 0.21/0.44  fof(f15,plain,(
% 0.21/0.44    ~r1_tarski(k9_relat_1(k7_relat_1(sK2,sK0),sK1),k9_relat_1(sK2,sK1))),
% 0.21/0.44    inference(cnf_transformation,[],[f8])).
% 0.21/0.44  fof(f19,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) | ~v1_relat_1(X2) | ~r1_tarski(X1,X2) | ~v1_relat_1(X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f12])).
% 0.21/0.44  fof(f12,plain,(
% 0.21/0.44    ! [X0,X1] : (! [X2] : (r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.21/0.44    inference(flattening,[],[f11])).
% 0.21/0.44  fof(f11,plain,(
% 0.21/0.44    ! [X0,X1] : (! [X2] : ((r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f4])).
% 0.21/0.44  fof(f4,axiom,(
% 0.21/0.44    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)))))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_relat_1)).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (9336)------------------------------
% 0.21/0.44  % (9336)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (9336)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (9336)Memory used [KB]: 10490
% 0.21/0.44  % (9336)Time elapsed: 0.004 s
% 0.21/0.44  % (9336)------------------------------
% 0.21/0.44  % (9336)------------------------------
% 0.21/0.45  % (9341)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.45  % (9335)Success in time 0.091 s
%------------------------------------------------------------------------------
