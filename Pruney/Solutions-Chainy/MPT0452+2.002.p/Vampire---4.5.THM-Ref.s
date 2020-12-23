%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:22 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   27 (  47 expanded)
%              Number of leaves         :    5 (  11 expanded)
%              Depth                    :    9
%              Number of atoms          :   43 (  82 expanded)
%              Number of equality atoms :   24 (  43 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f45,plain,(
    $false ),
    inference(subsumption_resolution,[],[f44,f12])).

fof(f12,plain,(
    k3_relat_1(sK0) != k3_relat_1(k4_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( k3_relat_1(X0) != k3_relat_1(k4_relat_1(X0))
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k3_relat_1(X0) = k3_relat_1(k4_relat_1(X0)) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k3_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relat_1)).

fof(f44,plain,(
    k3_relat_1(sK0) = k3_relat_1(k4_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f40,f22])).

fof(f22,plain,(
    k3_relat_1(sK0) = k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)) ),
    inference(resolution,[],[f14,f11])).

fof(f11,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f14,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(f40,plain,(
    k3_relat_1(k4_relat_1(sK0)) = k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)) ),
    inference(superposition,[],[f39,f17])).

fof(f17,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f39,plain,(
    k3_relat_1(k4_relat_1(sK0)) = k2_xboole_0(k2_relat_1(sK0),k1_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f38,f18])).

fof(f18,plain,(
    k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0)) ),
    inference(resolution,[],[f15,f11])).

fof(f15,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

fof(f38,plain,(
    k3_relat_1(k4_relat_1(sK0)) = k2_xboole_0(k1_relat_1(k4_relat_1(sK0)),k1_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f36,f20])).

fof(f20,plain,(
    k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0)) ),
    inference(resolution,[],[f16,f11])).

fof(f16,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f36,plain,(
    k3_relat_1(k4_relat_1(sK0)) = k2_xboole_0(k1_relat_1(k4_relat_1(sK0)),k2_relat_1(k4_relat_1(sK0))) ),
    inference(resolution,[],[f23,f11])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(k4_relat_1(X0)) = k2_xboole_0(k1_relat_1(k4_relat_1(X0)),k2_relat_1(k4_relat_1(X0))) ) ),
    inference(resolution,[],[f14,f13])).

fof(f13,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:25:05 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.41  % (32206)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.21/0.41  % (32206)Refutation found. Thanks to Tanya!
% 0.21/0.41  % SZS status Theorem for theBenchmark
% 0.21/0.41  % SZS output start Proof for theBenchmark
% 0.21/0.41  fof(f45,plain,(
% 0.21/0.41    $false),
% 0.21/0.41    inference(subsumption_resolution,[],[f44,f12])).
% 0.21/0.41  fof(f12,plain,(
% 0.21/0.41    k3_relat_1(sK0) != k3_relat_1(k4_relat_1(sK0))),
% 0.21/0.41    inference(cnf_transformation,[],[f7])).
% 0.21/0.41  fof(f7,plain,(
% 0.21/0.41    ? [X0] : (k3_relat_1(X0) != k3_relat_1(k4_relat_1(X0)) & v1_relat_1(X0))),
% 0.21/0.41    inference(ennf_transformation,[],[f6])).
% 0.21/0.41  fof(f6,negated_conjecture,(
% 0.21/0.41    ~! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k3_relat_1(k4_relat_1(X0)))),
% 0.21/0.41    inference(negated_conjecture,[],[f5])).
% 0.21/0.41  fof(f5,conjecture,(
% 0.21/0.41    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k3_relat_1(k4_relat_1(X0)))),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relat_1)).
% 0.21/0.41  fof(f44,plain,(
% 0.21/0.41    k3_relat_1(sK0) = k3_relat_1(k4_relat_1(sK0))),
% 0.21/0.41    inference(forward_demodulation,[],[f40,f22])).
% 0.21/0.41  fof(f22,plain,(
% 0.21/0.41    k3_relat_1(sK0) = k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0))),
% 0.21/0.41    inference(resolution,[],[f14,f11])).
% 0.21/0.41  fof(f11,plain,(
% 0.21/0.41    v1_relat_1(sK0)),
% 0.21/0.41    inference(cnf_transformation,[],[f7])).
% 0.21/0.41  fof(f14,plain,(
% 0.21/0.41    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))) )),
% 0.21/0.41    inference(cnf_transformation,[],[f9])).
% 0.21/0.41  fof(f9,plain,(
% 0.21/0.41    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.41    inference(ennf_transformation,[],[f2])).
% 0.21/0.41  fof(f2,axiom,(
% 0.21/0.41    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).
% 0.21/0.41  fof(f40,plain,(
% 0.21/0.41    k3_relat_1(k4_relat_1(sK0)) = k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0))),
% 0.21/0.41    inference(superposition,[],[f39,f17])).
% 0.21/0.41  fof(f17,plain,(
% 0.21/0.41    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f1])).
% 0.21/0.41  fof(f1,axiom,(
% 0.21/0.41    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.41  fof(f39,plain,(
% 0.21/0.41    k3_relat_1(k4_relat_1(sK0)) = k2_xboole_0(k2_relat_1(sK0),k1_relat_1(sK0))),
% 0.21/0.41    inference(forward_demodulation,[],[f38,f18])).
% 0.21/0.41  fof(f18,plain,(
% 0.21/0.41    k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0))),
% 0.21/0.41    inference(resolution,[],[f15,f11])).
% 0.21/0.41  fof(f15,plain,(
% 0.21/0.41    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) )),
% 0.21/0.41    inference(cnf_transformation,[],[f10])).
% 0.21/0.41  fof(f10,plain,(
% 0.21/0.41    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.41    inference(ennf_transformation,[],[f4])).
% 0.21/0.41  fof(f4,axiom,(
% 0.21/0.41    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).
% 0.21/0.41  fof(f38,plain,(
% 0.21/0.41    k3_relat_1(k4_relat_1(sK0)) = k2_xboole_0(k1_relat_1(k4_relat_1(sK0)),k1_relat_1(sK0))),
% 0.21/0.41    inference(forward_demodulation,[],[f36,f20])).
% 0.21/0.41  fof(f20,plain,(
% 0.21/0.41    k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0))),
% 0.21/0.41    inference(resolution,[],[f16,f11])).
% 0.21/0.41  fof(f16,plain,(
% 0.21/0.41    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))) )),
% 0.21/0.41    inference(cnf_transformation,[],[f10])).
% 0.21/0.41  fof(f36,plain,(
% 0.21/0.41    k3_relat_1(k4_relat_1(sK0)) = k2_xboole_0(k1_relat_1(k4_relat_1(sK0)),k2_relat_1(k4_relat_1(sK0)))),
% 0.21/0.41    inference(resolution,[],[f23,f11])).
% 0.21/0.41  fof(f23,plain,(
% 0.21/0.41    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(k4_relat_1(X0)) = k2_xboole_0(k1_relat_1(k4_relat_1(X0)),k2_relat_1(k4_relat_1(X0)))) )),
% 0.21/0.41    inference(resolution,[],[f14,f13])).
% 0.21/0.41  fof(f13,plain,(
% 0.21/0.41    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f8])).
% 0.21/0.41  fof(f8,plain,(
% 0.21/0.41    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.41    inference(ennf_transformation,[],[f3])).
% 0.21/0.41  fof(f3,axiom,(
% 0.21/0.41    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 0.21/0.41  % SZS output end Proof for theBenchmark
% 0.21/0.41  % (32206)------------------------------
% 0.21/0.41  % (32206)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.41  % (32206)Termination reason: Refutation
% 0.21/0.41  
% 0.21/0.41  % (32206)Memory used [KB]: 10490
% 0.21/0.41  % (32206)Time elapsed: 0.006 s
% 0.21/0.41  % (32206)------------------------------
% 0.21/0.41  % (32206)------------------------------
% 0.21/0.41  % (32205)Success in time 0.063 s
%------------------------------------------------------------------------------
