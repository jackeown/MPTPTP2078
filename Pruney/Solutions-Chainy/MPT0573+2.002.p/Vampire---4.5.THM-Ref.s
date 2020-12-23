%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:41 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   36 (  98 expanded)
%              Number of leaves         :    9 (  32 expanded)
%              Depth                    :   10
%              Number of atoms          :   52 ( 154 expanded)
%              Number of equality atoms :   16 (  55 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f481,plain,(
    $false ),
    inference(resolution,[],[f480,f163])).

fof(f163,plain,(
    ! [X0,X1] : r1_tarski(k10_relat_1(sK2,X0),k10_relat_1(sK2,k3_tarski(k2_tarski(X0,X1)))) ),
    inference(superposition,[],[f24,f160])).

fof(f160,plain,(
    ! [X0,X1] : k10_relat_1(sK2,k3_tarski(k2_tarski(X0,X1))) = k3_tarski(k2_tarski(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))) ),
    inference(resolution,[],[f26,f15])).

fof(f15,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ~ r1_tarski(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1)))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)),k10_relat_1(X2,k6_subset_1(X0,X1)))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1)))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)),k10_relat_1(X2,k6_subset_1(X0,X1)))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => r1_tarski(k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)),k10_relat_1(X2,k6_subset_1(X0,X1))) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)),k10_relat_1(X2,k6_subset_1(X0,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t177_relat_1)).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(X2,k3_tarski(k2_tarski(X0,X1))) = k3_tarski(k2_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) ) ),
    inference(definition_unfolding,[],[f22,f20,f20])).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_relat_1)).

fof(f24,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f17,f20])).

fof(f17,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f480,plain,(
    ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k3_tarski(k2_tarski(sK0,sK1)))) ),
    inference(forward_demodulation,[],[f479,f235])).

fof(f235,plain,(
    ! [X2,X3] : k10_relat_1(sK2,k3_tarski(k2_tarski(X2,X3))) = k10_relat_1(sK2,k3_tarski(k2_tarski(X3,X2))) ),
    inference(superposition,[],[f161,f160])).

fof(f161,plain,(
    ! [X0,X1] : k10_relat_1(sK2,k3_tarski(k2_tarski(X0,X1))) = k3_tarski(k2_tarski(k10_relat_1(sK2,X1),k10_relat_1(sK2,X0))) ),
    inference(superposition,[],[f160,f19])).

fof(f19,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f479,plain,(
    ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k3_tarski(k2_tarski(sK1,sK0)))) ),
    inference(forward_demodulation,[],[f474,f25])).

fof(f25,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k6_subset_1(X1,X0))) ),
    inference(definition_unfolding,[],[f21,f20,f18,f20])).

fof(f18,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f474,plain,(
    ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k3_tarski(k2_tarski(sK1,k6_subset_1(sK0,sK1))))) ),
    inference(resolution,[],[f164,f16])).

fof(f16,plain,(
    ~ r1_tarski(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f14])).

fof(f164,plain,(
    ! [X4,X2,X3] :
      ( r1_tarski(k6_subset_1(X4,k10_relat_1(sK2,X2)),k10_relat_1(sK2,X3))
      | ~ r1_tarski(X4,k10_relat_1(sK2,k3_tarski(k2_tarski(X2,X3)))) ) ),
    inference(superposition,[],[f27,f160])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))
      | r1_tarski(k6_subset_1(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f23,f18,f20])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:15:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  ipcrm: permission denied for id (828669952)
% 0.13/0.36  ipcrm: permission denied for id (828702721)
% 0.13/0.39  ipcrm: permission denied for id (828801046)
% 0.21/0.41  ipcrm: permission denied for id (828899370)
% 0.21/0.43  ipcrm: permission denied for id (829030465)
% 0.21/0.44  ipcrm: permission denied for id (829063242)
% 0.21/0.50  ipcrm: permission denied for id (829128823)
% 0.37/0.57  % (7432)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.37/0.60  % (7421)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.37/0.61  % (7428)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.37/0.62  % (7423)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.37/0.62  % (7421)Refutation found. Thanks to Tanya!
% 0.37/0.62  % SZS status Theorem for theBenchmark
% 0.37/0.62  % SZS output start Proof for theBenchmark
% 0.37/0.62  fof(f481,plain,(
% 0.37/0.62    $false),
% 0.37/0.62    inference(resolution,[],[f480,f163])).
% 0.37/0.62  fof(f163,plain,(
% 0.37/0.62    ( ! [X0,X1] : (r1_tarski(k10_relat_1(sK2,X0),k10_relat_1(sK2,k3_tarski(k2_tarski(X0,X1))))) )),
% 0.37/0.62    inference(superposition,[],[f24,f160])).
% 0.37/0.62  fof(f160,plain,(
% 0.37/0.62    ( ! [X0,X1] : (k10_relat_1(sK2,k3_tarski(k2_tarski(X0,X1))) = k3_tarski(k2_tarski(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)))) )),
% 0.37/0.62    inference(resolution,[],[f26,f15])).
% 0.37/0.62  fof(f15,plain,(
% 0.37/0.62    v1_relat_1(sK2)),
% 0.37/0.62    inference(cnf_transformation,[],[f14])).
% 0.37/0.62  fof(f14,plain,(
% 0.37/0.62    ~r1_tarski(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))) & v1_relat_1(sK2)),
% 0.37/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f13])).
% 0.37/0.62  fof(f13,plain,(
% 0.37/0.62    ? [X0,X1,X2] : (~r1_tarski(k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)),k10_relat_1(X2,k6_subset_1(X0,X1))) & v1_relat_1(X2)) => (~r1_tarski(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))) & v1_relat_1(sK2))),
% 0.37/0.62    introduced(choice_axiom,[])).
% 0.37/0.62  fof(f10,plain,(
% 0.37/0.62    ? [X0,X1,X2] : (~r1_tarski(k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)),k10_relat_1(X2,k6_subset_1(X0,X1))) & v1_relat_1(X2))),
% 0.37/0.62    inference(ennf_transformation,[],[f9])).
% 0.37/0.62  fof(f9,negated_conjecture,(
% 0.37/0.62    ~! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)),k10_relat_1(X2,k6_subset_1(X0,X1))))),
% 0.37/0.62    inference(negated_conjecture,[],[f8])).
% 0.37/0.62  fof(f8,conjecture,(
% 0.37/0.62    ! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)),k10_relat_1(X2,k6_subset_1(X0,X1))))),
% 0.37/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t177_relat_1)).
% 0.37/0.62  fof(f26,plain,(
% 0.37/0.62    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(X2,k3_tarski(k2_tarski(X0,X1))) = k3_tarski(k2_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))) )),
% 0.37/0.62    inference(definition_unfolding,[],[f22,f20,f20])).
% 0.37/0.62  fof(f20,plain,(
% 0.37/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.37/0.62    inference(cnf_transformation,[],[f5])).
% 0.37/0.62  fof(f5,axiom,(
% 0.37/0.62    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.37/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.37/0.62  fof(f22,plain,(
% 0.37/0.62    ( ! [X2,X0,X1] : (k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.37/0.62    inference(cnf_transformation,[],[f11])).
% 0.37/0.62  fof(f11,plain,(
% 0.37/0.62    ! [X0,X1,X2] : (k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 0.37/0.62    inference(ennf_transformation,[],[f7])).
% 0.37/0.62  fof(f7,axiom,(
% 0.37/0.62    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 0.37/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_relat_1)).
% 0.37/0.62  fof(f24,plain,(
% 0.37/0.62    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) )),
% 0.37/0.62    inference(definition_unfolding,[],[f17,f20])).
% 0.37/0.62  fof(f17,plain,(
% 0.37/0.62    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.37/0.62    inference(cnf_transformation,[],[f3])).
% 0.37/0.62  fof(f3,axiom,(
% 0.37/0.62    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.37/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.37/0.62  fof(f480,plain,(
% 0.37/0.62    ~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k3_tarski(k2_tarski(sK0,sK1))))),
% 0.37/0.62    inference(forward_demodulation,[],[f479,f235])).
% 0.37/0.62  fof(f235,plain,(
% 0.37/0.62    ( ! [X2,X3] : (k10_relat_1(sK2,k3_tarski(k2_tarski(X2,X3))) = k10_relat_1(sK2,k3_tarski(k2_tarski(X3,X2)))) )),
% 0.37/0.62    inference(superposition,[],[f161,f160])).
% 0.37/0.62  fof(f161,plain,(
% 0.37/0.62    ( ! [X0,X1] : (k10_relat_1(sK2,k3_tarski(k2_tarski(X0,X1))) = k3_tarski(k2_tarski(k10_relat_1(sK2,X1),k10_relat_1(sK2,X0)))) )),
% 0.37/0.62    inference(superposition,[],[f160,f19])).
% 0.37/0.62  fof(f19,plain,(
% 0.37/0.62    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.37/0.62    inference(cnf_transformation,[],[f4])).
% 0.37/0.62  fof(f4,axiom,(
% 0.37/0.62    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.37/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.37/0.62  fof(f479,plain,(
% 0.37/0.62    ~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k3_tarski(k2_tarski(sK1,sK0))))),
% 0.37/0.62    inference(forward_demodulation,[],[f474,f25])).
% 0.37/0.62  fof(f25,plain,(
% 0.37/0.62    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k6_subset_1(X1,X0)))) )),
% 0.37/0.62    inference(definition_unfolding,[],[f21,f20,f18,f20])).
% 0.37/0.62  fof(f18,plain,(
% 0.37/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.37/0.62    inference(cnf_transformation,[],[f6])).
% 0.37/0.62  fof(f6,axiom,(
% 0.37/0.62    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.37/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.37/0.62  fof(f21,plain,(
% 0.37/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 0.37/0.62    inference(cnf_transformation,[],[f1])).
% 0.37/0.62  fof(f1,axiom,(
% 0.37/0.62    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 0.37/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.37/0.62  fof(f474,plain,(
% 0.37/0.62    ~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k3_tarski(k2_tarski(sK1,k6_subset_1(sK0,sK1)))))),
% 0.37/0.62    inference(resolution,[],[f164,f16])).
% 0.37/0.62  fof(f16,plain,(
% 0.37/0.62    ~r1_tarski(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1)))),
% 0.37/0.62    inference(cnf_transformation,[],[f14])).
% 0.37/0.62  fof(f164,plain,(
% 0.37/0.62    ( ! [X4,X2,X3] : (r1_tarski(k6_subset_1(X4,k10_relat_1(sK2,X2)),k10_relat_1(sK2,X3)) | ~r1_tarski(X4,k10_relat_1(sK2,k3_tarski(k2_tarski(X2,X3))))) )),
% 0.37/0.62    inference(superposition,[],[f27,f160])).
% 0.37/0.62  fof(f27,plain,(
% 0.37/0.62    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) | r1_tarski(k6_subset_1(X0,X1),X2)) )),
% 0.37/0.62    inference(definition_unfolding,[],[f23,f18,f20])).
% 0.37/0.62  fof(f23,plain,(
% 0.37/0.62    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 0.37/0.62    inference(cnf_transformation,[],[f12])).
% 0.37/0.62  fof(f12,plain,(
% 0.37/0.62    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.37/0.62    inference(ennf_transformation,[],[f2])).
% 0.37/0.62  fof(f2,axiom,(
% 0.37/0.62    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.37/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 0.37/0.62  % SZS output end Proof for theBenchmark
% 0.37/0.62  % (7421)------------------------------
% 0.37/0.62  % (7421)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.37/0.62  % (7421)Termination reason: Refutation
% 0.37/0.62  
% 0.37/0.62  % (7421)Memory used [KB]: 6396
% 0.37/0.62  % (7421)Time elapsed: 0.057 s
% 0.37/0.62  % (7421)------------------------------
% 0.37/0.62  % (7421)------------------------------
% 0.37/0.62  % (7261)Success in time 0.266 s
%------------------------------------------------------------------------------
