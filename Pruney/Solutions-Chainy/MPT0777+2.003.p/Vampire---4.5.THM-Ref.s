%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:55 EST 2020

% Result     : Theorem 0.16s
% Output     : Refutation 0.16s
% Verified   : 
% Statistics : Number of formulae       :   34 (  95 expanded)
%              Number of leaves         :    7 (  30 expanded)
%              Depth                    :   10
%              Number of atoms          :   49 ( 150 expanded)
%              Number of equality atoms :   27 (  89 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f322,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f298])).

fof(f298,plain,(
    k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(k2_wellord1(sK2,sK0),sK1) ),
    inference(superposition,[],[f20,f286])).

fof(f286,plain,(
    ! [X2,X3] : k2_wellord1(k2_wellord1(sK2,X2),X3) = k2_wellord1(sK2,k1_setfam_1(k2_tarski(X2,X3))) ),
    inference(forward_demodulation,[],[f265,f42])).

fof(f42,plain,(
    ! [X0,X1] : k2_wellord1(k2_wellord1(sK2,X0),X1) = k1_setfam_1(k2_tarski(k2_wellord1(sK2,X0),k2_zfmisc_1(X1,X1))) ),
    inference(resolution,[],[f41,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k2_wellord1(X0,X1) = k1_setfam_1(k2_tarski(X0,k2_zfmisc_1(X1,X1))) ) ),
    inference(definition_unfolding,[],[f15,f16])).

fof(f16,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] : k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_wellord1)).

fof(f41,plain,(
    ! [X14] : v1_relat_1(k2_wellord1(sK2,X14)) ),
    inference(superposition,[],[f25,f31])).

fof(f31,plain,(
    ! [X0] : k2_wellord1(sK2,X0) = k1_setfam_1(k2_tarski(sK2,k2_zfmisc_1(X0,X0))) ),
    inference(resolution,[],[f21,f13])).

fof(f13,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(sK2,k3_xboole_0(sK0,sK1))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2] :
        ( k2_wellord1(k2_wellord1(X2,X0),X1) != k2_wellord1(X2,k3_xboole_0(X0,X1))
        & v1_relat_1(X2) )
   => ( k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(sK2,k3_xboole_0(sK0,sK1))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( k2_wellord1(k2_wellord1(X2,X0),X1) != k2_wellord1(X2,k3_xboole_0(X0,X1))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1)) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_wellord1)).

fof(f25,plain,(
    ! [X0] : v1_relat_1(k1_setfam_1(k2_tarski(sK2,X0))) ),
    inference(resolution,[],[f22,f13])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(definition_unfolding,[],[f17,f16])).

fof(f17,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

fof(f265,plain,(
    ! [X2,X3] : k1_setfam_1(k2_tarski(k2_wellord1(sK2,X2),k2_zfmisc_1(X3,X3))) = k2_wellord1(sK2,k1_setfam_1(k2_tarski(X2,X3))) ),
    inference(superposition,[],[f199,f77])).

fof(f77,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(k2_wellord1(sK2,X0),X1)) = k1_setfam_1(k2_tarski(sK2,k1_setfam_1(k2_tarski(k2_zfmisc_1(X0,X0),X1)))) ),
    inference(superposition,[],[f23,f31])).

fof(f23,plain,(
    ! [X2,X0,X1] : k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X2)) = k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(X1,X2)))) ),
    inference(definition_unfolding,[],[f18,f16,f16,f16,f16])).

fof(f18,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f199,plain,(
    ! [X12,X13] : k2_wellord1(sK2,k1_setfam_1(k2_tarski(X12,X13))) = k1_setfam_1(k2_tarski(sK2,k1_setfam_1(k2_tarski(k2_zfmisc_1(X12,X12),k2_zfmisc_1(X13,X13))))) ),
    inference(superposition,[],[f31,f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k1_setfam_1(k2_tarski(X0,X1)),k1_setfam_1(k2_tarski(X2,X3))) = k1_setfam_1(k2_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) ),
    inference(definition_unfolding,[],[f19,f16,f16,f16])).

fof(f19,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f20,plain,(
    k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(sK2,k1_setfam_1(k2_tarski(sK0,sK1))) ),
    inference(definition_unfolding,[],[f14,f16])).

fof(f14,plain,(
    k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(sK2,k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.10  % Command    : run_vampire %s %d
% 0.09/0.30  % Computer   : n007.cluster.edu
% 0.09/0.30  % Model      : x86_64 x86_64
% 0.09/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.09/0.30  % Memory     : 8042.1875MB
% 0.09/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.09/0.30  % CPULimit   : 60
% 0.09/0.30  % WCLimit    : 600
% 0.09/0.31  % DateTime   : Tue Dec  1 11:15:06 EST 2020
% 0.09/0.31  % CPUTime    : 
% 0.16/0.40  % (22540)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.16/0.43  % (22542)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.16/0.44  % (22535)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.16/0.45  % (22542)Refutation found. Thanks to Tanya!
% 0.16/0.45  % SZS status Theorem for theBenchmark
% 0.16/0.45  % SZS output start Proof for theBenchmark
% 0.16/0.45  fof(f322,plain,(
% 0.16/0.45    $false),
% 0.16/0.45    inference(trivial_inequality_removal,[],[f298])).
% 0.16/0.45  fof(f298,plain,(
% 0.16/0.45    k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(k2_wellord1(sK2,sK0),sK1)),
% 0.16/0.45    inference(superposition,[],[f20,f286])).
% 0.16/0.45  fof(f286,plain,(
% 0.16/0.45    ( ! [X2,X3] : (k2_wellord1(k2_wellord1(sK2,X2),X3) = k2_wellord1(sK2,k1_setfam_1(k2_tarski(X2,X3)))) )),
% 0.16/0.45    inference(forward_demodulation,[],[f265,f42])).
% 0.16/0.45  fof(f42,plain,(
% 0.16/0.45    ( ! [X0,X1] : (k2_wellord1(k2_wellord1(sK2,X0),X1) = k1_setfam_1(k2_tarski(k2_wellord1(sK2,X0),k2_zfmisc_1(X1,X1)))) )),
% 0.16/0.45    inference(resolution,[],[f41,f21])).
% 0.16/0.45  fof(f21,plain,(
% 0.16/0.45    ( ! [X0,X1] : (~v1_relat_1(X0) | k2_wellord1(X0,X1) = k1_setfam_1(k2_tarski(X0,k2_zfmisc_1(X1,X1)))) )),
% 0.16/0.45    inference(definition_unfolding,[],[f15,f16])).
% 0.16/0.45  fof(f16,plain,(
% 0.16/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.16/0.45    inference(cnf_transformation,[],[f3])).
% 0.16/0.45  fof(f3,axiom,(
% 0.16/0.45    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.16/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.16/0.45  fof(f15,plain,(
% 0.16/0.45    ( ! [X0,X1] : (k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) | ~v1_relat_1(X0)) )),
% 0.16/0.45    inference(cnf_transformation,[],[f9])).
% 0.16/0.45  fof(f9,plain,(
% 0.16/0.45    ! [X0] : (! [X1] : k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) | ~v1_relat_1(X0))),
% 0.16/0.45    inference(ennf_transformation,[],[f5])).
% 0.16/0.45  fof(f5,axiom,(
% 0.16/0.45    ! [X0] : (v1_relat_1(X0) => ! [X1] : k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1)))),
% 0.16/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_wellord1)).
% 0.16/0.45  fof(f41,plain,(
% 0.16/0.45    ( ! [X14] : (v1_relat_1(k2_wellord1(sK2,X14))) )),
% 0.16/0.45    inference(superposition,[],[f25,f31])).
% 0.16/0.45  fof(f31,plain,(
% 0.16/0.45    ( ! [X0] : (k2_wellord1(sK2,X0) = k1_setfam_1(k2_tarski(sK2,k2_zfmisc_1(X0,X0)))) )),
% 0.16/0.45    inference(resolution,[],[f21,f13])).
% 0.16/0.45  fof(f13,plain,(
% 0.16/0.45    v1_relat_1(sK2)),
% 0.16/0.45    inference(cnf_transformation,[],[f12])).
% 0.16/0.45  fof(f12,plain,(
% 0.16/0.45    k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(sK2,k3_xboole_0(sK0,sK1)) & v1_relat_1(sK2)),
% 0.16/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f11])).
% 0.16/0.45  fof(f11,plain,(
% 0.16/0.45    ? [X0,X1,X2] : (k2_wellord1(k2_wellord1(X2,X0),X1) != k2_wellord1(X2,k3_xboole_0(X0,X1)) & v1_relat_1(X2)) => (k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(sK2,k3_xboole_0(sK0,sK1)) & v1_relat_1(sK2))),
% 0.16/0.45    introduced(choice_axiom,[])).
% 0.16/0.45  fof(f8,plain,(
% 0.16/0.45    ? [X0,X1,X2] : (k2_wellord1(k2_wellord1(X2,X0),X1) != k2_wellord1(X2,k3_xboole_0(X0,X1)) & v1_relat_1(X2))),
% 0.16/0.45    inference(ennf_transformation,[],[f7])).
% 0.16/0.45  fof(f7,negated_conjecture,(
% 0.16/0.45    ~! [X0,X1,X2] : (v1_relat_1(X2) => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1)))),
% 0.16/0.45    inference(negated_conjecture,[],[f6])).
% 0.16/0.45  fof(f6,conjecture,(
% 0.16/0.45    ! [X0,X1,X2] : (v1_relat_1(X2) => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1)))),
% 0.16/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_wellord1)).
% 0.16/0.45  fof(f25,plain,(
% 0.16/0.45    ( ! [X0] : (v1_relat_1(k1_setfam_1(k2_tarski(sK2,X0)))) )),
% 0.16/0.45    inference(resolution,[],[f22,f13])).
% 0.16/0.45  fof(f22,plain,(
% 0.16/0.45    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k1_setfam_1(k2_tarski(X0,X1)))) )),
% 0.16/0.45    inference(definition_unfolding,[],[f17,f16])).
% 0.16/0.45  fof(f17,plain,(
% 0.16/0.45    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.16/0.45    inference(cnf_transformation,[],[f10])).
% 0.16/0.45  fof(f10,plain,(
% 0.16/0.45    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 0.16/0.45    inference(ennf_transformation,[],[f4])).
% 0.16/0.45  fof(f4,axiom,(
% 0.16/0.45    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 0.16/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).
% 0.16/0.45  fof(f265,plain,(
% 0.16/0.45    ( ! [X2,X3] : (k1_setfam_1(k2_tarski(k2_wellord1(sK2,X2),k2_zfmisc_1(X3,X3))) = k2_wellord1(sK2,k1_setfam_1(k2_tarski(X2,X3)))) )),
% 0.16/0.45    inference(superposition,[],[f199,f77])).
% 0.16/0.45  fof(f77,plain,(
% 0.16/0.45    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(k2_wellord1(sK2,X0),X1)) = k1_setfam_1(k2_tarski(sK2,k1_setfam_1(k2_tarski(k2_zfmisc_1(X0,X0),X1))))) )),
% 0.16/0.45    inference(superposition,[],[f23,f31])).
% 0.16/0.45  fof(f23,plain,(
% 0.16/0.45    ( ! [X2,X0,X1] : (k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X2)) = k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(X1,X2))))) )),
% 0.16/0.45    inference(definition_unfolding,[],[f18,f16,f16,f16,f16])).
% 0.16/0.45  fof(f18,plain,(
% 0.16/0.45    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 0.16/0.45    inference(cnf_transformation,[],[f1])).
% 0.16/0.45  fof(f1,axiom,(
% 0.16/0.45    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 0.16/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).
% 0.16/0.45  fof(f199,plain,(
% 0.16/0.45    ( ! [X12,X13] : (k2_wellord1(sK2,k1_setfam_1(k2_tarski(X12,X13))) = k1_setfam_1(k2_tarski(sK2,k1_setfam_1(k2_tarski(k2_zfmisc_1(X12,X12),k2_zfmisc_1(X13,X13)))))) )),
% 0.16/0.45    inference(superposition,[],[f31,f24])).
% 0.16/0.45  fof(f24,plain,(
% 0.16/0.45    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k1_setfam_1(k2_tarski(X0,X1)),k1_setfam_1(k2_tarski(X2,X3))) = k1_setfam_1(k2_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))) )),
% 0.16/0.45    inference(definition_unfolding,[],[f19,f16,f16,f16])).
% 0.16/0.45  fof(f19,plain,(
% 0.16/0.45    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 0.16/0.45    inference(cnf_transformation,[],[f2])).
% 0.16/0.45  fof(f2,axiom,(
% 0.16/0.45    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 0.16/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).
% 0.16/0.45  fof(f20,plain,(
% 0.16/0.45    k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(sK2,k1_setfam_1(k2_tarski(sK0,sK1)))),
% 0.16/0.45    inference(definition_unfolding,[],[f14,f16])).
% 0.16/0.45  fof(f14,plain,(
% 0.16/0.45    k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(sK2,k3_xboole_0(sK0,sK1))),
% 0.16/0.45    inference(cnf_transformation,[],[f12])).
% 0.16/0.45  % SZS output end Proof for theBenchmark
% 0.16/0.45  % (22542)------------------------------
% 0.16/0.45  % (22542)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.16/0.45  % (22542)Termination reason: Refutation
% 0.16/0.45  
% 0.16/0.45  % (22542)Memory used [KB]: 1918
% 0.16/0.45  % (22542)Time elapsed: 0.068 s
% 0.16/0.45  % (22542)------------------------------
% 0.16/0.45  % (22542)------------------------------
% 0.16/0.46  % (22523)Success in time 0.138 s
%------------------------------------------------------------------------------
