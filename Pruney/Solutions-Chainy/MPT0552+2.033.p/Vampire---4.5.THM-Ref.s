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
% DateTime   : Thu Dec  3 12:49:49 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 128 expanded)
%              Number of leaves         :    9 (  31 expanded)
%              Depth                    :   13
%              Number of atoms          :   86 ( 232 expanded)
%              Number of equality atoms :   14 (  40 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f103,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f38,f96,f102])).

fof(f102,plain,(
    spl3_2 ),
    inference(avatar_contradiction_clause,[],[f101])).

fof(f101,plain,
    ( $false
    | spl3_2 ),
    inference(subsumption_resolution,[],[f100,f16])).

fof(f16,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_relat_1)).

fof(f100,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_2 ),
    inference(resolution,[],[f97,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f97,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | spl3_2 ),
    inference(resolution,[],[f92,f37])).

fof(f37,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k9_relat_1(sK2,sK1))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl3_2
  <=> r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k9_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f92,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(sK2,k3_xboole_0(X1,X0)),k9_relat_1(sK2,X0))
      | ~ v1_relat_1(k7_relat_1(sK2,X0)) ) ),
    inference(superposition,[],[f88,f18])).

fof(f18,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f88,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(sK2,k3_xboole_0(X0,X1)),k9_relat_1(sK2,X0))
      | ~ v1_relat_1(k7_relat_1(sK2,X0)) ) ),
    inference(superposition,[],[f26,f81])).

fof(f81,plain,(
    ! [X0,X1] : k9_relat_1(k7_relat_1(sK2,X0),X1) = k9_relat_1(sK2,k3_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f80,f24])).

fof(f24,plain,(
    ! [X0] : k9_relat_1(sK2,X0) = k2_relat_1(k7_relat_1(sK2,X0)) ),
    inference(resolution,[],[f21,f16])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f80,plain,(
    ! [X0,X1] : k9_relat_1(k7_relat_1(sK2,X0),X1) = k2_relat_1(k7_relat_1(sK2,k3_xboole_0(X0,X1))) ),
    inference(forward_demodulation,[],[f76,f39])).

fof(f39,plain,(
    ! [X0,X1] : k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k3_xboole_0(X0,X1)) ),
    inference(resolution,[],[f22,f16])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

fof(f76,plain,(
    ! [X0,X1] : k9_relat_1(k7_relat_1(sK2,X0),X1) = k2_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1)) ),
    inference(resolution,[],[f25,f16])).

fof(f25,plain,(
    ! [X2,X3,X1] :
      ( ~ v1_relat_1(X1)
      | k9_relat_1(k7_relat_1(X1,X2),X3) = k2_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3)) ) ),
    inference(resolution,[],[f21,f19])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(k7_relat_1(sK2,X0),X1),k9_relat_1(sK2,X0))
      | ~ v1_relat_1(k7_relat_1(sK2,X0)) ) ),
    inference(superposition,[],[f20,f24])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

fof(f96,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f95])).

fof(f95,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f94,f16])).

fof(f94,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_1 ),
    inference(resolution,[],[f91,f19])).

fof(f91,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | spl3_1 ),
    inference(resolution,[],[f88,f33])).

fof(f33,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k9_relat_1(sK2,sK0))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f31])).

fof(f31,plain,
    ( spl3_1
  <=> r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k9_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f38,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f27,f35,f31])).

fof(f27,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k9_relat_1(sK2,sK1))
    | ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k9_relat_1(sK2,sK0)) ),
    inference(resolution,[],[f23,f17])).

fof(f17,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f9])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:46:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.41  % (1552)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.22/0.42  % (1550)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.42  % (1551)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.22/0.43  % (1549)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.22/0.44  % (1545)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.22/0.44  % (1545)Refutation found. Thanks to Tanya!
% 0.22/0.44  % SZS status Theorem for theBenchmark
% 0.22/0.44  % SZS output start Proof for theBenchmark
% 0.22/0.44  fof(f103,plain,(
% 0.22/0.44    $false),
% 0.22/0.44    inference(avatar_sat_refutation,[],[f38,f96,f102])).
% 0.22/0.44  fof(f102,plain,(
% 0.22/0.44    spl3_2),
% 0.22/0.44    inference(avatar_contradiction_clause,[],[f101])).
% 0.22/0.44  fof(f101,plain,(
% 0.22/0.44    $false | spl3_2),
% 0.22/0.44    inference(subsumption_resolution,[],[f100,f16])).
% 0.22/0.44  fof(f16,plain,(
% 0.22/0.44    v1_relat_1(sK2)),
% 0.22/0.44    inference(cnf_transformation,[],[f9])).
% 0.22/0.44  fof(f9,plain,(
% 0.22/0.44    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) & v1_relat_1(X2))),
% 0.22/0.44    inference(ennf_transformation,[],[f8])).
% 0.22/0.44  fof(f8,negated_conjecture,(
% 0.22/0.44    ~! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.22/0.44    inference(negated_conjecture,[],[f7])).
% 0.22/0.44  fof(f7,conjecture,(
% 0.22/0.44    ! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_relat_1)).
% 0.22/0.44  fof(f100,plain,(
% 0.22/0.44    ~v1_relat_1(sK2) | spl3_2),
% 0.22/0.44    inference(resolution,[],[f97,f19])).
% 0.22/0.44  fof(f19,plain,(
% 0.22/0.44    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f10])).
% 0.22/0.44  fof(f10,plain,(
% 0.22/0.44    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.22/0.44    inference(ennf_transformation,[],[f3])).
% 0.22/0.44  fof(f3,axiom,(
% 0.22/0.44    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.22/0.44  fof(f97,plain,(
% 0.22/0.44    ~v1_relat_1(k7_relat_1(sK2,sK1)) | spl3_2),
% 0.22/0.44    inference(resolution,[],[f92,f37])).
% 0.22/0.44  fof(f37,plain,(
% 0.22/0.44    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k9_relat_1(sK2,sK1)) | spl3_2),
% 0.22/0.44    inference(avatar_component_clause,[],[f35])).
% 0.22/0.44  fof(f35,plain,(
% 0.22/0.44    spl3_2 <=> r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k9_relat_1(sK2,sK1))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.44  fof(f92,plain,(
% 0.22/0.44    ( ! [X0,X1] : (r1_tarski(k9_relat_1(sK2,k3_xboole_0(X1,X0)),k9_relat_1(sK2,X0)) | ~v1_relat_1(k7_relat_1(sK2,X0))) )),
% 0.22/0.44    inference(superposition,[],[f88,f18])).
% 0.22/0.44  fof(f18,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f1])).
% 0.22/0.44  fof(f1,axiom,(
% 0.22/0.44    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.44  fof(f88,plain,(
% 0.22/0.44    ( ! [X0,X1] : (r1_tarski(k9_relat_1(sK2,k3_xboole_0(X0,X1)),k9_relat_1(sK2,X0)) | ~v1_relat_1(k7_relat_1(sK2,X0))) )),
% 0.22/0.44    inference(superposition,[],[f26,f81])).
% 0.22/0.44  fof(f81,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k9_relat_1(k7_relat_1(sK2,X0),X1) = k9_relat_1(sK2,k3_xboole_0(X0,X1))) )),
% 0.22/0.44    inference(forward_demodulation,[],[f80,f24])).
% 0.22/0.44  fof(f24,plain,(
% 0.22/0.44    ( ! [X0] : (k9_relat_1(sK2,X0) = k2_relat_1(k7_relat_1(sK2,X0))) )),
% 0.22/0.44    inference(resolution,[],[f21,f16])).
% 0.22/0.44  fof(f21,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~v1_relat_1(X1) | k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f12])).
% 0.22/0.44  fof(f12,plain,(
% 0.22/0.44    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 0.22/0.44    inference(ennf_transformation,[],[f6])).
% 0.22/0.44  fof(f6,axiom,(
% 0.22/0.44    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.22/0.44  fof(f80,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k9_relat_1(k7_relat_1(sK2,X0),X1) = k2_relat_1(k7_relat_1(sK2,k3_xboole_0(X0,X1)))) )),
% 0.22/0.44    inference(forward_demodulation,[],[f76,f39])).
% 0.22/0.44  fof(f39,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k3_xboole_0(X0,X1))) )),
% 0.22/0.44    inference(resolution,[],[f22,f16])).
% 0.22/0.45  fof(f22,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f13])).
% 0.22/0.45  fof(f13,plain,(
% 0.22/0.45    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.22/0.45    inference(ennf_transformation,[],[f4])).
% 0.22/0.45  fof(f4,axiom,(
% 0.22/0.45    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).
% 0.22/0.45  fof(f76,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k9_relat_1(k7_relat_1(sK2,X0),X1) = k2_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1))) )),
% 0.22/0.45    inference(resolution,[],[f25,f16])).
% 0.22/0.45  fof(f25,plain,(
% 0.22/0.45    ( ! [X2,X3,X1] : (~v1_relat_1(X1) | k9_relat_1(k7_relat_1(X1,X2),X3) = k2_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3))) )),
% 0.22/0.45    inference(resolution,[],[f21,f19])).
% 0.22/0.45  fof(f26,plain,(
% 0.22/0.45    ( ! [X0,X1] : (r1_tarski(k9_relat_1(k7_relat_1(sK2,X0),X1),k9_relat_1(sK2,X0)) | ~v1_relat_1(k7_relat_1(sK2,X0))) )),
% 0.22/0.45    inference(superposition,[],[f20,f24])).
% 0.22/0.45  fof(f20,plain,(
% 0.22/0.45    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f11])).
% 0.22/0.45  fof(f11,plain,(
% 0.22/0.45    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.22/0.45    inference(ennf_transformation,[],[f5])).
% 0.22/0.45  fof(f5,axiom,(
% 0.22/0.45    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).
% 0.22/0.45  fof(f96,plain,(
% 0.22/0.45    spl3_1),
% 0.22/0.45    inference(avatar_contradiction_clause,[],[f95])).
% 0.22/0.45  fof(f95,plain,(
% 0.22/0.45    $false | spl3_1),
% 0.22/0.45    inference(subsumption_resolution,[],[f94,f16])).
% 0.22/0.45  fof(f94,plain,(
% 0.22/0.45    ~v1_relat_1(sK2) | spl3_1),
% 0.22/0.45    inference(resolution,[],[f91,f19])).
% 0.22/0.45  fof(f91,plain,(
% 0.22/0.45    ~v1_relat_1(k7_relat_1(sK2,sK0)) | spl3_1),
% 0.22/0.45    inference(resolution,[],[f88,f33])).
% 0.22/0.45  fof(f33,plain,(
% 0.22/0.45    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k9_relat_1(sK2,sK0)) | spl3_1),
% 0.22/0.45    inference(avatar_component_clause,[],[f31])).
% 0.22/0.45  fof(f31,plain,(
% 0.22/0.45    spl3_1 <=> r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k9_relat_1(sK2,sK0))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.45  fof(f38,plain,(
% 0.22/0.45    ~spl3_1 | ~spl3_2),
% 0.22/0.45    inference(avatar_split_clause,[],[f27,f35,f31])).
% 0.22/0.45  fof(f27,plain,(
% 0.22/0.45    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k9_relat_1(sK2,sK1)) | ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k9_relat_1(sK2,sK0))),
% 0.22/0.45    inference(resolution,[],[f23,f17])).
% 0.22/0.45  fof(f17,plain,(
% 0.22/0.45    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))),
% 0.22/0.45    inference(cnf_transformation,[],[f9])).
% 0.22/0.45  fof(f23,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f15])).
% 0.22/0.45  fof(f15,plain,(
% 0.22/0.45    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.45    inference(flattening,[],[f14])).
% 0.22/0.45  fof(f14,plain,(
% 0.22/0.45    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.45    inference(ennf_transformation,[],[f2])).
% 0.22/0.45  fof(f2,axiom,(
% 0.22/0.45    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.22/0.45  % SZS output end Proof for theBenchmark
% 0.22/0.45  % (1545)------------------------------
% 0.22/0.45  % (1545)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.45  % (1545)Termination reason: Refutation
% 0.22/0.45  
% 0.22/0.45  % (1545)Memory used [KB]: 10618
% 0.22/0.45  % (1545)Time elapsed: 0.008 s
% 0.22/0.45  % (1545)------------------------------
% 0.22/0.45  % (1545)------------------------------
% 0.22/0.45  % (1544)Success in time 0.089 s
%------------------------------------------------------------------------------
