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
% DateTime   : Thu Dec  3 12:49:38 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   52 (  93 expanded)
%              Number of leaves         :    9 (  25 expanded)
%              Depth                    :   13
%              Number of atoms          :  111 ( 210 expanded)
%              Number of equality atoms :   37 (  67 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f89,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f34,f35,f52,f85])).

fof(f85,plain,
    ( ~ spl2_1
    | spl2_2 ),
    inference(avatar_contradiction_clause,[],[f84])).

fof(f84,plain,
    ( $false
    | ~ spl2_1
    | spl2_2 ),
    inference(subsumption_resolution,[],[f83,f17])).

fof(f17,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k9_relat_1(X1,X0)
      <~> r1_xboole_0(k1_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k9_relat_1(X1,X0)
        <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

fof(f83,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl2_1
    | spl2_2 ),
    inference(subsumption_resolution,[],[f80,f32])).

fof(f32,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f31])).

fof(f31,plain,
    ( spl2_2
  <=> r1_xboole_0(k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f80,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl2_1 ),
    inference(trivial_inequality_removal,[],[f78])).

fof(f78,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl2_1 ),
    inference(superposition,[],[f25,f72])).

fof(f72,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ spl2_1 ),
    inference(forward_demodulation,[],[f71,f40])).

fof(f40,plain,(
    ! [X0] : k1_xboole_0 = k8_relat_1(k1_xboole_0,k7_relat_1(sK1,X0)) ),
    inference(resolution,[],[f37,f17])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k8_relat_1(k1_xboole_0,k7_relat_1(X0,X1)) ) ),
    inference(resolution,[],[f20,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k8_relat_1(k1_xboole_0,X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k1_xboole_0 = k8_relat_1(k1_xboole_0,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k8_relat_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_relat_1)).

fof(f71,plain,
    ( k7_relat_1(sK1,sK0) = k8_relat_1(k1_xboole_0,k7_relat_1(sK1,sK0))
    | ~ spl2_1 ),
    inference(superposition,[],[f68,f29])).

fof(f29,plain,
    ( k1_xboole_0 = k9_relat_1(sK1,sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f27])).

fof(f27,plain,
    ( spl2_1
  <=> k1_xboole_0 = k9_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f68,plain,(
    ! [X0] : k7_relat_1(sK1,X0) = k8_relat_1(k9_relat_1(sK1,X0),k7_relat_1(sK1,X0)) ),
    inference(forward_demodulation,[],[f66,f42])).

fof(f42,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0) ),
    inference(resolution,[],[f23,f17])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f66,plain,(
    ! [X0] : k7_relat_1(sK1,X0) = k8_relat_1(k2_relat_1(k7_relat_1(sK1,X0)),k7_relat_1(sK1,X0)) ),
    inference(resolution,[],[f39,f17])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(X0,X1) = k8_relat_1(k2_relat_1(k7_relat_1(X0,X1)),k7_relat_1(X0,X1)) ) ),
    inference(resolution,[],[f21,f22])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k8_relat_1(k2_relat_1(X0),X0) = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k8_relat_1(k2_relat_1(X0),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k8_relat_1(k2_relat_1(X0),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_relat_1)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k7_relat_1(X1,X0)
      | r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

fof(f52,plain,
    ( spl2_1
    | ~ spl2_2 ),
    inference(avatar_contradiction_clause,[],[f51])).

fof(f51,plain,
    ( $false
    | spl2_1
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f50,f28])).

fof(f28,plain,
    ( k1_xboole_0 != k9_relat_1(sK1,sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f27])).

fof(f50,plain,
    ( k1_xboole_0 = k9_relat_1(sK1,sK0)
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f47,f19])).

fof(f19,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f47,plain,
    ( k2_relat_1(k1_xboole_0) = k9_relat_1(sK1,sK0)
    | ~ spl2_2 ),
    inference(superposition,[],[f42,f46])).

fof(f46,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f44,f17])).

fof(f44,plain,
    ( ~ v1_relat_1(sK1)
    | k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ spl2_2 ),
    inference(resolution,[],[f24,f33])).

fof(f33,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f31])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | k1_xboole_0 = k7_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f35,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f16,f31,f27])).

fof(f16,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 != k9_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f34,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f15,f31,f27])).

fof(f15,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 = k9_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:40:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.38  % (27487)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.41  % (27481)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.21/0.41  % (27481)Refutation found. Thanks to Tanya!
% 0.21/0.41  % SZS status Theorem for theBenchmark
% 0.21/0.41  % SZS output start Proof for theBenchmark
% 0.21/0.41  fof(f89,plain,(
% 0.21/0.41    $false),
% 0.21/0.41    inference(avatar_sat_refutation,[],[f34,f35,f52,f85])).
% 0.21/0.41  fof(f85,plain,(
% 0.21/0.41    ~spl2_1 | spl2_2),
% 0.21/0.41    inference(avatar_contradiction_clause,[],[f84])).
% 0.21/0.41  fof(f84,plain,(
% 0.21/0.41    $false | (~spl2_1 | spl2_2)),
% 0.21/0.41    inference(subsumption_resolution,[],[f83,f17])).
% 0.21/0.41  fof(f17,plain,(
% 0.21/0.41    v1_relat_1(sK1)),
% 0.21/0.41    inference(cnf_transformation,[],[f9])).
% 0.21/0.41  fof(f9,plain,(
% 0.21/0.41    ? [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) <~> r1_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1))),
% 0.21/0.41    inference(ennf_transformation,[],[f8])).
% 0.21/0.41  fof(f8,negated_conjecture,(
% 0.21/0.41    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.21/0.41    inference(negated_conjecture,[],[f7])).
% 0.21/0.41  fof(f7,conjecture,(
% 0.21/0.41    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).
% 0.21/0.41  fof(f83,plain,(
% 0.21/0.41    ~v1_relat_1(sK1) | (~spl2_1 | spl2_2)),
% 0.21/0.41    inference(subsumption_resolution,[],[f80,f32])).
% 0.21/0.41  fof(f32,plain,(
% 0.21/0.41    ~r1_xboole_0(k1_relat_1(sK1),sK0) | spl2_2),
% 0.21/0.41    inference(avatar_component_clause,[],[f31])).
% 0.21/0.41  fof(f31,plain,(
% 0.21/0.41    spl2_2 <=> r1_xboole_0(k1_relat_1(sK1),sK0)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.41  fof(f80,plain,(
% 0.21/0.41    r1_xboole_0(k1_relat_1(sK1),sK0) | ~v1_relat_1(sK1) | ~spl2_1),
% 0.21/0.41    inference(trivial_inequality_removal,[],[f78])).
% 0.21/0.41  fof(f78,plain,(
% 0.21/0.41    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_relat_1(sK1),sK0) | ~v1_relat_1(sK1) | ~spl2_1),
% 0.21/0.41    inference(superposition,[],[f25,f72])).
% 0.21/0.41  fof(f72,plain,(
% 0.21/0.41    k1_xboole_0 = k7_relat_1(sK1,sK0) | ~spl2_1),
% 0.21/0.41    inference(forward_demodulation,[],[f71,f40])).
% 0.21/0.41  fof(f40,plain,(
% 0.21/0.41    ( ! [X0] : (k1_xboole_0 = k8_relat_1(k1_xboole_0,k7_relat_1(sK1,X0))) )),
% 0.21/0.41    inference(resolution,[],[f37,f17])).
% 0.21/0.41  fof(f37,plain,(
% 0.21/0.41    ( ! [X0,X1] : (~v1_relat_1(X0) | k1_xboole_0 = k8_relat_1(k1_xboole_0,k7_relat_1(X0,X1))) )),
% 0.21/0.41    inference(resolution,[],[f20,f22])).
% 0.21/0.41  fof(f22,plain,(
% 0.21/0.41    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f12])).
% 0.21/0.41  fof(f12,plain,(
% 0.21/0.41    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.41    inference(ennf_transformation,[],[f1])).
% 0.21/0.41  fof(f1,axiom,(
% 0.21/0.41    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.21/0.41  fof(f20,plain,(
% 0.21/0.41    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k8_relat_1(k1_xboole_0,X0)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f10])).
% 0.21/0.41  fof(f10,plain,(
% 0.21/0.41    ! [X0] : (k1_xboole_0 = k8_relat_1(k1_xboole_0,X0) | ~v1_relat_1(X0))),
% 0.21/0.41    inference(ennf_transformation,[],[f3])).
% 0.21/0.41  fof(f3,axiom,(
% 0.21/0.41    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k8_relat_1(k1_xboole_0,X0))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_relat_1)).
% 0.21/0.41  fof(f71,plain,(
% 0.21/0.41    k7_relat_1(sK1,sK0) = k8_relat_1(k1_xboole_0,k7_relat_1(sK1,sK0)) | ~spl2_1),
% 0.21/0.41    inference(superposition,[],[f68,f29])).
% 0.21/0.41  fof(f29,plain,(
% 0.21/0.41    k1_xboole_0 = k9_relat_1(sK1,sK0) | ~spl2_1),
% 0.21/0.41    inference(avatar_component_clause,[],[f27])).
% 0.21/0.41  fof(f27,plain,(
% 0.21/0.41    spl2_1 <=> k1_xboole_0 = k9_relat_1(sK1,sK0)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.41  fof(f68,plain,(
% 0.21/0.41    ( ! [X0] : (k7_relat_1(sK1,X0) = k8_relat_1(k9_relat_1(sK1,X0),k7_relat_1(sK1,X0))) )),
% 0.21/0.41    inference(forward_demodulation,[],[f66,f42])).
% 0.21/0.41  fof(f42,plain,(
% 0.21/0.41    ( ! [X0] : (k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0)) )),
% 0.21/0.41    inference(resolution,[],[f23,f17])).
% 0.21/0.41  fof(f23,plain,(
% 0.21/0.41    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f13])).
% 0.21/0.41  fof(f13,plain,(
% 0.21/0.41    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.41    inference(ennf_transformation,[],[f4])).
% 0.21/0.41  fof(f4,axiom,(
% 0.21/0.41    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.21/0.41  fof(f66,plain,(
% 0.21/0.41    ( ! [X0] : (k7_relat_1(sK1,X0) = k8_relat_1(k2_relat_1(k7_relat_1(sK1,X0)),k7_relat_1(sK1,X0))) )),
% 0.21/0.41    inference(resolution,[],[f39,f17])).
% 0.21/0.41  fof(f39,plain,(
% 0.21/0.41    ( ! [X0,X1] : (~v1_relat_1(X0) | k7_relat_1(X0,X1) = k8_relat_1(k2_relat_1(k7_relat_1(X0,X1)),k7_relat_1(X0,X1))) )),
% 0.21/0.41    inference(resolution,[],[f21,f22])).
% 0.21/0.41  fof(f21,plain,(
% 0.21/0.41    ( ! [X0] : (~v1_relat_1(X0) | k8_relat_1(k2_relat_1(X0),X0) = X0) )),
% 0.21/0.41    inference(cnf_transformation,[],[f11])).
% 0.21/0.41  fof(f11,plain,(
% 0.21/0.41    ! [X0] : (k8_relat_1(k2_relat_1(X0),X0) = X0 | ~v1_relat_1(X0))),
% 0.21/0.41    inference(ennf_transformation,[],[f2])).
% 0.21/0.41  fof(f2,axiom,(
% 0.21/0.41    ! [X0] : (v1_relat_1(X0) => k8_relat_1(k2_relat_1(X0),X0) = X0)),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_relat_1)).
% 0.21/0.41  fof(f25,plain,(
% 0.21/0.41    ( ! [X0,X1] : (k1_xboole_0 != k7_relat_1(X1,X0) | r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f14])).
% 0.21/0.41  fof(f14,plain,(
% 0.21/0.41    ! [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.41    inference(ennf_transformation,[],[f6])).
% 0.21/0.41  fof(f6,axiom,(
% 0.21/0.41    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).
% 0.21/0.41  fof(f52,plain,(
% 0.21/0.41    spl2_1 | ~spl2_2),
% 0.21/0.41    inference(avatar_contradiction_clause,[],[f51])).
% 0.21/0.41  fof(f51,plain,(
% 0.21/0.41    $false | (spl2_1 | ~spl2_2)),
% 0.21/0.41    inference(subsumption_resolution,[],[f50,f28])).
% 0.21/0.41  fof(f28,plain,(
% 0.21/0.41    k1_xboole_0 != k9_relat_1(sK1,sK0) | spl2_1),
% 0.21/0.41    inference(avatar_component_clause,[],[f27])).
% 0.21/0.41  fof(f50,plain,(
% 0.21/0.41    k1_xboole_0 = k9_relat_1(sK1,sK0) | ~spl2_2),
% 0.21/0.41    inference(forward_demodulation,[],[f47,f19])).
% 0.21/0.41  fof(f19,plain,(
% 0.21/0.41    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.41    inference(cnf_transformation,[],[f5])).
% 0.21/0.41  fof(f5,axiom,(
% 0.21/0.41    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.41  fof(f47,plain,(
% 0.21/0.41    k2_relat_1(k1_xboole_0) = k9_relat_1(sK1,sK0) | ~spl2_2),
% 0.21/0.41    inference(superposition,[],[f42,f46])).
% 0.21/0.41  fof(f46,plain,(
% 0.21/0.41    k1_xboole_0 = k7_relat_1(sK1,sK0) | ~spl2_2),
% 0.21/0.41    inference(subsumption_resolution,[],[f44,f17])).
% 0.21/0.41  fof(f44,plain,(
% 0.21/0.41    ~v1_relat_1(sK1) | k1_xboole_0 = k7_relat_1(sK1,sK0) | ~spl2_2),
% 0.21/0.41    inference(resolution,[],[f24,f33])).
% 0.21/0.41  fof(f33,plain,(
% 0.21/0.41    r1_xboole_0(k1_relat_1(sK1),sK0) | ~spl2_2),
% 0.21/0.41    inference(avatar_component_clause,[],[f31])).
% 0.21/0.41  fof(f24,plain,(
% 0.21/0.41    ( ! [X0,X1] : (~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | k1_xboole_0 = k7_relat_1(X1,X0)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f14])).
% 0.21/0.41  fof(f35,plain,(
% 0.21/0.41    ~spl2_1 | ~spl2_2),
% 0.21/0.41    inference(avatar_split_clause,[],[f16,f31,f27])).
% 0.21/0.41  fof(f16,plain,(
% 0.21/0.41    ~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k9_relat_1(sK1,sK0)),
% 0.21/0.41    inference(cnf_transformation,[],[f9])).
% 0.21/0.41  fof(f34,plain,(
% 0.21/0.41    spl2_1 | spl2_2),
% 0.21/0.41    inference(avatar_split_clause,[],[f15,f31,f27])).
% 0.21/0.41  fof(f15,plain,(
% 0.21/0.41    r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k9_relat_1(sK1,sK0)),
% 0.21/0.41    inference(cnf_transformation,[],[f9])).
% 0.21/0.41  % SZS output end Proof for theBenchmark
% 0.21/0.41  % (27481)------------------------------
% 0.21/0.41  % (27481)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.41  % (27481)Termination reason: Refutation
% 0.21/0.41  
% 0.21/0.41  % (27481)Memory used [KB]: 10618
% 0.21/0.41  % (27481)Time elapsed: 0.007 s
% 0.21/0.41  % (27481)------------------------------
% 0.21/0.41  % (27481)------------------------------
% 0.21/0.41  % (27480)Success in time 0.064 s
%------------------------------------------------------------------------------
