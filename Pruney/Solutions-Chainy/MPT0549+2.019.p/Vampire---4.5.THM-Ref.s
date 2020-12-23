%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:38 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   56 (  95 expanded)
%              Number of leaves         :   10 (  26 expanded)
%              Depth                    :   16
%              Number of atoms          :  125 ( 216 expanded)
%              Number of equality atoms :   29 (  59 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f86,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f38,f56,f85])).

fof(f85,plain,
    ( ~ spl3_1
    | spl3_2 ),
    inference(avatar_contradiction_clause,[],[f84])).

fof(f84,plain,
    ( $false
    | ~ spl3_1
    | spl3_2 ),
    inference(subsumption_resolution,[],[f83,f19])).

fof(f19,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k9_relat_1(X1,X0)
      <~> r1_xboole_0(k1_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k9_relat_1(X1,X0)
        <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

fof(f83,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl3_1
    | spl3_2 ),
    inference(subsumption_resolution,[],[f82,f35])).

fof(f35,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl3_2
  <=> r1_xboole_0(k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f82,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl3_1 ),
    inference(trivial_inequality_removal,[],[f81])).

fof(f81,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl3_1 ),
    inference(superposition,[],[f27,f60])).

fof(f60,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ spl3_1 ),
    inference(resolution,[],[f59,f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f59,plain,
    ( v1_xboole_0(k7_relat_1(sK1,sK0))
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f58,f40])).

fof(f40,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[],[f28,f39])).

fof(f39,plain,(
    k1_xboole_0 = sK2 ),
    inference(resolution,[],[f22,f28])).

fof(f28,plain,(
    v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ? [X0] : v1_xboole_0(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).

fof(f58,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(k7_relat_1(sK1,sK0))
    | ~ spl3_1 ),
    inference(superposition,[],[f47,f32])).

fof(f32,plain,
    ( k1_xboole_0 = k9_relat_1(sK1,sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f30])).

fof(f30,plain,
    ( spl3_1
  <=> k1_xboole_0 = k9_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k9_relat_1(sK1,X0))
      | v1_xboole_0(k7_relat_1(sK1,X0)) ) ),
    inference(subsumption_resolution,[],[f46,f19])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k9_relat_1(sK1,X0))
      | v1_xboole_0(k7_relat_1(sK1,X0))
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f45,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f45,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k7_relat_1(sK1,X0))
      | ~ v1_xboole_0(k9_relat_1(sK1,X0))
      | v1_xboole_0(k7_relat_1(sK1,X0)) ) ),
    inference(superposition,[],[f23,f43])).

fof(f43,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0) ),
    inference(resolution,[],[f25,f19])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k7_relat_1(X1,X0)
      | r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

fof(f56,plain,
    ( spl3_1
    | ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f55])).

fof(f55,plain,
    ( $false
    | spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f54,f31])).

fof(f31,plain,
    ( k1_xboole_0 != k9_relat_1(sK1,sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f30])).

fof(f54,plain,
    ( k1_xboole_0 = k9_relat_1(sK1,sK0)
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f52,f21])).

fof(f21,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f52,plain,
    ( k2_relat_1(k1_xboole_0) = k9_relat_1(sK1,sK0)
    | ~ spl3_2 ),
    inference(superposition,[],[f43,f50])).

fof(f50,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f48,f19])).

fof(f48,plain,
    ( ~ v1_relat_1(sK1)
    | k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ spl3_2 ),
    inference(resolution,[],[f26,f36])).

fof(f36,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f34])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | k1_xboole_0 = k7_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f38,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f18,f34,f30])).

fof(f18,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 != k9_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f37,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f17,f34,f30])).

fof(f17,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 = k9_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:12:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.41  % (13251)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.20/0.41  % (13258)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.20/0.41  % (13251)Refutation found. Thanks to Tanya!
% 0.20/0.41  % SZS status Theorem for theBenchmark
% 0.20/0.41  % SZS output start Proof for theBenchmark
% 0.20/0.41  fof(f86,plain,(
% 0.20/0.41    $false),
% 0.20/0.41    inference(avatar_sat_refutation,[],[f37,f38,f56,f85])).
% 0.20/0.41  fof(f85,plain,(
% 0.20/0.41    ~spl3_1 | spl3_2),
% 0.20/0.41    inference(avatar_contradiction_clause,[],[f84])).
% 0.20/0.41  fof(f84,plain,(
% 0.20/0.41    $false | (~spl3_1 | spl3_2)),
% 0.20/0.41    inference(subsumption_resolution,[],[f83,f19])).
% 0.20/0.41  fof(f19,plain,(
% 0.20/0.41    v1_relat_1(sK1)),
% 0.20/0.41    inference(cnf_transformation,[],[f10])).
% 0.20/0.41  fof(f10,plain,(
% 0.20/0.41    ? [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) <~> r1_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1))),
% 0.20/0.41    inference(ennf_transformation,[],[f9])).
% 0.20/0.42  fof(f9,negated_conjecture,(
% 0.20/0.42    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.20/0.42    inference(negated_conjecture,[],[f8])).
% 0.20/0.42  fof(f8,conjecture,(
% 0.20/0.42    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).
% 0.20/0.42  fof(f83,plain,(
% 0.20/0.42    ~v1_relat_1(sK1) | (~spl3_1 | spl3_2)),
% 0.20/0.42    inference(subsumption_resolution,[],[f82,f35])).
% 0.20/0.42  fof(f35,plain,(
% 0.20/0.42    ~r1_xboole_0(k1_relat_1(sK1),sK0) | spl3_2),
% 0.20/0.42    inference(avatar_component_clause,[],[f34])).
% 0.20/0.42  fof(f34,plain,(
% 0.20/0.42    spl3_2 <=> r1_xboole_0(k1_relat_1(sK1),sK0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.42  fof(f82,plain,(
% 0.20/0.42    r1_xboole_0(k1_relat_1(sK1),sK0) | ~v1_relat_1(sK1) | ~spl3_1),
% 0.20/0.42    inference(trivial_inequality_removal,[],[f81])).
% 0.20/0.42  fof(f81,plain,(
% 0.20/0.42    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_relat_1(sK1),sK0) | ~v1_relat_1(sK1) | ~spl3_1),
% 0.20/0.42    inference(superposition,[],[f27,f60])).
% 0.20/0.42  fof(f60,plain,(
% 0.20/0.42    k1_xboole_0 = k7_relat_1(sK1,sK0) | ~spl3_1),
% 0.20/0.42    inference(resolution,[],[f59,f22])).
% 0.20/0.42  fof(f22,plain,(
% 0.20/0.42    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.20/0.42    inference(cnf_transformation,[],[f11])).
% 0.20/0.42  fof(f11,plain,(
% 0.20/0.42    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.42    inference(ennf_transformation,[],[f1])).
% 0.20/0.42  fof(f1,axiom,(
% 0.20/0.42    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.42  fof(f59,plain,(
% 0.20/0.42    v1_xboole_0(k7_relat_1(sK1,sK0)) | ~spl3_1),
% 0.20/0.42    inference(subsumption_resolution,[],[f58,f40])).
% 0.20/0.42  fof(f40,plain,(
% 0.20/0.42    v1_xboole_0(k1_xboole_0)),
% 0.20/0.42    inference(superposition,[],[f28,f39])).
% 0.20/0.42  fof(f39,plain,(
% 0.20/0.42    k1_xboole_0 = sK2),
% 0.20/0.42    inference(resolution,[],[f22,f28])).
% 0.20/0.42  fof(f28,plain,(
% 0.20/0.42    v1_xboole_0(sK2)),
% 0.20/0.42    inference(cnf_transformation,[],[f2])).
% 0.20/0.42  fof(f2,axiom,(
% 0.20/0.42    ? [X0] : v1_xboole_0(X0)),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).
% 0.20/0.42  fof(f58,plain,(
% 0.20/0.42    ~v1_xboole_0(k1_xboole_0) | v1_xboole_0(k7_relat_1(sK1,sK0)) | ~spl3_1),
% 0.20/0.42    inference(superposition,[],[f47,f32])).
% 0.20/0.42  fof(f32,plain,(
% 0.20/0.42    k1_xboole_0 = k9_relat_1(sK1,sK0) | ~spl3_1),
% 0.20/0.42    inference(avatar_component_clause,[],[f30])).
% 0.20/0.42  fof(f30,plain,(
% 0.20/0.42    spl3_1 <=> k1_xboole_0 = k9_relat_1(sK1,sK0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.42  fof(f47,plain,(
% 0.20/0.42    ( ! [X0] : (~v1_xboole_0(k9_relat_1(sK1,X0)) | v1_xboole_0(k7_relat_1(sK1,X0))) )),
% 0.20/0.42    inference(subsumption_resolution,[],[f46,f19])).
% 0.20/0.42  fof(f46,plain,(
% 0.20/0.42    ( ! [X0] : (~v1_xboole_0(k9_relat_1(sK1,X0)) | v1_xboole_0(k7_relat_1(sK1,X0)) | ~v1_relat_1(sK1)) )),
% 0.20/0.42    inference(resolution,[],[f45,f24])).
% 0.20/0.42  fof(f24,plain,(
% 0.20/0.42    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f14])).
% 0.20/0.42  fof(f14,plain,(
% 0.20/0.42    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.20/0.42    inference(ennf_transformation,[],[f3])).
% 0.20/0.42  fof(f3,axiom,(
% 0.20/0.42    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.20/0.42  fof(f45,plain,(
% 0.20/0.42    ( ! [X0] : (~v1_relat_1(k7_relat_1(sK1,X0)) | ~v1_xboole_0(k9_relat_1(sK1,X0)) | v1_xboole_0(k7_relat_1(sK1,X0))) )),
% 0.20/0.42    inference(superposition,[],[f23,f43])).
% 0.20/0.42  fof(f43,plain,(
% 0.20/0.42    ( ! [X0] : (k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0)) )),
% 0.20/0.42    inference(resolution,[],[f25,f19])).
% 0.20/0.42  fof(f25,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f15])).
% 0.20/0.42  fof(f15,plain,(
% 0.20/0.42    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.42    inference(ennf_transformation,[],[f5])).
% 0.20/0.42  fof(f5,axiom,(
% 0.20/0.42    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.20/0.42  fof(f23,plain,(
% 0.20/0.42    ( ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f13])).
% 0.20/0.42  fof(f13,plain,(
% 0.20/0.42    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 0.20/0.42    inference(flattening,[],[f12])).
% 0.20/0.42  fof(f12,plain,(
% 0.20/0.42    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 0.20/0.42    inference(ennf_transformation,[],[f4])).
% 0.20/0.42  fof(f4,axiom,(
% 0.20/0.42    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k2_relat_1(X0)))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).
% 0.20/0.42  fof(f27,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k1_xboole_0 != k7_relat_1(X1,X0) | r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f16])).
% 0.20/0.42  fof(f16,plain,(
% 0.20/0.42    ! [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.42    inference(ennf_transformation,[],[f7])).
% 0.20/0.42  fof(f7,axiom,(
% 0.20/0.42    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).
% 0.20/0.42  fof(f56,plain,(
% 0.20/0.42    spl3_1 | ~spl3_2),
% 0.20/0.42    inference(avatar_contradiction_clause,[],[f55])).
% 0.20/0.42  fof(f55,plain,(
% 0.20/0.42    $false | (spl3_1 | ~spl3_2)),
% 0.20/0.42    inference(subsumption_resolution,[],[f54,f31])).
% 0.20/0.42  fof(f31,plain,(
% 0.20/0.42    k1_xboole_0 != k9_relat_1(sK1,sK0) | spl3_1),
% 0.20/0.42    inference(avatar_component_clause,[],[f30])).
% 0.20/0.42  fof(f54,plain,(
% 0.20/0.42    k1_xboole_0 = k9_relat_1(sK1,sK0) | ~spl3_2),
% 0.20/0.42    inference(forward_demodulation,[],[f52,f21])).
% 0.20/0.42  fof(f21,plain,(
% 0.20/0.42    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.20/0.42    inference(cnf_transformation,[],[f6])).
% 0.20/0.42  fof(f6,axiom,(
% 0.20/0.42    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.20/0.42  fof(f52,plain,(
% 0.20/0.42    k2_relat_1(k1_xboole_0) = k9_relat_1(sK1,sK0) | ~spl3_2),
% 0.20/0.42    inference(superposition,[],[f43,f50])).
% 0.20/0.42  fof(f50,plain,(
% 0.20/0.42    k1_xboole_0 = k7_relat_1(sK1,sK0) | ~spl3_2),
% 0.20/0.42    inference(subsumption_resolution,[],[f48,f19])).
% 0.20/0.42  fof(f48,plain,(
% 0.20/0.42    ~v1_relat_1(sK1) | k1_xboole_0 = k7_relat_1(sK1,sK0) | ~spl3_2),
% 0.20/0.42    inference(resolution,[],[f26,f36])).
% 0.20/0.42  fof(f36,plain,(
% 0.20/0.42    r1_xboole_0(k1_relat_1(sK1),sK0) | ~spl3_2),
% 0.20/0.42    inference(avatar_component_clause,[],[f34])).
% 0.20/0.42  fof(f26,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | k1_xboole_0 = k7_relat_1(X1,X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f16])).
% 0.20/0.42  fof(f38,plain,(
% 0.20/0.42    ~spl3_1 | ~spl3_2),
% 0.20/0.42    inference(avatar_split_clause,[],[f18,f34,f30])).
% 0.20/0.42  fof(f18,plain,(
% 0.20/0.42    ~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k9_relat_1(sK1,sK0)),
% 0.20/0.42    inference(cnf_transformation,[],[f10])).
% 0.20/0.42  fof(f37,plain,(
% 0.20/0.42    spl3_1 | spl3_2),
% 0.20/0.42    inference(avatar_split_clause,[],[f17,f34,f30])).
% 0.20/0.42  fof(f17,plain,(
% 0.20/0.42    r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k9_relat_1(sK1,sK0)),
% 0.20/0.42    inference(cnf_transformation,[],[f10])).
% 0.20/0.42  % SZS output end Proof for theBenchmark
% 0.20/0.42  % (13251)------------------------------
% 0.20/0.42  % (13251)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.42  % (13251)Termination reason: Refutation
% 0.20/0.42  
% 0.20/0.42  % (13251)Memory used [KB]: 10618
% 0.20/0.42  % (13251)Time elapsed: 0.007 s
% 0.20/0.42  % (13251)------------------------------
% 0.20/0.42  % (13251)------------------------------
% 0.20/0.42  % (13250)Success in time 0.066 s
%------------------------------------------------------------------------------
