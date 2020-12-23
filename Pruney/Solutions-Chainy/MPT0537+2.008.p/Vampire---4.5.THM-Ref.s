%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:07 EST 2020

% Result     : Theorem 0.68s
% Output     : Refutation 0.68s
% Verified   : 
% Statistics : Number of formulae       :   33 (  41 expanded)
%              Number of leaves         :    9 (  14 expanded)
%              Depth                    :    7
%              Number of atoms          :   68 (  86 expanded)
%              Number of equality atoms :   14 (  21 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f43,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f25,f30,f35,f42])).

fof(f42,plain,
    ( ~ spl1_1
    | ~ spl1_2
    | spl1_3 ),
    inference(avatar_contradiction_clause,[],[f41])).

fof(f41,plain,
    ( $false
    | ~ spl1_1
    | ~ spl1_2
    | spl1_3 ),
    inference(subsumption_resolution,[],[f39,f37])).

fof(f37,plain,
    ( ~ v1_xboole_0(k8_relat_1(k1_xboole_0,sK0))
    | spl1_3 ),
    inference(unit_resulting_resolution,[],[f34,f17])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f34,plain,
    ( k1_xboole_0 != k8_relat_1(k1_xboole_0,sK0)
    | spl1_3 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl1_3
  <=> k1_xboole_0 = k8_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f39,plain,
    ( v1_xboole_0(k8_relat_1(k1_xboole_0,sK0))
    | ~ spl1_1
    | ~ spl1_2 ),
    inference(unit_resulting_resolution,[],[f24,f29,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k8_relat_1(X1,X0))
      | ~ v1_xboole_0(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( v1_relat_1(k8_relat_1(X1,X0))
        & v1_xboole_0(k8_relat_1(X1,X0)) )
      | ~ v1_xboole_0(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( v1_relat_1(k8_relat_1(X1,X0))
        & v1_xboole_0(k8_relat_1(X1,X0)) )
      | ~ v1_xboole_0(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X1)
        & v1_relat_1(X0) )
     => ( v1_relat_1(k8_relat_1(X1,X0))
        & v1_xboole_0(k8_relat_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc18_relat_1)).

fof(f29,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f27])).

fof(f27,plain,
    ( spl1_2
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f24,plain,
    ( v1_relat_1(sK0)
    | ~ spl1_1 ),
    inference(avatar_component_clause,[],[f22])).

fof(f22,plain,
    ( spl1_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f35,plain,(
    ~ spl1_3 ),
    inference(avatar_split_clause,[],[f14,f32])).

fof(f14,plain,(
    k1_xboole_0 != k8_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( k1_xboole_0 != k8_relat_1(k1_xboole_0,sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f11])).

fof(f11,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k8_relat_1(k1_xboole_0,X0)
        & v1_relat_1(X0) )
   => ( k1_xboole_0 != k8_relat_1(k1_xboole_0,sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( k1_xboole_0 != k8_relat_1(k1_xboole_0,X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k1_xboole_0 = k8_relat_1(k1_xboole_0,X0) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k8_relat_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_relat_1)).

fof(f30,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f20,f27])).

fof(f20,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(definition_unfolding,[],[f15,f16])).

fof(f16,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(f15,plain,(
    ! [X0] : v1_xboole_0(k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : v1_xboole_0(k1_subset_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc13_subset_1)).

fof(f25,plain,(
    spl1_1 ),
    inference(avatar_split_clause,[],[f13,f22])).

fof(f13,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:15:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.37  ipcrm: permission denied for id (811204608)
% 0.13/0.38  ipcrm: permission denied for id (811270149)
% 0.13/0.38  ipcrm: permission denied for id (811302920)
% 0.13/0.39  ipcrm: permission denied for id (811335693)
% 0.13/0.39  ipcrm: permission denied for id (811368462)
% 0.13/0.39  ipcrm: permission denied for id (811401236)
% 0.13/0.40  ipcrm: permission denied for id (811532315)
% 0.13/0.41  ipcrm: permission denied for id (811597853)
% 0.13/0.41  ipcrm: permission denied for id (811663392)
% 0.13/0.41  ipcrm: permission denied for id (811696165)
% 0.13/0.42  ipcrm: permission denied for id (811794476)
% 0.21/0.43  ipcrm: permission denied for id (811860016)
% 0.21/0.43  ipcrm: permission denied for id (811892787)
% 0.21/0.43  ipcrm: permission denied for id (811925557)
% 0.21/0.45  ipcrm: permission denied for id (811991109)
% 0.21/0.46  ipcrm: permission denied for id (812089416)
% 0.21/0.46  ipcrm: permission denied for id (812122188)
% 0.21/0.48  ipcrm: permission denied for id (812220505)
% 0.21/0.48  ipcrm: permission denied for id (812253278)
% 0.21/0.49  ipcrm: permission denied for id (812286048)
% 0.21/0.49  ipcrm: permission denied for id (812384356)
% 0.21/0.50  ipcrm: permission denied for id (812482663)
% 0.21/0.50  ipcrm: permission denied for id (812580970)
% 0.21/0.51  ipcrm: permission denied for id (812646512)
% 0.68/0.59  % (4824)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.68/0.59  % (4824)Refutation found. Thanks to Tanya!
% 0.68/0.59  % SZS status Theorem for theBenchmark
% 0.68/0.59  % SZS output start Proof for theBenchmark
% 0.68/0.59  fof(f43,plain,(
% 0.68/0.59    $false),
% 0.68/0.59    inference(avatar_sat_refutation,[],[f25,f30,f35,f42])).
% 0.68/0.59  fof(f42,plain,(
% 0.68/0.59    ~spl1_1 | ~spl1_2 | spl1_3),
% 0.68/0.59    inference(avatar_contradiction_clause,[],[f41])).
% 0.68/0.59  fof(f41,plain,(
% 0.68/0.59    $false | (~spl1_1 | ~spl1_2 | spl1_3)),
% 0.68/0.59    inference(subsumption_resolution,[],[f39,f37])).
% 0.68/0.59  fof(f37,plain,(
% 0.68/0.59    ~v1_xboole_0(k8_relat_1(k1_xboole_0,sK0)) | spl1_3),
% 0.68/0.59    inference(unit_resulting_resolution,[],[f34,f17])).
% 0.68/0.59  fof(f17,plain,(
% 0.68/0.59    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.68/0.59    inference(cnf_transformation,[],[f8])).
% 0.68/0.59  fof(f8,plain,(
% 0.68/0.59    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.68/0.59    inference(ennf_transformation,[],[f1])).
% 0.68/0.59  fof(f1,axiom,(
% 0.68/0.59    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.68/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.68/0.59  fof(f34,plain,(
% 0.68/0.59    k1_xboole_0 != k8_relat_1(k1_xboole_0,sK0) | spl1_3),
% 0.68/0.59    inference(avatar_component_clause,[],[f32])).
% 0.68/0.59  fof(f32,plain,(
% 0.68/0.59    spl1_3 <=> k1_xboole_0 = k8_relat_1(k1_xboole_0,sK0)),
% 0.68/0.59    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.68/0.59  fof(f39,plain,(
% 0.68/0.59    v1_xboole_0(k8_relat_1(k1_xboole_0,sK0)) | (~spl1_1 | ~spl1_2)),
% 0.68/0.59    inference(unit_resulting_resolution,[],[f24,f29,f18])).
% 0.68/0.59  fof(f18,plain,(
% 0.68/0.59    ( ! [X0,X1] : (v1_xboole_0(k8_relat_1(X1,X0)) | ~v1_xboole_0(X1) | ~v1_relat_1(X0)) )),
% 0.68/0.59    inference(cnf_transformation,[],[f10])).
% 0.68/0.59  fof(f10,plain,(
% 0.68/0.59    ! [X0,X1] : ((v1_relat_1(k8_relat_1(X1,X0)) & v1_xboole_0(k8_relat_1(X1,X0))) | ~v1_xboole_0(X1) | ~v1_relat_1(X0))),
% 0.68/0.59    inference(flattening,[],[f9])).
% 0.68/0.59  fof(f9,plain,(
% 0.68/0.59    ! [X0,X1] : ((v1_relat_1(k8_relat_1(X1,X0)) & v1_xboole_0(k8_relat_1(X1,X0))) | (~v1_xboole_0(X1) | ~v1_relat_1(X0)))),
% 0.68/0.59    inference(ennf_transformation,[],[f4])).
% 0.68/0.59  fof(f4,axiom,(
% 0.68/0.59    ! [X0,X1] : ((v1_xboole_0(X1) & v1_relat_1(X0)) => (v1_relat_1(k8_relat_1(X1,X0)) & v1_xboole_0(k8_relat_1(X1,X0))))),
% 0.68/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc18_relat_1)).
% 0.68/0.59  fof(f29,plain,(
% 0.68/0.59    v1_xboole_0(k1_xboole_0) | ~spl1_2),
% 0.68/0.59    inference(avatar_component_clause,[],[f27])).
% 0.68/0.59  fof(f27,plain,(
% 0.68/0.59    spl1_2 <=> v1_xboole_0(k1_xboole_0)),
% 0.68/0.59    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.68/0.59  fof(f24,plain,(
% 0.68/0.59    v1_relat_1(sK0) | ~spl1_1),
% 0.68/0.59    inference(avatar_component_clause,[],[f22])).
% 0.68/0.59  fof(f22,plain,(
% 0.68/0.59    spl1_1 <=> v1_relat_1(sK0)),
% 0.68/0.59    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.68/0.59  fof(f35,plain,(
% 0.68/0.59    ~spl1_3),
% 0.68/0.59    inference(avatar_split_clause,[],[f14,f32])).
% 0.68/0.59  fof(f14,plain,(
% 0.68/0.59    k1_xboole_0 != k8_relat_1(k1_xboole_0,sK0)),
% 0.68/0.59    inference(cnf_transformation,[],[f12])).
% 0.68/0.59  fof(f12,plain,(
% 0.68/0.59    k1_xboole_0 != k8_relat_1(k1_xboole_0,sK0) & v1_relat_1(sK0)),
% 0.68/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f11])).
% 0.68/0.59  fof(f11,plain,(
% 0.68/0.59    ? [X0] : (k1_xboole_0 != k8_relat_1(k1_xboole_0,X0) & v1_relat_1(X0)) => (k1_xboole_0 != k8_relat_1(k1_xboole_0,sK0) & v1_relat_1(sK0))),
% 0.68/0.59    introduced(choice_axiom,[])).
% 0.68/0.59  fof(f7,plain,(
% 0.68/0.59    ? [X0] : (k1_xboole_0 != k8_relat_1(k1_xboole_0,X0) & v1_relat_1(X0))),
% 0.68/0.59    inference(ennf_transformation,[],[f6])).
% 0.68/0.59  fof(f6,negated_conjecture,(
% 0.68/0.59    ~! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k8_relat_1(k1_xboole_0,X0))),
% 0.68/0.59    inference(negated_conjecture,[],[f5])).
% 0.68/0.59  fof(f5,conjecture,(
% 0.68/0.59    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k8_relat_1(k1_xboole_0,X0))),
% 0.68/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_relat_1)).
% 0.68/0.59  fof(f30,plain,(
% 0.68/0.59    spl1_2),
% 0.68/0.59    inference(avatar_split_clause,[],[f20,f27])).
% 0.68/0.59  fof(f20,plain,(
% 0.68/0.59    v1_xboole_0(k1_xboole_0)),
% 0.68/0.59    inference(definition_unfolding,[],[f15,f16])).
% 0.68/0.59  fof(f16,plain,(
% 0.68/0.59    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 0.68/0.59    inference(cnf_transformation,[],[f2])).
% 0.68/0.59  fof(f2,axiom,(
% 0.68/0.59    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 0.68/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).
% 0.68/0.59  fof(f15,plain,(
% 0.68/0.59    ( ! [X0] : (v1_xboole_0(k1_subset_1(X0))) )),
% 0.68/0.59    inference(cnf_transformation,[],[f3])).
% 0.68/0.59  fof(f3,axiom,(
% 0.68/0.59    ! [X0] : v1_xboole_0(k1_subset_1(X0))),
% 0.68/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc13_subset_1)).
% 0.68/0.59  fof(f25,plain,(
% 0.68/0.59    spl1_1),
% 0.68/0.59    inference(avatar_split_clause,[],[f13,f22])).
% 0.68/0.59  fof(f13,plain,(
% 0.68/0.59    v1_relat_1(sK0)),
% 0.68/0.59    inference(cnf_transformation,[],[f12])).
% 0.68/0.59  % SZS output end Proof for theBenchmark
% 0.68/0.59  % (4824)------------------------------
% 0.68/0.59  % (4824)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.68/0.59  % (4824)Termination reason: Refutation
% 0.68/0.59  
% 0.68/0.59  % (4824)Memory used [KB]: 10618
% 0.68/0.59  % (4824)Time elapsed: 0.025 s
% 0.68/0.59  % (4824)------------------------------
% 0.68/0.59  % (4824)------------------------------
% 0.68/0.60  % (4653)Success in time 0.232 s
%------------------------------------------------------------------------------
