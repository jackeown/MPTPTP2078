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
% DateTime   : Thu Dec  3 12:49:17 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   43 (  53 expanded)
%              Number of leaves         :   12 (  22 expanded)
%              Depth                    :    6
%              Number of atoms          :   81 ( 101 expanded)
%              Number of equality atoms :   17 (  21 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f63,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f23,f28,f33,f41,f47,f53,f57])).

fof(f57,plain,
    ( spl1_1
    | ~ spl1_6 ),
    inference(avatar_contradiction_clause,[],[f56])).

fof(f56,plain,
    ( $false
    | spl1_1
    | ~ spl1_6 ),
    inference(trivial_inequality_removal,[],[f54])).

fof(f54,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl1_1
    | ~ spl1_6 ),
    inference(superposition,[],[f22,f52])).

fof(f52,plain,
    ( ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl1_6
  <=> ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f22,plain,
    ( k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0)
    | spl1_1 ),
    inference(avatar_component_clause,[],[f20])).

fof(f20,plain,
    ( spl1_1
  <=> k1_xboole_0 = k8_relat_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f53,plain,
    ( spl1_6
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f49,f45,f51])).

fof(f45,plain,
    ( spl1_5
  <=> ! [X0] : r1_tarski(k8_relat_1(X0,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f49,plain,
    ( ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)
    | ~ spl1_5 ),
    inference(resolution,[],[f46,f17])).

fof(f17,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f46,plain,
    ( ! [X0] : r1_tarski(k8_relat_1(X0,k1_xboole_0),k1_xboole_0)
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f45])).

fof(f47,plain,
    ( spl1_5
    | ~ spl1_4 ),
    inference(avatar_split_clause,[],[f43,f38,f45])).

fof(f38,plain,
    ( spl1_4
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f43,plain,
    ( ! [X0] : r1_tarski(k8_relat_1(X0,k1_xboole_0),k1_xboole_0)
    | ~ spl1_4 ),
    inference(resolution,[],[f40,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k8_relat_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k8_relat_1(X0,X1),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).

fof(f40,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f38])).

fof(f41,plain,
    ( spl1_4
    | ~ spl1_2
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f36,f30,f25,f38])).

fof(f25,plain,
    ( spl1_2
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f30,plain,
    ( spl1_3
  <=> k1_xboole_0 = k4_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f36,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl1_2
    | ~ spl1_3 ),
    inference(subsumption_resolution,[],[f35,f27])).

fof(f27,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f25])).

fof(f35,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ spl1_3 ),
    inference(superposition,[],[f16,f32])).

fof(f32,plain,
    ( k1_xboole_0 = k4_relat_1(k1_xboole_0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f30])).

fof(f16,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ( v1_relat_1(k4_relat_1(X0))
        & v1_xboole_0(k4_relat_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ( v1_relat_1(k4_relat_1(X0))
        & v1_xboole_0(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_relat_1)).

fof(f33,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f14,f30])).

fof(f14,plain,(
    k1_xboole_0 = k4_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    k1_xboole_0 = k4_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_relat_1)).

fof(f28,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f13,f25])).

fof(f13,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f23,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f12,f20])).

fof(f12,plain,(
    k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] : k1_xboole_0 != k8_relat_1(X0,k1_xboole_0) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:46:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.42  % (26048)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.22/0.42  % (26042)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.22/0.42  % (26042)Refutation found. Thanks to Tanya!
% 0.22/0.42  % SZS status Theorem for theBenchmark
% 0.22/0.42  % SZS output start Proof for theBenchmark
% 0.22/0.42  fof(f63,plain,(
% 0.22/0.42    $false),
% 0.22/0.42    inference(avatar_sat_refutation,[],[f23,f28,f33,f41,f47,f53,f57])).
% 0.22/0.42  fof(f57,plain,(
% 0.22/0.42    spl1_1 | ~spl1_6),
% 0.22/0.42    inference(avatar_contradiction_clause,[],[f56])).
% 0.22/0.42  fof(f56,plain,(
% 0.22/0.42    $false | (spl1_1 | ~spl1_6)),
% 0.22/0.42    inference(trivial_inequality_removal,[],[f54])).
% 0.22/0.42  fof(f54,plain,(
% 0.22/0.42    k1_xboole_0 != k1_xboole_0 | (spl1_1 | ~spl1_6)),
% 0.22/0.42    inference(superposition,[],[f22,f52])).
% 0.22/0.42  fof(f52,plain,(
% 0.22/0.42    ( ! [X0] : (k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)) ) | ~spl1_6),
% 0.22/0.42    inference(avatar_component_clause,[],[f51])).
% 0.22/0.42  fof(f51,plain,(
% 0.22/0.42    spl1_6 <=> ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.22/0.42  fof(f22,plain,(
% 0.22/0.42    k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0) | spl1_1),
% 0.22/0.42    inference(avatar_component_clause,[],[f20])).
% 0.22/0.42  fof(f20,plain,(
% 0.22/0.42    spl1_1 <=> k1_xboole_0 = k8_relat_1(sK0,k1_xboole_0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.22/0.42  fof(f53,plain,(
% 0.22/0.42    spl1_6 | ~spl1_5),
% 0.22/0.42    inference(avatar_split_clause,[],[f49,f45,f51])).
% 0.22/0.42  fof(f45,plain,(
% 0.22/0.42    spl1_5 <=> ! [X0] : r1_tarski(k8_relat_1(X0,k1_xboole_0),k1_xboole_0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.22/0.42  fof(f49,plain,(
% 0.22/0.42    ( ! [X0] : (k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)) ) | ~spl1_5),
% 0.22/0.42    inference(resolution,[],[f46,f17])).
% 0.22/0.42  fof(f17,plain,(
% 0.22/0.42    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.22/0.42    inference(cnf_transformation,[],[f10])).
% 0.22/0.42  fof(f10,plain,(
% 0.22/0.42    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.22/0.42    inference(ennf_transformation,[],[f2])).
% 0.22/0.42  fof(f2,axiom,(
% 0.22/0.42    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.22/0.42  fof(f46,plain,(
% 0.22/0.42    ( ! [X0] : (r1_tarski(k8_relat_1(X0,k1_xboole_0),k1_xboole_0)) ) | ~spl1_5),
% 0.22/0.42    inference(avatar_component_clause,[],[f45])).
% 0.22/0.42  fof(f47,plain,(
% 0.22/0.42    spl1_5 | ~spl1_4),
% 0.22/0.42    inference(avatar_split_clause,[],[f43,f38,f45])).
% 0.22/0.42  fof(f38,plain,(
% 0.22/0.42    spl1_4 <=> v1_relat_1(k1_xboole_0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.22/0.42  fof(f43,plain,(
% 0.22/0.42    ( ! [X0] : (r1_tarski(k8_relat_1(X0,k1_xboole_0),k1_xboole_0)) ) | ~spl1_4),
% 0.22/0.42    inference(resolution,[],[f40,f18])).
% 0.22/0.42  fof(f18,plain,(
% 0.22/0.42    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k8_relat_1(X0,X1),X1)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f11])).
% 0.22/0.42  fof(f11,plain,(
% 0.22/0.42    ! [X0,X1] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1))),
% 0.22/0.42    inference(ennf_transformation,[],[f4])).
% 0.22/0.42  fof(f4,axiom,(
% 0.22/0.42    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k8_relat_1(X0,X1),X1))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).
% 0.22/0.42  fof(f40,plain,(
% 0.22/0.42    v1_relat_1(k1_xboole_0) | ~spl1_4),
% 0.22/0.42    inference(avatar_component_clause,[],[f38])).
% 0.22/0.42  fof(f41,plain,(
% 0.22/0.42    spl1_4 | ~spl1_2 | ~spl1_3),
% 0.22/0.42    inference(avatar_split_clause,[],[f36,f30,f25,f38])).
% 0.22/0.42  fof(f25,plain,(
% 0.22/0.42    spl1_2 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.22/0.42  fof(f30,plain,(
% 0.22/0.42    spl1_3 <=> k1_xboole_0 = k4_relat_1(k1_xboole_0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.22/0.42  fof(f36,plain,(
% 0.22/0.42    v1_relat_1(k1_xboole_0) | (~spl1_2 | ~spl1_3)),
% 0.22/0.42    inference(subsumption_resolution,[],[f35,f27])).
% 0.22/0.42  fof(f27,plain,(
% 0.22/0.42    v1_xboole_0(k1_xboole_0) | ~spl1_2),
% 0.22/0.42    inference(avatar_component_clause,[],[f25])).
% 0.22/0.42  fof(f35,plain,(
% 0.22/0.42    v1_relat_1(k1_xboole_0) | ~v1_xboole_0(k1_xboole_0) | ~spl1_3),
% 0.22/0.42    inference(superposition,[],[f16,f32])).
% 0.22/0.42  fof(f32,plain,(
% 0.22/0.42    k1_xboole_0 = k4_relat_1(k1_xboole_0) | ~spl1_3),
% 0.22/0.42    inference(avatar_component_clause,[],[f30])).
% 0.22/0.42  fof(f16,plain,(
% 0.22/0.42    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_xboole_0(X0)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f9])).
% 0.22/0.42  fof(f9,plain,(
% 0.22/0.42    ! [X0] : ((v1_relat_1(k4_relat_1(X0)) & v1_xboole_0(k4_relat_1(X0))) | ~v1_xboole_0(X0))),
% 0.22/0.42    inference(ennf_transformation,[],[f3])).
% 0.22/0.42  fof(f3,axiom,(
% 0.22/0.42    ! [X0] : (v1_xboole_0(X0) => (v1_relat_1(k4_relat_1(X0)) & v1_xboole_0(k4_relat_1(X0))))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_relat_1)).
% 0.22/0.42  fof(f33,plain,(
% 0.22/0.42    spl1_3),
% 0.22/0.42    inference(avatar_split_clause,[],[f14,f30])).
% 0.22/0.42  fof(f14,plain,(
% 0.22/0.42    k1_xboole_0 = k4_relat_1(k1_xboole_0)),
% 0.22/0.42    inference(cnf_transformation,[],[f5])).
% 0.22/0.42  fof(f5,axiom,(
% 0.22/0.42    k1_xboole_0 = k4_relat_1(k1_xboole_0)),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_relat_1)).
% 0.22/0.42  fof(f28,plain,(
% 0.22/0.42    spl1_2),
% 0.22/0.42    inference(avatar_split_clause,[],[f13,f25])).
% 0.22/0.42  fof(f13,plain,(
% 0.22/0.42    v1_xboole_0(k1_xboole_0)),
% 0.22/0.42    inference(cnf_transformation,[],[f1])).
% 0.22/0.42  fof(f1,axiom,(
% 0.22/0.42    v1_xboole_0(k1_xboole_0)),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.42  fof(f23,plain,(
% 0.22/0.42    ~spl1_1),
% 0.22/0.42    inference(avatar_split_clause,[],[f12,f20])).
% 0.22/0.42  fof(f12,plain,(
% 0.22/0.42    k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0)),
% 0.22/0.42    inference(cnf_transformation,[],[f8])).
% 0.22/0.42  fof(f8,plain,(
% 0.22/0.42    ? [X0] : k1_xboole_0 != k8_relat_1(X0,k1_xboole_0)),
% 0.22/0.42    inference(ennf_transformation,[],[f7])).
% 0.22/0.42  fof(f7,negated_conjecture,(
% 0.22/0.42    ~! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)),
% 0.22/0.42    inference(negated_conjecture,[],[f6])).
% 0.22/0.42  fof(f6,conjecture,(
% 0.22/0.42    ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_relat_1)).
% 0.22/0.42  % SZS output end Proof for theBenchmark
% 0.22/0.42  % (26042)------------------------------
% 0.22/0.42  % (26042)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.42  % (26042)Termination reason: Refutation
% 0.22/0.42  
% 0.22/0.42  % (26042)Memory used [KB]: 10490
% 0.22/0.42  % (26042)Time elapsed: 0.006 s
% 0.22/0.42  % (26042)------------------------------
% 0.22/0.42  % (26042)------------------------------
% 0.22/0.43  % (26040)Success in time 0.066 s
%------------------------------------------------------------------------------
