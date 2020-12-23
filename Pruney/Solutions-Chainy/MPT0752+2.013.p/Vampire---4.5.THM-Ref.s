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
% DateTime   : Thu Dec  3 12:55:44 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   38 (  45 expanded)
%              Number of leaves         :   10 (  16 expanded)
%              Depth                    :    6
%              Number of atoms          :   71 (  83 expanded)
%              Number of equality atoms :    2 (   4 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f46,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f34,f39,f41,f43,f45])).

fof(f45,plain,(
    spl1_4 ),
    inference(avatar_contradiction_clause,[],[f44])).

fof(f44,plain,
    ( $false
    | spl1_4 ),
    inference(subsumption_resolution,[],[f33,f36])).

fof(f36,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f14,f13])).

fof(f13,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

fof(f14,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

% (2278)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
fof(f4,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f33,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl1_4 ),
    inference(avatar_component_clause,[],[f31])).

fof(f31,plain,
    ( spl1_4
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f43,plain,(
    spl1_3 ),
    inference(avatar_contradiction_clause,[],[f42])).

fof(f42,plain,
    ( $false
    | spl1_3 ),
    inference(subsumption_resolution,[],[f29,f17])).

fof(f17,plain,(
    ! [X1] : v5_relat_1(k1_xboole_0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] : v5_relat_1(k1_xboole_0,X1) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v5_relat_1(k1_xboole_0,X1)
      & v4_relat_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l222_relat_1)).

fof(f29,plain,
    ( ~ v5_relat_1(k1_xboole_0,sK0)
    | spl1_3 ),
    inference(avatar_component_clause,[],[f27])).

fof(f27,plain,
    ( spl1_3
  <=> v5_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f41,plain,(
    spl1_2 ),
    inference(avatar_contradiction_clause,[],[f40])).

fof(f40,plain,
    ( $false
    | spl1_2 ),
    inference(subsumption_resolution,[],[f25,f35])).

fof(f35,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[],[f15,f13])).

fof(f15,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f25,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | spl1_2 ),
    inference(avatar_component_clause,[],[f23])).

fof(f23,plain,
    ( spl1_2
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f39,plain,(
    spl1_1 ),
    inference(avatar_contradiction_clause,[],[f38])).

fof(f38,plain,
    ( $false
    | spl1_1 ),
    inference(subsumption_resolution,[],[f37,f12])).

fof(f12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f37,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl1_1 ),
    inference(resolution,[],[f16,f21])).

fof(f21,plain,
    ( ~ v5_ordinal1(k1_xboole_0)
    | spl1_1 ),
    inference(avatar_component_clause,[],[f19])).

fof(f19,plain,
    ( spl1_1
  <=> v5_ordinal1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f16,plain,(
    ! [X0] :
      ( v5_ordinal1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( v5_ordinal1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v5_ordinal1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_ordinal1)).

fof(f34,plain,
    ( ~ spl1_1
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_4 ),
    inference(avatar_split_clause,[],[f11,f31,f27,f23,f19])).

fof(f11,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v5_relat_1(k1_xboole_0,sK0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v5_ordinal1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ~ v5_ordinal1(k1_xboole_0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v5_relat_1(k1_xboole_0,X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( v5_ordinal1(k1_xboole_0)
        & v1_funct_1(k1_xboole_0)
        & v5_relat_1(k1_xboole_0,X0)
        & v1_relat_1(k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( v5_ordinal1(k1_xboole_0)
      & v1_funct_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,X0)
      & v1_relat_1(k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_ordinal1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:40:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.41  % (2283)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.21/0.42  % (2275)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.21/0.42  % (2285)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.21/0.42  % (2275)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f46,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(avatar_sat_refutation,[],[f34,f39,f41,f43,f45])).
% 0.21/0.42  fof(f45,plain,(
% 0.21/0.42    spl1_4),
% 0.21/0.42    inference(avatar_contradiction_clause,[],[f44])).
% 0.21/0.42  fof(f44,plain,(
% 0.21/0.42    $false | spl1_4),
% 0.21/0.42    inference(subsumption_resolution,[],[f33,f36])).
% 0.21/0.42  fof(f36,plain,(
% 0.21/0.42    v1_relat_1(k1_xboole_0)),
% 0.21/0.42    inference(superposition,[],[f14,f13])).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.21/0.42    inference(cnf_transformation,[],[f3])).
% 0.21/0.42  fof(f3,axiom,(
% 0.21/0.42    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f4])).
% 0.21/0.43  % (2278)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.21/0.43  fof(f4,axiom,(
% 0.21/0.43    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.21/0.43  fof(f33,plain,(
% 0.21/0.43    ~v1_relat_1(k1_xboole_0) | spl1_4),
% 0.21/0.43    inference(avatar_component_clause,[],[f31])).
% 0.21/0.43  fof(f31,plain,(
% 0.21/0.43    spl1_4 <=> v1_relat_1(k1_xboole_0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.21/0.43  fof(f43,plain,(
% 0.21/0.43    spl1_3),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f42])).
% 0.21/0.43  fof(f42,plain,(
% 0.21/0.43    $false | spl1_3),
% 0.21/0.43    inference(subsumption_resolution,[],[f29,f17])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    ( ! [X1] : (v5_relat_1(k1_xboole_0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f8])).
% 0.21/0.43  fof(f8,plain,(
% 0.21/0.43    ! [X0,X1] : v5_relat_1(k1_xboole_0,X1)),
% 0.21/0.43    inference(pure_predicate_removal,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0,X1] : (v5_relat_1(k1_xboole_0,X1) & v4_relat_1(k1_xboole_0,X0))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l222_relat_1)).
% 0.21/0.43  fof(f29,plain,(
% 0.21/0.43    ~v5_relat_1(k1_xboole_0,sK0) | spl1_3),
% 0.21/0.43    inference(avatar_component_clause,[],[f27])).
% 0.21/0.43  fof(f27,plain,(
% 0.21/0.43    spl1_3 <=> v5_relat_1(k1_xboole_0,sK0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.21/0.43  fof(f41,plain,(
% 0.21/0.43    spl1_2),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f40])).
% 0.21/0.43  fof(f40,plain,(
% 0.21/0.43    $false | spl1_2),
% 0.21/0.43    inference(subsumption_resolution,[],[f25,f35])).
% 0.21/0.43  fof(f35,plain,(
% 0.21/0.43    v1_funct_1(k1_xboole_0)),
% 0.21/0.43    inference(superposition,[],[f15,f13])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f4])).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    ~v1_funct_1(k1_xboole_0) | spl1_2),
% 0.21/0.43    inference(avatar_component_clause,[],[f23])).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    spl1_2 <=> v1_funct_1(k1_xboole_0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.21/0.43  fof(f39,plain,(
% 0.21/0.43    spl1_1),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f38])).
% 0.21/0.43  fof(f38,plain,(
% 0.21/0.43    $false | spl1_1),
% 0.21/0.43    inference(subsumption_resolution,[],[f37,f12])).
% 0.21/0.43  fof(f12,plain,(
% 0.21/0.43    v1_xboole_0(k1_xboole_0)),
% 0.21/0.43    inference(cnf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    v1_xboole_0(k1_xboole_0)),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.43  fof(f37,plain,(
% 0.21/0.43    ~v1_xboole_0(k1_xboole_0) | spl1_1),
% 0.21/0.43    inference(resolution,[],[f16,f21])).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    ~v5_ordinal1(k1_xboole_0) | spl1_1),
% 0.21/0.43    inference(avatar_component_clause,[],[f19])).
% 0.21/0.43  fof(f19,plain,(
% 0.21/0.43    spl1_1 <=> v5_ordinal1(k1_xboole_0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    ( ! [X0] : (v5_ordinal1(X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f10])).
% 0.21/0.43  fof(f10,plain,(
% 0.21/0.43    ! [X0] : (v5_ordinal1(X0) | ~v1_xboole_0(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f5])).
% 0.21/0.43  fof(f5,axiom,(
% 0.21/0.43    ! [X0] : (v1_xboole_0(X0) => v5_ordinal1(X0))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_ordinal1)).
% 0.21/0.43  fof(f34,plain,(
% 0.21/0.43    ~spl1_1 | ~spl1_2 | ~spl1_3 | ~spl1_4),
% 0.21/0.43    inference(avatar_split_clause,[],[f11,f31,f27,f23,f19])).
% 0.21/0.43  fof(f11,plain,(
% 0.21/0.43    ~v1_relat_1(k1_xboole_0) | ~v5_relat_1(k1_xboole_0,sK0) | ~v1_funct_1(k1_xboole_0) | ~v5_ordinal1(k1_xboole_0)),
% 0.21/0.43    inference(cnf_transformation,[],[f9])).
% 0.21/0.43  fof(f9,plain,(
% 0.21/0.43    ? [X0] : (~v5_ordinal1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v5_relat_1(k1_xboole_0,X0) | ~v1_relat_1(k1_xboole_0))),
% 0.21/0.43    inference(ennf_transformation,[],[f7])).
% 0.21/0.43  fof(f7,negated_conjecture,(
% 0.21/0.43    ~! [X0] : (v5_ordinal1(k1_xboole_0) & v1_funct_1(k1_xboole_0) & v5_relat_1(k1_xboole_0,X0) & v1_relat_1(k1_xboole_0))),
% 0.21/0.43    inference(negated_conjecture,[],[f6])).
% 0.21/0.43  fof(f6,conjecture,(
% 0.21/0.43    ! [X0] : (v5_ordinal1(k1_xboole_0) & v1_funct_1(k1_xboole_0) & v5_relat_1(k1_xboole_0,X0) & v1_relat_1(k1_xboole_0))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_ordinal1)).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (2275)------------------------------
% 0.21/0.43  % (2275)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (2275)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (2275)Memory used [KB]: 10490
% 0.21/0.43  % (2275)Time elapsed: 0.005 s
% 0.21/0.43  % (2275)------------------------------
% 0.21/0.43  % (2275)------------------------------
% 0.21/0.43  % (2274)Success in time 0.072 s
%------------------------------------------------------------------------------
