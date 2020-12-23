%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:44 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   45 (  56 expanded)
%              Number of leaves         :   12 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :   84 ( 102 expanded)
%              Number of equality atoms :    6 (   8 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f51,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f33,f40,f44,f46,f48,f50])).

fof(f50,plain,(
    spl2_4 ),
    inference(avatar_contradiction_clause,[],[f49])).

fof(f49,plain,
    ( $false
    | spl2_4 ),
    inference(subsumption_resolution,[],[f32,f35])).

fof(f35,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f14,f13])).

fof(f13,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

fof(f14,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f32,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl2_4 ),
    inference(avatar_component_clause,[],[f31])).

fof(f31,plain,
    ( spl2_4
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f48,plain,(
    spl2_3 ),
    inference(avatar_contradiction_clause,[],[f47])).

fof(f47,plain,
    ( $false
    | spl2_3 ),
    inference(subsumption_resolution,[],[f29,f19])).

fof(f19,plain,(
    ! [X1] : v5_relat_1(k1_xboole_0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v5_relat_1(k1_xboole_0,X1)
      & v4_relat_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l222_relat_1)).

fof(f29,plain,
    ( ~ v5_relat_1(k1_xboole_0,sK0)
    | spl2_3 ),
    inference(avatar_component_clause,[],[f28])).

fof(f28,plain,
    ( spl2_3
  <=> v5_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f46,plain,(
    spl2_2 ),
    inference(avatar_contradiction_clause,[],[f45])).

fof(f45,plain,
    ( $false
    | spl2_2 ),
    inference(subsumption_resolution,[],[f26,f34])).

fof(f34,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[],[f15,f13])).

fof(f15,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f26,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f25])).

fof(f25,plain,
    ( spl2_2
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f44,plain,(
    spl2_5 ),
    inference(avatar_contradiction_clause,[],[f43])).

fof(f43,plain,
    ( $false
    | spl2_5 ),
    inference(subsumption_resolution,[],[f42,f39])).

fof(f39,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl2_5 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl2_5
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f42,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[],[f20,f41])).

fof(f41,plain,(
    k1_xboole_0 = sK1 ),
    inference(resolution,[],[f17,f20])).

fof(f17,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f20,plain,(
    v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ? [X0] : v1_xboole_0(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

fof(f40,plain,
    ( ~ spl2_5
    | spl2_1 ),
    inference(avatar_split_clause,[],[f36,f22,f38])).

fof(f22,plain,
    ( spl2_1
  <=> v5_ordinal1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f36,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl2_1 ),
    inference(resolution,[],[f16,f23])).

fof(f23,plain,
    ( ~ v5_ordinal1(k1_xboole_0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f22])).

fof(f16,plain,(
    ! [X0] :
      ( v5_ordinal1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( v5_ordinal1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

% (9767)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v5_ordinal1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_ordinal1)).

fof(f33,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f12,f31,f28,f25,f22])).

fof(f12,plain,
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
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( v5_ordinal1(k1_xboole_0)
        & v1_funct_1(k1_xboole_0)
        & v5_relat_1(k1_xboole_0,X0)
        & v1_relat_1(k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( v5_ordinal1(k1_xboole_0)
      & v1_funct_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,X0)
      & v1_relat_1(k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_ordinal1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:50:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.41  % (9763)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.13/0.41  % (9765)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.21/0.43  % (9766)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.21/0.43  % (9764)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.21/0.44  % (9762)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.44  % (9760)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.21/0.44  % (9760)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f51,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(avatar_sat_refutation,[],[f33,f40,f44,f46,f48,f50])).
% 0.21/0.44  fof(f50,plain,(
% 0.21/0.44    spl2_4),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f49])).
% 0.21/0.44  fof(f49,plain,(
% 0.21/0.44    $false | spl2_4),
% 0.21/0.44    inference(subsumption_resolution,[],[f32,f35])).
% 0.21/0.44  fof(f35,plain,(
% 0.21/0.44    v1_relat_1(k1_xboole_0)),
% 0.21/0.44    inference(superposition,[],[f14,f13])).
% 0.21/0.44  fof(f13,plain,(
% 0.21/0.44    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.21/0.44    inference(cnf_transformation,[],[f4])).
% 0.21/0.44  fof(f4,axiom,(
% 0.21/0.44    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).
% 0.21/0.44  fof(f14,plain,(
% 0.21/0.44    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f5])).
% 0.21/0.44  fof(f5,axiom,(
% 0.21/0.44    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.21/0.44  fof(f32,plain,(
% 0.21/0.44    ~v1_relat_1(k1_xboole_0) | spl2_4),
% 0.21/0.44    inference(avatar_component_clause,[],[f31])).
% 0.21/0.44  fof(f31,plain,(
% 0.21/0.44    spl2_4 <=> v1_relat_1(k1_xboole_0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.44  fof(f48,plain,(
% 0.21/0.44    spl2_3),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f47])).
% 0.21/0.44  fof(f47,plain,(
% 0.21/0.44    $false | spl2_3),
% 0.21/0.44    inference(subsumption_resolution,[],[f29,f19])).
% 0.21/0.44  fof(f19,plain,(
% 0.21/0.44    ( ! [X1] : (v5_relat_1(k1_xboole_0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0,X1] : (v5_relat_1(k1_xboole_0,X1) & v4_relat_1(k1_xboole_0,X0))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l222_relat_1)).
% 0.21/0.44  fof(f29,plain,(
% 0.21/0.44    ~v5_relat_1(k1_xboole_0,sK0) | spl2_3),
% 0.21/0.44    inference(avatar_component_clause,[],[f28])).
% 0.21/0.44  fof(f28,plain,(
% 0.21/0.44    spl2_3 <=> v5_relat_1(k1_xboole_0,sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.44  fof(f46,plain,(
% 0.21/0.44    spl2_2),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f45])).
% 0.21/0.44  fof(f45,plain,(
% 0.21/0.44    $false | spl2_2),
% 0.21/0.44    inference(subsumption_resolution,[],[f26,f34])).
% 0.21/0.44  fof(f34,plain,(
% 0.21/0.44    v1_funct_1(k1_xboole_0)),
% 0.21/0.44    inference(superposition,[],[f15,f13])).
% 0.21/0.44  fof(f15,plain,(
% 0.21/0.44    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f5])).
% 0.21/0.44  fof(f26,plain,(
% 0.21/0.44    ~v1_funct_1(k1_xboole_0) | spl2_2),
% 0.21/0.44    inference(avatar_component_clause,[],[f25])).
% 0.21/0.44  fof(f25,plain,(
% 0.21/0.44    spl2_2 <=> v1_funct_1(k1_xboole_0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.44  fof(f44,plain,(
% 0.21/0.44    spl2_5),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f43])).
% 0.21/0.44  fof(f43,plain,(
% 0.21/0.44    $false | spl2_5),
% 0.21/0.44    inference(subsumption_resolution,[],[f42,f39])).
% 0.21/0.44  fof(f39,plain,(
% 0.21/0.44    ~v1_xboole_0(k1_xboole_0) | spl2_5),
% 0.21/0.44    inference(avatar_component_clause,[],[f38])).
% 0.21/0.44  fof(f38,plain,(
% 0.21/0.44    spl2_5 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.44  fof(f42,plain,(
% 0.21/0.44    v1_xboole_0(k1_xboole_0)),
% 0.21/0.44    inference(superposition,[],[f20,f41])).
% 0.21/0.44  fof(f41,plain,(
% 0.21/0.44    k1_xboole_0 = sK1),
% 0.21/0.44    inference(resolution,[],[f17,f20])).
% 0.21/0.44  fof(f17,plain,(
% 0.21/0.44    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.44    inference(cnf_transformation,[],[f11])).
% 0.21/0.44  fof(f11,plain,(
% 0.21/0.44    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    v1_xboole_0(sK1)),
% 0.21/0.44    inference(cnf_transformation,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ? [X0] : v1_xboole_0(X0)),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).
% 0.21/0.44  fof(f40,plain,(
% 0.21/0.44    ~spl2_5 | spl2_1),
% 0.21/0.44    inference(avatar_split_clause,[],[f36,f22,f38])).
% 0.21/0.44  fof(f22,plain,(
% 0.21/0.44    spl2_1 <=> v5_ordinal1(k1_xboole_0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.44  fof(f36,plain,(
% 0.21/0.44    ~v1_xboole_0(k1_xboole_0) | spl2_1),
% 0.21/0.44    inference(resolution,[],[f16,f23])).
% 0.21/0.44  fof(f23,plain,(
% 0.21/0.44    ~v5_ordinal1(k1_xboole_0) | spl2_1),
% 0.21/0.44    inference(avatar_component_clause,[],[f22])).
% 0.21/0.44  fof(f16,plain,(
% 0.21/0.44    ( ! [X0] : (v5_ordinal1(X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f10])).
% 0.21/0.44  fof(f10,plain,(
% 0.21/0.44    ! [X0] : (v5_ordinal1(X0) | ~v1_xboole_0(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f6])).
% 0.21/0.44  % (9767)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.21/0.44  fof(f6,axiom,(
% 0.21/0.44    ! [X0] : (v1_xboole_0(X0) => v5_ordinal1(X0))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_ordinal1)).
% 0.21/0.44  fof(f33,plain,(
% 0.21/0.44    ~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4),
% 0.21/0.44    inference(avatar_split_clause,[],[f12,f31,f28,f25,f22])).
% 0.21/0.44  fof(f12,plain,(
% 0.21/0.44    ~v1_relat_1(k1_xboole_0) | ~v5_relat_1(k1_xboole_0,sK0) | ~v1_funct_1(k1_xboole_0) | ~v5_ordinal1(k1_xboole_0)),
% 0.21/0.44    inference(cnf_transformation,[],[f9])).
% 0.21/0.44  fof(f9,plain,(
% 0.21/0.44    ? [X0] : (~v5_ordinal1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v5_relat_1(k1_xboole_0,X0) | ~v1_relat_1(k1_xboole_0))),
% 0.21/0.44    inference(ennf_transformation,[],[f8])).
% 0.21/0.44  fof(f8,negated_conjecture,(
% 0.21/0.44    ~! [X0] : (v5_ordinal1(k1_xboole_0) & v1_funct_1(k1_xboole_0) & v5_relat_1(k1_xboole_0,X0) & v1_relat_1(k1_xboole_0))),
% 0.21/0.44    inference(negated_conjecture,[],[f7])).
% 0.21/0.44  fof(f7,conjecture,(
% 0.21/0.44    ! [X0] : (v5_ordinal1(k1_xboole_0) & v1_funct_1(k1_xboole_0) & v5_relat_1(k1_xboole_0,X0) & v1_relat_1(k1_xboole_0))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_ordinal1)).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (9760)------------------------------
% 0.21/0.44  % (9760)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (9760)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (9760)Memory used [KB]: 10490
% 0.21/0.44  % (9760)Time elapsed: 0.034 s
% 0.21/0.44  % (9760)------------------------------
% 0.21/0.44  % (9760)------------------------------
% 0.21/0.45  % (9756)Success in time 0.089 s
%------------------------------------------------------------------------------
