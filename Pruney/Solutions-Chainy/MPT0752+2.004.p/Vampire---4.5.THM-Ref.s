%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:43 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   45 (  59 expanded)
%              Number of leaves         :   12 (  20 expanded)
%              Depth                    :    6
%              Number of atoms          :   95 ( 113 expanded)
%              Number of equality atoms :    2 (   6 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (10266)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
fof(f53,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f44,f46,f49,f52])).

fof(f52,plain,(
    spl1_4 ),
    inference(avatar_contradiction_clause,[],[f51])).

fof(f51,plain,
    ( $false
    | spl1_4 ),
    inference(resolution,[],[f50,f24])).

fof(f24,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(definition_unfolding,[],[f18,f19])).

fof(f19,plain,(
    ! [X0] : k1_subset_1(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k1_subset_1(X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(f18,plain,(
    ! [X0] : v1_xboole_0(k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : v1_xboole_0(k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc13_subset_1)).

fof(f50,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl1_4 ),
    inference(resolution,[],[f40,f22])).

fof(f22,plain,(
    ! [X0] :
      ( v5_ordinal1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( v5_ordinal1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v5_ordinal1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_ordinal1)).

fof(f40,plain,
    ( ~ v5_ordinal1(k1_xboole_0)
    | spl1_4 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl1_4
  <=> v5_ordinal1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f49,plain,(
    spl1_3 ),
    inference(avatar_contradiction_clause,[],[f48])).

fof(f48,plain,
    ( $false
    | spl1_3 ),
    inference(resolution,[],[f47,f24])).

fof(f47,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl1_3 ),
    inference(resolution,[],[f36,f21])).

fof(f21,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).

fof(f36,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | spl1_3 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl1_3
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f46,plain,(
    spl1_2 ),
    inference(avatar_contradiction_clause,[],[f45])).

fof(f45,plain,
    ( $false
    | spl1_2 ),
    inference(resolution,[],[f32,f23])).

fof(f23,plain,(
    ! [X1] : v5_relat_1(k1_xboole_0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X1] : v5_relat_1(k1_xboole_0,X1) ),
    inference(rectify,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] : v5_relat_1(k1_xboole_0,X1) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v5_relat_1(k1_xboole_0,X1)
      & v4_relat_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t206_relat_1)).

fof(f32,plain,
    ( ~ v5_relat_1(k1_xboole_0,sK0)
    | spl1_2 ),
    inference(avatar_component_clause,[],[f30])).

fof(f30,plain,
    ( spl1_2
  <=> v5_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f44,plain,(
    spl1_1 ),
    inference(avatar_contradiction_clause,[],[f43])).

fof(f43,plain,
    ( $false
    | spl1_1 ),
    inference(resolution,[],[f42,f24])).

fof(f42,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl1_1 ),
    inference(resolution,[],[f28,f20])).

fof(f20,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f28,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl1_1 ),
    inference(avatar_component_clause,[],[f26])).

fof(f26,plain,
    ( spl1_1
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f41,plain,
    ( ~ spl1_1
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_4 ),
    inference(avatar_split_clause,[],[f17,f38,f34,f30,f26])).

fof(f17,plain,
    ( ~ v5_ordinal1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v5_relat_1(k1_xboole_0,sK0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ~ v5_ordinal1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v5_relat_1(k1_xboole_0,sK0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f14])).

fof(f14,plain,
    ( ? [X0] :
        ( ~ v5_ordinal1(k1_xboole_0)
        | ~ v1_funct_1(k1_xboole_0)
        | ~ v5_relat_1(k1_xboole_0,X0)
        | ~ v1_relat_1(k1_xboole_0) )
   => ( ~ v5_ordinal1(k1_xboole_0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v5_relat_1(k1_xboole_0,sK0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_ordinal1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:27:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (10267)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.46  % (10261)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.46  % (10262)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.46  % (10261)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  % (10266)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.46  fof(f53,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(avatar_sat_refutation,[],[f41,f44,f46,f49,f52])).
% 0.20/0.46  fof(f52,plain,(
% 0.20/0.46    spl1_4),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f51])).
% 0.20/0.46  fof(f51,plain,(
% 0.20/0.46    $false | spl1_4),
% 0.20/0.46    inference(resolution,[],[f50,f24])).
% 0.20/0.46  fof(f24,plain,(
% 0.20/0.46    v1_xboole_0(k1_xboole_0)),
% 0.20/0.46    inference(definition_unfolding,[],[f18,f19])).
% 0.20/0.46  fof(f19,plain,(
% 0.20/0.46    ( ! [X0] : (k1_subset_1(X0) = k1_xboole_0) )),
% 0.20/0.46    inference(cnf_transformation,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    ! [X0] : k1_subset_1(X0) = k1_xboole_0),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).
% 0.20/0.46  fof(f18,plain,(
% 0.20/0.46    ( ! [X0] : (v1_xboole_0(k1_subset_1(X0))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f2])).
% 0.20/0.46  fof(f2,axiom,(
% 0.20/0.46    ! [X0] : v1_xboole_0(k1_subset_1(X0))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc13_subset_1)).
% 0.20/0.46  fof(f50,plain,(
% 0.20/0.46    ~v1_xboole_0(k1_xboole_0) | spl1_4),
% 0.20/0.46    inference(resolution,[],[f40,f22])).
% 0.20/0.46  fof(f22,plain,(
% 0.20/0.46    ( ! [X0] : (v5_ordinal1(X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f13])).
% 0.20/0.46  fof(f13,plain,(
% 0.20/0.46    ! [X0] : (v5_ordinal1(X0) | ~v1_xboole_0(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f6])).
% 0.20/0.46  fof(f6,axiom,(
% 0.20/0.46    ! [X0] : (v1_xboole_0(X0) => v5_ordinal1(X0))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_ordinal1)).
% 0.20/0.46  fof(f40,plain,(
% 0.20/0.46    ~v5_ordinal1(k1_xboole_0) | spl1_4),
% 0.20/0.46    inference(avatar_component_clause,[],[f38])).
% 0.20/0.46  fof(f38,plain,(
% 0.20/0.46    spl1_4 <=> v5_ordinal1(k1_xboole_0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.20/0.46  fof(f49,plain,(
% 0.20/0.46    spl1_3),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f48])).
% 0.20/0.46  fof(f48,plain,(
% 0.20/0.46    $false | spl1_3),
% 0.20/0.46    inference(resolution,[],[f47,f24])).
% 0.20/0.46  fof(f47,plain,(
% 0.20/0.46    ~v1_xboole_0(k1_xboole_0) | spl1_3),
% 0.20/0.46    inference(resolution,[],[f36,f21])).
% 0.20/0.46  fof(f21,plain,(
% 0.20/0.46    ( ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f12])).
% 0.20/0.46  fof(f12,plain,(
% 0.20/0.46    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f5])).
% 0.20/0.46  fof(f5,axiom,(
% 0.20/0.46    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).
% 0.20/0.46  fof(f36,plain,(
% 0.20/0.46    ~v1_funct_1(k1_xboole_0) | spl1_3),
% 0.20/0.46    inference(avatar_component_clause,[],[f34])).
% 0.20/0.46  fof(f34,plain,(
% 0.20/0.46    spl1_3 <=> v1_funct_1(k1_xboole_0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.20/0.46  fof(f46,plain,(
% 0.20/0.46    spl1_2),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f45])).
% 0.20/0.46  fof(f45,plain,(
% 0.20/0.46    $false | spl1_2),
% 0.20/0.46    inference(resolution,[],[f32,f23])).
% 0.20/0.46  fof(f23,plain,(
% 0.20/0.46    ( ! [X1] : (v5_relat_1(k1_xboole_0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f16])).
% 0.20/0.46  fof(f16,plain,(
% 0.20/0.46    ! [X1] : v5_relat_1(k1_xboole_0,X1)),
% 0.20/0.46    inference(rectify,[],[f9])).
% 0.20/0.47  fof(f9,plain,(
% 0.20/0.47    ! [X0,X1] : v5_relat_1(k1_xboole_0,X1)),
% 0.20/0.47    inference(pure_predicate_removal,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0,X1] : (v5_relat_1(k1_xboole_0,X1) & v4_relat_1(k1_xboole_0,X0))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t206_relat_1)).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    ~v5_relat_1(k1_xboole_0,sK0) | spl1_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f30])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    spl1_2 <=> v5_relat_1(k1_xboole_0,sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.20/0.47  fof(f44,plain,(
% 0.20/0.47    spl1_1),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f43])).
% 0.20/0.47  fof(f43,plain,(
% 0.20/0.47    $false | spl1_1),
% 0.20/0.47    inference(resolution,[],[f42,f24])).
% 0.20/0.47  fof(f42,plain,(
% 0.20/0.47    ~v1_xboole_0(k1_xboole_0) | spl1_1),
% 0.20/0.47    inference(resolution,[],[f28,f20])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f11])).
% 0.20/0.47  fof(f11,plain,(
% 0.20/0.47    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ~v1_relat_1(k1_xboole_0) | spl1_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f26])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    spl1_1 <=> v1_relat_1(k1_xboole_0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.20/0.47  fof(f41,plain,(
% 0.20/0.47    ~spl1_1 | ~spl1_2 | ~spl1_3 | ~spl1_4),
% 0.20/0.47    inference(avatar_split_clause,[],[f17,f38,f34,f30,f26])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ~v5_ordinal1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v5_relat_1(k1_xboole_0,sK0) | ~v1_relat_1(k1_xboole_0)),
% 0.20/0.47    inference(cnf_transformation,[],[f15])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ~v5_ordinal1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v5_relat_1(k1_xboole_0,sK0) | ~v1_relat_1(k1_xboole_0)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ? [X0] : (~v5_ordinal1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v5_relat_1(k1_xboole_0,X0) | ~v1_relat_1(k1_xboole_0)) => (~v5_ordinal1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v5_relat_1(k1_xboole_0,sK0) | ~v1_relat_1(k1_xboole_0))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f10,plain,(
% 0.20/0.47    ? [X0] : (~v5_ordinal1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v5_relat_1(k1_xboole_0,X0) | ~v1_relat_1(k1_xboole_0))),
% 0.20/0.47    inference(ennf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,negated_conjecture,(
% 0.20/0.47    ~! [X0] : (v5_ordinal1(k1_xboole_0) & v1_funct_1(k1_xboole_0) & v5_relat_1(k1_xboole_0,X0) & v1_relat_1(k1_xboole_0))),
% 0.20/0.47    inference(negated_conjecture,[],[f7])).
% 0.20/0.47  fof(f7,conjecture,(
% 0.20/0.47    ! [X0] : (v5_ordinal1(k1_xboole_0) & v1_funct_1(k1_xboole_0) & v5_relat_1(k1_xboole_0,X0) & v1_relat_1(k1_xboole_0))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_ordinal1)).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (10261)------------------------------
% 0.20/0.47  % (10261)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (10261)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (10261)Memory used [KB]: 6012
% 0.20/0.47  % (10261)Time elapsed: 0.051 s
% 0.20/0.47  % (10261)------------------------------
% 0.20/0.47  % (10261)------------------------------
% 0.20/0.47  % (10268)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.47  % (10258)Success in time 0.111 s
%------------------------------------------------------------------------------
