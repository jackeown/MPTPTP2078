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
% DateTime   : Thu Dec  3 12:55:43 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   54 (  65 expanded)
%              Number of leaves         :   15 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :  131 ( 156 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f69,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f30,f38,f42,f46,f59,f62,f65,f68])).

fof(f68,plain,
    ( ~ spl1_1
    | ~ spl1_5
    | spl1_8 ),
    inference(avatar_contradiction_clause,[],[f67])).

fof(f67,plain,
    ( $false
    | ~ spl1_1
    | ~ spl1_5
    | spl1_8 ),
    inference(subsumption_resolution,[],[f66,f29])).

fof(f29,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl1_1 ),
    inference(avatar_component_clause,[],[f27])).

fof(f27,plain,
    ( spl1_1
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f66,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl1_5
    | spl1_8 ),
    inference(resolution,[],[f58,f45])).

fof(f45,plain,
    ( ! [X0] :
        ( v5_ordinal1(X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl1_5
  <=> ! [X0] :
        ( v5_ordinal1(X0)
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f58,plain,
    ( ~ v5_ordinal1(k1_xboole_0)
    | spl1_8 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl1_8
  <=> v5_ordinal1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f65,plain,
    ( ~ spl1_1
    | ~ spl1_4
    | spl1_7 ),
    inference(avatar_contradiction_clause,[],[f64])).

fof(f64,plain,
    ( $false
    | ~ spl1_1
    | ~ spl1_4
    | spl1_7 ),
    inference(subsumption_resolution,[],[f63,f29])).

fof(f63,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl1_4
    | spl1_7 ),
    inference(resolution,[],[f54,f41])).

fof(f41,plain,
    ( ! [X0] :
        ( v1_funct_1(X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl1_4
  <=> ! [X0] :
        ( v1_funct_1(X0)
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f54,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | spl1_7 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl1_7
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f62,plain,
    ( ~ spl1_1
    | ~ spl1_3
    | spl1_6 ),
    inference(avatar_contradiction_clause,[],[f61])).

fof(f61,plain,
    ( $false
    | ~ spl1_1
    | ~ spl1_3
    | spl1_6 ),
    inference(subsumption_resolution,[],[f60,f29])).

fof(f60,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl1_3
    | spl1_6 ),
    inference(resolution,[],[f50,f37])).

fof(f37,plain,
    ( ! [X0] :
        ( v1_relat_1(X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl1_3
  <=> ! [X0] :
        ( v1_relat_1(X0)
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f50,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl1_6 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl1_6
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f59,plain,
    ( ~ spl1_6
    | ~ spl1_7
    | ~ spl1_8 ),
    inference(avatar_split_clause,[],[f25,f56,f52,f48])).

fof(f25,plain,
    ( ~ v5_ordinal1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f17,f23])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l222_relat_1)).

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

fof(f46,plain,(
    spl1_5 ),
    inference(avatar_split_clause,[],[f22,f44])).

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

fof(f42,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f21,f40])).

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

fof(f38,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f20,f36])).

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

fof(f30,plain,(
    spl1_1 ),
    inference(avatar_split_clause,[],[f24,f27])).

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
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:26:14 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.40  % (31423)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.19/0.40  % (31423)Refutation found. Thanks to Tanya!
% 0.19/0.40  % SZS status Theorem for theBenchmark
% 0.19/0.40  % SZS output start Proof for theBenchmark
% 0.19/0.40  fof(f69,plain,(
% 0.19/0.40    $false),
% 0.19/0.40    inference(avatar_sat_refutation,[],[f30,f38,f42,f46,f59,f62,f65,f68])).
% 0.19/0.40  fof(f68,plain,(
% 0.19/0.40    ~spl1_1 | ~spl1_5 | spl1_8),
% 0.19/0.40    inference(avatar_contradiction_clause,[],[f67])).
% 0.19/0.40  fof(f67,plain,(
% 0.19/0.40    $false | (~spl1_1 | ~spl1_5 | spl1_8)),
% 0.19/0.40    inference(subsumption_resolution,[],[f66,f29])).
% 0.19/0.40  fof(f29,plain,(
% 0.19/0.40    v1_xboole_0(k1_xboole_0) | ~spl1_1),
% 0.19/0.40    inference(avatar_component_clause,[],[f27])).
% 0.19/0.40  fof(f27,plain,(
% 0.19/0.40    spl1_1 <=> v1_xboole_0(k1_xboole_0)),
% 0.19/0.40    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.19/0.40  fof(f66,plain,(
% 0.19/0.40    ~v1_xboole_0(k1_xboole_0) | (~spl1_5 | spl1_8)),
% 0.19/0.40    inference(resolution,[],[f58,f45])).
% 0.19/0.40  fof(f45,plain,(
% 0.19/0.40    ( ! [X0] : (v5_ordinal1(X0) | ~v1_xboole_0(X0)) ) | ~spl1_5),
% 0.19/0.40    inference(avatar_component_clause,[],[f44])).
% 0.19/0.40  fof(f44,plain,(
% 0.19/0.40    spl1_5 <=> ! [X0] : (v5_ordinal1(X0) | ~v1_xboole_0(X0))),
% 0.19/0.40    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.19/0.40  fof(f58,plain,(
% 0.19/0.40    ~v5_ordinal1(k1_xboole_0) | spl1_8),
% 0.19/0.40    inference(avatar_component_clause,[],[f56])).
% 0.19/0.40  fof(f56,plain,(
% 0.19/0.40    spl1_8 <=> v5_ordinal1(k1_xboole_0)),
% 0.19/0.40    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.19/0.40  fof(f65,plain,(
% 0.19/0.40    ~spl1_1 | ~spl1_4 | spl1_7),
% 0.19/0.40    inference(avatar_contradiction_clause,[],[f64])).
% 0.19/0.40  fof(f64,plain,(
% 0.19/0.40    $false | (~spl1_1 | ~spl1_4 | spl1_7)),
% 0.19/0.40    inference(subsumption_resolution,[],[f63,f29])).
% 0.19/0.40  fof(f63,plain,(
% 0.19/0.40    ~v1_xboole_0(k1_xboole_0) | (~spl1_4 | spl1_7)),
% 0.19/0.40    inference(resolution,[],[f54,f41])).
% 0.19/0.40  fof(f41,plain,(
% 0.19/0.40    ( ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0)) ) | ~spl1_4),
% 0.19/0.40    inference(avatar_component_clause,[],[f40])).
% 0.19/0.40  fof(f40,plain,(
% 0.19/0.40    spl1_4 <=> ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 0.19/0.40    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.19/0.40  fof(f54,plain,(
% 0.19/0.40    ~v1_funct_1(k1_xboole_0) | spl1_7),
% 0.19/0.40    inference(avatar_component_clause,[],[f52])).
% 0.19/0.40  fof(f52,plain,(
% 0.19/0.40    spl1_7 <=> v1_funct_1(k1_xboole_0)),
% 0.19/0.40    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.19/0.40  fof(f62,plain,(
% 0.19/0.40    ~spl1_1 | ~spl1_3 | spl1_6),
% 0.19/0.40    inference(avatar_contradiction_clause,[],[f61])).
% 0.19/0.40  fof(f61,plain,(
% 0.19/0.40    $false | (~spl1_1 | ~spl1_3 | spl1_6)),
% 0.19/0.40    inference(subsumption_resolution,[],[f60,f29])).
% 0.19/0.40  fof(f60,plain,(
% 0.19/0.40    ~v1_xboole_0(k1_xboole_0) | (~spl1_3 | spl1_6)),
% 0.19/0.40    inference(resolution,[],[f50,f37])).
% 0.19/0.40  fof(f37,plain,(
% 0.19/0.40    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) ) | ~spl1_3),
% 0.19/0.40    inference(avatar_component_clause,[],[f36])).
% 0.19/0.40  fof(f36,plain,(
% 0.19/0.40    spl1_3 <=> ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.19/0.40    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.19/0.40  fof(f50,plain,(
% 0.19/0.40    ~v1_relat_1(k1_xboole_0) | spl1_6),
% 0.19/0.40    inference(avatar_component_clause,[],[f48])).
% 0.19/0.40  fof(f48,plain,(
% 0.19/0.40    spl1_6 <=> v1_relat_1(k1_xboole_0)),
% 0.19/0.40    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.19/0.40  fof(f59,plain,(
% 0.19/0.40    ~spl1_6 | ~spl1_7 | ~spl1_8),
% 0.19/0.40    inference(avatar_split_clause,[],[f25,f56,f52,f48])).
% 0.19/0.40  fof(f25,plain,(
% 0.19/0.40    ~v5_ordinal1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 0.19/0.40    inference(subsumption_resolution,[],[f17,f23])).
% 0.19/0.40  fof(f23,plain,(
% 0.19/0.40    ( ! [X1] : (v5_relat_1(k1_xboole_0,X1)) )),
% 0.19/0.40    inference(cnf_transformation,[],[f16])).
% 0.19/0.40  fof(f16,plain,(
% 0.19/0.40    ! [X1] : v5_relat_1(k1_xboole_0,X1)),
% 0.19/0.40    inference(rectify,[],[f9])).
% 0.19/0.40  fof(f9,plain,(
% 0.19/0.40    ! [X0,X1] : v5_relat_1(k1_xboole_0,X1)),
% 0.19/0.40    inference(pure_predicate_removal,[],[f4])).
% 0.19/0.40  fof(f4,axiom,(
% 0.19/0.40    ! [X0,X1] : (v5_relat_1(k1_xboole_0,X1) & v4_relat_1(k1_xboole_0,X0))),
% 0.19/0.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l222_relat_1)).
% 0.19/0.40  fof(f17,plain,(
% 0.19/0.40    ~v5_ordinal1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v5_relat_1(k1_xboole_0,sK0) | ~v1_relat_1(k1_xboole_0)),
% 0.19/0.40    inference(cnf_transformation,[],[f15])).
% 0.19/0.40  fof(f15,plain,(
% 0.19/0.40    ~v5_ordinal1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v5_relat_1(k1_xboole_0,sK0) | ~v1_relat_1(k1_xboole_0)),
% 0.19/0.40    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f14])).
% 0.19/0.40  fof(f14,plain,(
% 0.19/0.40    ? [X0] : (~v5_ordinal1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v5_relat_1(k1_xboole_0,X0) | ~v1_relat_1(k1_xboole_0)) => (~v5_ordinal1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v5_relat_1(k1_xboole_0,sK0) | ~v1_relat_1(k1_xboole_0))),
% 0.19/0.40    introduced(choice_axiom,[])).
% 0.19/0.40  fof(f10,plain,(
% 0.19/0.40    ? [X0] : (~v5_ordinal1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v5_relat_1(k1_xboole_0,X0) | ~v1_relat_1(k1_xboole_0))),
% 0.19/0.40    inference(ennf_transformation,[],[f8])).
% 0.19/0.40  fof(f8,negated_conjecture,(
% 0.19/0.40    ~! [X0] : (v5_ordinal1(k1_xboole_0) & v1_funct_1(k1_xboole_0) & v5_relat_1(k1_xboole_0,X0) & v1_relat_1(k1_xboole_0))),
% 0.19/0.40    inference(negated_conjecture,[],[f7])).
% 0.19/0.40  fof(f7,conjecture,(
% 0.19/0.40    ! [X0] : (v5_ordinal1(k1_xboole_0) & v1_funct_1(k1_xboole_0) & v5_relat_1(k1_xboole_0,X0) & v1_relat_1(k1_xboole_0))),
% 0.19/0.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_ordinal1)).
% 0.19/0.40  fof(f46,plain,(
% 0.19/0.40    spl1_5),
% 0.19/0.40    inference(avatar_split_clause,[],[f22,f44])).
% 0.19/0.41  fof(f22,plain,(
% 0.19/0.41    ( ! [X0] : (v5_ordinal1(X0) | ~v1_xboole_0(X0)) )),
% 0.19/0.41    inference(cnf_transformation,[],[f13])).
% 0.19/0.41  fof(f13,plain,(
% 0.19/0.41    ! [X0] : (v5_ordinal1(X0) | ~v1_xboole_0(X0))),
% 0.19/0.41    inference(ennf_transformation,[],[f6])).
% 0.19/0.41  fof(f6,axiom,(
% 0.19/0.41    ! [X0] : (v1_xboole_0(X0) => v5_ordinal1(X0))),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_ordinal1)).
% 0.19/0.41  fof(f42,plain,(
% 0.19/0.41    spl1_4),
% 0.19/0.41    inference(avatar_split_clause,[],[f21,f40])).
% 0.19/0.41  fof(f21,plain,(
% 0.19/0.41    ( ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0)) )),
% 0.19/0.41    inference(cnf_transformation,[],[f12])).
% 0.19/0.41  fof(f12,plain,(
% 0.19/0.41    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 0.19/0.41    inference(ennf_transformation,[],[f5])).
% 0.19/0.41  fof(f5,axiom,(
% 0.19/0.41    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).
% 0.19/0.41  fof(f38,plain,(
% 0.19/0.41    spl1_3),
% 0.19/0.41    inference(avatar_split_clause,[],[f20,f36])).
% 0.19/0.41  fof(f20,plain,(
% 0.19/0.41    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.19/0.41    inference(cnf_transformation,[],[f11])).
% 0.19/0.41  fof(f11,plain,(
% 0.19/0.41    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.19/0.41    inference(ennf_transformation,[],[f3])).
% 0.19/0.41  fof(f3,axiom,(
% 0.19/0.41    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.19/0.41  fof(f30,plain,(
% 0.19/0.41    spl1_1),
% 0.19/0.41    inference(avatar_split_clause,[],[f24,f27])).
% 0.19/0.41  fof(f24,plain,(
% 0.19/0.41    v1_xboole_0(k1_xboole_0)),
% 0.19/0.41    inference(definition_unfolding,[],[f18,f19])).
% 0.19/0.41  fof(f19,plain,(
% 0.19/0.41    ( ! [X0] : (k1_subset_1(X0) = k1_xboole_0) )),
% 0.19/0.41    inference(cnf_transformation,[],[f1])).
% 0.19/0.41  fof(f1,axiom,(
% 0.19/0.41    ! [X0] : k1_subset_1(X0) = k1_xboole_0),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).
% 0.19/0.41  fof(f18,plain,(
% 0.19/0.41    ( ! [X0] : (v1_xboole_0(k1_subset_1(X0))) )),
% 0.19/0.41    inference(cnf_transformation,[],[f2])).
% 0.19/0.41  fof(f2,axiom,(
% 0.19/0.41    ! [X0] : v1_xboole_0(k1_subset_1(X0))),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc13_subset_1)).
% 0.19/0.41  % SZS output end Proof for theBenchmark
% 0.19/0.41  % (31423)------------------------------
% 0.19/0.41  % (31423)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.41  % (31423)Termination reason: Refutation
% 0.19/0.41  
% 0.19/0.41  % (31423)Memory used [KB]: 6012
% 0.19/0.41  % (31423)Time elapsed: 0.004 s
% 0.19/0.41  % (31423)------------------------------
% 0.19/0.41  % (31423)------------------------------
% 0.19/0.41  % (31415)Success in time 0.057 s
%------------------------------------------------------------------------------
