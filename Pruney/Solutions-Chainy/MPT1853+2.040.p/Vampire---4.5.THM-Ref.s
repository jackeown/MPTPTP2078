%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:47 EST 2020

% Result     : Theorem 1.57s
% Output     : Refutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 637 expanded)
%              Number of leaves         :   25 ( 180 expanded)
%              Depth                    :   17
%              Number of atoms          :  492 (3404 expanded)
%              Number of equality atoms :   14 (  20 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f571,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f138,f139,f177,f239,f337,f340,f343,f357,f414,f420,f500,f503,f514,f570])).

fof(f570,plain,
    ( spl7_16
    | ~ spl7_17
    | ~ spl7_23 ),
    inference(avatar_contradiction_clause,[],[f569])).

fof(f569,plain,
    ( $false
    | spl7_16
    | ~ spl7_17
    | ~ spl7_23 ),
    inference(subsumption_resolution,[],[f568,f308])).

fof(f308,plain,
    ( ~ v2_struct_0(k1_tex_2(sK0,sK1))
    | spl7_16 ),
    inference(avatar_component_clause,[],[f307])).

fof(f307,plain,
    ( spl7_16
  <=> v2_struct_0(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f568,plain,
    ( v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl7_17
    | ~ spl7_23 ),
    inference(subsumption_resolution,[],[f567,f312])).

fof(f312,plain,
    ( l1_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f311])).

fof(f311,plain,
    ( spl7_17
  <=> l1_struct_0(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f567,plain,
    ( ~ l1_struct_0(k1_tex_2(sK0,sK1))
    | v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl7_23 ),
    inference(resolution,[],[f356,f98])).

fof(f98,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f356,plain,
    ( v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))
    | ~ spl7_23 ),
    inference(avatar_component_clause,[],[f354])).

fof(f354,plain,
    ( spl7_23
  <=> v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f514,plain,(
    ~ spl7_16 ),
    inference(avatar_contradiction_clause,[],[f513])).

fof(f513,plain,
    ( $false
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f512,f80])).

fof(f80,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,
    ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
      | ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0) )
    & ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
      | v1_tex_2(k1_tex_2(sK0,sK1),sK0) )
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f56,f58,f57])).

fof(f57,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
              | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
            & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
              | v1_tex_2(k1_tex_2(X0,X1),X0) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0))
            | ~ v1_tex_2(k1_tex_2(sK0,X1),sK0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0))
            | v1_tex_2(k1_tex_2(sK0,X1),sK0) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,
    ( ? [X1] :
        ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0))
          | ~ v1_tex_2(k1_tex_2(sK0,X1),sK0) )
        & ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0))
          | v1_tex_2(k1_tex_2(sK0,X1),sK0) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
        | ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0) )
      & ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
        | v1_tex_2(k1_tex_2(sK0,sK1),sK0) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f55])).

% (3137)Refutation not found, incomplete strategy% (3137)------------------------------
% (3137)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (3137)Termination reason: Refutation not found, incomplete strategy

fof(f55,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f27])).

% (3137)Memory used [KB]: 10618
% (3137)Time elapsed: 0.154 s
% (3137)------------------------------
% (3137)------------------------------
fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( v1_tex_2(k1_tex_2(X0,X1),X0)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_tex_2)).

fof(f512,plain,
    ( v2_struct_0(sK0)
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f511,f81])).

fof(f81,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f59])).

fof(f511,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f505,f82])).

fof(f82,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f59])).

fof(f505,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_16 ),
    inference(resolution,[],[f309,f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).

fof(f309,plain,
    ( v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f307])).

fof(f503,plain,
    ( spl7_16
    | spl7_19
    | ~ spl7_17
    | ~ spl7_18
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f502,f334,f315,f311,f319,f307])).

fof(f319,plain,
    ( spl7_19
  <=> ! [X0] :
        ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f315,plain,
    ( spl7_18
  <=> v7_struct_0(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f334,plain,
    ( spl7_22
  <=> u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f502,plain,
    ( ! [X0] :
        ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(k1_tex_2(sK0,sK1)) )
    | ~ spl7_17
    | ~ spl7_18
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f501,f312])).

fof(f501,plain,
    ( ! [X0] :
        ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_struct_0(k1_tex_2(sK0,sK1))
        | v2_struct_0(k1_tex_2(sK0,sK1)) )
    | ~ spl7_18
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f422,f316])).

fof(f316,plain,
    ( v7_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f315])).

fof(f422,plain,
    ( ! [X0] :
        ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),u1_struct_0(sK0))
        | ~ v7_struct_0(k1_tex_2(sK0,sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_struct_0(k1_tex_2(sK0,sK1))
        | v2_struct_0(k1_tex_2(sK0,sK1)) )
    | ~ spl7_22 ),
    inference(superposition,[],[f99,f336])).

fof(f336,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f334])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
      | ~ v7_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v7_struct_0(X0)
          | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v7_struct_0(X0)
          | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ~ ( v7_struct_0(X0)
              & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_tex_2)).

fof(f500,plain,
    ( ~ spl7_2
    | ~ spl7_19 ),
    inference(avatar_contradiction_clause,[],[f499])).

fof(f499,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_19 ),
    inference(subsumption_resolution,[],[f498,f82])).

fof(f498,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl7_2
    | ~ spl7_19 ),
    inference(resolution,[],[f320,f136])).

fof(f136,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl7_2
  <=> v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f320,plain,
    ( ! [X0] :
        ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f319])).

fof(f420,plain,(
    spl7_18 ),
    inference(avatar_contradiction_clause,[],[f419])).

fof(f419,plain,
    ( $false
    | spl7_18 ),
    inference(subsumption_resolution,[],[f418,f80])).

fof(f418,plain,
    ( v2_struct_0(sK0)
    | spl7_18 ),
    inference(subsumption_resolution,[],[f417,f81])).

fof(f417,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl7_18 ),
    inference(subsumption_resolution,[],[f416,f82])).

fof(f416,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl7_18 ),
    inference(resolution,[],[f317,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( v7_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f317,plain,
    ( ~ v7_struct_0(k1_tex_2(sK0,sK1))
    | spl7_18 ),
    inference(avatar_component_clause,[],[f315])).

fof(f414,plain,(
    spl7_17 ),
    inference(avatar_contradiction_clause,[],[f413])).

fof(f413,plain,
    ( $false
    | spl7_17 ),
    inference(subsumption_resolution,[],[f412,f149])).

fof(f149,plain,(
    l1_pre_topc(k1_tex_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f147,f81])).

fof(f147,plain,
    ( l1_pre_topc(k1_tex_2(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f145,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f145,plain,(
    m1_pre_topc(k1_tex_2(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f144,f80])).

fof(f144,plain,
    ( m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f142,f81])).

fof(f142,plain,
    ( m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f82,f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).

fof(f412,plain,
    ( ~ l1_pre_topc(k1_tex_2(sK0,sK1))
    | spl7_17 ),
    inference(resolution,[],[f313,f89])).

fof(f89,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f313,plain,
    ( ~ l1_struct_0(k1_tex_2(sK0,sK1))
    | spl7_17 ),
    inference(avatar_component_clause,[],[f311])).

fof(f357,plain,
    ( ~ spl7_21
    | spl7_23
    | spl7_2
    | spl7_5 ),
    inference(avatar_split_clause,[],[f352,f167,f135,f354,f330])).

fof(f330,plain,
    ( spl7_21
  <=> v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f167,plain,
    ( spl7_5
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f352,plain,
    ( v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))
    | ~ v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | spl7_2
    | spl7_5 ),
    inference(subsumption_resolution,[],[f351,f168])).

fof(f168,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl7_5 ),
    inference(avatar_component_clause,[],[f167])).

fof(f351,plain,
    ( v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))
    | ~ v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | spl7_2
    | spl7_5 ),
    inference(subsumption_resolution,[],[f265,f349])).

fof(f349,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | spl7_2
    | spl7_5 ),
    inference(subsumption_resolution,[],[f348,f168])).

fof(f348,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | spl7_2 ),
    inference(subsumption_resolution,[],[f143,f137])).

fof(f137,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | spl7_2 ),
    inference(avatar_component_clause,[],[f135])).

fof(f143,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | v1_zfmisc_1(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f82,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_subset_1(k6_domain_1(X0,X1),X0)
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( ( ~ v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tex_2)).

fof(f265,plain,
    ( v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))
    | ~ v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ v1_zfmisc_1(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f148,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | ~ v1_subset_1(X1,X0)
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( ~ v1_xboole_0(X1)
           => ~ v1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).

fof(f148,plain,(
    m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f146,f81])).

fof(f146,plain,
    ( m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f145,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f343,plain,
    ( spl7_1
    | ~ spl7_21 ),
    inference(avatar_split_clause,[],[f342,f330,f131])).

fof(f131,plain,
    ( spl7_1
  <=> v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f342,plain,
    ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f341,f81])).

fof(f341,plain,
    ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f261,f145])).

fof(f261,plain,
    ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f148,f123])).

fof(f123,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
      | v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( v1_tex_2(X1,X0)
      | ~ v1_subset_1(X2,u1_struct_0(X0))
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v1_subset_1(X2,u1_struct_0(X0))
                  | ~ v1_tex_2(X1,X0) )
                & ( v1_tex_2(X1,X0)
                  | ~ v1_subset_1(X2,u1_struct_0(X0)) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v1_subset_1(X2,u1_struct_0(X0))
              <=> v1_tex_2(X1,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v1_subset_1(X2,u1_struct_0(X0))
              <=> v1_tex_2(X1,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( v1_subset_1(X2,u1_struct_0(X0))
                <=> v1_tex_2(X1,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_tex_2)).

fof(f340,plain,
    ( spl7_21
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f339,f131,f330])).

fof(f339,plain,
    ( ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f338,f81])).

fof(f338,plain,
    ( ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f262,f145])).

fof(f262,plain,
    ( ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f148,f122])).

fof(f122,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tex_2(X1,X0)
      | v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( v1_subset_1(X2,u1_struct_0(X0))
      | ~ v1_tex_2(X1,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f337,plain,
    ( spl7_21
    | spl7_22 ),
    inference(avatar_split_clause,[],[f264,f334,f330])).

fof(f264,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))
    | v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) ),
    inference(resolution,[],[f148,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

fof(f239,plain,
    ( ~ spl7_3
    | ~ spl7_5 ),
    inference(avatar_contradiction_clause,[],[f238])).

fof(f238,plain,
    ( $false
    | ~ spl7_3
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f237,f80])).

fof(f237,plain,
    ( v2_struct_0(sK0)
    | ~ spl7_3
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f236,f158])).

fof(f158,plain,
    ( l1_struct_0(sK0)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl7_3
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f236,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_5 ),
    inference(resolution,[],[f169,f98])).

fof(f169,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f167])).

fof(f177,plain,(
    spl7_3 ),
    inference(avatar_contradiction_clause,[],[f176])).

fof(f176,plain,
    ( $false
    | spl7_3 ),
    inference(subsumption_resolution,[],[f175,f81])).

fof(f175,plain,
    ( ~ l1_pre_topc(sK0)
    | spl7_3 ),
    inference(resolution,[],[f159,f89])).

fof(f159,plain,
    ( ~ l1_struct_0(sK0)
    | spl7_3 ),
    inference(avatar_component_clause,[],[f157])).

fof(f139,plain,
    ( spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f83,f135,f131])).

fof(f83,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f59])).

fof(f138,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f84,f135,f131])).

fof(f84,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f59])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n018.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:30:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.48  % (3126)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.19/0.50  % (3141)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.19/0.51  % (3123)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.19/0.51  % (3133)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.19/0.52  % (3142)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.19/0.52  % (3142)Refutation not found, incomplete strategy% (3142)------------------------------
% 0.19/0.52  % (3142)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (3149)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.19/0.52  % (3145)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.19/0.53  % (3125)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.19/0.53  % (3142)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.53  
% 0.19/0.53  % (3142)Memory used [KB]: 10746
% 0.19/0.53  % (3142)Time elapsed: 0.111 s
% 0.19/0.53  % (3142)------------------------------
% 0.19/0.53  % (3142)------------------------------
% 0.19/0.53  % (3120)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.19/0.53  % (3134)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.19/0.53  % (3124)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.19/0.53  % (3148)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.37/0.53  % (3131)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.37/0.54  % (3131)Refutation not found, incomplete strategy% (3131)------------------------------
% 1.37/0.54  % (3131)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.54  % (3122)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.37/0.54  % (3136)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.37/0.54  % (3121)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.37/0.54  % (3140)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.37/0.54  % (3130)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.37/0.54  % (3130)Refutation not found, incomplete strategy% (3130)------------------------------
% 1.37/0.54  % (3130)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.54  % (3130)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.54  
% 1.37/0.54  % (3130)Memory used [KB]: 10618
% 1.37/0.54  % (3130)Time elapsed: 0.140 s
% 1.37/0.54  % (3130)------------------------------
% 1.37/0.54  % (3130)------------------------------
% 1.37/0.54  % (3128)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.37/0.55  % (3139)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.37/0.55  % (3131)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.55  
% 1.37/0.55  % (3131)Memory used [KB]: 10746
% 1.37/0.55  % (3131)Time elapsed: 0.131 s
% 1.37/0.55  % (3131)------------------------------
% 1.37/0.55  % (3131)------------------------------
% 1.37/0.55  % (3138)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.37/0.55  % (3132)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.57/0.55  % (3135)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.57/0.55  % (3137)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.57/0.55  % (3147)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.57/0.56  % (3128)Refutation found. Thanks to Tanya!
% 1.57/0.56  % SZS status Theorem for theBenchmark
% 1.57/0.56  % SZS output start Proof for theBenchmark
% 1.57/0.56  fof(f571,plain,(
% 1.57/0.56    $false),
% 1.57/0.56    inference(avatar_sat_refutation,[],[f138,f139,f177,f239,f337,f340,f343,f357,f414,f420,f500,f503,f514,f570])).
% 1.57/0.56  fof(f570,plain,(
% 1.57/0.56    spl7_16 | ~spl7_17 | ~spl7_23),
% 1.57/0.56    inference(avatar_contradiction_clause,[],[f569])).
% 1.57/0.56  fof(f569,plain,(
% 1.57/0.56    $false | (spl7_16 | ~spl7_17 | ~spl7_23)),
% 1.57/0.56    inference(subsumption_resolution,[],[f568,f308])).
% 1.57/0.56  fof(f308,plain,(
% 1.57/0.56    ~v2_struct_0(k1_tex_2(sK0,sK1)) | spl7_16),
% 1.57/0.56    inference(avatar_component_clause,[],[f307])).
% 1.57/0.56  fof(f307,plain,(
% 1.57/0.56    spl7_16 <=> v2_struct_0(k1_tex_2(sK0,sK1))),
% 1.57/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 1.57/0.56  fof(f568,plain,(
% 1.57/0.56    v2_struct_0(k1_tex_2(sK0,sK1)) | (~spl7_17 | ~spl7_23)),
% 1.57/0.56    inference(subsumption_resolution,[],[f567,f312])).
% 1.57/0.56  fof(f312,plain,(
% 1.57/0.56    l1_struct_0(k1_tex_2(sK0,sK1)) | ~spl7_17),
% 1.57/0.56    inference(avatar_component_clause,[],[f311])).
% 1.57/0.56  fof(f311,plain,(
% 1.57/0.56    spl7_17 <=> l1_struct_0(k1_tex_2(sK0,sK1))),
% 1.57/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 1.57/0.56  fof(f567,plain,(
% 1.57/0.56    ~l1_struct_0(k1_tex_2(sK0,sK1)) | v2_struct_0(k1_tex_2(sK0,sK1)) | ~spl7_23),
% 1.57/0.56    inference(resolution,[],[f356,f98])).
% 1.57/0.56  fof(f98,plain,(
% 1.57/0.56    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.57/0.56    inference(cnf_transformation,[],[f40])).
% 1.57/0.56  fof(f40,plain,(
% 1.57/0.56    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.57/0.56    inference(flattening,[],[f39])).
% 1.57/0.56  fof(f39,plain,(
% 1.57/0.56    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.57/0.56    inference(ennf_transformation,[],[f10])).
% 1.57/0.56  fof(f10,axiom,(
% 1.57/0.56    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.57/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 1.57/0.56  fof(f356,plain,(
% 1.57/0.56    v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) | ~spl7_23),
% 1.57/0.56    inference(avatar_component_clause,[],[f354])).
% 1.57/0.56  fof(f354,plain,(
% 1.57/0.56    spl7_23 <=> v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))),
% 1.57/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).
% 1.57/0.56  fof(f514,plain,(
% 1.57/0.56    ~spl7_16),
% 1.57/0.56    inference(avatar_contradiction_clause,[],[f513])).
% 1.57/0.56  fof(f513,plain,(
% 1.57/0.56    $false | ~spl7_16),
% 1.57/0.56    inference(subsumption_resolution,[],[f512,f80])).
% 1.57/0.56  fof(f80,plain,(
% 1.57/0.56    ~v2_struct_0(sK0)),
% 1.57/0.56    inference(cnf_transformation,[],[f59])).
% 1.57/0.56  fof(f59,plain,(
% 1.57/0.56    ((~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,sK1),sK0)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0)) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.57/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f56,f58,f57])).
% 1.57/0.56  fof(f57,plain,(
% 1.57/0.56    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,X1),sK0)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,X1),sK0)) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.57/0.56    introduced(choice_axiom,[])).
% 1.57/0.56  fof(f58,plain,(
% 1.57/0.56    ? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,X1),sK0)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,X1),sK0)) & m1_subset_1(X1,u1_struct_0(sK0))) => ((~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,sK1),sK0)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0)) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 1.57/0.56    introduced(choice_axiom,[])).
% 1.57/0.56  fof(f56,plain,(
% 1.57/0.56    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.57/0.56    inference(flattening,[],[f55])).
% 1.57/0.56  % (3137)Refutation not found, incomplete strategy% (3137)------------------------------
% 1.57/0.56  % (3137)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.56  % (3137)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.56  
% 1.57/0.56  fof(f55,plain,(
% 1.57/0.56    ? [X0] : (? [X1] : (((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.57/0.56    inference(nnf_transformation,[],[f27])).
% 1.57/0.56  % (3137)Memory used [KB]: 10618
% 1.57/0.56  % (3137)Time elapsed: 0.154 s
% 1.57/0.56  % (3137)------------------------------
% 1.57/0.56  % (3137)------------------------------
% 1.57/0.56  fof(f27,plain,(
% 1.57/0.56    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.57/0.56    inference(flattening,[],[f26])).
% 1.57/0.56  fof(f26,plain,(
% 1.57/0.56    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.57/0.56    inference(ennf_transformation,[],[f23])).
% 1.57/0.56  fof(f23,negated_conjecture,(
% 1.57/0.56    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 1.57/0.56    inference(negated_conjecture,[],[f22])).
% 1.57/0.56  fof(f22,conjecture,(
% 1.57/0.56    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 1.57/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_tex_2)).
% 1.57/0.56  fof(f512,plain,(
% 1.57/0.56    v2_struct_0(sK0) | ~spl7_16),
% 1.57/0.56    inference(subsumption_resolution,[],[f511,f81])).
% 1.57/0.56  fof(f81,plain,(
% 1.57/0.56    l1_pre_topc(sK0)),
% 1.57/0.56    inference(cnf_transformation,[],[f59])).
% 1.57/0.56  fof(f511,plain,(
% 1.57/0.56    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl7_16),
% 1.57/0.56    inference(subsumption_resolution,[],[f505,f82])).
% 1.57/0.56  fof(f82,plain,(
% 1.57/0.56    m1_subset_1(sK1,u1_struct_0(sK0))),
% 1.57/0.56    inference(cnf_transformation,[],[f59])).
% 1.57/0.56  fof(f505,plain,(
% 1.57/0.56    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl7_16),
% 1.57/0.56    inference(resolution,[],[f309,f107])).
% 1.57/0.56  fof(f107,plain,(
% 1.57/0.56    ( ! [X0,X1] : (~v2_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.57/0.56    inference(cnf_transformation,[],[f51])).
% 1.57/0.56  fof(f51,plain,(
% 1.57/0.56    ! [X0,X1] : ((v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.57/0.56    inference(flattening,[],[f50])).
% 1.57/0.56  fof(f50,plain,(
% 1.57/0.56    ! [X0,X1] : ((v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.57/0.56    inference(ennf_transformation,[],[f25])).
% 1.57/0.56  fof(f25,plain,(
% 1.57/0.56    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 1.57/0.56    inference(pure_predicate_removal,[],[f16])).
% 1.57/0.56  fof(f16,axiom,(
% 1.57/0.56    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 1.57/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).
% 1.57/0.56  fof(f309,plain,(
% 1.57/0.56    v2_struct_0(k1_tex_2(sK0,sK1)) | ~spl7_16),
% 1.57/0.56    inference(avatar_component_clause,[],[f307])).
% 1.57/0.56  fof(f503,plain,(
% 1.57/0.56    spl7_16 | spl7_19 | ~spl7_17 | ~spl7_18 | ~spl7_22),
% 1.57/0.56    inference(avatar_split_clause,[],[f502,f334,f315,f311,f319,f307])).
% 1.57/0.56  fof(f319,plain,(
% 1.57/0.56    spl7_19 <=> ! [X0] : (~v1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)))),
% 1.57/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 1.57/0.56  fof(f315,plain,(
% 1.57/0.56    spl7_18 <=> v7_struct_0(k1_tex_2(sK0,sK1))),
% 1.57/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 1.57/0.56  fof(f334,plain,(
% 1.57/0.56    spl7_22 <=> u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))),
% 1.57/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 1.57/0.56  fof(f502,plain,(
% 1.57/0.56    ( ! [X0] : (~v1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(k1_tex_2(sK0,sK1))) ) | (~spl7_17 | ~spl7_18 | ~spl7_22)),
% 1.57/0.56    inference(subsumption_resolution,[],[f501,f312])).
% 1.57/0.56  fof(f501,plain,(
% 1.57/0.56    ( ! [X0] : (~v1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_struct_0(k1_tex_2(sK0,sK1)) | v2_struct_0(k1_tex_2(sK0,sK1))) ) | (~spl7_18 | ~spl7_22)),
% 1.57/0.56    inference(subsumption_resolution,[],[f422,f316])).
% 1.57/0.56  fof(f316,plain,(
% 1.57/0.56    v7_struct_0(k1_tex_2(sK0,sK1)) | ~spl7_18),
% 1.57/0.56    inference(avatar_component_clause,[],[f315])).
% 1.57/0.56  fof(f422,plain,(
% 1.57/0.56    ( ! [X0] : (~v1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),u1_struct_0(sK0)) | ~v7_struct_0(k1_tex_2(sK0,sK1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_struct_0(k1_tex_2(sK0,sK1)) | v2_struct_0(k1_tex_2(sK0,sK1))) ) | ~spl7_22),
% 1.57/0.56    inference(superposition,[],[f99,f336])).
% 1.57/0.56  fof(f336,plain,(
% 1.57/0.56    u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) | ~spl7_22),
% 1.57/0.56    inference(avatar_component_clause,[],[f334])).
% 1.57/0.56  fof(f99,plain,(
% 1.57/0.56    ( ! [X0,X1] : (~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v7_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.57/0.56    inference(cnf_transformation,[],[f42])).
% 1.57/0.56  fof(f42,plain,(
% 1.57/0.56    ! [X0] : (! [X1] : (~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.57/0.56    inference(flattening,[],[f41])).
% 1.57/0.56  fof(f41,plain,(
% 1.57/0.56    ! [X0] : (! [X1] : ((~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.57/0.56    inference(ennf_transformation,[],[f21])).
% 1.57/0.56  fof(f21,axiom,(
% 1.57/0.56    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~(v7_struct_0(X0) & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 1.57/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_tex_2)).
% 1.57/0.56  fof(f500,plain,(
% 1.57/0.56    ~spl7_2 | ~spl7_19),
% 1.57/0.56    inference(avatar_contradiction_clause,[],[f499])).
% 1.57/0.56  fof(f499,plain,(
% 1.57/0.56    $false | (~spl7_2 | ~spl7_19)),
% 1.57/0.56    inference(subsumption_resolution,[],[f498,f82])).
% 1.57/0.56  fof(f498,plain,(
% 1.57/0.56    ~m1_subset_1(sK1,u1_struct_0(sK0)) | (~spl7_2 | ~spl7_19)),
% 1.57/0.56    inference(resolution,[],[f320,f136])).
% 1.57/0.56  fof(f136,plain,(
% 1.57/0.56    v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~spl7_2),
% 1.57/0.56    inference(avatar_component_clause,[],[f135])).
% 1.57/0.56  fof(f135,plain,(
% 1.57/0.56    spl7_2 <=> v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))),
% 1.57/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.57/0.56  fof(f320,plain,(
% 1.57/0.56    ( ! [X0] : (~v1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl7_19),
% 1.57/0.56    inference(avatar_component_clause,[],[f319])).
% 1.57/0.56  fof(f420,plain,(
% 1.57/0.56    spl7_18),
% 1.57/0.56    inference(avatar_contradiction_clause,[],[f419])).
% 1.57/0.56  fof(f419,plain,(
% 1.57/0.56    $false | spl7_18),
% 1.57/0.56    inference(subsumption_resolution,[],[f418,f80])).
% 1.57/0.56  fof(f418,plain,(
% 1.57/0.56    v2_struct_0(sK0) | spl7_18),
% 1.57/0.56    inference(subsumption_resolution,[],[f417,f81])).
% 1.57/0.56  fof(f417,plain,(
% 1.57/0.56    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | spl7_18),
% 1.57/0.56    inference(subsumption_resolution,[],[f416,f82])).
% 1.57/0.56  fof(f416,plain,(
% 1.57/0.56    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | spl7_18),
% 1.57/0.56    inference(resolution,[],[f317,f108])).
% 1.57/0.56  fof(f108,plain,(
% 1.57/0.56    ( ! [X0,X1] : (v7_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.57/0.56    inference(cnf_transformation,[],[f51])).
% 1.57/0.56  fof(f317,plain,(
% 1.57/0.56    ~v7_struct_0(k1_tex_2(sK0,sK1)) | spl7_18),
% 1.57/0.56    inference(avatar_component_clause,[],[f315])).
% 1.57/0.56  fof(f414,plain,(
% 1.57/0.56    spl7_17),
% 1.57/0.56    inference(avatar_contradiction_clause,[],[f413])).
% 1.57/0.56  fof(f413,plain,(
% 1.57/0.56    $false | spl7_17),
% 1.57/0.56    inference(subsumption_resolution,[],[f412,f149])).
% 1.57/0.56  fof(f149,plain,(
% 1.57/0.56    l1_pre_topc(k1_tex_2(sK0,sK1))),
% 1.57/0.56    inference(subsumption_resolution,[],[f147,f81])).
% 1.57/0.56  fof(f147,plain,(
% 1.57/0.56    l1_pre_topc(k1_tex_2(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 1.57/0.56    inference(resolution,[],[f145,f90])).
% 1.57/0.56  fof(f90,plain,(
% 1.57/0.56    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.57/0.56    inference(cnf_transformation,[],[f32])).
% 1.57/0.56  fof(f32,plain,(
% 1.57/0.56    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.57/0.56    inference(ennf_transformation,[],[f8])).
% 1.57/0.56  fof(f8,axiom,(
% 1.57/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.57/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.57/0.56  fof(f145,plain,(
% 1.57/0.56    m1_pre_topc(k1_tex_2(sK0,sK1),sK0)),
% 1.57/0.56    inference(subsumption_resolution,[],[f144,f80])).
% 1.57/0.56  fof(f144,plain,(
% 1.57/0.56    m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | v2_struct_0(sK0)),
% 1.57/0.56    inference(subsumption_resolution,[],[f142,f81])).
% 1.57/0.56  fof(f142,plain,(
% 1.57/0.56    m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.57/0.56    inference(resolution,[],[f82,f110])).
% 1.57/0.56  fof(f110,plain,(
% 1.57/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | m1_pre_topc(k1_tex_2(X0,X1),X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.57/0.56    inference(cnf_transformation,[],[f53])).
% 1.57/0.56  fof(f53,plain,(
% 1.57/0.56    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.57/0.56    inference(flattening,[],[f52])).
% 1.57/0.56  fof(f52,plain,(
% 1.57/0.56    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.57/0.56    inference(ennf_transformation,[],[f24])).
% 1.57/0.56  fof(f24,plain,(
% 1.57/0.56    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 1.57/0.56    inference(pure_predicate_removal,[],[f15])).
% 1.57/0.56  fof(f15,axiom,(
% 1.57/0.56    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 1.57/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).
% 1.57/0.56  fof(f412,plain,(
% 1.57/0.56    ~l1_pre_topc(k1_tex_2(sK0,sK1)) | spl7_17),
% 1.57/0.56    inference(resolution,[],[f313,f89])).
% 1.57/0.56  fof(f89,plain,(
% 1.57/0.56    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.57/0.56    inference(cnf_transformation,[],[f31])).
% 1.57/0.56  fof(f31,plain,(
% 1.57/0.56    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.57/0.56    inference(ennf_transformation,[],[f7])).
% 1.57/0.56  fof(f7,axiom,(
% 1.57/0.56    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.57/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.57/0.56  fof(f313,plain,(
% 1.57/0.56    ~l1_struct_0(k1_tex_2(sK0,sK1)) | spl7_17),
% 1.57/0.56    inference(avatar_component_clause,[],[f311])).
% 1.57/0.56  fof(f357,plain,(
% 1.57/0.56    ~spl7_21 | spl7_23 | spl7_2 | spl7_5),
% 1.57/0.56    inference(avatar_split_clause,[],[f352,f167,f135,f354,f330])).
% 1.57/0.56  fof(f330,plain,(
% 1.57/0.56    spl7_21 <=> v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))),
% 1.57/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 1.57/0.56  fof(f167,plain,(
% 1.57/0.56    spl7_5 <=> v1_xboole_0(u1_struct_0(sK0))),
% 1.57/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 1.57/0.56  fof(f352,plain,(
% 1.57/0.56    v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) | ~v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | (spl7_2 | spl7_5)),
% 1.57/0.56    inference(subsumption_resolution,[],[f351,f168])).
% 1.57/0.56  fof(f168,plain,(
% 1.57/0.56    ~v1_xboole_0(u1_struct_0(sK0)) | spl7_5),
% 1.57/0.56    inference(avatar_component_clause,[],[f167])).
% 1.57/0.56  fof(f351,plain,(
% 1.57/0.56    v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) | ~v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | (spl7_2 | spl7_5)),
% 1.57/0.56    inference(subsumption_resolution,[],[f265,f349])).
% 1.57/0.56  fof(f349,plain,(
% 1.57/0.56    v1_zfmisc_1(u1_struct_0(sK0)) | (spl7_2 | spl7_5)),
% 1.57/0.56    inference(subsumption_resolution,[],[f348,f168])).
% 1.57/0.56  fof(f348,plain,(
% 1.57/0.56    v1_zfmisc_1(u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | spl7_2),
% 1.57/0.56    inference(subsumption_resolution,[],[f143,f137])).
% 1.57/0.56  fof(f137,plain,(
% 1.57/0.56    ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | spl7_2),
% 1.57/0.56    inference(avatar_component_clause,[],[f135])).
% 1.57/0.56  fof(f143,plain,(
% 1.57/0.56    v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | v1_zfmisc_1(u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))),
% 1.57/0.56    inference(resolution,[],[f82,f100])).
% 1.57/0.56  fof(f100,plain,(
% 1.57/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | v1_subset_1(k6_domain_1(X0,X1),X0) | v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 1.57/0.56    inference(cnf_transformation,[],[f44])).
% 1.57/0.56  fof(f44,plain,(
% 1.57/0.56    ! [X0] : (! [X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 1.57/0.56    inference(flattening,[],[f43])).
% 1.57/0.56  fof(f43,plain,(
% 1.57/0.56    ! [X0] : (! [X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | (v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 1.57/0.56    inference(ennf_transformation,[],[f20])).
% 1.57/0.56  fof(f20,axiom,(
% 1.57/0.56    ! [X0] : ((~v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,X0) => v1_subset_1(k6_domain_1(X0,X1),X0)))),
% 1.57/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tex_2)).
% 1.57/0.56  fof(f265,plain,(
% 1.57/0.56    v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) | ~v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | ~v1_zfmisc_1(u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))),
% 1.57/0.56    inference(resolution,[],[f148,f101])).
% 1.57/0.56  fof(f101,plain,(
% 1.57/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | ~v1_subset_1(X1,X0) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 1.57/0.56    inference(cnf_transformation,[],[f46])).
% 1.57/0.56  fof(f46,plain,(
% 1.57/0.56    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 1.57/0.56    inference(flattening,[],[f45])).
% 1.57/0.56  fof(f45,plain,(
% 1.57/0.56    ! [X0] : (! [X1] : ((~v1_subset_1(X1,X0) | v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | (~v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 1.57/0.56    inference(ennf_transformation,[],[f13])).
% 1.57/0.56  fof(f13,axiom,(
% 1.57/0.56    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (~v1_xboole_0(X1) => ~v1_subset_1(X1,X0))))),
% 1.57/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).
% 1.57/0.56  fof(f148,plain,(
% 1.57/0.56    m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.57/0.56    inference(subsumption_resolution,[],[f146,f81])).
% 1.57/0.56  fof(f146,plain,(
% 1.57/0.56    m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 1.57/0.56    inference(resolution,[],[f145,f91])).
% 1.57/0.56  fof(f91,plain,(
% 1.57/0.56    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.57/0.56    inference(cnf_transformation,[],[f33])).
% 1.57/0.56  fof(f33,plain,(
% 1.57/0.56    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.57/0.56    inference(ennf_transformation,[],[f12])).
% 1.57/0.56  fof(f12,axiom,(
% 1.57/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.57/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 1.57/0.56  fof(f343,plain,(
% 1.57/0.56    spl7_1 | ~spl7_21),
% 1.57/0.56    inference(avatar_split_clause,[],[f342,f330,f131])).
% 1.57/0.56  fof(f131,plain,(
% 1.57/0.56    spl7_1 <=> v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 1.57/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.57/0.56  fof(f342,plain,(
% 1.57/0.56    ~v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 1.57/0.56    inference(subsumption_resolution,[],[f341,f81])).
% 1.57/0.56  fof(f341,plain,(
% 1.57/0.56    ~v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~l1_pre_topc(sK0)),
% 1.57/0.56    inference(subsumption_resolution,[],[f261,f145])).
% 1.57/0.56  fof(f261,plain,(
% 1.57/0.56    ~v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~l1_pre_topc(sK0)),
% 1.57/0.56    inference(resolution,[],[f148,f123])).
% 1.57/0.56  fof(f123,plain,(
% 1.57/0.56    ( ! [X0,X1] : (~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) | v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.57/0.56    inference(equality_resolution,[],[f92])).
% 1.57/0.56  fof(f92,plain,(
% 1.57/0.56    ( ! [X2,X0,X1] : (v1_tex_2(X1,X0) | ~v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.57/0.56    inference(cnf_transformation,[],[f62])).
% 1.57/0.56  fof(f62,plain,(
% 1.57/0.56    ! [X0] : (! [X1] : (! [X2] : (((v1_subset_1(X2,u1_struct_0(X0)) | ~v1_tex_2(X1,X0)) & (v1_tex_2(X1,X0) | ~v1_subset_1(X2,u1_struct_0(X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.57/0.56    inference(nnf_transformation,[],[f35])).
% 1.57/0.56  fof(f35,plain,(
% 1.57/0.56    ! [X0] : (! [X1] : (! [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) <=> v1_tex_2(X1,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.57/0.56    inference(flattening,[],[f34])).
% 1.57/0.56  fof(f34,plain,(
% 1.57/0.56    ! [X0] : (! [X1] : (! [X2] : (((v1_subset_1(X2,u1_struct_0(X0)) <=> v1_tex_2(X1,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.57/0.56    inference(ennf_transformation,[],[f18])).
% 1.57/0.56  fof(f18,axiom,(
% 1.57/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => (v1_subset_1(X2,u1_struct_0(X0)) <=> v1_tex_2(X1,X0))))))),
% 1.57/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_tex_2)).
% 1.57/0.56  fof(f340,plain,(
% 1.57/0.56    spl7_21 | ~spl7_1),
% 1.57/0.56    inference(avatar_split_clause,[],[f339,f131,f330])).
% 1.57/0.56  fof(f339,plain,(
% 1.57/0.56    ~v1_tex_2(k1_tex_2(sK0,sK1),sK0) | v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))),
% 1.57/0.56    inference(subsumption_resolution,[],[f338,f81])).
% 1.57/0.56  fof(f338,plain,(
% 1.57/0.56    ~v1_tex_2(k1_tex_2(sK0,sK1),sK0) | v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | ~l1_pre_topc(sK0)),
% 1.57/0.56    inference(subsumption_resolution,[],[f262,f145])).
% 1.57/0.56  fof(f262,plain,(
% 1.57/0.56    ~v1_tex_2(k1_tex_2(sK0,sK1),sK0) | v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~l1_pre_topc(sK0)),
% 1.57/0.56    inference(resolution,[],[f148,f122])).
% 1.57/0.56  fof(f122,plain,(
% 1.57/0.56    ( ! [X0,X1] : (~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tex_2(X1,X0) | v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.57/0.56    inference(equality_resolution,[],[f93])).
% 1.57/0.56  fof(f93,plain,(
% 1.57/0.56    ( ! [X2,X0,X1] : (v1_subset_1(X2,u1_struct_0(X0)) | ~v1_tex_2(X1,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.57/0.56    inference(cnf_transformation,[],[f62])).
% 1.57/0.56  fof(f337,plain,(
% 1.57/0.56    spl7_21 | spl7_22),
% 1.57/0.56    inference(avatar_split_clause,[],[f264,f334,f330])).
% 1.57/0.56  fof(f264,plain,(
% 1.57/0.56    u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) | v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))),
% 1.57/0.56    inference(resolution,[],[f148,f106])).
% 1.57/0.56  fof(f106,plain,(
% 1.57/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 1.57/0.56    inference(cnf_transformation,[],[f69])).
% 1.57/0.56  fof(f69,plain,(
% 1.57/0.56    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.57/0.56    inference(nnf_transformation,[],[f49])).
% 1.57/0.56  fof(f49,plain,(
% 1.57/0.56    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.57/0.56    inference(ennf_transformation,[],[f14])).
% 1.57/0.56  fof(f14,axiom,(
% 1.57/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 1.57/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).
% 1.57/0.56  fof(f239,plain,(
% 1.57/0.56    ~spl7_3 | ~spl7_5),
% 1.57/0.56    inference(avatar_contradiction_clause,[],[f238])).
% 1.57/0.56  fof(f238,plain,(
% 1.57/0.56    $false | (~spl7_3 | ~spl7_5)),
% 1.57/0.56    inference(subsumption_resolution,[],[f237,f80])).
% 1.57/0.56  fof(f237,plain,(
% 1.57/0.56    v2_struct_0(sK0) | (~spl7_3 | ~spl7_5)),
% 1.57/0.56    inference(subsumption_resolution,[],[f236,f158])).
% 1.57/0.56  fof(f158,plain,(
% 1.57/0.56    l1_struct_0(sK0) | ~spl7_3),
% 1.57/0.56    inference(avatar_component_clause,[],[f157])).
% 1.57/0.56  fof(f157,plain,(
% 1.57/0.56    spl7_3 <=> l1_struct_0(sK0)),
% 1.57/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.57/0.56  fof(f236,plain,(
% 1.57/0.56    ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~spl7_5),
% 1.57/0.56    inference(resolution,[],[f169,f98])).
% 1.57/0.56  fof(f169,plain,(
% 1.57/0.56    v1_xboole_0(u1_struct_0(sK0)) | ~spl7_5),
% 1.57/0.56    inference(avatar_component_clause,[],[f167])).
% 1.57/0.56  fof(f177,plain,(
% 1.57/0.56    spl7_3),
% 1.57/0.56    inference(avatar_contradiction_clause,[],[f176])).
% 1.57/0.56  fof(f176,plain,(
% 1.57/0.56    $false | spl7_3),
% 1.57/0.56    inference(subsumption_resolution,[],[f175,f81])).
% 1.57/0.56  fof(f175,plain,(
% 1.57/0.56    ~l1_pre_topc(sK0) | spl7_3),
% 1.57/0.56    inference(resolution,[],[f159,f89])).
% 1.57/0.56  fof(f159,plain,(
% 1.57/0.56    ~l1_struct_0(sK0) | spl7_3),
% 1.57/0.56    inference(avatar_component_clause,[],[f157])).
% 1.57/0.56  fof(f139,plain,(
% 1.57/0.56    spl7_1 | spl7_2),
% 1.57/0.56    inference(avatar_split_clause,[],[f83,f135,f131])).
% 1.57/0.56  fof(f83,plain,(
% 1.57/0.56    v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 1.57/0.56    inference(cnf_transformation,[],[f59])).
% 1.57/0.56  fof(f138,plain,(
% 1.57/0.56    ~spl7_1 | ~spl7_2),
% 1.57/0.56    inference(avatar_split_clause,[],[f84,f135,f131])).
% 1.57/0.56  fof(f84,plain,(
% 1.57/0.56    ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 1.57/0.56    inference(cnf_transformation,[],[f59])).
% 1.57/0.56  % SZS output end Proof for theBenchmark
% 1.57/0.56  % (3128)------------------------------
% 1.57/0.56  % (3128)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.56  % (3128)Termination reason: Refutation
% 1.57/0.56  
% 1.57/0.56  % (3128)Memory used [KB]: 10874
% 1.57/0.56  % (3128)Time elapsed: 0.160 s
% 1.57/0.56  % (3128)------------------------------
% 1.57/0.56  % (3128)------------------------------
% 1.57/0.56  % (3119)Success in time 0.205 s
%------------------------------------------------------------------------------
