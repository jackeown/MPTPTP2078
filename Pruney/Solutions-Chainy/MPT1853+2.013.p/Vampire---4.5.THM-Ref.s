%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:43 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 630 expanded)
%              Number of leaves         :   22 ( 174 expanded)
%              Depth                    :   20
%              Number of atoms          :  494 (3331 expanded)
%              Number of equality atoms :   11 (  26 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f371,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f98,f110,f115,f319,f333,f341,f356,f363,f370])).

fof(f370,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f369])).

fof(f369,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f364,f97])).

fof(f97,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl3_2
  <=> v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f364,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f49,f93])).

fof(f93,plain,
    ( v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl3_1
  <=> v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f49,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
      | ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0) )
    & ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
      | v1_tex_2(k1_tex_2(sK0,sK1),sK0) )
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f39,f41,f40])).

fof(f40,plain,
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

fof(f41,plain,
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

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( v1_tex_2(k1_tex_2(X0,X1),X0)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_tex_2)).

fof(f363,plain,
    ( spl3_2
    | ~ spl3_3
    | spl3_4 ),
    inference(avatar_contradiction_clause,[],[f362])).

fof(f362,plain,
    ( $false
    | spl3_2
    | ~ spl3_3
    | spl3_4 ),
    inference(subsumption_resolution,[],[f361,f354])).

fof(f354,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | spl3_2 ),
    inference(subsumption_resolution,[],[f352,f47])).

fof(f47,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f42])).

fof(f352,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_zfmisc_1(u1_struct_0(sK0))
    | spl3_2 ),
    inference(resolution,[],[f96,f155])).

fof(f155,plain,(
    ! [X0,X1] :
      ( v1_subset_1(k6_domain_1(X0,X1),X0)
      | ~ m1_subset_1(X1,X0)
      | v1_zfmisc_1(X0) ) ),
    inference(subsumption_resolution,[],[f56,f50])).

fof(f50,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_zfmisc_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_zfmisc_1)).

fof(f56,plain,(
    ! [X0,X1] :
      ( v1_subset_1(k6_domain_1(X0,X1),X0)
      | ~ m1_subset_1(X1,X0)
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( ~ v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tex_2)).

fof(f96,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f95])).

fof(f361,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl3_3
    | spl3_4 ),
    inference(subsumption_resolution,[],[f359,f104])).

fof(f104,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl3_3
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f359,plain,
    ( ~ l1_struct_0(sK0)
    | ~ v1_zfmisc_1(u1_struct_0(sK0))
    | spl3_4 ),
    inference(resolution,[],[f109,f57])).

fof(f57,plain,(
    ! [X0] :
      ( v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | ~ v1_zfmisc_1(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v7_struct_0(X0) )
     => ~ v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_struct_0)).

fof(f109,plain,
    ( ~ v7_struct_0(sK0)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl3_4
  <=> v7_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f356,plain,
    ( ~ spl3_1
    | ~ spl3_4
    | spl3_5 ),
    inference(avatar_contradiction_clause,[],[f355])).

fof(f355,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_4
    | spl3_5 ),
    inference(unit_resulting_resolution,[],[f45,f108,f46,f187,f93,f313,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v1_tex_2(X1,X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tex_2(X1,X0)
            & ~ v2_struct_0(X1) )
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tex_2(X1,X0)
            & ~ v2_struct_0(X1) )
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( ~ v2_struct_0(X1)
           => ( ~ v1_tex_2(X1,X0)
              & ~ v2_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc10_tex_2)).

fof(f313,plain,
    ( ~ v2_struct_0(k1_tex_2(sK0,sK1))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f312])).

fof(f312,plain,
    ( spl3_5
  <=> v2_struct_0(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f187,plain,(
    m1_pre_topc(k1_tex_2(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f186,f45])).

fof(f186,plain,
    ( m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f185,f46])).

fof(f185,plain,
    ( m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f64,f47])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).

fof(f46,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f108,plain,
    ( v7_struct_0(sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f107])).

fof(f45,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f341,plain,(
    ~ spl3_5 ),
    inference(avatar_contradiction_clause,[],[f340])).

fof(f340,plain,
    ( $false
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f339,f45])).

fof(f339,plain,
    ( v2_struct_0(sK0)
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f338,f46])).

fof(f338,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f335,f47])).

fof(f335,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_5 ),
    inference(resolution,[],[f314,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f314,plain,
    ( v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f312])).

fof(f333,plain,(
    spl3_6 ),
    inference(avatar_contradiction_clause,[],[f330])).

fof(f330,plain,
    ( $false
    | spl3_6 ),
    inference(unit_resulting_resolution,[],[f46,f187,f326,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f326,plain,
    ( ~ l1_pre_topc(k1_tex_2(sK0,sK1))
    | spl3_6 ),
    inference(resolution,[],[f318,f51])).

fof(f51,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f318,plain,
    ( ~ l1_struct_0(k1_tex_2(sK0,sK1))
    | spl3_6 ),
    inference(avatar_component_clause,[],[f316])).

fof(f316,plain,
    ( spl3_6
  <=> l1_struct_0(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f319,plain,
    ( spl3_5
    | ~ spl3_6
    | spl3_1
    | ~ spl3_3
    | spl3_4 ),
    inference(avatar_split_clause,[],[f302,f107,f103,f91,f316,f312])).

fof(f302,plain,
    ( ~ l1_struct_0(k1_tex_2(sK0,sK1))
    | v2_struct_0(k1_tex_2(sK0,sK1))
    | spl3_1
    | ~ spl3_3
    | spl3_4 ),
    inference(subsumption_resolution,[],[f301,f169])).

fof(f169,plain,(
    v7_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f168,f45])).

fof(f168,plain,
    ( v7_struct_0(k1_tex_2(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f167,f46])).

fof(f167,plain,
    ( v7_struct_0(k1_tex_2(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f66,f47])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | v7_struct_0(k1_tex_2(X0,X1))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_tex_2)).

fof(f301,plain,
    ( ~ v7_struct_0(k1_tex_2(sK0,sK1))
    | ~ l1_struct_0(k1_tex_2(sK0,sK1))
    | v2_struct_0(k1_tex_2(sK0,sK1))
    | spl3_1
    | ~ spl3_3
    | spl3_4 ),
    inference(subsumption_resolution,[],[f296,f280])).

fof(f280,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(k1_tex_2(sK0,sK1)))
    | spl3_1
    | ~ spl3_3
    | spl3_4 ),
    inference(resolution,[],[f277,f122])).

fof(f122,plain,
    ( ! [X0] :
        ( ~ sQ2_eqProxy(u1_struct_0(sK0),X0)
        | ~ v1_zfmisc_1(X0) )
    | ~ spl3_3
    | spl3_4 ),
    inference(resolution,[],[f118,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( sQ2_eqProxy(X1,X0)
      | ~ sQ2_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f70])).

fof(f70,plain,(
    ! [X1,X0] :
      ( sQ2_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ2_eqProxy])])).

fof(f118,plain,
    ( ! [X0] :
        ( ~ sQ2_eqProxy(X0,u1_struct_0(sK0))
        | ~ v1_zfmisc_1(X0) )
    | ~ spl3_3
    | spl3_4 ),
    inference(resolution,[],[f117,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v1_zfmisc_1(X1)
      | ~ v1_zfmisc_1(X0)
      | ~ sQ2_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f70])).

fof(f117,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl3_3
    | spl3_4 ),
    inference(subsumption_resolution,[],[f116,f104])).

fof(f116,plain,
    ( ~ l1_struct_0(sK0)
    | ~ v1_zfmisc_1(u1_struct_0(sK0))
    | spl3_4 ),
    inference(resolution,[],[f109,f57])).

fof(f277,plain,
    ( sQ2_eqProxy(u1_struct_0(sK0),u1_struct_0(k1_tex_2(sK0,sK1)))
    | spl3_1 ),
    inference(subsumption_resolution,[],[f192,f204])).

fof(f204,plain,
    ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | spl3_1 ),
    inference(subsumption_resolution,[],[f203,f46])).

fof(f203,plain,
    ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | spl3_1 ),
    inference(subsumption_resolution,[],[f202,f92])).

fof(f92,plain,
    ( ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f91])).

fof(f202,plain,
    ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f198,f187])).

fof(f198,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
      | v1_tex_2(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f68,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f68,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | ~ v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v1_tex_2(X1,X0)
      | ~ v1_subset_1(X2,u1_struct_0(X0))
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v1_subset_1(X2,u1_struct_0(X0))
              <=> v1_tex_2(X1,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v1_subset_1(X2,u1_struct_0(X0))
              <=> v1_tex_2(X1,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( v1_subset_1(X2,u1_struct_0(X0))
                <=> v1_tex_2(X1,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_tex_2)).

fof(f192,plain,
    ( sQ2_eqProxy(u1_struct_0(sK0),u1_struct_0(k1_tex_2(sK0,sK1)))
    | v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) ),
    inference(resolution,[],[f190,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | sQ2_eqProxy(X0,X1)
      | v1_subset_1(X1,X0) ) ),
    inference(equality_proxy_replacement,[],[f62,f70])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(f190,plain,(
    m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f189,f46])).

fof(f189,plain,
    ( m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f187,f53])).

fof(f296,plain,
    ( v1_zfmisc_1(u1_struct_0(k1_tex_2(sK0,sK1)))
    | ~ v7_struct_0(k1_tex_2(sK0,sK1))
    | ~ l1_struct_0(k1_tex_2(sK0,sK1))
    | v2_struct_0(k1_tex_2(sK0,sK1))
    | spl3_1 ),
    inference(resolution,[],[f279,f161])).

fof(f161,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | v1_zfmisc_1(u1_struct_0(X1))
      | ~ v7_struct_0(X1)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f160])).

fof(f160,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | v1_zfmisc_1(u1_struct_0(X1))
      | ~ v7_struct_0(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f155,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
      | ~ v7_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v7_struct_0(X0)
          | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v7_struct_0(X0)
          | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ~ ( v7_struct_0(X0)
              & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_tex_2)).

fof(f279,plain,
    ( m1_subset_1(sK1,u1_struct_0(k1_tex_2(sK0,sK1)))
    | spl3_1 ),
    inference(resolution,[],[f277,f199])).

fof(f199,plain,(
    ! [X0] :
      ( ~ sQ2_eqProxy(u1_struct_0(sK0),X0)
      | m1_subset_1(sK1,X0) ) ),
    inference(resolution,[],[f176,f87])).

fof(f87,plain,(
    ! [X0] : sQ2_eqProxy(X0,X0) ),
    inference(equality_proxy_axiom,[],[f70])).

fof(f176,plain,(
    ! [X0,X1] :
      ( ~ sQ2_eqProxy(sK1,X1)
      | ~ sQ2_eqProxy(u1_struct_0(sK0),X0)
      | m1_subset_1(X1,X0) ) ),
    inference(resolution,[],[f82,f47])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,X2)
      | ~ sQ2_eqProxy(X2,X3)
      | ~ sQ2_eqProxy(X0,X1)
      | m1_subset_1(X1,X3) ) ),
    inference(equality_proxy_axiom,[],[f70])).

fof(f115,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f114])).

fof(f114,plain,
    ( $false
    | spl3_3 ),
    inference(subsumption_resolution,[],[f112,f46])).

fof(f112,plain,
    ( ~ l1_pre_topc(sK0)
    | spl3_3 ),
    inference(resolution,[],[f105,f51])).

fof(f105,plain,
    ( ~ l1_struct_0(sK0)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f103])).

fof(f110,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f101,f95,f107,f103])).

fof(f101,plain,
    ( ~ v7_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f100,f45])).

fof(f100,plain,
    ( ~ v7_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f99,f47])).

fof(f99,plain,
    ( ~ v7_struct_0(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_2 ),
    inference(resolution,[],[f58,f97])).

fof(f98,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f48,f95,f91])).

fof(f48,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:44:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.45  % (23122)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.47  % (23129)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.47  % (23129)Refutation not found, incomplete strategy% (23129)------------------------------
% 0.21/0.47  % (23129)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (23129)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (23129)Memory used [KB]: 6140
% 0.21/0.47  % (23129)Time elapsed: 0.057 s
% 0.21/0.47  % (23129)------------------------------
% 0.21/0.47  % (23129)------------------------------
% 0.21/0.48  % (23122)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f371,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f98,f110,f115,f319,f333,f341,f356,f363,f370])).
% 0.21/0.48  fof(f370,plain,(
% 0.21/0.48    ~spl3_1 | ~spl3_2),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f369])).
% 0.21/0.48  fof(f369,plain,(
% 0.21/0.48    $false | (~spl3_1 | ~spl3_2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f364,f97])).
% 0.21/0.48  fof(f97,plain,(
% 0.21/0.48    v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~spl3_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f95])).
% 0.21/0.48  fof(f95,plain,(
% 0.21/0.48    spl3_2 <=> v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.48  fof(f364,plain,(
% 0.21/0.48    ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~spl3_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f49,f93])).
% 0.21/0.48  fof(f93,plain,(
% 0.21/0.48    v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~spl3_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f91])).
% 0.21/0.48  fof(f91,plain,(
% 0.21/0.48    spl3_1 <=> v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ((~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,sK1),sK0)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0)) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f39,f41,f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,X1),sK0)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,X1),sK0)) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,X1),sK0)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,X1),sK0)) & m1_subset_1(X1,u1_struct_0(sK0))) => ((~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,sK1),sK0)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0)) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,negated_conjecture,(
% 0.21/0.48    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 0.21/0.48    inference(negated_conjecture,[],[f13])).
% 0.21/0.48  fof(f13,conjecture,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_tex_2)).
% 0.21/0.48  fof(f363,plain,(
% 0.21/0.48    spl3_2 | ~spl3_3 | spl3_4),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f362])).
% 0.21/0.48  fof(f362,plain,(
% 0.21/0.48    $false | (spl3_2 | ~spl3_3 | spl3_4)),
% 0.21/0.48    inference(subsumption_resolution,[],[f361,f354])).
% 0.21/0.48  fof(f354,plain,(
% 0.21/0.48    v1_zfmisc_1(u1_struct_0(sK0)) | spl3_2),
% 0.21/0.48    inference(subsumption_resolution,[],[f352,f47])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.48    inference(cnf_transformation,[],[f42])).
% 0.21/0.48  fof(f352,plain,(
% 0.21/0.48    ~m1_subset_1(sK1,u1_struct_0(sK0)) | v1_zfmisc_1(u1_struct_0(sK0)) | spl3_2),
% 0.21/0.48    inference(resolution,[],[f96,f155])).
% 0.21/0.48  fof(f155,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0) | v1_zfmisc_1(X0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f56,f50])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ( ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0] : (v1_xboole_0(X0) => v1_zfmisc_1(X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_zfmisc_1)).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0) | v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 0.21/0.48    inference(flattening,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | (v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,axiom,(
% 0.21/0.48    ! [X0] : ((~v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,X0) => v1_subset_1(k6_domain_1(X0,X1),X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tex_2)).
% 0.21/0.48  fof(f96,plain,(
% 0.21/0.48    ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | spl3_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f95])).
% 0.21/0.48  fof(f361,plain,(
% 0.21/0.48    ~v1_zfmisc_1(u1_struct_0(sK0)) | (~spl3_3 | spl3_4)),
% 0.21/0.48    inference(subsumption_resolution,[],[f359,f104])).
% 0.21/0.48  fof(f104,plain,(
% 0.21/0.48    l1_struct_0(sK0) | ~spl3_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f103])).
% 0.21/0.48  fof(f103,plain,(
% 0.21/0.48    spl3_3 <=> l1_struct_0(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.48  fof(f359,plain,(
% 0.21/0.48    ~l1_struct_0(sK0) | ~v1_zfmisc_1(u1_struct_0(sK0)) | spl3_4),
% 0.21/0.48    inference(resolution,[],[f109,f57])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    ( ! [X0] : (v7_struct_0(X0) | ~l1_struct_0(X0) | ~v1_zfmisc_1(u1_struct_0(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | v7_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0] : ((l1_struct_0(X0) & ~v7_struct_0(X0)) => ~v1_zfmisc_1(u1_struct_0(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_struct_0)).
% 0.21/0.48  fof(f109,plain,(
% 0.21/0.48    ~v7_struct_0(sK0) | spl3_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f107])).
% 0.21/0.48  fof(f107,plain,(
% 0.21/0.48    spl3_4 <=> v7_struct_0(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.48  fof(f356,plain,(
% 0.21/0.48    ~spl3_1 | ~spl3_4 | spl3_5),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f355])).
% 0.21/0.48  fof(f355,plain,(
% 0.21/0.48    $false | (~spl3_1 | ~spl3_4 | spl3_5)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f45,f108,f46,f187,f93,f313,f60])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_tex_2(X1,X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((~v1_tex_2(X1,X0) & ~v2_struct_0(X1)) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (((~v1_tex_2(X1,X0) & ~v2_struct_0(X1)) | v2_struct_0(X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (~v2_struct_0(X1) => (~v1_tex_2(X1,X0) & ~v2_struct_0(X1)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc10_tex_2)).
% 0.21/0.48  fof(f313,plain,(
% 0.21/0.48    ~v2_struct_0(k1_tex_2(sK0,sK1)) | spl3_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f312])).
% 0.21/0.48  fof(f312,plain,(
% 0.21/0.48    spl3_5 <=> v2_struct_0(k1_tex_2(sK0,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.48  fof(f187,plain,(
% 0.21/0.48    m1_pre_topc(k1_tex_2(sK0,sK1),sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f186,f45])).
% 0.21/0.48  fof(f186,plain,(
% 0.21/0.48    m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f185,f46])).
% 0.21/0.48  fof(f185,plain,(
% 0.21/0.48    m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(resolution,[],[f64,f47])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | m1_pre_topc(k1_tex_2(X0,X1),X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.21/0.48    inference(pure_predicate_removal,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    l1_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f42])).
% 0.21/0.48  fof(f108,plain,(
% 0.21/0.48    v7_struct_0(sK0) | ~spl3_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f107])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ~v2_struct_0(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f42])).
% 0.21/0.48  fof(f341,plain,(
% 0.21/0.48    ~spl3_5),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f340])).
% 0.21/0.48  fof(f340,plain,(
% 0.21/0.48    $false | ~spl3_5),
% 0.21/0.48    inference(subsumption_resolution,[],[f339,f45])).
% 0.21/0.48  fof(f339,plain,(
% 0.21/0.48    v2_struct_0(sK0) | ~spl3_5),
% 0.21/0.48    inference(subsumption_resolution,[],[f338,f46])).
% 0.21/0.48  fof(f338,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl3_5),
% 0.21/0.48    inference(subsumption_resolution,[],[f335,f47])).
% 0.21/0.48  fof(f335,plain,(
% 0.21/0.48    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl3_5),
% 0.21/0.48    inference(resolution,[],[f314,f63])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v2_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f35])).
% 0.21/0.48  fof(f314,plain,(
% 0.21/0.48    v2_struct_0(k1_tex_2(sK0,sK1)) | ~spl3_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f312])).
% 0.21/0.48  fof(f333,plain,(
% 0.21/0.48    spl3_6),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f330])).
% 0.21/0.48  fof(f330,plain,(
% 0.21/0.48    $false | spl3_6),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f46,f187,f326,f52])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.48  fof(f326,plain,(
% 0.21/0.48    ~l1_pre_topc(k1_tex_2(sK0,sK1)) | spl3_6),
% 0.21/0.48    inference(resolution,[],[f318,f51])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.48  fof(f318,plain,(
% 0.21/0.48    ~l1_struct_0(k1_tex_2(sK0,sK1)) | spl3_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f316])).
% 0.21/0.48  fof(f316,plain,(
% 0.21/0.48    spl3_6 <=> l1_struct_0(k1_tex_2(sK0,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.48  fof(f319,plain,(
% 0.21/0.48    spl3_5 | ~spl3_6 | spl3_1 | ~spl3_3 | spl3_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f302,f107,f103,f91,f316,f312])).
% 0.21/0.48  fof(f302,plain,(
% 0.21/0.48    ~l1_struct_0(k1_tex_2(sK0,sK1)) | v2_struct_0(k1_tex_2(sK0,sK1)) | (spl3_1 | ~spl3_3 | spl3_4)),
% 0.21/0.48    inference(subsumption_resolution,[],[f301,f169])).
% 0.21/0.48  fof(f169,plain,(
% 0.21/0.48    v7_struct_0(k1_tex_2(sK0,sK1))),
% 0.21/0.48    inference(subsumption_resolution,[],[f168,f45])).
% 0.21/0.48  fof(f168,plain,(
% 0.21/0.48    v7_struct_0(k1_tex_2(sK0,sK1)) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f167,f46])).
% 0.21/0.48  fof(f167,plain,(
% 0.21/0.48    v7_struct_0(k1_tex_2(sK0,sK1)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(resolution,[],[f66,f47])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | v7_struct_0(k1_tex_2(X0,X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ! [X0,X1] : ((v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ! [X0,X1] : ((v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.21/0.48    inference(pure_predicate_removal,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_tex_2)).
% 0.21/0.48  fof(f301,plain,(
% 0.21/0.48    ~v7_struct_0(k1_tex_2(sK0,sK1)) | ~l1_struct_0(k1_tex_2(sK0,sK1)) | v2_struct_0(k1_tex_2(sK0,sK1)) | (spl3_1 | ~spl3_3 | spl3_4)),
% 0.21/0.48    inference(subsumption_resolution,[],[f296,f280])).
% 0.21/0.48  fof(f280,plain,(
% 0.21/0.48    ~v1_zfmisc_1(u1_struct_0(k1_tex_2(sK0,sK1))) | (spl3_1 | ~spl3_3 | spl3_4)),
% 0.21/0.48    inference(resolution,[],[f277,f122])).
% 0.21/0.48  fof(f122,plain,(
% 0.21/0.48    ( ! [X0] : (~sQ2_eqProxy(u1_struct_0(sK0),X0) | ~v1_zfmisc_1(X0)) ) | (~spl3_3 | spl3_4)),
% 0.21/0.48    inference(resolution,[],[f118,f88])).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    ( ! [X0,X1] : (sQ2_eqProxy(X1,X0) | ~sQ2_eqProxy(X0,X1)) )),
% 0.21/0.48    inference(equality_proxy_axiom,[],[f70])).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    ! [X1,X0] : (sQ2_eqProxy(X0,X1) <=> X0 = X1)),
% 0.21/0.48    introduced(equality_proxy_definition,[new_symbols(naming,[sQ2_eqProxy])])).
% 0.21/0.48  fof(f118,plain,(
% 0.21/0.48    ( ! [X0] : (~sQ2_eqProxy(X0,u1_struct_0(sK0)) | ~v1_zfmisc_1(X0)) ) | (~spl3_3 | spl3_4)),
% 0.21/0.48    inference(resolution,[],[f117,f77])).
% 0.21/0.48  fof(f77,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v1_zfmisc_1(X1) | ~v1_zfmisc_1(X0) | ~sQ2_eqProxy(X0,X1)) )),
% 0.21/0.48    inference(equality_proxy_axiom,[],[f70])).
% 0.21/0.48  fof(f117,plain,(
% 0.21/0.48    ~v1_zfmisc_1(u1_struct_0(sK0)) | (~spl3_3 | spl3_4)),
% 0.21/0.48    inference(subsumption_resolution,[],[f116,f104])).
% 0.21/0.48  fof(f116,plain,(
% 0.21/0.48    ~l1_struct_0(sK0) | ~v1_zfmisc_1(u1_struct_0(sK0)) | spl3_4),
% 0.21/0.48    inference(resolution,[],[f109,f57])).
% 0.21/0.48  fof(f277,plain,(
% 0.21/0.48    sQ2_eqProxy(u1_struct_0(sK0),u1_struct_0(k1_tex_2(sK0,sK1))) | spl3_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f192,f204])).
% 0.21/0.48  fof(f204,plain,(
% 0.21/0.48    ~v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | spl3_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f203,f46])).
% 0.21/0.48  fof(f203,plain,(
% 0.21/0.48    ~v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | spl3_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f202,f92])).
% 0.21/0.48  fof(f92,plain,(
% 0.21/0.48    ~v1_tex_2(k1_tex_2(sK0,sK1),sK0) | spl3_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f91])).
% 0.21/0.48  fof(f202,plain,(
% 0.21/0.48    ~v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~l1_pre_topc(sK0)),
% 0.21/0.48    inference(resolution,[],[f198,f187])).
% 0.21/0.48  fof(f198,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) | v1_tex_2(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f68,f53])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v1_tex_2(X1,X0) | ~v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(equality_resolution,[],[f54])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (v1_tex_2(X1,X0) | ~v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f43])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (((v1_subset_1(X2,u1_struct_0(X0)) | ~v1_tex_2(X1,X0)) & (v1_tex_2(X1,X0) | ~v1_subset_1(X2,u1_struct_0(X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) <=> v1_tex_2(X1,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (((v1_subset_1(X2,u1_struct_0(X0)) <=> v1_tex_2(X1,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => (v1_subset_1(X2,u1_struct_0(X0)) <=> v1_tex_2(X1,X0))))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_tex_2)).
% 0.21/0.48  fof(f192,plain,(
% 0.21/0.48    sQ2_eqProxy(u1_struct_0(sK0),u1_struct_0(k1_tex_2(sK0,sK1))) | v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))),
% 0.21/0.48    inference(resolution,[],[f190,f71])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | sQ2_eqProxy(X0,X1) | v1_subset_1(X1,X0)) )),
% 0.21/0.48    inference(equality_proxy_replacement,[],[f62,f70])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f44])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.48    inference(nnf_transformation,[],[f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).
% 0.21/0.48  fof(f190,plain,(
% 0.21/0.48    m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    inference(subsumption_resolution,[],[f189,f46])).
% 0.21/0.48  fof(f189,plain,(
% 0.21/0.48    m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.21/0.48    inference(resolution,[],[f187,f53])).
% 0.21/0.48  fof(f296,plain,(
% 0.21/0.48    v1_zfmisc_1(u1_struct_0(k1_tex_2(sK0,sK1))) | ~v7_struct_0(k1_tex_2(sK0,sK1)) | ~l1_struct_0(k1_tex_2(sK0,sK1)) | v2_struct_0(k1_tex_2(sK0,sK1)) | spl3_1),
% 0.21/0.48    inference(resolution,[],[f279,f161])).
% 0.21/0.48  fof(f161,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | v1_zfmisc_1(u1_struct_0(X1)) | ~v7_struct_0(X1) | ~l1_struct_0(X1) | v2_struct_0(X1)) )),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f160])).
% 0.21/0.48  fof(f160,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | v1_zfmisc_1(u1_struct_0(X1)) | ~v7_struct_0(X1) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_struct_0(X1) | v2_struct_0(X1)) )),
% 0.21/0.48    inference(resolution,[],[f155,f58])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v7_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,axiom,(
% 0.21/0.48    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~(v7_struct_0(X0) & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_tex_2)).
% 0.21/0.48  fof(f279,plain,(
% 0.21/0.48    m1_subset_1(sK1,u1_struct_0(k1_tex_2(sK0,sK1))) | spl3_1),
% 0.21/0.48    inference(resolution,[],[f277,f199])).
% 0.21/0.48  fof(f199,plain,(
% 0.21/0.48    ( ! [X0] : (~sQ2_eqProxy(u1_struct_0(sK0),X0) | m1_subset_1(sK1,X0)) )),
% 0.21/0.48    inference(resolution,[],[f176,f87])).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    ( ! [X0] : (sQ2_eqProxy(X0,X0)) )),
% 0.21/0.48    inference(equality_proxy_axiom,[],[f70])).
% 0.21/0.48  fof(f176,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~sQ2_eqProxy(sK1,X1) | ~sQ2_eqProxy(u1_struct_0(sK0),X0) | m1_subset_1(X1,X0)) )),
% 0.21/0.48    inference(resolution,[],[f82,f47])).
% 0.21/0.48  fof(f82,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,X2) | ~sQ2_eqProxy(X2,X3) | ~sQ2_eqProxy(X0,X1) | m1_subset_1(X1,X3)) )),
% 0.21/0.48    inference(equality_proxy_axiom,[],[f70])).
% 0.21/0.48  fof(f115,plain,(
% 0.21/0.48    spl3_3),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f114])).
% 0.21/0.48  fof(f114,plain,(
% 0.21/0.48    $false | spl3_3),
% 0.21/0.48    inference(subsumption_resolution,[],[f112,f46])).
% 0.21/0.48  fof(f112,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | spl3_3),
% 0.21/0.48    inference(resolution,[],[f105,f51])).
% 0.21/0.48  fof(f105,plain,(
% 0.21/0.48    ~l1_struct_0(sK0) | spl3_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f103])).
% 0.21/0.48  fof(f110,plain,(
% 0.21/0.48    ~spl3_3 | ~spl3_4 | ~spl3_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f101,f95,f107,f103])).
% 0.21/0.48  fof(f101,plain,(
% 0.21/0.48    ~v7_struct_0(sK0) | ~l1_struct_0(sK0) | ~spl3_2),
% 0.21/0.48    inference(subsumption_resolution,[],[f100,f45])).
% 0.21/0.48  fof(f100,plain,(
% 0.21/0.48    ~v7_struct_0(sK0) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~spl3_2),
% 0.21/0.48    inference(subsumption_resolution,[],[f99,f47])).
% 0.21/0.48  fof(f99,plain,(
% 0.21/0.48    ~v7_struct_0(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~spl3_2),
% 0.21/0.48    inference(resolution,[],[f58,f97])).
% 0.21/0.48  fof(f98,plain,(
% 0.21/0.48    spl3_1 | spl3_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f48,f95,f91])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f42])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (23122)------------------------------
% 0.21/0.48  % (23122)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (23122)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (23122)Memory used [KB]: 6268
% 0.21/0.48  % (23122)Time elapsed: 0.032 s
% 0.21/0.48  % (23122)------------------------------
% 0.21/0.48  % (23122)------------------------------
% 0.21/0.49  % (23116)Success in time 0.129 s
%------------------------------------------------------------------------------
