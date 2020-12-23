%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:48 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  190 ( 336 expanded)
%              Number of leaves         :   34 ( 119 expanded)
%              Depth                    :   11
%              Number of atoms          :  638 (1039 expanded)
%              Number of equality atoms :   24 (  38 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f389,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f76,f81,f90,f99,f111,f114,f126,f140,f150,f155,f158,f172,f203,f230,f235,f264,f279,f283,f289,f323,f334,f365,f371,f388])).

fof(f388,plain,
    ( ~ spl4_3
    | ~ spl4_5
    | spl4_6
    | ~ spl4_15 ),
    inference(avatar_contradiction_clause,[],[f387])).

fof(f387,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_5
    | spl4_6
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f384,f89])).

fof(f89,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl4_3
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f384,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl4_5
    | spl4_6
    | ~ spl4_15 ),
    inference(resolution,[],[f383,f98])).

fof(f98,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl4_5
  <=> v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f383,plain,
    ( ! [X1] :
        ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | spl4_6
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f116,f177])).

fof(f177,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f176])).

fof(f176,plain,
    ( spl4_15
  <=> v1_zfmisc_1(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f116,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0))
        | ~ v1_zfmisc_1(u1_struct_0(sK0)) )
    | spl4_6 ),
    inference(resolution,[],[f106,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | ~ v1_subset_1(k6_domain_1(X0,X1),X0)
      | ~ v1_zfmisc_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_zfmisc_1(X0)
          | ~ v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_zfmisc_1(X0)
          | ~ v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

fof(f106,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl4_6 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl4_6
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f371,plain,
    ( spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | spl4_30 ),
    inference(avatar_contradiction_clause,[],[f370])).

fof(f370,plain,
    ( $false
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | spl4_30 ),
    inference(subsumption_resolution,[],[f369,f75])).

fof(f75,plain,
    ( ~ v2_struct_0(sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl4_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f369,plain,
    ( v2_struct_0(sK0)
    | ~ spl4_2
    | ~ spl4_3
    | spl4_30 ),
    inference(subsumption_resolution,[],[f368,f89])).

fof(f368,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl4_2
    | spl4_30 ),
    inference(subsumption_resolution,[],[f367,f80])).

fof(f80,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl4_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f367,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | spl4_30 ),
    inference(resolution,[],[f364,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v7_struct_0(k1_tex_2(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).

fof(f364,plain,
    ( ~ v7_struct_0(k1_tex_2(sK0,sK1))
    | spl4_30 ),
    inference(avatar_component_clause,[],[f362])).

fof(f362,plain,
    ( spl4_30
  <=> v7_struct_0(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f365,plain,
    ( ~ spl4_30
    | ~ spl4_10
    | spl4_15
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f358,f227,f176,f137,f362])).

fof(f137,plain,
    ( spl4_10
  <=> l1_struct_0(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f227,plain,
    ( spl4_22
  <=> u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f358,plain,
    ( ~ v7_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl4_10
    | spl4_15
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f357,f138])).

fof(f138,plain,
    ( l1_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f137])).

fof(f357,plain,
    ( ~ l1_struct_0(k1_tex_2(sK0,sK1))
    | ~ v7_struct_0(k1_tex_2(sK0,sK1))
    | spl4_15
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f351,f178])).

fof(f178,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | spl4_15 ),
    inference(avatar_component_clause,[],[f176])).

fof(f351,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | ~ l1_struct_0(k1_tex_2(sK0,sK1))
    | ~ v7_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl4_22 ),
    inference(superposition,[],[f60,f229])).

fof(f229,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f227])).

fof(f60,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).

fof(f334,plain,
    ( ~ spl4_2
    | ~ spl4_4
    | ~ spl4_12
    | spl4_14
    | ~ spl4_21 ),
    inference(avatar_contradiction_clause,[],[f333])).

fof(f333,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_12
    | spl4_14
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f332,f94])).

fof(f94,plain,
    ( v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl4_4
  <=> v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f332,plain,
    ( ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ spl4_2
    | ~ spl4_12
    | spl4_14
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f331,f80])).

fof(f331,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ spl4_12
    | spl4_14
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f330,f224])).

fof(f224,plain,
    ( m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f223])).

fof(f223,plain,
    ( spl4_21
  <=> m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f330,plain,
    ( ~ m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ spl4_12
    | spl4_14 ),
    inference(subsumption_resolution,[],[f328,f148])).

fof(f148,plain,
    ( m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl4_12
  <=> m1_pre_topc(k1_tex_2(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f328,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | spl4_14 ),
    inference(resolution,[],[f171,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v1_tex_2(X1,X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | v1_subset_1(X2,u1_struct_0(X0))
      | ~ v1_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tex_2)).

fof(f171,plain,
    ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | spl4_14 ),
    inference(avatar_component_clause,[],[f169])).

fof(f169,plain,
    ( spl4_14
  <=> v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f323,plain,
    ( spl4_6
    | spl4_9
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_21 ),
    inference(avatar_contradiction_clause,[],[f322])).

fof(f322,plain,
    ( $false
    | spl4_6
    | spl4_9
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f321,f224])).

fof(f321,plain,
    ( ~ m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_6
    | spl4_9
    | ~ spl4_14
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f316,f135])).

fof(f135,plain,
    ( ~ v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))
    | spl4_9 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl4_9
  <=> v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f316,plain,
    ( v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))
    | ~ m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_6
    | ~ spl4_14
    | ~ spl4_15 ),
    inference(resolution,[],[f309,f170])).

fof(f170,plain,
    ( v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f169])).

fof(f309,plain,
    ( ! [X0] :
        ( ~ v1_subset_1(X0,u1_struct_0(sK0))
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl4_6
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f115,f177])).

fof(f115,plain,
    ( ! [X0] :
        ( ~ v1_zfmisc_1(u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X0)
        | ~ v1_subset_1(X0,u1_struct_0(sK0)) )
    | spl4_6 ),
    inference(resolution,[],[f106,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ v1_zfmisc_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | ~ v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( ~ v1_xboole_0(X1)
           => ~ v1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).

fof(f289,plain,
    ( ~ spl4_3
    | spl4_6
    | spl4_15
    | ~ spl4_26 ),
    inference(avatar_contradiction_clause,[],[f288])).

fof(f288,plain,
    ( $false
    | ~ spl4_3
    | spl4_6
    | spl4_15
    | ~ spl4_26 ),
    inference(subsumption_resolution,[],[f287,f89])).

fof(f287,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | spl4_6
    | spl4_15
    | ~ spl4_26 ),
    inference(trivial_inequality_removal,[],[f285])).

fof(f285,plain,
    ( u1_struct_0(sK0) != u1_struct_0(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | spl4_6
    | spl4_15
    | ~ spl4_26 ),
    inference(superposition,[],[f187,f278])).

fof(f278,plain,
    ( u1_struct_0(sK0) = k6_domain_1(u1_struct_0(sK0),sK1)
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f276])).

fof(f276,plain,
    ( spl4_26
  <=> u1_struct_0(sK0) = k6_domain_1(u1_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f187,plain,
    ( ! [X0] :
        ( u1_struct_0(sK0) != k6_domain_1(u1_struct_0(sK0),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | spl4_6
    | spl4_15 ),
    inference(subsumption_resolution,[],[f185,f106])).

fof(f185,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | u1_struct_0(sK0) != k6_domain_1(u1_struct_0(sK0),X0)
        | v1_xboole_0(u1_struct_0(sK0)) )
    | spl4_15 ),
    inference(resolution,[],[f178,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_zfmisc_1(X0)
      | ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) != X0
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).

fof(f283,plain,
    ( ~ spl4_3
    | spl4_6
    | spl4_25 ),
    inference(avatar_contradiction_clause,[],[f282])).

fof(f282,plain,
    ( $false
    | ~ spl4_3
    | spl4_6
    | spl4_25 ),
    inference(subsumption_resolution,[],[f281,f106])).

fof(f281,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl4_3
    | spl4_25 ),
    inference(subsumption_resolution,[],[f280,f89])).

fof(f280,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | spl4_25 ),
    inference(resolution,[],[f274,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f274,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_25 ),
    inference(avatar_component_clause,[],[f272])).

fof(f272,plain,
    ( spl4_25
  <=> m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f279,plain,
    ( ~ spl4_25
    | spl4_26
    | spl4_5 ),
    inference(avatar_split_clause,[],[f266,f96,f276,f272])).

fof(f266,plain,
    ( u1_struct_0(sK0) = k6_domain_1(u1_struct_0(sK0),sK1)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_5 ),
    inference(resolution,[],[f97,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

fof(f97,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f96])).

fof(f264,plain,
    ( ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_contradiction_clause,[],[f263])).

fof(f263,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f262,f94])).

fof(f262,plain,
    ( ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f42,f98])).

fof(f42,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f18])).

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
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( v1_tex_2(k1_tex_2(X0,X1),X0)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_tex_2)).

fof(f235,plain,
    ( ~ spl4_2
    | ~ spl4_12
    | spl4_21 ),
    inference(avatar_contradiction_clause,[],[f234])).

fof(f234,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_12
    | spl4_21 ),
    inference(subsumption_resolution,[],[f233,f80])).

fof(f233,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl4_12
    | spl4_21 ),
    inference(subsumption_resolution,[],[f232,f148])).

fof(f232,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | spl4_21 ),
    inference(resolution,[],[f225,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f225,plain,
    ( ~ m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_21 ),
    inference(avatar_component_clause,[],[f223])).

fof(f230,plain,
    ( ~ spl4_21
    | spl4_22
    | spl4_14 ),
    inference(avatar_split_clause,[],[f174,f169,f227,f223])).

fof(f174,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))
    | ~ m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_14 ),
    inference(resolution,[],[f171,f61])).

fof(f203,plain,
    ( spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | spl4_13 ),
    inference(avatar_contradiction_clause,[],[f202])).

fof(f202,plain,
    ( $false
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | spl4_13 ),
    inference(subsumption_resolution,[],[f201,f89])).

fof(f201,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | spl4_1
    | ~ spl4_2
    | spl4_13 ),
    inference(subsumption_resolution,[],[f198,f80])).

fof(f198,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | spl4_1
    | ~ spl4_2
    | spl4_13 ),
    inference(resolution,[],[f159,f127])).

fof(f127,plain,
    ( ! [X1] :
        ( m1_pre_topc(k1_tex_2(sK0,X1),sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f83,f80])).

fof(f83,plain,
    ( ! [X1] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | m1_pre_topc(k1_tex_2(sK0,X1),sK0) )
    | spl4_1 ),
    inference(resolution,[],[f75,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | m1_pre_topc(k1_tex_2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).

fof(f159,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k1_tex_2(sK0,sK1),X0)
        | ~ l1_pre_topc(X0) )
    | spl4_13 ),
    inference(resolution,[],[f154,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f154,plain,
    ( ~ l1_pre_topc(k1_tex_2(sK0,sK1))
    | spl4_13 ),
    inference(avatar_component_clause,[],[f152])).

fof(f152,plain,
    ( spl4_13
  <=> l1_pre_topc(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f172,plain,
    ( ~ spl4_14
    | ~ spl4_2
    | spl4_4
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f164,f147,f143,f92,f78,f169])).

fof(f143,plain,
    ( spl4_11
  <=> u1_struct_0(k1_tex_2(sK0,sK1)) = sK3(sK0,k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f164,plain,
    ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl4_2
    | spl4_4
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f163,f93])).

fof(f93,plain,
    ( ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f92])).

fof(f163,plain,
    ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ spl4_2
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f162,f80])).

fof(f162,plain,
    ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f161,f148])).

fof(f161,plain,
    ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ spl4_11 ),
    inference(superposition,[],[f56,f145])).

fof(f145,plain,
    ( u1_struct_0(k1_tex_2(sK0,sK1)) = sK3(sK0,k1_tex_2(sK0,sK1))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f143])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(sK3(X0,X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v1_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f158,plain,
    ( spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | spl4_12 ),
    inference(avatar_contradiction_clause,[],[f157])).

fof(f157,plain,
    ( $false
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | spl4_12 ),
    inference(subsumption_resolution,[],[f156,f89])).

fof(f156,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | spl4_1
    | ~ spl4_2
    | spl4_12 ),
    inference(resolution,[],[f149,f127])).

fof(f149,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | spl4_12 ),
    inference(avatar_component_clause,[],[f147])).

fof(f155,plain,
    ( ~ spl4_13
    | spl4_10 ),
    inference(avatar_split_clause,[],[f141,f137,f152])).

fof(f141,plain,
    ( ~ l1_pre_topc(k1_tex_2(sK0,sK1))
    | spl4_10 ),
    inference(resolution,[],[f139,f50])).

fof(f50,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f139,plain,
    ( ~ l1_struct_0(k1_tex_2(sK0,sK1))
    | spl4_10 ),
    inference(avatar_component_clause,[],[f137])).

fof(f150,plain,
    ( spl4_11
    | ~ spl4_12
    | ~ spl4_2
    | spl4_4 ),
    inference(avatar_split_clause,[],[f101,f92,f78,f147,f143])).

fof(f101,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | u1_struct_0(k1_tex_2(sK0,sK1)) = sK3(sK0,k1_tex_2(sK0,sK1))
    | ~ spl4_2
    | spl4_4 ),
    inference(subsumption_resolution,[],[f100,f80])).

fof(f100,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | u1_struct_0(k1_tex_2(sK0,sK1)) = sK3(sK0,k1_tex_2(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | spl4_4 ),
    inference(resolution,[],[f93,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | u1_struct_0(X1) = sK3(X0,X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f140,plain,
    ( ~ spl4_9
    | ~ spl4_10
    | spl4_8 ),
    inference(avatar_split_clause,[],[f131,f123,f137,f133])).

fof(f123,plain,
    ( spl4_8
  <=> v2_struct_0(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f131,plain,
    ( ~ l1_struct_0(k1_tex_2(sK0,sK1))
    | ~ v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))
    | spl4_8 ),
    inference(resolution,[],[f125,f58])).

fof(f58,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f125,plain,
    ( ~ v2_struct_0(k1_tex_2(sK0,sK1))
    | spl4_8 ),
    inference(avatar_component_clause,[],[f123])).

fof(f126,plain,
    ( ~ spl4_8
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f119,f87,f78,f73,f123])).

fof(f119,plain,
    ( ~ v2_struct_0(k1_tex_2(sK0,sK1))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(resolution,[],[f118,f89])).

fof(f118,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v2_struct_0(k1_tex_2(sK0,X0)) )
    | spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f82,f80])).

fof(f82,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v2_struct_0(k1_tex_2(sK0,X0)) )
    | spl4_1 ),
    inference(resolution,[],[f75,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v2_struct_0(k1_tex_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f114,plain,
    ( ~ spl4_2
    | spl4_7 ),
    inference(avatar_contradiction_clause,[],[f113])).

fof(f113,plain,
    ( $false
    | ~ spl4_2
    | spl4_7 ),
    inference(subsumption_resolution,[],[f112,f80])).

fof(f112,plain,
    ( ~ l1_pre_topc(sK0)
    | spl4_7 ),
    inference(resolution,[],[f110,f50])).

fof(f110,plain,
    ( ~ l1_struct_0(sK0)
    | spl4_7 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl4_7
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f111,plain,
    ( ~ spl4_6
    | ~ spl4_7
    | spl4_1 ),
    inference(avatar_split_clause,[],[f85,f73,f108,f104])).

fof(f85,plain,
    ( ~ l1_struct_0(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0))
    | spl4_1 ),
    inference(resolution,[],[f75,f58])).

fof(f99,plain,
    ( spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f41,f96,f92])).

fof(f41,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f90,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f43,f87])).

fof(f43,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f81,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f45,f78])).

fof(f45,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f76,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f44,f73])).

fof(f44,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n017.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 12:17:01 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.47  % (16586)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.48  % (16584)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.48  % (16592)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.49  % (16584)Refutation not found, incomplete strategy% (16584)------------------------------
% 0.22/0.49  % (16584)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (16584)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (16584)Memory used [KB]: 10618
% 0.22/0.49  % (16584)Time elapsed: 0.070 s
% 0.22/0.49  % (16584)------------------------------
% 0.22/0.49  % (16584)------------------------------
% 0.22/0.49  % (16586)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % (16594)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f389,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f76,f81,f90,f99,f111,f114,f126,f140,f150,f155,f158,f172,f203,f230,f235,f264,f279,f283,f289,f323,f334,f365,f371,f388])).
% 0.22/0.49  fof(f388,plain,(
% 0.22/0.49    ~spl4_3 | ~spl4_5 | spl4_6 | ~spl4_15),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f387])).
% 0.22/0.49  fof(f387,plain,(
% 0.22/0.49    $false | (~spl4_3 | ~spl4_5 | spl4_6 | ~spl4_15)),
% 0.22/0.49    inference(subsumption_resolution,[],[f384,f89])).
% 0.22/0.49  fof(f89,plain,(
% 0.22/0.49    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl4_3),
% 0.22/0.49    inference(avatar_component_clause,[],[f87])).
% 0.22/0.49  fof(f87,plain,(
% 0.22/0.49    spl4_3 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.49  fof(f384,plain,(
% 0.22/0.49    ~m1_subset_1(sK1,u1_struct_0(sK0)) | (~spl4_5 | spl4_6 | ~spl4_15)),
% 0.22/0.49    inference(resolution,[],[f383,f98])).
% 0.22/0.49  fof(f98,plain,(
% 0.22/0.49    v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~spl4_5),
% 0.22/0.49    inference(avatar_component_clause,[],[f96])).
% 0.22/0.49  fof(f96,plain,(
% 0.22/0.49    spl4_5 <=> v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.49  fof(f383,plain,(
% 0.22/0.49    ( ! [X1] : (~v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | (spl4_6 | ~spl4_15)),
% 0.22/0.49    inference(subsumption_resolution,[],[f116,f177])).
% 0.22/0.49  fof(f177,plain,(
% 0.22/0.49    v1_zfmisc_1(u1_struct_0(sK0)) | ~spl4_15),
% 0.22/0.49    inference(avatar_component_clause,[],[f176])).
% 0.22/0.49  fof(f176,plain,(
% 0.22/0.49    spl4_15 <=> v1_zfmisc_1(u1_struct_0(sK0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.22/0.49  fof(f116,plain,(
% 0.22/0.49    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0)) | ~v1_zfmisc_1(u1_struct_0(sK0))) ) | spl4_6),
% 0.22/0.49    inference(resolution,[],[f106,f49])).
% 0.22/0.49  fof(f49,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | ~v1_subset_1(k6_domain_1(X0,X1),X0) | ~v1_zfmisc_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (~v1_zfmisc_1(X0) | ~v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | v1_xboole_0(X0))),
% 0.22/0.49    inference(flattening,[],[f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : ((~v1_zfmisc_1(X0) | ~v1_subset_1(k6_domain_1(X0,X1),X0)) | ~m1_subset_1(X1,X0)) | v1_xboole_0(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,axiom,(
% 0.22/0.49    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).
% 0.22/0.49  fof(f106,plain,(
% 0.22/0.49    ~v1_xboole_0(u1_struct_0(sK0)) | spl4_6),
% 0.22/0.49    inference(avatar_component_clause,[],[f104])).
% 0.22/0.49  fof(f104,plain,(
% 0.22/0.49    spl4_6 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.49  fof(f371,plain,(
% 0.22/0.49    spl4_1 | ~spl4_2 | ~spl4_3 | spl4_30),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f370])).
% 0.22/0.49  fof(f370,plain,(
% 0.22/0.49    $false | (spl4_1 | ~spl4_2 | ~spl4_3 | spl4_30)),
% 0.22/0.49    inference(subsumption_resolution,[],[f369,f75])).
% 0.22/0.49  fof(f75,plain,(
% 0.22/0.49    ~v2_struct_0(sK0) | spl4_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f73])).
% 0.22/0.49  fof(f73,plain,(
% 0.22/0.49    spl4_1 <=> v2_struct_0(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.49  fof(f369,plain,(
% 0.22/0.49    v2_struct_0(sK0) | (~spl4_2 | ~spl4_3 | spl4_30)),
% 0.22/0.49    inference(subsumption_resolution,[],[f368,f89])).
% 0.22/0.49  fof(f368,plain,(
% 0.22/0.49    ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | (~spl4_2 | spl4_30)),
% 0.22/0.49    inference(subsumption_resolution,[],[f367,f80])).
% 0.22/0.49  fof(f80,plain,(
% 0.22/0.49    l1_pre_topc(sK0) | ~spl4_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f78])).
% 0.22/0.49  fof(f78,plain,(
% 0.22/0.49    spl4_2 <=> l1_pre_topc(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.49  fof(f367,plain,(
% 0.22/0.49    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | spl4_30),
% 0.22/0.49    inference(resolution,[],[f364,f64])).
% 0.22/0.49  fof(f64,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v7_struct_0(k1_tex_2(X0,X1)) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f36])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    ! [X0,X1] : ((v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f35])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    ! [X0,X1] : ((v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f13])).
% 0.22/0.49  fof(f13,axiom,(
% 0.22/0.49    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).
% 0.22/0.49  fof(f364,plain,(
% 0.22/0.49    ~v7_struct_0(k1_tex_2(sK0,sK1)) | spl4_30),
% 0.22/0.49    inference(avatar_component_clause,[],[f362])).
% 0.22/0.49  fof(f362,plain,(
% 0.22/0.49    spl4_30 <=> v7_struct_0(k1_tex_2(sK0,sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 0.22/0.49  fof(f365,plain,(
% 0.22/0.49    ~spl4_30 | ~spl4_10 | spl4_15 | ~spl4_22),
% 0.22/0.49    inference(avatar_split_clause,[],[f358,f227,f176,f137,f362])).
% 0.22/0.49  fof(f137,plain,(
% 0.22/0.49    spl4_10 <=> l1_struct_0(k1_tex_2(sK0,sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.22/0.49  fof(f227,plain,(
% 0.22/0.49    spl4_22 <=> u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.22/0.49  fof(f358,plain,(
% 0.22/0.49    ~v7_struct_0(k1_tex_2(sK0,sK1)) | (~spl4_10 | spl4_15 | ~spl4_22)),
% 0.22/0.49    inference(subsumption_resolution,[],[f357,f138])).
% 0.22/0.49  fof(f138,plain,(
% 0.22/0.49    l1_struct_0(k1_tex_2(sK0,sK1)) | ~spl4_10),
% 0.22/0.49    inference(avatar_component_clause,[],[f137])).
% 0.22/0.49  fof(f357,plain,(
% 0.22/0.49    ~l1_struct_0(k1_tex_2(sK0,sK1)) | ~v7_struct_0(k1_tex_2(sK0,sK1)) | (spl4_15 | ~spl4_22)),
% 0.22/0.49    inference(subsumption_resolution,[],[f351,f178])).
% 0.22/0.49  fof(f178,plain,(
% 0.22/0.49    ~v1_zfmisc_1(u1_struct_0(sK0)) | spl4_15),
% 0.22/0.49    inference(avatar_component_clause,[],[f176])).
% 0.22/0.49  fof(f351,plain,(
% 0.22/0.49    v1_zfmisc_1(u1_struct_0(sK0)) | ~l1_struct_0(k1_tex_2(sK0,sK1)) | ~v7_struct_0(k1_tex_2(sK0,sK1)) | ~spl4_22),
% 0.22/0.49    inference(superposition,[],[f60,f229])).
% 0.22/0.49  fof(f229,plain,(
% 0.22/0.49    u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) | ~spl4_22),
% 0.22/0.49    inference(avatar_component_clause,[],[f227])).
% 0.22/0.49  fof(f60,plain,(
% 0.22/0.49    ( ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f33])).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f32])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).
% 0.22/0.49  fof(f334,plain,(
% 0.22/0.49    ~spl4_2 | ~spl4_4 | ~spl4_12 | spl4_14 | ~spl4_21),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f333])).
% 0.22/0.49  fof(f333,plain,(
% 0.22/0.49    $false | (~spl4_2 | ~spl4_4 | ~spl4_12 | spl4_14 | ~spl4_21)),
% 0.22/0.49    inference(subsumption_resolution,[],[f332,f94])).
% 0.22/0.49  fof(f94,plain,(
% 0.22/0.49    v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~spl4_4),
% 0.22/0.49    inference(avatar_component_clause,[],[f92])).
% 0.22/0.49  fof(f92,plain,(
% 0.22/0.49    spl4_4 <=> v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.49  fof(f332,plain,(
% 0.22/0.49    ~v1_tex_2(k1_tex_2(sK0,sK1),sK0) | (~spl4_2 | ~spl4_12 | spl4_14 | ~spl4_21)),
% 0.22/0.49    inference(subsumption_resolution,[],[f331,f80])).
% 0.22/0.49  fof(f331,plain,(
% 0.22/0.49    ~l1_pre_topc(sK0) | ~v1_tex_2(k1_tex_2(sK0,sK1),sK0) | (~spl4_12 | spl4_14 | ~spl4_21)),
% 0.22/0.49    inference(subsumption_resolution,[],[f330,f224])).
% 0.22/0.49  fof(f224,plain,(
% 0.22/0.49    m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_21),
% 0.22/0.49    inference(avatar_component_clause,[],[f223])).
% 0.22/0.49  fof(f223,plain,(
% 0.22/0.49    spl4_21 <=> m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.22/0.49  fof(f330,plain,(
% 0.22/0.49    ~m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v1_tex_2(k1_tex_2(sK0,sK1),sK0) | (~spl4_12 | spl4_14)),
% 0.22/0.49    inference(subsumption_resolution,[],[f328,f148])).
% 0.22/0.49  fof(f148,plain,(
% 0.22/0.49    m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~spl4_12),
% 0.22/0.49    inference(avatar_component_clause,[],[f147])).
% 0.22/0.49  fof(f147,plain,(
% 0.22/0.49    spl4_12 <=> m1_pre_topc(k1_tex_2(sK0,sK1),sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.22/0.49  fof(f328,plain,(
% 0.22/0.49    ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v1_tex_2(k1_tex_2(sK0,sK1),sK0) | spl4_14),
% 0.22/0.49    inference(resolution,[],[f171,f70])).
% 0.22/0.49  fof(f70,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v1_tex_2(X1,X0)) )),
% 0.22/0.49    inference(equality_resolution,[],[f53])).
% 0.22/0.49  fof(f53,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X2 | v1_subset_1(X2,u1_struct_0(X0)) | ~v1_tex_2(X1,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f26])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(flattening,[],[f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,axiom,(
% 0.22/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v1_subset_1(X2,u1_struct_0(X0)))))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tex_2)).
% 0.22/0.49  fof(f171,plain,(
% 0.22/0.49    ~v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | spl4_14),
% 0.22/0.49    inference(avatar_component_clause,[],[f169])).
% 0.22/0.49  fof(f169,plain,(
% 0.22/0.49    spl4_14 <=> v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.22/0.49  fof(f323,plain,(
% 0.22/0.49    spl4_6 | spl4_9 | ~spl4_14 | ~spl4_15 | ~spl4_21),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f322])).
% 0.22/0.49  fof(f322,plain,(
% 0.22/0.49    $false | (spl4_6 | spl4_9 | ~spl4_14 | ~spl4_15 | ~spl4_21)),
% 0.22/0.49    inference(subsumption_resolution,[],[f321,f224])).
% 0.22/0.49  fof(f321,plain,(
% 0.22/0.49    ~m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | (spl4_6 | spl4_9 | ~spl4_14 | ~spl4_15)),
% 0.22/0.49    inference(subsumption_resolution,[],[f316,f135])).
% 0.22/0.49  fof(f135,plain,(
% 0.22/0.49    ~v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) | spl4_9),
% 0.22/0.49    inference(avatar_component_clause,[],[f133])).
% 0.22/0.49  fof(f133,plain,(
% 0.22/0.49    spl4_9 <=> v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.22/0.49  fof(f316,plain,(
% 0.22/0.49    v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) | ~m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | (spl4_6 | ~spl4_14 | ~spl4_15)),
% 0.22/0.49    inference(resolution,[],[f309,f170])).
% 0.22/0.49  fof(f170,plain,(
% 0.22/0.49    v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | ~spl4_14),
% 0.22/0.49    inference(avatar_component_clause,[],[f169])).
% 0.22/0.49  fof(f309,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_subset_1(X0,u1_struct_0(sK0)) | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (spl4_6 | ~spl4_15)),
% 0.22/0.49    inference(subsumption_resolution,[],[f115,f177])).
% 0.22/0.49  fof(f115,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_zfmisc_1(u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X0) | ~v1_subset_1(X0,u1_struct_0(sK0))) ) | spl4_6),
% 0.22/0.49    inference(resolution,[],[f106,f59])).
% 0.22/0.49  fof(f59,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v1_xboole_0(X0) | ~v1_zfmisc_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | ~v1_subset_1(X1,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f31])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 0.22/0.49    inference(flattening,[],[f30])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : ((~v1_subset_1(X1,X0) | v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | (~v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,axiom,(
% 0.22/0.49    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (~v1_xboole_0(X1) => ~v1_subset_1(X1,X0))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).
% 0.22/0.49  fof(f289,plain,(
% 0.22/0.49    ~spl4_3 | spl4_6 | spl4_15 | ~spl4_26),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f288])).
% 0.22/0.49  fof(f288,plain,(
% 0.22/0.49    $false | (~spl4_3 | spl4_6 | spl4_15 | ~spl4_26)),
% 0.22/0.49    inference(subsumption_resolution,[],[f287,f89])).
% 0.22/0.49  fof(f287,plain,(
% 0.22/0.49    ~m1_subset_1(sK1,u1_struct_0(sK0)) | (spl4_6 | spl4_15 | ~spl4_26)),
% 0.22/0.49    inference(trivial_inequality_removal,[],[f285])).
% 0.22/0.49  fof(f285,plain,(
% 0.22/0.49    u1_struct_0(sK0) != u1_struct_0(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | (spl4_6 | spl4_15 | ~spl4_26)),
% 0.22/0.49    inference(superposition,[],[f187,f278])).
% 0.22/0.49  fof(f278,plain,(
% 0.22/0.49    u1_struct_0(sK0) = k6_domain_1(u1_struct_0(sK0),sK1) | ~spl4_26),
% 0.22/0.49    inference(avatar_component_clause,[],[f276])).
% 0.22/0.49  fof(f276,plain,(
% 0.22/0.49    spl4_26 <=> u1_struct_0(sK0) = k6_domain_1(u1_struct_0(sK0),sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.22/0.49  fof(f187,plain,(
% 0.22/0.49    ( ! [X0] : (u1_struct_0(sK0) != k6_domain_1(u1_struct_0(sK0),X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (spl4_6 | spl4_15)),
% 0.22/0.49    inference(subsumption_resolution,[],[f185,f106])).
% 0.22/0.49  fof(f185,plain,(
% 0.22/0.49    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | u1_struct_0(sK0) != k6_domain_1(u1_struct_0(sK0),X0) | v1_xboole_0(u1_struct_0(sK0))) ) | spl4_15),
% 0.22/0.49    inference(resolution,[],[f178,f48])).
% 0.22/0.49  fof(f48,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v1_zfmisc_1(X0) | ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) != X0 | v1_xboole_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ! [X0] : ((v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))) | v1_xboole_0(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,axiom,(
% 0.22/0.49    ! [X0] : (~v1_xboole_0(X0) => (v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).
% 0.22/0.49  fof(f283,plain,(
% 0.22/0.49    ~spl4_3 | spl4_6 | spl4_25),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f282])).
% 0.22/0.49  fof(f282,plain,(
% 0.22/0.49    $false | (~spl4_3 | spl4_6 | spl4_25)),
% 0.22/0.49    inference(subsumption_resolution,[],[f281,f106])).
% 0.22/0.49  fof(f281,plain,(
% 0.22/0.49    v1_xboole_0(u1_struct_0(sK0)) | (~spl4_3 | spl4_25)),
% 0.22/0.49    inference(subsumption_resolution,[],[f280,f89])).
% 0.22/0.49  fof(f280,plain,(
% 0.22/0.49    ~m1_subset_1(sK1,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | spl4_25),
% 0.22/0.49    inference(resolution,[],[f274,f69])).
% 0.22/0.49  fof(f69,plain,(
% 0.22/0.49    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f40])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.22/0.49    inference(flattening,[],[f39])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.22/0.49  fof(f274,plain,(
% 0.22/0.49    ~m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl4_25),
% 0.22/0.49    inference(avatar_component_clause,[],[f272])).
% 0.22/0.49  fof(f272,plain,(
% 0.22/0.49    spl4_25 <=> m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.22/0.49  fof(f279,plain,(
% 0.22/0.49    ~spl4_25 | spl4_26 | spl4_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f266,f96,f276,f272])).
% 0.22/0.49  fof(f266,plain,(
% 0.22/0.49    u1_struct_0(sK0) = k6_domain_1(u1_struct_0(sK0),sK1) | ~m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl4_5),
% 0.22/0.49    inference(resolution,[],[f97,f61])).
% 0.22/0.49  fof(f61,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f34])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f11])).
% 0.22/0.49  fof(f11,axiom,(
% 0.22/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).
% 0.22/0.49  fof(f97,plain,(
% 0.22/0.49    ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | spl4_5),
% 0.22/0.49    inference(avatar_component_clause,[],[f96])).
% 0.22/0.49  fof(f264,plain,(
% 0.22/0.49    ~spl4_4 | ~spl4_5),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f263])).
% 0.22/0.49  fof(f263,plain,(
% 0.22/0.49    $false | (~spl4_4 | ~spl4_5)),
% 0.22/0.49    inference(subsumption_resolution,[],[f262,f94])).
% 0.22/0.49  fof(f262,plain,(
% 0.22/0.49    ~v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~spl4_5),
% 0.22/0.49    inference(subsumption_resolution,[],[f42,f98])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f16])).
% 0.22/0.49  fof(f16,negated_conjecture,(
% 0.22/0.49    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 0.22/0.49    inference(negated_conjecture,[],[f15])).
% 0.22/0.49  fof(f15,conjecture,(
% 0.22/0.49    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_tex_2)).
% 0.22/0.49  fof(f235,plain,(
% 0.22/0.49    ~spl4_2 | ~spl4_12 | spl4_21),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f234])).
% 0.22/0.49  fof(f234,plain,(
% 0.22/0.49    $false | (~spl4_2 | ~spl4_12 | spl4_21)),
% 0.22/0.49    inference(subsumption_resolution,[],[f233,f80])).
% 0.22/0.49  fof(f233,plain,(
% 0.22/0.49    ~l1_pre_topc(sK0) | (~spl4_12 | spl4_21)),
% 0.22/0.49    inference(subsumption_resolution,[],[f232,f148])).
% 0.22/0.49  fof(f232,plain,(
% 0.22/0.49    ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | spl4_21),
% 0.22/0.49    inference(resolution,[],[f225,f52])).
% 0.22/0.49  fof(f52,plain,(
% 0.22/0.49    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.22/0.49  fof(f225,plain,(
% 0.22/0.49    ~m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | spl4_21),
% 0.22/0.49    inference(avatar_component_clause,[],[f223])).
% 0.22/0.49  fof(f230,plain,(
% 0.22/0.49    ~spl4_21 | spl4_22 | spl4_14),
% 0.22/0.49    inference(avatar_split_clause,[],[f174,f169,f227,f223])).
% 0.22/0.49  fof(f174,plain,(
% 0.22/0.49    u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) | ~m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | spl4_14),
% 0.22/0.49    inference(resolution,[],[f171,f61])).
% 0.22/0.49  fof(f203,plain,(
% 0.22/0.49    spl4_1 | ~spl4_2 | ~spl4_3 | spl4_13),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f202])).
% 0.22/0.49  fof(f202,plain,(
% 0.22/0.49    $false | (spl4_1 | ~spl4_2 | ~spl4_3 | spl4_13)),
% 0.22/0.49    inference(subsumption_resolution,[],[f201,f89])).
% 0.22/0.49  fof(f201,plain,(
% 0.22/0.49    ~m1_subset_1(sK1,u1_struct_0(sK0)) | (spl4_1 | ~spl4_2 | spl4_13)),
% 0.22/0.49    inference(subsumption_resolution,[],[f198,f80])).
% 0.22/0.49  fof(f198,plain,(
% 0.22/0.49    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | (spl4_1 | ~spl4_2 | spl4_13)),
% 0.22/0.49    inference(resolution,[],[f159,f127])).
% 0.22/0.49  fof(f127,plain,(
% 0.22/0.49    ( ! [X1] : (m1_pre_topc(k1_tex_2(sK0,X1),sK0) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | (spl4_1 | ~spl4_2)),
% 0.22/0.49    inference(subsumption_resolution,[],[f83,f80])).
% 0.22/0.49  fof(f83,plain,(
% 0.22/0.49    ( ! [X1] : (~l1_pre_topc(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | m1_pre_topc(k1_tex_2(sK0,X1),sK0)) ) | spl4_1),
% 0.22/0.49    inference(resolution,[],[f75,f68])).
% 0.22/0.49  fof(f68,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | m1_pre_topc(k1_tex_2(X0,X1),X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f38])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f37])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f12])).
% 0.22/0.49  fof(f12,axiom,(
% 0.22/0.49    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).
% 0.22/0.49  fof(f159,plain,(
% 0.22/0.49    ( ! [X0] : (~m1_pre_topc(k1_tex_2(sK0,sK1),X0) | ~l1_pre_topc(X0)) ) | spl4_13),
% 0.22/0.49    inference(resolution,[],[f154,f51])).
% 0.22/0.49  fof(f51,plain,(
% 0.22/0.49    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f23])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.22/0.49  fof(f154,plain,(
% 0.22/0.49    ~l1_pre_topc(k1_tex_2(sK0,sK1)) | spl4_13),
% 0.22/0.49    inference(avatar_component_clause,[],[f152])).
% 0.22/0.49  fof(f152,plain,(
% 0.22/0.49    spl4_13 <=> l1_pre_topc(k1_tex_2(sK0,sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.22/0.49  fof(f172,plain,(
% 0.22/0.49    ~spl4_14 | ~spl4_2 | spl4_4 | ~spl4_11 | ~spl4_12),
% 0.22/0.49    inference(avatar_split_clause,[],[f164,f147,f143,f92,f78,f169])).
% 0.22/0.49  fof(f143,plain,(
% 0.22/0.49    spl4_11 <=> u1_struct_0(k1_tex_2(sK0,sK1)) = sK3(sK0,k1_tex_2(sK0,sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.22/0.49  fof(f164,plain,(
% 0.22/0.49    ~v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | (~spl4_2 | spl4_4 | ~spl4_11 | ~spl4_12)),
% 0.22/0.49    inference(subsumption_resolution,[],[f163,f93])).
% 0.22/0.49  fof(f93,plain,(
% 0.22/0.49    ~v1_tex_2(k1_tex_2(sK0,sK1),sK0) | spl4_4),
% 0.22/0.49    inference(avatar_component_clause,[],[f92])).
% 0.22/0.49  fof(f163,plain,(
% 0.22/0.49    ~v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0) | (~spl4_2 | ~spl4_11 | ~spl4_12)),
% 0.22/0.49    inference(subsumption_resolution,[],[f162,f80])).
% 0.22/0.49  fof(f162,plain,(
% 0.22/0.49    ~v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | v1_tex_2(k1_tex_2(sK0,sK1),sK0) | (~spl4_11 | ~spl4_12)),
% 0.22/0.49    inference(subsumption_resolution,[],[f161,f148])).
% 0.22/0.49  fof(f161,plain,(
% 0.22/0.49    ~v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~spl4_11),
% 0.22/0.49    inference(superposition,[],[f56,f145])).
% 0.22/0.49  fof(f145,plain,(
% 0.22/0.49    u1_struct_0(k1_tex_2(sK0,sK1)) = sK3(sK0,k1_tex_2(sK0,sK1)) | ~spl4_11),
% 0.22/0.49    inference(avatar_component_clause,[],[f143])).
% 0.22/0.49  fof(f56,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v1_subset_1(sK3(X0,X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v1_tex_2(X1,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f26])).
% 0.22/0.49  fof(f158,plain,(
% 0.22/0.49    spl4_1 | ~spl4_2 | ~spl4_3 | spl4_12),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f157])).
% 0.22/0.49  fof(f157,plain,(
% 0.22/0.49    $false | (spl4_1 | ~spl4_2 | ~spl4_3 | spl4_12)),
% 0.22/0.49    inference(subsumption_resolution,[],[f156,f89])).
% 0.22/0.49  fof(f156,plain,(
% 0.22/0.49    ~m1_subset_1(sK1,u1_struct_0(sK0)) | (spl4_1 | ~spl4_2 | spl4_12)),
% 0.22/0.49    inference(resolution,[],[f149,f127])).
% 0.22/0.49  fof(f149,plain,(
% 0.22/0.49    ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | spl4_12),
% 0.22/0.49    inference(avatar_component_clause,[],[f147])).
% 0.22/0.49  fof(f155,plain,(
% 0.22/0.49    ~spl4_13 | spl4_10),
% 0.22/0.49    inference(avatar_split_clause,[],[f141,f137,f152])).
% 0.22/0.49  fof(f141,plain,(
% 0.22/0.49    ~l1_pre_topc(k1_tex_2(sK0,sK1)) | spl4_10),
% 0.22/0.49    inference(resolution,[],[f139,f50])).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.49  fof(f139,plain,(
% 0.22/0.49    ~l1_struct_0(k1_tex_2(sK0,sK1)) | spl4_10),
% 0.22/0.49    inference(avatar_component_clause,[],[f137])).
% 0.22/0.49  fof(f150,plain,(
% 0.22/0.49    spl4_11 | ~spl4_12 | ~spl4_2 | spl4_4),
% 0.22/0.49    inference(avatar_split_clause,[],[f101,f92,f78,f147,f143])).
% 0.22/0.49  fof(f101,plain,(
% 0.22/0.49    ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | u1_struct_0(k1_tex_2(sK0,sK1)) = sK3(sK0,k1_tex_2(sK0,sK1)) | (~spl4_2 | spl4_4)),
% 0.22/0.49    inference(subsumption_resolution,[],[f100,f80])).
% 0.22/0.49  fof(f100,plain,(
% 0.22/0.49    ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | u1_struct_0(k1_tex_2(sK0,sK1)) = sK3(sK0,k1_tex_2(sK0,sK1)) | ~l1_pre_topc(sK0) | spl4_4),
% 0.22/0.49    inference(resolution,[],[f93,f55])).
% 0.22/0.49  fof(f55,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | u1_struct_0(X1) = sK3(X0,X1) | ~l1_pre_topc(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f26])).
% 0.22/0.49  fof(f140,plain,(
% 0.22/0.49    ~spl4_9 | ~spl4_10 | spl4_8),
% 0.22/0.49    inference(avatar_split_clause,[],[f131,f123,f137,f133])).
% 0.22/0.49  fof(f123,plain,(
% 0.22/0.49    spl4_8 <=> v2_struct_0(k1_tex_2(sK0,sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.22/0.50  fof(f131,plain,(
% 0.22/0.50    ~l1_struct_0(k1_tex_2(sK0,sK1)) | ~v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) | spl4_8),
% 0.22/0.50    inference(resolution,[],[f125,f58])).
% 0.22/0.50  fof(f58,plain,(
% 0.22/0.50    ( ! [X0] : (v2_struct_0(X0) | ~l1_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f29])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f28])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.22/0.50  fof(f125,plain,(
% 0.22/0.50    ~v2_struct_0(k1_tex_2(sK0,sK1)) | spl4_8),
% 0.22/0.50    inference(avatar_component_clause,[],[f123])).
% 0.22/0.50  fof(f126,plain,(
% 0.22/0.50    ~spl4_8 | spl4_1 | ~spl4_2 | ~spl4_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f119,f87,f78,f73,f123])).
% 0.22/0.50  fof(f119,plain,(
% 0.22/0.50    ~v2_struct_0(k1_tex_2(sK0,sK1)) | (spl4_1 | ~spl4_2 | ~spl4_3)),
% 0.22/0.50    inference(resolution,[],[f118,f89])).
% 0.22/0.50  fof(f118,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~v2_struct_0(k1_tex_2(sK0,X0))) ) | (spl4_1 | ~spl4_2)),
% 0.22/0.50    inference(subsumption_resolution,[],[f82,f80])).
% 0.22/0.50  fof(f82,plain,(
% 0.22/0.50    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v2_struct_0(k1_tex_2(sK0,X0))) ) | spl4_1),
% 0.22/0.50    inference(resolution,[],[f75,f66])).
% 0.22/0.50  fof(f66,plain,(
% 0.22/0.50    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v2_struct_0(k1_tex_2(X0,X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f38])).
% 0.22/0.50  fof(f114,plain,(
% 0.22/0.50    ~spl4_2 | spl4_7),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f113])).
% 0.22/0.50  fof(f113,plain,(
% 0.22/0.50    $false | (~spl4_2 | spl4_7)),
% 0.22/0.50    inference(subsumption_resolution,[],[f112,f80])).
% 0.22/0.50  fof(f112,plain,(
% 0.22/0.50    ~l1_pre_topc(sK0) | spl4_7),
% 0.22/0.50    inference(resolution,[],[f110,f50])).
% 0.22/0.50  fof(f110,plain,(
% 0.22/0.50    ~l1_struct_0(sK0) | spl4_7),
% 0.22/0.50    inference(avatar_component_clause,[],[f108])).
% 0.22/0.50  fof(f108,plain,(
% 0.22/0.50    spl4_7 <=> l1_struct_0(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.22/0.50  fof(f111,plain,(
% 0.22/0.50    ~spl4_6 | ~spl4_7 | spl4_1),
% 0.22/0.50    inference(avatar_split_clause,[],[f85,f73,f108,f104])).
% 0.22/0.50  fof(f85,plain,(
% 0.22/0.50    ~l1_struct_0(sK0) | ~v1_xboole_0(u1_struct_0(sK0)) | spl4_1),
% 0.22/0.50    inference(resolution,[],[f75,f58])).
% 0.22/0.50  fof(f99,plain,(
% 0.22/0.50    spl4_4 | spl4_5),
% 0.22/0.50    inference(avatar_split_clause,[],[f41,f96,f92])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f18])).
% 0.22/0.50  fof(f90,plain,(
% 0.22/0.50    spl4_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f43,f87])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.50    inference(cnf_transformation,[],[f18])).
% 0.22/0.50  fof(f81,plain,(
% 0.22/0.50    spl4_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f45,f78])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    l1_pre_topc(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f18])).
% 0.22/0.50  fof(f76,plain,(
% 0.22/0.50    ~spl4_1),
% 0.22/0.50    inference(avatar_split_clause,[],[f44,f73])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    ~v2_struct_0(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f18])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (16586)------------------------------
% 0.22/0.50  % (16586)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (16586)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (16586)Memory used [KB]: 10746
% 0.22/0.50  % (16586)Time elapsed: 0.069 s
% 0.22/0.50  % (16586)------------------------------
% 0.22/0.50  % (16586)------------------------------
% 0.22/0.50  % (16582)Success in time 0.133 s
%------------------------------------------------------------------------------
