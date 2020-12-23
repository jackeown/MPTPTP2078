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
% DateTime   : Thu Dec  3 13:20:46 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  216 ( 397 expanded)
%              Number of leaves         :   44 ( 159 expanded)
%              Depth                    :   12
%              Number of atoms          :  772 (1397 expanded)
%              Number of equality atoms :   64 (  94 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f528,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f100,f105,f110,f122,f124,f134,f145,f172,f176,f183,f201,f224,f244,f250,f259,f267,f285,f332,f335,f390,f432,f437,f464,f472,f480,f517,f524])).

fof(f524,plain,
    ( ~ spl4_3
    | ~ spl4_5
    | ~ spl4_48 ),
    inference(avatar_contradiction_clause,[],[f523])).

fof(f523,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_48 ),
    inference(subsumption_resolution,[],[f520,f121])).

fof(f121,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl4_5
  <=> v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f520,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl4_3
    | ~ spl4_48 ),
    inference(resolution,[],[f516,f109])).

fof(f109,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl4_3
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f516,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),X3),u1_struct_0(sK0)) )
    | ~ spl4_48 ),
    inference(avatar_component_clause,[],[f515])).

fof(f515,plain,
    ( spl4_48
  <=> ! [X3] :
        ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),X3),u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).

fof(f517,plain,
    ( spl4_48
    | ~ spl4_8
    | ~ spl4_20
    | ~ spl4_37
    | spl4_45 ),
    inference(avatar_split_clause,[],[f502,f469,f417,f241,f142,f515])).

fof(f142,plain,
    ( spl4_8
  <=> v7_struct_0(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f241,plain,
    ( spl4_20
  <=> u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f417,plain,
    ( spl4_37
  <=> l1_struct_0(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f469,plain,
    ( spl4_45
  <=> v2_struct_0(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).

fof(f502,plain,
    ( ! [X3] :
        ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),X3),u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl4_8
    | ~ spl4_20
    | ~ spl4_37
    | spl4_45 ),
    inference(subsumption_resolution,[],[f501,f470])).

fof(f470,plain,
    ( ~ v2_struct_0(k1_tex_2(sK0,sK1))
    | spl4_45 ),
    inference(avatar_component_clause,[],[f469])).

fof(f501,plain,
    ( ! [X3] :
        ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),X3),u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | v2_struct_0(k1_tex_2(sK0,sK1)) )
    | ~ spl4_8
    | ~ spl4_20
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f500,f418])).

fof(f418,plain,
    ( l1_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl4_37 ),
    inference(avatar_component_clause,[],[f417])).

fof(f500,plain,
    ( ! [X3] :
        ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),X3),u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ l1_struct_0(k1_tex_2(sK0,sK1))
        | v2_struct_0(k1_tex_2(sK0,sK1)) )
    | ~ spl4_8
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f494,f144])).

fof(f144,plain,
    ( v7_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f142])).

fof(f494,plain,
    ( ! [X3] :
        ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),X3),u1_struct_0(sK0))
        | ~ v7_struct_0(k1_tex_2(sK0,sK1))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ l1_struct_0(k1_tex_2(sK0,sK1))
        | v2_struct_0(k1_tex_2(sK0,sK1)) )
    | ~ spl4_20 ),
    inference(superposition,[],[f83,f242])).

fof(f242,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f241])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
      | ~ v7_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v7_struct_0(X0)
          | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v7_struct_0(X0)
          | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ~ ( v7_struct_0(X0)
              & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_tex_2)).

fof(f480,plain,
    ( spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_45 ),
    inference(avatar_contradiction_clause,[],[f479])).

fof(f479,plain,
    ( $false
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_45 ),
    inference(subsumption_resolution,[],[f478,f99])).

fof(f99,plain,
    ( ~ v2_struct_0(sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl4_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f478,plain,
    ( v2_struct_0(sK0)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_45 ),
    inference(subsumption_resolution,[],[f477,f104])).

fof(f104,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl4_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f477,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_3
    | ~ spl4_45 ),
    inference(subsumption_resolution,[],[f474,f109])).

fof(f474,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_45 ),
    inference(resolution,[],[f471,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_tex_2)).

fof(f471,plain,
    ( v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl4_45 ),
    inference(avatar_component_clause,[],[f469])).

fof(f472,plain,
    ( spl4_45
    | ~ spl4_37
    | ~ spl4_38 ),
    inference(avatar_split_clause,[],[f467,f421,f417,f469])).

fof(f421,plain,
    ( spl4_38
  <=> v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f467,plain,
    ( v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl4_37
    | ~ spl4_38 ),
    inference(subsumption_resolution,[],[f465,f418])).

fof(f465,plain,
    ( ~ l1_struct_0(k1_tex_2(sK0,sK1))
    | v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl4_38 ),
    inference(resolution,[],[f423,f82])).

fof(f82,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f423,plain,
    ( v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))
    | ~ spl4_38 ),
    inference(avatar_component_clause,[],[f421])).

fof(f464,plain,
    ( spl4_38
    | ~ spl4_13
    | spl4_20
    | ~ spl4_40 ),
    inference(avatar_split_clause,[],[f459,f435,f241,f180,f421])).

fof(f180,plain,
    ( spl4_13
  <=> m1_pre_topc(k1_tex_2(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f435,plain,
    ( spl4_40
  <=> ! [X0] :
        ( u1_struct_0(X0) = u1_struct_0(sK0)
        | v1_xboole_0(u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f459,plain,
    ( v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))
    | ~ spl4_13
    | spl4_20
    | ~ spl4_40 ),
    inference(subsumption_resolution,[],[f457,f243])).

fof(f243,plain,
    ( u1_struct_0(sK0) != u1_struct_0(k1_tex_2(sK0,sK1))
    | spl4_20 ),
    inference(avatar_component_clause,[],[f241])).

fof(f457,plain,
    ( v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))
    | u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl4_13
    | ~ spl4_40 ),
    inference(resolution,[],[f436,f182])).

fof(f182,plain,
    ( m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f180])).

fof(f436,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v1_xboole_0(u1_struct_0(X0))
        | u1_struct_0(X0) = u1_struct_0(sK0) )
    | ~ spl4_40 ),
    inference(avatar_component_clause,[],[f435])).

fof(f437,plain,
    ( spl4_40
    | ~ spl4_2
    | ~ spl4_32 ),
    inference(avatar_split_clause,[],[f397,f388,f102,f435])).

fof(f388,plain,
    ( spl4_32
  <=> ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK0))
        | u1_struct_0(sK0) = X0
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f397,plain,
    ( ! [X0] :
        ( u1_struct_0(X0) = u1_struct_0(sK0)
        | v1_xboole_0(u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK0) )
    | ~ spl4_2
    | ~ spl4_32 ),
    inference(subsumption_resolution,[],[f396,f104])).

fof(f396,plain,
    ( ! [X0] :
        ( u1_struct_0(X0) = u1_struct_0(sK0)
        | v1_xboole_0(u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0) )
    | ~ spl4_32 ),
    inference(resolution,[],[f389,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_borsuk_1)).

fof(f389,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK0))
        | u1_struct_0(sK0) = X0
        | v1_xboole_0(X0) )
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f388])).

fof(f432,plain,
    ( ~ spl4_14
    | spl4_37 ),
    inference(avatar_contradiction_clause,[],[f431])).

fof(f431,plain,
    ( $false
    | ~ spl4_14
    | spl4_37 ),
    inference(subsumption_resolution,[],[f429,f200])).

fof(f200,plain,
    ( l1_pre_topc(k1_tex_2(sK0,sK1))
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f198])).

fof(f198,plain,
    ( spl4_14
  <=> l1_pre_topc(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f429,plain,
    ( ~ l1_pre_topc(k1_tex_2(sK0,sK1))
    | spl4_37 ),
    inference(resolution,[],[f419,f71])).

fof(f71,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f419,plain,
    ( ~ l1_struct_0(k1_tex_2(sK0,sK1))
    | spl4_37 ),
    inference(avatar_component_clause,[],[f417])).

fof(f390,plain,
    ( spl4_32
    | spl4_15
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f342,f207,f203,f388])).

fof(f203,plain,
    ( spl4_15
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f207,plain,
    ( spl4_16
  <=> v1_zfmisc_1(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f342,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK0))
        | u1_struct_0(sK0) = X0
        | v1_xboole_0(X0) )
    | spl4_15
    | ~ spl4_16 ),
    inference(subsumption_resolution,[],[f340,f204])).

fof(f204,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl4_15 ),
    inference(avatar_component_clause,[],[f203])).

fof(f340,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK0))
        | u1_struct_0(sK0) = X0
        | v1_xboole_0(u1_struct_0(sK0))
        | v1_xboole_0(X0) )
    | ~ spl4_16 ),
    inference(resolution,[],[f208,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X1)
      | ~ r1_tarski(X0,X1)
      | X0 = X1
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

fof(f208,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f207])).

fof(f335,plain,
    ( ~ spl4_18
    | spl4_20
    | spl4_28 ),
    inference(avatar_contradiction_clause,[],[f333])).

fof(f333,plain,
    ( $false
    | ~ spl4_18
    | spl4_20
    | spl4_28 ),
    inference(unit_resulting_resolution,[],[f243,f223,f331,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(f331,plain,
    ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | spl4_28 ),
    inference(avatar_component_clause,[],[f329])).

fof(f329,plain,
    ( spl4_28
  <=> v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f223,plain,
    ( m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f221])).

fof(f221,plain,
    ( spl4_18
  <=> m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f332,plain,
    ( ~ spl4_28
    | ~ spl4_2
    | spl4_4
    | ~ spl4_13
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f327,f256,f180,f115,f102,f329])).

fof(f115,plain,
    ( spl4_4
  <=> v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f256,plain,
    ( spl4_22
  <=> u1_struct_0(k1_tex_2(sK0,sK1)) = sK3(sK0,k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f327,plain,
    ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl4_2
    | spl4_4
    | ~ spl4_13
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f326,f104])).

fof(f326,plain,
    ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | spl4_4
    | ~ spl4_13
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f325,f182])).

fof(f325,plain,
    ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | spl4_4
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f324,f116])).

fof(f116,plain,
    ( ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f115])).

fof(f324,plain,
    ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl4_22 ),
    inference(superposition,[],[f78,f258])).

fof(f258,plain,
    ( u1_struct_0(k1_tex_2(sK0,sK1)) = sK3(sK0,k1_tex_2(sK0,sK1))
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f256])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(sK3(X0,X1),u1_struct_0(X0))
      | v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ( ~ v1_subset_1(sK3(X0,X1),u1_struct_0(X0))
                & u1_struct_0(X1) = sK3(X0,X1)
                & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v1_subset_1(X3,u1_struct_0(X0))
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f58,f59])).

fof(f59,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v1_subset_1(X2,u1_struct_0(X0))
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_subset_1(sK3(X0,X1),u1_struct_0(X0))
        & u1_struct_0(X1) = sK3(X0,X1)
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ? [X2] :
                  ( ~ v1_subset_1(X2,u1_struct_0(X0))
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v1_subset_1(X3,u1_struct_0(X0))
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ? [X2] :
                  ( ~ v1_subset_1(X2,u1_struct_0(X0))
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v1_subset_1(X2,u1_struct_0(X0))
                  | u1_struct_0(X1) != X2
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tex_2)).

fof(f285,plain,
    ( spl4_16
    | ~ spl4_3
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f284,f247,f107,f207])).

fof(f247,plain,
    ( spl4_21
  <=> u1_struct_0(sK0) = k6_domain_1(u1_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f284,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl4_3
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f277,f109])).

fof(f277,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl4_21 ),
    inference(trivial_inequality_removal,[],[f275])).

fof(f275,plain,
    ( u1_struct_0(sK0) != u1_struct_0(sK0)
    | v1_zfmisc_1(u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl4_21 ),
    inference(superposition,[],[f125,f249])).

fof(f249,plain,
    ( u1_struct_0(sK0) = k6_domain_1(u1_struct_0(sK0),sK1)
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f247])).

fof(f125,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) != X0
      | v1_zfmisc_1(X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f69,f80])).

fof(f80,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_zfmisc_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_zfmisc_1)).

fof(f69,plain,(
    ! [X0,X1] :
      ( v1_zfmisc_1(X0)
      | k6_domain_1(X0,X1) != X0
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ( k6_domain_1(X0,sK2(X0)) = X0
            & m1_subset_1(sK2(X0),X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f54,f55])).

fof(f55,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k6_domain_1(X0,X2) = X0
          & m1_subset_1(X2,X0) )
     => ( k6_domain_1(X0,sK2(X0)) = X0
        & m1_subset_1(sK2(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ? [X2] :
              ( k6_domain_1(X0,X2) = X0
              & m1_subset_1(X2,X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(rectify,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ? [X1] :
              ( k6_domain_1(X0,X1) = X0
              & m1_subset_1(X1,X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

fof(f267,plain,
    ( spl4_1
    | ~ spl4_10
    | ~ spl4_15 ),
    inference(avatar_contradiction_clause,[],[f266])).

fof(f266,plain,
    ( $false
    | spl4_1
    | ~ spl4_10
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f265,f99])).

fof(f265,plain,
    ( v2_struct_0(sK0)
    | ~ spl4_10
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f262,f160])).

fof(f160,plain,
    ( l1_struct_0(sK0)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl4_10
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f262,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_15 ),
    inference(resolution,[],[f205,f82])).

fof(f205,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f203])).

fof(f259,plain,
    ( spl4_22
    | ~ spl4_2
    | spl4_4
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f253,f180,f115,f102,f256])).

fof(f253,plain,
    ( u1_struct_0(k1_tex_2(sK0,sK1)) = sK3(sK0,k1_tex_2(sK0,sK1))
    | ~ spl4_2
    | spl4_4
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f232,f116])).

fof(f232,plain,
    ( u1_struct_0(k1_tex_2(sK0,sK1)) = sK3(sK0,k1_tex_2(sK0,sK1))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ spl4_2
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f188,f104])).

fof(f188,plain,
    ( u1_struct_0(k1_tex_2(sK0,sK1)) = sK3(sK0,k1_tex_2(sK0,sK1))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl4_13 ),
    inference(resolution,[],[f182,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | u1_struct_0(X1) = sK3(X0,X1)
      | v1_tex_2(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f250,plain,
    ( spl4_21
    | ~ spl4_3
    | spl4_5
    | spl4_15 ),
    inference(avatar_split_clause,[],[f239,f203,f119,f107,f247])).

fof(f239,plain,
    ( u1_struct_0(sK0) = k6_domain_1(u1_struct_0(sK0),sK1)
    | ~ spl4_3
    | spl4_5
    | spl4_15 ),
    inference(subsumption_resolution,[],[f238,f109])).

fof(f238,plain,
    ( u1_struct_0(sK0) = k6_domain_1(u1_struct_0(sK0),sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | spl4_5
    | spl4_15 ),
    inference(subsumption_resolution,[],[f237,f204])).

fof(f237,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | u1_struct_0(sK0) = k6_domain_1(u1_struct_0(sK0),sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | spl4_5 ),
    inference(resolution,[],[f120,f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( v1_subset_1(k6_domain_1(X1,X0),X1)
      | v1_xboole_0(X1)
      | k6_domain_1(X1,X0) = X1
      | ~ m1_subset_1(X0,X1) ) ),
    inference(resolution,[],[f93,f86])).

fof(f93,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f120,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f119])).

fof(f244,plain,
    ( ~ spl4_20
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f236,f180,f115,f102,f241])).

fof(f236,plain,
    ( u1_struct_0(sK0) != u1_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f235,f104])).

fof(f235,plain,
    ( u1_struct_0(sK0) != u1_struct_0(k1_tex_2(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_4
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f234,f182])).

fof(f234,plain,
    ( u1_struct_0(sK0) != u1_struct_0(k1_tex_2(sK0,sK1))
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl4_4 ),
    inference(resolution,[],[f117,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ v1_tex_2(X1,X0)
      | u1_struct_0(X0) != u1_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_tex_2(X1,X0)
          | u1_struct_0(X0) != u1_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_tex_2(X1,X0)
          | u1_struct_0(X0) != u1_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ~ ( v1_tex_2(X1,X0)
              & u1_struct_0(X0) = u1_struct_0(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_tex_2)).

fof(f117,plain,
    ( v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f115])).

fof(f224,plain,
    ( spl4_18
    | ~ spl4_2
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f195,f180,f102,f221])).

fof(f195,plain,
    ( m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_2
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f189,f104])).

fof(f189,plain,
    ( m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_13 ),
    inference(resolution,[],[f182,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f201,plain,
    ( spl4_14
    | ~ spl4_2
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f196,f180,f102,f198])).

fof(f196,plain,
    ( l1_pre_topc(k1_tex_2(sK0,sK1))
    | ~ spl4_2
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f190,f104])).

fof(f190,plain,
    ( l1_pre_topc(k1_tex_2(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_13 ),
    inference(resolution,[],[f182,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f183,plain,
    ( spl4_13
    | ~ spl4_3
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f177,f174,f107,f180])).

fof(f174,plain,
    ( spl4_12
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | m1_pre_topc(k1_tex_2(sK0,X0),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f177,plain,
    ( m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ spl4_3
    | ~ spl4_12 ),
    inference(resolution,[],[f175,f109])).

fof(f175,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | m1_pre_topc(k1_tex_2(sK0,X0),sK0) )
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f174])).

fof(f176,plain,
    ( spl4_12
    | spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f147,f102,f97,f174])).

fof(f147,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | m1_pre_topc(k1_tex_2(sK0,X0),sK0) )
    | spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f146,f99])).

fof(f146,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | m1_pre_topc(k1_tex_2(sK0,X0),sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_2 ),
    inference(resolution,[],[f92,f104])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | m1_pre_topc(k1_tex_2(X0,X1),X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
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
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).

fof(f172,plain,
    ( ~ spl4_2
    | spl4_10 ),
    inference(avatar_contradiction_clause,[],[f171])).

fof(f171,plain,
    ( $false
    | ~ spl4_2
    | spl4_10 ),
    inference(subsumption_resolution,[],[f169,f104])).

fof(f169,plain,
    ( ~ l1_pre_topc(sK0)
    | spl4_10 ),
    inference(resolution,[],[f161,f71])).

fof(f161,plain,
    ( ~ l1_struct_0(sK0)
    | spl4_10 ),
    inference(avatar_component_clause,[],[f159])).

fof(f145,plain,
    ( spl4_8
    | ~ spl4_3
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f139,f132,f107,f142])).

fof(f132,plain,
    ( spl4_6
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v7_struct_0(k1_tex_2(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f139,plain,
    ( v7_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl4_3
    | ~ spl4_6 ),
    inference(resolution,[],[f133,f109])).

fof(f133,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v7_struct_0(k1_tex_2(sK0,X0)) )
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f132])).

fof(f134,plain,
    ( spl4_6
    | spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f128,f102,f97,f132])).

fof(f128,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v7_struct_0(k1_tex_2(sK0,X0)) )
    | spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f127,f99])).

fof(f127,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v7_struct_0(k1_tex_2(sK0,X0))
        | v2_struct_0(sK0) )
    | ~ spl4_2 ),
    inference(resolution,[],[f88,f104])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v7_struct_0(k1_tex_2(X0,X1))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f124,plain,
    ( ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f123,f119,f115])).

fof(f123,plain,
    ( ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f66,f121])).

fof(f66,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,
    ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
      | ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0) )
    & ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
      | v1_tex_2(k1_tex_2(sK0,sK1),sK0) )
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f49,f51,f50])).

fof(f50,plain,
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

fof(f51,plain,
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

fof(f49,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( v1_tex_2(k1_tex_2(X0,X1),X0)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_tex_2)).

fof(f122,plain,
    ( spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f65,f119,f115])).

fof(f65,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f110,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f64,f107])).

fof(f64,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f52])).

fof(f105,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f63,f102])).

fof(f63,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f100,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f62,f97])).

fof(f62,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f52])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.20/0.34  % WCLimit    : 600
% 0.20/0.34  % DateTime   : Tue Dec  1 15:52:56 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.21/0.46  % (18304)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.47  % (18296)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.48  % (18320)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.48  % (18296)Refutation not found, incomplete strategy% (18296)------------------------------
% 0.21/0.48  % (18296)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (18296)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (18296)Memory used [KB]: 10618
% 0.21/0.48  % (18296)Time elapsed: 0.094 s
% 0.21/0.48  % (18296)------------------------------
% 0.21/0.48  % (18296)------------------------------
% 0.21/0.49  % (18297)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.49  % (18318)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.49  % (18295)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.50  % (18301)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.50  % (18305)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.50  % (18299)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.50  % (18302)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.50  % (18301)Refutation not found, incomplete strategy% (18301)------------------------------
% 0.21/0.50  % (18301)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (18301)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (18301)Memory used [KB]: 10746
% 0.21/0.50  % (18301)Time elapsed: 0.096 s
% 0.21/0.50  % (18301)------------------------------
% 0.21/0.50  % (18301)------------------------------
% 0.21/0.50  % (18317)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.51  % (18297)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f528,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f100,f105,f110,f122,f124,f134,f145,f172,f176,f183,f201,f224,f244,f250,f259,f267,f285,f332,f335,f390,f432,f437,f464,f472,f480,f517,f524])).
% 0.21/0.51  fof(f524,plain,(
% 0.21/0.51    ~spl4_3 | ~spl4_5 | ~spl4_48),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f523])).
% 0.21/0.51  fof(f523,plain,(
% 0.21/0.51    $false | (~spl4_3 | ~spl4_5 | ~spl4_48)),
% 0.21/0.51    inference(subsumption_resolution,[],[f520,f121])).
% 0.21/0.51  fof(f121,plain,(
% 0.21/0.51    v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~spl4_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f119])).
% 0.21/0.51  fof(f119,plain,(
% 0.21/0.51    spl4_5 <=> v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.51  fof(f520,plain,(
% 0.21/0.51    ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | (~spl4_3 | ~spl4_48)),
% 0.21/0.51    inference(resolution,[],[f516,f109])).
% 0.21/0.51  fof(f109,plain,(
% 0.21/0.51    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl4_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f107])).
% 0.21/0.51  fof(f107,plain,(
% 0.21/0.51    spl4_3 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.51  fof(f516,plain,(
% 0.21/0.51    ( ! [X3] : (~m1_subset_1(X3,u1_struct_0(sK0)) | ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),X3),u1_struct_0(sK0))) ) | ~spl4_48),
% 0.21/0.51    inference(avatar_component_clause,[],[f515])).
% 0.21/0.51  fof(f515,plain,(
% 0.21/0.51    spl4_48 <=> ! [X3] : (~v1_subset_1(k6_domain_1(u1_struct_0(sK0),X3),u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).
% 0.21/0.51  fof(f517,plain,(
% 0.21/0.51    spl4_48 | ~spl4_8 | ~spl4_20 | ~spl4_37 | spl4_45),
% 0.21/0.51    inference(avatar_split_clause,[],[f502,f469,f417,f241,f142,f515])).
% 0.21/0.51  fof(f142,plain,(
% 0.21/0.51    spl4_8 <=> v7_struct_0(k1_tex_2(sK0,sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.51  fof(f241,plain,(
% 0.21/0.51    spl4_20 <=> u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.21/0.51  fof(f417,plain,(
% 0.21/0.51    spl4_37 <=> l1_struct_0(k1_tex_2(sK0,sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 0.21/0.51  fof(f469,plain,(
% 0.21/0.51    spl4_45 <=> v2_struct_0(k1_tex_2(sK0,sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).
% 0.21/0.51  fof(f502,plain,(
% 0.21/0.51    ( ! [X3] : (~v1_subset_1(k6_domain_1(u1_struct_0(sK0),X3),u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0))) ) | (~spl4_8 | ~spl4_20 | ~spl4_37 | spl4_45)),
% 0.21/0.51    inference(subsumption_resolution,[],[f501,f470])).
% 0.21/0.51  fof(f470,plain,(
% 0.21/0.51    ~v2_struct_0(k1_tex_2(sK0,sK1)) | spl4_45),
% 0.21/0.51    inference(avatar_component_clause,[],[f469])).
% 0.21/0.51  fof(f501,plain,(
% 0.21/0.51    ( ! [X3] : (~v1_subset_1(k6_domain_1(u1_struct_0(sK0),X3),u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | v2_struct_0(k1_tex_2(sK0,sK1))) ) | (~spl4_8 | ~spl4_20 | ~spl4_37)),
% 0.21/0.51    inference(subsumption_resolution,[],[f500,f418])).
% 0.21/0.51  fof(f418,plain,(
% 0.21/0.51    l1_struct_0(k1_tex_2(sK0,sK1)) | ~spl4_37),
% 0.21/0.51    inference(avatar_component_clause,[],[f417])).
% 0.21/0.51  fof(f500,plain,(
% 0.21/0.51    ( ! [X3] : (~v1_subset_1(k6_domain_1(u1_struct_0(sK0),X3),u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~l1_struct_0(k1_tex_2(sK0,sK1)) | v2_struct_0(k1_tex_2(sK0,sK1))) ) | (~spl4_8 | ~spl4_20)),
% 0.21/0.51    inference(subsumption_resolution,[],[f494,f144])).
% 0.21/0.51  fof(f144,plain,(
% 0.21/0.51    v7_struct_0(k1_tex_2(sK0,sK1)) | ~spl4_8),
% 0.21/0.51    inference(avatar_component_clause,[],[f142])).
% 0.21/0.51  fof(f494,plain,(
% 0.21/0.51    ( ! [X3] : (~v1_subset_1(k6_domain_1(u1_struct_0(sK0),X3),u1_struct_0(sK0)) | ~v7_struct_0(k1_tex_2(sK0,sK1)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~l1_struct_0(k1_tex_2(sK0,sK1)) | v2_struct_0(k1_tex_2(sK0,sK1))) ) | ~spl4_20),
% 0.21/0.51    inference(superposition,[],[f83,f242])).
% 0.21/0.51  fof(f242,plain,(
% 0.21/0.51    u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) | ~spl4_20),
% 0.21/0.51    inference(avatar_component_clause,[],[f241])).
% 0.21/0.51  fof(f83,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v7_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,axiom,(
% 0.21/0.51    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~(v7_struct_0(X0) & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_tex_2)).
% 0.21/0.51  fof(f480,plain,(
% 0.21/0.51    spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_45),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f479])).
% 0.21/0.51  fof(f479,plain,(
% 0.21/0.51    $false | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_45)),
% 0.21/0.51    inference(subsumption_resolution,[],[f478,f99])).
% 0.21/0.51  fof(f99,plain,(
% 0.21/0.51    ~v2_struct_0(sK0) | spl4_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f97])).
% 0.21/0.51  fof(f97,plain,(
% 0.21/0.51    spl4_1 <=> v2_struct_0(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.51  fof(f478,plain,(
% 0.21/0.51    v2_struct_0(sK0) | (~spl4_2 | ~spl4_3 | ~spl4_45)),
% 0.21/0.51    inference(subsumption_resolution,[],[f477,f104])).
% 0.21/0.51  fof(f104,plain,(
% 0.21/0.51    l1_pre_topc(sK0) | ~spl4_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f102])).
% 0.21/0.51  fof(f102,plain,(
% 0.21/0.51    spl4_2 <=> l1_pre_topc(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.51  fof(f477,plain,(
% 0.21/0.51    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_3 | ~spl4_45)),
% 0.21/0.51    inference(subsumption_resolution,[],[f474,f109])).
% 0.21/0.51  fof(f474,plain,(
% 0.21/0.51    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl4_45),
% 0.21/0.51    inference(resolution,[],[f471,f87])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v2_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f43])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    ! [X0,X1] : ((v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ! [X0,X1] : ((v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,axiom,(
% 0.21/0.51    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_tex_2)).
% 0.21/0.51  fof(f471,plain,(
% 0.21/0.51    v2_struct_0(k1_tex_2(sK0,sK1)) | ~spl4_45),
% 0.21/0.51    inference(avatar_component_clause,[],[f469])).
% 0.21/0.51  fof(f472,plain,(
% 0.21/0.51    spl4_45 | ~spl4_37 | ~spl4_38),
% 0.21/0.51    inference(avatar_split_clause,[],[f467,f421,f417,f469])).
% 0.21/0.51  fof(f421,plain,(
% 0.21/0.51    spl4_38 <=> v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 0.21/0.51  fof(f467,plain,(
% 0.21/0.51    v2_struct_0(k1_tex_2(sK0,sK1)) | (~spl4_37 | ~spl4_38)),
% 0.21/0.51    inference(subsumption_resolution,[],[f465,f418])).
% 0.21/0.51  fof(f465,plain,(
% 0.21/0.51    ~l1_struct_0(k1_tex_2(sK0,sK1)) | v2_struct_0(k1_tex_2(sK0,sK1)) | ~spl4_38),
% 0.21/0.51    inference(resolution,[],[f423,f82])).
% 0.21/0.51  fof(f82,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.51  fof(f423,plain,(
% 0.21/0.51    v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) | ~spl4_38),
% 0.21/0.51    inference(avatar_component_clause,[],[f421])).
% 0.21/0.51  fof(f464,plain,(
% 0.21/0.51    spl4_38 | ~spl4_13 | spl4_20 | ~spl4_40),
% 0.21/0.51    inference(avatar_split_clause,[],[f459,f435,f241,f180,f421])).
% 0.21/0.51  fof(f180,plain,(
% 0.21/0.51    spl4_13 <=> m1_pre_topc(k1_tex_2(sK0,sK1),sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.51  fof(f435,plain,(
% 0.21/0.51    spl4_40 <=> ! [X0] : (u1_struct_0(X0) = u1_struct_0(sK0) | v1_xboole_0(u1_struct_0(X0)) | ~m1_pre_topc(X0,sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).
% 0.21/0.51  fof(f459,plain,(
% 0.21/0.51    v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) | (~spl4_13 | spl4_20 | ~spl4_40)),
% 0.21/0.51    inference(subsumption_resolution,[],[f457,f243])).
% 0.21/0.51  fof(f243,plain,(
% 0.21/0.51    u1_struct_0(sK0) != u1_struct_0(k1_tex_2(sK0,sK1)) | spl4_20),
% 0.21/0.51    inference(avatar_component_clause,[],[f241])).
% 0.21/0.51  fof(f457,plain,(
% 0.21/0.51    v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) | u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) | (~spl4_13 | ~spl4_40)),
% 0.21/0.51    inference(resolution,[],[f436,f182])).
% 0.21/0.51  fof(f182,plain,(
% 0.21/0.51    m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~spl4_13),
% 0.21/0.51    inference(avatar_component_clause,[],[f180])).
% 0.21/0.51  fof(f436,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v1_xboole_0(u1_struct_0(X0)) | u1_struct_0(X0) = u1_struct_0(sK0)) ) | ~spl4_40),
% 0.21/0.51    inference(avatar_component_clause,[],[f435])).
% 0.21/0.51  fof(f437,plain,(
% 0.21/0.51    spl4_40 | ~spl4_2 | ~spl4_32),
% 0.21/0.51    inference(avatar_split_clause,[],[f397,f388,f102,f435])).
% 0.21/0.51  fof(f388,plain,(
% 0.21/0.51    spl4_32 <=> ! [X0] : (~r1_tarski(X0,u1_struct_0(sK0)) | u1_struct_0(sK0) = X0 | v1_xboole_0(X0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 0.21/0.51  fof(f397,plain,(
% 0.21/0.51    ( ! [X0] : (u1_struct_0(X0) = u1_struct_0(sK0) | v1_xboole_0(u1_struct_0(X0)) | ~m1_pre_topc(X0,sK0)) ) | (~spl4_2 | ~spl4_32)),
% 0.21/0.51    inference(subsumption_resolution,[],[f396,f104])).
% 0.21/0.51  fof(f396,plain,(
% 0.21/0.51    ( ! [X0] : (u1_struct_0(X0) = u1_struct_0(sK0) | v1_xboole_0(u1_struct_0(X0)) | ~m1_pre_topc(X0,sK0) | ~l1_pre_topc(sK0)) ) | ~spl4_32),
% 0.21/0.51    inference(resolution,[],[f389,f73])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_borsuk_1)).
% 0.21/0.51  fof(f389,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK0)) | u1_struct_0(sK0) = X0 | v1_xboole_0(X0)) ) | ~spl4_32),
% 0.21/0.51    inference(avatar_component_clause,[],[f388])).
% 0.21/0.51  fof(f432,plain,(
% 0.21/0.51    ~spl4_14 | spl4_37),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f431])).
% 0.21/0.51  fof(f431,plain,(
% 0.21/0.51    $false | (~spl4_14 | spl4_37)),
% 0.21/0.51    inference(subsumption_resolution,[],[f429,f200])).
% 0.21/0.51  fof(f200,plain,(
% 0.21/0.51    l1_pre_topc(k1_tex_2(sK0,sK1)) | ~spl4_14),
% 0.21/0.51    inference(avatar_component_clause,[],[f198])).
% 0.21/0.51  fof(f198,plain,(
% 0.21/0.51    spl4_14 <=> l1_pre_topc(k1_tex_2(sK0,sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.21/0.51  fof(f429,plain,(
% 0.21/0.51    ~l1_pre_topc(k1_tex_2(sK0,sK1)) | spl4_37),
% 0.21/0.51    inference(resolution,[],[f419,f71])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.51  fof(f419,plain,(
% 0.21/0.51    ~l1_struct_0(k1_tex_2(sK0,sK1)) | spl4_37),
% 0.21/0.51    inference(avatar_component_clause,[],[f417])).
% 0.21/0.51  fof(f390,plain,(
% 0.21/0.51    spl4_32 | spl4_15 | ~spl4_16),
% 0.21/0.51    inference(avatar_split_clause,[],[f342,f207,f203,f388])).
% 0.21/0.51  fof(f203,plain,(
% 0.21/0.51    spl4_15 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.21/0.51  fof(f207,plain,(
% 0.21/0.51    spl4_16 <=> v1_zfmisc_1(u1_struct_0(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.21/0.51  fof(f342,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK0)) | u1_struct_0(sK0) = X0 | v1_xboole_0(X0)) ) | (spl4_15 | ~spl4_16)),
% 0.21/0.51    inference(subsumption_resolution,[],[f340,f204])).
% 0.21/0.51  fof(f204,plain,(
% 0.21/0.51    ~v1_xboole_0(u1_struct_0(sK0)) | spl4_15),
% 0.21/0.51    inference(avatar_component_clause,[],[f203])).
% 0.21/0.51  fof(f340,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK0)) | u1_struct_0(sK0) = X0 | v1_xboole_0(u1_struct_0(sK0)) | v1_xboole_0(X0)) ) | ~spl4_16),
% 0.21/0.51    inference(resolution,[],[f208,f70])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_zfmisc_1(X1) | ~r1_tarski(X0,X1) | X0 = X1 | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.21/0.51    inference(flattening,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,axiom,(
% 0.21/0.51    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).
% 0.21/0.51  fof(f208,plain,(
% 0.21/0.51    v1_zfmisc_1(u1_struct_0(sK0)) | ~spl4_16),
% 0.21/0.51    inference(avatar_component_clause,[],[f207])).
% 0.21/0.51  fof(f335,plain,(
% 0.21/0.51    ~spl4_18 | spl4_20 | spl4_28),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f333])).
% 0.21/0.51  fof(f333,plain,(
% 0.21/0.51    $false | (~spl4_18 | spl4_20 | spl4_28)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f243,f223,f331,f86])).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f61])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.51    inference(nnf_transformation,[],[f41])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).
% 0.21/0.51  fof(f331,plain,(
% 0.21/0.51    ~v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | spl4_28),
% 0.21/0.51    inference(avatar_component_clause,[],[f329])).
% 0.21/0.51  fof(f329,plain,(
% 0.21/0.51    spl4_28 <=> v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.21/0.51  fof(f223,plain,(
% 0.21/0.51    m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_18),
% 0.21/0.51    inference(avatar_component_clause,[],[f221])).
% 0.21/0.51  fof(f221,plain,(
% 0.21/0.51    spl4_18 <=> m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.21/0.51  fof(f332,plain,(
% 0.21/0.51    ~spl4_28 | ~spl4_2 | spl4_4 | ~spl4_13 | ~spl4_22),
% 0.21/0.51    inference(avatar_split_clause,[],[f327,f256,f180,f115,f102,f329])).
% 0.21/0.51  fof(f115,plain,(
% 0.21/0.51    spl4_4 <=> v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.51  fof(f256,plain,(
% 0.21/0.51    spl4_22 <=> u1_struct_0(k1_tex_2(sK0,sK1)) = sK3(sK0,k1_tex_2(sK0,sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.21/0.51  fof(f327,plain,(
% 0.21/0.51    ~v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | (~spl4_2 | spl4_4 | ~spl4_13 | ~spl4_22)),
% 0.21/0.51    inference(subsumption_resolution,[],[f326,f104])).
% 0.21/0.51  fof(f326,plain,(
% 0.21/0.51    ~v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | (spl4_4 | ~spl4_13 | ~spl4_22)),
% 0.21/0.51    inference(subsumption_resolution,[],[f325,f182])).
% 0.21/0.51  fof(f325,plain,(
% 0.21/0.51    ~v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | (spl4_4 | ~spl4_22)),
% 0.21/0.51    inference(subsumption_resolution,[],[f324,f116])).
% 0.21/0.51  fof(f116,plain,(
% 0.21/0.51    ~v1_tex_2(k1_tex_2(sK0,sK1),sK0) | spl4_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f115])).
% 0.21/0.51  fof(f324,plain,(
% 0.21/0.51    ~v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | ~spl4_22),
% 0.21/0.51    inference(superposition,[],[f78,f258])).
% 0.21/0.51  fof(f258,plain,(
% 0.21/0.51    u1_struct_0(k1_tex_2(sK0,sK1)) = sK3(sK0,k1_tex_2(sK0,sK1)) | ~spl4_22),
% 0.21/0.51    inference(avatar_component_clause,[],[f256])).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_subset_1(sK3(X0,X1),u1_struct_0(X0)) | v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f60])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | (~v1_subset_1(sK3(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK3(X0,X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f58,f59])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    ! [X1,X0] : (? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_subset_1(sK3(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK3(X0,X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(rectify,[],[f57])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v1_subset_1(X2,u1_struct_0(X0)))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tex_2)).
% 0.21/0.51  fof(f285,plain,(
% 0.21/0.51    spl4_16 | ~spl4_3 | ~spl4_21),
% 0.21/0.51    inference(avatar_split_clause,[],[f284,f247,f107,f207])).
% 0.21/0.51  fof(f247,plain,(
% 0.21/0.51    spl4_21 <=> u1_struct_0(sK0) = k6_domain_1(u1_struct_0(sK0),sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.21/0.51  fof(f284,plain,(
% 0.21/0.51    v1_zfmisc_1(u1_struct_0(sK0)) | (~spl4_3 | ~spl4_21)),
% 0.21/0.51    inference(subsumption_resolution,[],[f277,f109])).
% 0.21/0.51  fof(f277,plain,(
% 0.21/0.51    v1_zfmisc_1(u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl4_21),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f275])).
% 0.21/0.51  fof(f275,plain,(
% 0.21/0.51    u1_struct_0(sK0) != u1_struct_0(sK0) | v1_zfmisc_1(u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl4_21),
% 0.21/0.51    inference(superposition,[],[f125,f249])).
% 0.21/0.51  fof(f249,plain,(
% 0.21/0.51    u1_struct_0(sK0) = k6_domain_1(u1_struct_0(sK0),sK1) | ~spl4_21),
% 0.21/0.51    inference(avatar_component_clause,[],[f247])).
% 0.21/0.51  fof(f125,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k6_domain_1(X0,X1) != X0 | v1_zfmisc_1(X0) | ~m1_subset_1(X1,X0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f69,f80])).
% 0.21/0.51  fof(f80,plain,(
% 0.21/0.51    ( ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0] : (v1_xboole_0(X0) => v1_zfmisc_1(X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_zfmisc_1)).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v1_zfmisc_1(X0) | k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f56])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & ((k6_domain_1(X0,sK2(X0)) = X0 & m1_subset_1(sK2(X0),X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f54,f55])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    ! [X0] : (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) => (k6_domain_1(X0,sK2(X0)) = X0 & m1_subset_1(sK2(X0),X0)))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 0.21/0.51    inference(rectify,[],[f53])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0] : ((v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))) | v1_xboole_0(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,axiom,(
% 0.21/0.51    ! [X0] : (~v1_xboole_0(X0) => (v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).
% 0.21/0.51  fof(f267,plain,(
% 0.21/0.51    spl4_1 | ~spl4_10 | ~spl4_15),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f266])).
% 0.21/0.51  fof(f266,plain,(
% 0.21/0.51    $false | (spl4_1 | ~spl4_10 | ~spl4_15)),
% 0.21/0.51    inference(subsumption_resolution,[],[f265,f99])).
% 0.21/0.51  fof(f265,plain,(
% 0.21/0.51    v2_struct_0(sK0) | (~spl4_10 | ~spl4_15)),
% 0.21/0.51    inference(subsumption_resolution,[],[f262,f160])).
% 0.21/0.51  fof(f160,plain,(
% 0.21/0.51    l1_struct_0(sK0) | ~spl4_10),
% 0.21/0.51    inference(avatar_component_clause,[],[f159])).
% 0.21/0.51  fof(f159,plain,(
% 0.21/0.51    spl4_10 <=> l1_struct_0(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.51  fof(f262,plain,(
% 0.21/0.51    ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~spl4_15),
% 0.21/0.51    inference(resolution,[],[f205,f82])).
% 0.21/0.51  fof(f205,plain,(
% 0.21/0.51    v1_xboole_0(u1_struct_0(sK0)) | ~spl4_15),
% 0.21/0.51    inference(avatar_component_clause,[],[f203])).
% 0.21/0.51  fof(f259,plain,(
% 0.21/0.51    spl4_22 | ~spl4_2 | spl4_4 | ~spl4_13),
% 0.21/0.51    inference(avatar_split_clause,[],[f253,f180,f115,f102,f256])).
% 0.21/0.51  fof(f253,plain,(
% 0.21/0.51    u1_struct_0(k1_tex_2(sK0,sK1)) = sK3(sK0,k1_tex_2(sK0,sK1)) | (~spl4_2 | spl4_4 | ~spl4_13)),
% 0.21/0.51    inference(subsumption_resolution,[],[f232,f116])).
% 0.21/0.51  fof(f232,plain,(
% 0.21/0.51    u1_struct_0(k1_tex_2(sK0,sK1)) = sK3(sK0,k1_tex_2(sK0,sK1)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0) | (~spl4_2 | ~spl4_13)),
% 0.21/0.51    inference(subsumption_resolution,[],[f188,f104])).
% 0.21/0.51  fof(f188,plain,(
% 0.21/0.51    u1_struct_0(k1_tex_2(sK0,sK1)) = sK3(sK0,k1_tex_2(sK0,sK1)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | ~spl4_13),
% 0.21/0.51    inference(resolution,[],[f182,f77])).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | u1_struct_0(X1) = sK3(X0,X1) | v1_tex_2(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f60])).
% 0.21/0.51  fof(f250,plain,(
% 0.21/0.51    spl4_21 | ~spl4_3 | spl4_5 | spl4_15),
% 0.21/0.51    inference(avatar_split_clause,[],[f239,f203,f119,f107,f247])).
% 0.21/0.51  fof(f239,plain,(
% 0.21/0.51    u1_struct_0(sK0) = k6_domain_1(u1_struct_0(sK0),sK1) | (~spl4_3 | spl4_5 | spl4_15)),
% 0.21/0.51    inference(subsumption_resolution,[],[f238,f109])).
% 0.21/0.51  fof(f238,plain,(
% 0.21/0.51    u1_struct_0(sK0) = k6_domain_1(u1_struct_0(sK0),sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | (spl4_5 | spl4_15)),
% 0.21/0.51    inference(subsumption_resolution,[],[f237,f204])).
% 0.21/0.51  fof(f237,plain,(
% 0.21/0.51    v1_xboole_0(u1_struct_0(sK0)) | u1_struct_0(sK0) = k6_domain_1(u1_struct_0(sK0),sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | spl4_5),
% 0.21/0.51    inference(resolution,[],[f120,f113])).
% 0.21/0.51  fof(f113,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v1_subset_1(k6_domain_1(X1,X0),X1) | v1_xboole_0(X1) | k6_domain_1(X1,X0) = X1 | ~m1_subset_1(X0,X1)) )),
% 0.21/0.51    inference(resolution,[],[f93,f86])).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f47])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.51    inference(flattening,[],[f46])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.21/0.51  fof(f120,plain,(
% 0.21/0.51    ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | spl4_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f119])).
% 0.21/0.51  fof(f244,plain,(
% 0.21/0.51    ~spl4_20 | ~spl4_2 | ~spl4_4 | ~spl4_13),
% 0.21/0.51    inference(avatar_split_clause,[],[f236,f180,f115,f102,f241])).
% 0.21/0.51  fof(f236,plain,(
% 0.21/0.51    u1_struct_0(sK0) != u1_struct_0(k1_tex_2(sK0,sK1)) | (~spl4_2 | ~spl4_4 | ~spl4_13)),
% 0.21/0.51    inference(subsumption_resolution,[],[f235,f104])).
% 0.21/0.51  fof(f235,plain,(
% 0.21/0.51    u1_struct_0(sK0) != u1_struct_0(k1_tex_2(sK0,sK1)) | ~l1_pre_topc(sK0) | (~spl4_4 | ~spl4_13)),
% 0.21/0.51    inference(subsumption_resolution,[],[f234,f182])).
% 0.21/0.51  fof(f234,plain,(
% 0.21/0.51    u1_struct_0(sK0) != u1_struct_0(k1_tex_2(sK0,sK1)) | ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | ~spl4_4),
% 0.21/0.51    inference(resolution,[],[f117,f79])).
% 0.21/0.51  fof(f79,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_tex_2(X1,X0) | u1_struct_0(X0) != u1_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (~v1_tex_2(X1,X0) | u1_struct_0(X0) != u1_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((~v1_tex_2(X1,X0) | u1_struct_0(X0) != u1_struct_0(X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ~(v1_tex_2(X1,X0) & u1_struct_0(X0) = u1_struct_0(X1))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_tex_2)).
% 0.21/0.51  fof(f117,plain,(
% 0.21/0.51    v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~spl4_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f115])).
% 0.21/0.51  fof(f224,plain,(
% 0.21/0.51    spl4_18 | ~spl4_2 | ~spl4_13),
% 0.21/0.51    inference(avatar_split_clause,[],[f195,f180,f102,f221])).
% 0.21/0.51  fof(f195,plain,(
% 0.21/0.51    m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_2 | ~spl4_13)),
% 0.21/0.51    inference(subsumption_resolution,[],[f189,f104])).
% 0.21/0.51  fof(f189,plain,(
% 0.21/0.51    m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl4_13),
% 0.21/0.51    inference(resolution,[],[f182,f74])).
% 0.21/0.51  fof(f74,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.21/0.51  fof(f201,plain,(
% 0.21/0.51    spl4_14 | ~spl4_2 | ~spl4_13),
% 0.21/0.51    inference(avatar_split_clause,[],[f196,f180,f102,f198])).
% 0.21/0.51  fof(f196,plain,(
% 0.21/0.51    l1_pre_topc(k1_tex_2(sK0,sK1)) | (~spl4_2 | ~spl4_13)),
% 0.21/0.51    inference(subsumption_resolution,[],[f190,f104])).
% 0.21/0.51  fof(f190,plain,(
% 0.21/0.51    l1_pre_topc(k1_tex_2(sK0,sK1)) | ~l1_pre_topc(sK0) | ~spl4_13),
% 0.21/0.51    inference(resolution,[],[f182,f72])).
% 0.21/0.51  fof(f72,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.51  fof(f183,plain,(
% 0.21/0.51    spl4_13 | ~spl4_3 | ~spl4_12),
% 0.21/0.51    inference(avatar_split_clause,[],[f177,f174,f107,f180])).
% 0.21/0.51  fof(f174,plain,(
% 0.21/0.51    spl4_12 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | m1_pre_topc(k1_tex_2(sK0,X0),sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.51  fof(f177,plain,(
% 0.21/0.51    m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | (~spl4_3 | ~spl4_12)),
% 0.21/0.51    inference(resolution,[],[f175,f109])).
% 0.21/0.51  fof(f175,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | m1_pre_topc(k1_tex_2(sK0,X0),sK0)) ) | ~spl4_12),
% 0.21/0.51    inference(avatar_component_clause,[],[f174])).
% 0.21/0.51  fof(f176,plain,(
% 0.21/0.51    spl4_12 | spl4_1 | ~spl4_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f147,f102,f97,f174])).
% 0.21/0.51  fof(f147,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | m1_pre_topc(k1_tex_2(sK0,X0),sK0)) ) | (spl4_1 | ~spl4_2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f146,f99])).
% 0.21/0.51  fof(f146,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | m1_pre_topc(k1_tex_2(sK0,X0),sK0) | v2_struct_0(sK0)) ) | ~spl4_2),
% 0.21/0.51    inference(resolution,[],[f92,f104])).
% 0.21/0.51  fof(f92,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | m1_pre_topc(k1_tex_2(X0,X1),X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f45])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f44])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,axiom,(
% 0.21/0.51    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).
% 0.21/0.51  fof(f172,plain,(
% 0.21/0.51    ~spl4_2 | spl4_10),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f171])).
% 0.21/0.51  fof(f171,plain,(
% 0.21/0.51    $false | (~spl4_2 | spl4_10)),
% 0.21/0.51    inference(subsumption_resolution,[],[f169,f104])).
% 0.21/0.51  fof(f169,plain,(
% 0.21/0.51    ~l1_pre_topc(sK0) | spl4_10),
% 0.21/0.51    inference(resolution,[],[f161,f71])).
% 0.21/0.51  fof(f161,plain,(
% 0.21/0.51    ~l1_struct_0(sK0) | spl4_10),
% 0.21/0.51    inference(avatar_component_clause,[],[f159])).
% 0.21/0.51  fof(f145,plain,(
% 0.21/0.51    spl4_8 | ~spl4_3 | ~spl4_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f139,f132,f107,f142])).
% 0.21/0.51  fof(f132,plain,(
% 0.21/0.51    spl4_6 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | v7_struct_0(k1_tex_2(sK0,X0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.51  fof(f139,plain,(
% 0.21/0.51    v7_struct_0(k1_tex_2(sK0,sK1)) | (~spl4_3 | ~spl4_6)),
% 0.21/0.51    inference(resolution,[],[f133,f109])).
% 0.21/0.51  fof(f133,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | v7_struct_0(k1_tex_2(sK0,X0))) ) | ~spl4_6),
% 0.21/0.51    inference(avatar_component_clause,[],[f132])).
% 0.21/0.51  fof(f134,plain,(
% 0.21/0.51    spl4_6 | spl4_1 | ~spl4_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f128,f102,f97,f132])).
% 0.21/0.51  fof(f128,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | v7_struct_0(k1_tex_2(sK0,X0))) ) | (spl4_1 | ~spl4_2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f127,f99])).
% 0.21/0.51  fof(f127,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | v7_struct_0(k1_tex_2(sK0,X0)) | v2_struct_0(sK0)) ) | ~spl4_2),
% 0.21/0.51    inference(resolution,[],[f88,f104])).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v7_struct_0(k1_tex_2(X0,X1)) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f43])).
% 0.21/0.51  fof(f124,plain,(
% 0.21/0.51    ~spl4_4 | ~spl4_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f123,f119,f115])).
% 0.21/0.51  fof(f123,plain,(
% 0.21/0.51    ~v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~spl4_5),
% 0.21/0.51    inference(subsumption_resolution,[],[f66,f121])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f52])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    ((~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,sK1),sK0)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0)) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f49,f51,f50])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,X1),sK0)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,X1),sK0)) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    ? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,X1),sK0)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,X1),sK0)) & m1_subset_1(X1,u1_struct_0(sK0))) => ((~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,sK1),sK0)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0)) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f48])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f19])).
% 0.21/0.51  fof(f19,negated_conjecture,(
% 0.21/0.51    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 0.21/0.51    inference(negated_conjecture,[],[f18])).
% 0.21/0.51  fof(f18,conjecture,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_tex_2)).
% 0.21/0.51  fof(f122,plain,(
% 0.21/0.51    spl4_4 | spl4_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f65,f119,f115])).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f52])).
% 0.21/0.51  fof(f110,plain,(
% 0.21/0.51    spl4_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f64,f107])).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.51    inference(cnf_transformation,[],[f52])).
% 0.21/0.51  fof(f105,plain,(
% 0.21/0.51    spl4_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f63,f102])).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    l1_pre_topc(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f52])).
% 0.21/0.51  fof(f100,plain,(
% 0.21/0.51    ~spl4_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f62,f97])).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    ~v2_struct_0(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f52])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (18297)------------------------------
% 0.21/0.51  % (18297)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (18297)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (18297)Memory used [KB]: 6396
% 0.21/0.51  % (18297)Time elapsed: 0.101 s
% 0.21/0.51  % (18297)------------------------------
% 0.21/0.51  % (18297)------------------------------
% 0.21/0.51  % (18319)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.51  % (18294)Success in time 0.154 s
%------------------------------------------------------------------------------
