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
% DateTime   : Thu Dec  3 13:21:19 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 226 expanded)
%              Number of leaves         :   22 (  94 expanded)
%              Depth                    :   12
%              Number of atoms          :  507 ( 803 expanded)
%              Number of equality atoms :   21 (  21 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f146,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f54,f58,f62,f83,f87,f91,f95,f99,f125,f129,f140,f144,f145])).

fof(f145,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) != u1_struct_0(k1_tex_2(sK0,sK1))
    | v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK1),sK0)
    | ~ v2_tex_2(u1_struct_0(k1_tex_2(sK0,sK1)),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f144,plain,
    ( spl2_14
    | spl2_1
    | ~ spl2_3
    | spl2_5
    | ~ spl2_9
    | ~ spl2_11
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f136,f127,f123,f97,f81,f56,f48,f142])).

fof(f142,plain,
    ( spl2_14
  <=> v2_tex_2(u1_struct_0(k1_tex_2(sK0,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f48,plain,
    ( spl2_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f56,plain,
    ( spl2_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f81,plain,
    ( spl2_5
  <=> v2_struct_0(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f97,plain,
    ( spl2_9
  <=> m1_pre_topc(k1_tex_2(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f123,plain,
    ( spl2_11
  <=> v1_tdlat_3(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f127,plain,
    ( spl2_12
  <=> m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f136,plain,
    ( v2_tex_2(u1_struct_0(k1_tex_2(sK0,sK1)),sK0)
    | spl2_1
    | ~ spl2_3
    | spl2_5
    | ~ spl2_9
    | ~ spl2_11
    | ~ spl2_12 ),
    inference(subsumption_resolution,[],[f135,f124])).

fof(f124,plain,
    ( v1_tdlat_3(k1_tex_2(sK0,sK1))
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f123])).

fof(f135,plain,
    ( ~ v1_tdlat_3(k1_tex_2(sK0,sK1))
    | v2_tex_2(u1_struct_0(k1_tex_2(sK0,sK1)),sK0)
    | spl2_1
    | ~ spl2_3
    | spl2_5
    | ~ spl2_9
    | ~ spl2_12 ),
    inference(subsumption_resolution,[],[f134,f49])).

fof(f49,plain,
    ( ~ v2_struct_0(sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f48])).

fof(f134,plain,
    ( v2_struct_0(sK0)
    | ~ v1_tdlat_3(k1_tex_2(sK0,sK1))
    | v2_tex_2(u1_struct_0(k1_tex_2(sK0,sK1)),sK0)
    | ~ spl2_3
    | spl2_5
    | ~ spl2_9
    | ~ spl2_12 ),
    inference(subsumption_resolution,[],[f133,f98])).

fof(f98,plain,
    ( m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f97])).

fof(f133,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | v2_struct_0(sK0)
    | ~ v1_tdlat_3(k1_tex_2(sK0,sK1))
    | v2_tex_2(u1_struct_0(k1_tex_2(sK0,sK1)),sK0)
    | ~ spl2_3
    | spl2_5
    | ~ spl2_12 ),
    inference(subsumption_resolution,[],[f132,f82])).

fof(f82,plain,
    ( ~ v2_struct_0(k1_tex_2(sK0,sK1))
    | spl2_5 ),
    inference(avatar_component_clause,[],[f81])).

fof(f132,plain,
    ( v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | v2_struct_0(sK0)
    | ~ v1_tdlat_3(k1_tex_2(sK0,sK1))
    | v2_tex_2(u1_struct_0(k1_tex_2(sK0,sK1)),sK0)
    | ~ spl2_3
    | ~ spl2_12 ),
    inference(subsumption_resolution,[],[f130,f57])).

fof(f57,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f56])).

fof(f130,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | v2_struct_0(sK0)
    | ~ v1_tdlat_3(k1_tex_2(sK0,sK1))
    | v2_tex_2(u1_struct_0(k1_tex_2(sK0,sK1)),sK0)
    | ~ spl2_12 ),
    inference(resolution,[],[f128,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0)
      | ~ v1_tdlat_3(X1)
      | v2_tex_2(u1_struct_0(X1),X0) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | ~ v1_tdlat_3(X1)
      | v2_tex_2(X2,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( v2_tex_2(X2,X0)
                <=> v1_tdlat_3(X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_tex_2)).

fof(f128,plain,
    ( m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f127])).

fof(f140,plain,
    ( spl2_13
    | spl2_1
    | ~ spl2_3
    | ~ spl2_4
    | spl2_5
    | ~ spl2_7
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f108,f97,f89,f81,f60,f56,f48,f138])).

fof(f138,plain,
    ( spl2_13
  <=> k6_domain_1(u1_struct_0(sK0),sK1) = u1_struct_0(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f60,plain,
    ( spl2_4
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f89,plain,
    ( spl2_7
  <=> v1_pre_topc(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f108,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = u1_struct_0(k1_tex_2(sK0,sK1))
    | spl2_1
    | ~ spl2_3
    | ~ spl2_4
    | spl2_5
    | ~ spl2_7
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f107,f49])).

fof(f107,plain,
    ( v2_struct_0(sK0)
    | k6_domain_1(u1_struct_0(sK0),sK1) = u1_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_4
    | spl2_5
    | ~ spl2_7
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f106,f90])).

fof(f90,plain,
    ( v1_pre_topc(k1_tex_2(sK0,sK1))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f89])).

fof(f106,plain,
    ( ~ v1_pre_topc(k1_tex_2(sK0,sK1))
    | v2_struct_0(sK0)
    | k6_domain_1(u1_struct_0(sK0),sK1) = u1_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_4
    | spl2_5
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f105,f82])).

fof(f105,plain,
    ( v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ v1_pre_topc(k1_tex_2(sK0,sK1))
    | v2_struct_0(sK0)
    | k6_domain_1(u1_struct_0(sK0),sK1) = u1_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f104,f61])).

fof(f61,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f60])).

fof(f104,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ v1_pre_topc(k1_tex_2(sK0,sK1))
    | v2_struct_0(sK0)
    | k6_domain_1(u1_struct_0(sK0),sK1) = u1_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f100,f57])).

fof(f100,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ v1_pre_topc(k1_tex_2(sK0,sK1))
    | v2_struct_0(sK0)
    | k6_domain_1(u1_struct_0(sK0),sK1) = u1_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl2_9 ),
    inference(resolution,[],[f98,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(k1_tex_2(X0,X1))
      | ~ v1_pre_topc(k1_tex_2(X0,X1))
      | v2_struct_0(X0)
      | k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X2)
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X2,X0)
      | u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)
      | k1_tex_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_tex_2(X0,X1) = X2
              <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_tex_2(X0,X1) = X2
              <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_pre_topc(X2)
                & ~ v2_struct_0(X2) )
             => ( k1_tex_2(X0,X1) = X2
              <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tex_2)).

fof(f129,plain,
    ( spl2_12
    | ~ spl2_3
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f109,f97,f56,f127])).

fof(f109,plain,
    ( m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f101,f57])).

fof(f101,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_9 ),
    inference(resolution,[],[f98,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f125,plain,
    ( spl2_11
    | spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | spl2_5
    | ~ spl2_8
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f116,f97,f93,f81,f56,f52,f48,f123])).

fof(f52,plain,
    ( spl2_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f93,plain,
    ( spl2_8
  <=> v7_struct_0(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f116,plain,
    ( v1_tdlat_3(k1_tex_2(sK0,sK1))
    | spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | spl2_5
    | ~ spl2_8
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f113,f115])).

fof(f115,plain,
    ( v2_pre_topc(k1_tex_2(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f114,f53])).

fof(f53,plain,
    ( v2_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f52])).

fof(f114,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_pre_topc(k1_tex_2(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f103,f57])).

fof(f103,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_pre_topc(k1_tex_2(sK0,sK1))
    | ~ spl2_9 ),
    inference(resolution,[],[f98,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f113,plain,
    ( ~ v2_pre_topc(k1_tex_2(sK0,sK1))
    | v1_tdlat_3(k1_tex_2(sK0,sK1))
    | spl2_1
    | ~ spl2_3
    | spl2_5
    | ~ spl2_8
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f112,f94])).

fof(f94,plain,
    ( v7_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f93])).

fof(f112,plain,
    ( ~ v7_struct_0(k1_tex_2(sK0,sK1))
    | ~ v2_pre_topc(k1_tex_2(sK0,sK1))
    | v1_tdlat_3(k1_tex_2(sK0,sK1))
    | spl2_1
    | ~ spl2_3
    | spl2_5
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f111,f82])).

fof(f111,plain,
    ( v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ v7_struct_0(k1_tex_2(sK0,sK1))
    | ~ v2_pre_topc(k1_tex_2(sK0,sK1))
    | v1_tdlat_3(k1_tex_2(sK0,sK1))
    | spl2_1
    | ~ spl2_3
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f110,f49])).

fof(f110,plain,
    ( v2_struct_0(sK0)
    | v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ v7_struct_0(k1_tex_2(sK0,sK1))
    | ~ v2_pre_topc(k1_tex_2(sK0,sK1))
    | v1_tdlat_3(k1_tex_2(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f102,f57])).

fof(f102,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ v7_struct_0(k1_tex_2(sK0,sK1))
    | ~ v2_pre_topc(k1_tex_2(sK0,sK1))
    | v1_tdlat_3(k1_tex_2(sK0,sK1))
    | ~ spl2_9 ),
    inference(resolution,[],[f98,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | ~ v7_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | v1_tdlat_3(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tdlat_3(X1)
            & ~ v2_struct_0(X1) )
          | ~ v2_pre_topc(X1)
          | ~ v7_struct_0(X1)
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tdlat_3(X1)
            & ~ v2_struct_0(X1) )
          | ~ v2_pre_topc(X1)
          | ~ v7_struct_0(X1)
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( ( v2_pre_topc(X1)
              & v7_struct_0(X1)
              & ~ v2_struct_0(X1) )
           => ( v1_tdlat_3(X1)
              & ~ v2_struct_0(X1) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( ( v2_pre_topc(X1)
              & v7_struct_0(X1)
              & ~ v2_struct_0(X1) )
           => ( v2_tdlat_3(X1)
              & v1_tdlat_3(X1)
              & ~ v2_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc25_tex_2)).

fof(f99,plain,
    ( spl2_9
    | spl2_1
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f77,f60,f56,f48,f97])).

fof(f77,plain,
    ( m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | spl2_1
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f76,f49])).

fof(f76,plain,
    ( v2_struct_0(sK0)
    | m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f66,f57])).

fof(f66,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ spl2_4 ),
    inference(resolution,[],[f61,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | m1_pre_topc(k1_tex_2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f18])).

% (26114)Refutation not found, incomplete strategy% (26114)------------------------------
% (26114)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (26114)Termination reason: Refutation not found, incomplete strategy

% (26114)Memory used [KB]: 10490
% (26114)Time elapsed: 0.079 s
% (26114)------------------------------
% (26114)------------------------------
fof(f18,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).

fof(f95,plain,
    ( spl2_8
    | spl2_1
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f79,f60,f56,f48,f93])).

fof(f79,plain,
    ( v7_struct_0(k1_tex_2(sK0,sK1))
    | spl2_1
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f78,f49])).

fof(f78,plain,
    ( v2_struct_0(sK0)
    | v7_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f68,f57])).

% (26123)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
fof(f68,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v7_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl2_4 ),
    inference(resolution,[],[f61,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v7_struct_0(k1_tex_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_tex_2)).

fof(f91,plain,
    ( spl2_7
    | spl2_1
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f75,f60,f56,f48,f89])).

fof(f75,plain,
    ( v1_pre_topc(k1_tex_2(sK0,sK1))
    | spl2_1
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f74,f49])).

fof(f74,plain,
    ( v2_struct_0(sK0)
    | v1_pre_topc(k1_tex_2(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f65,f57])).

fof(f65,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_pre_topc(k1_tex_2(sK0,sK1))
    | ~ spl2_4 ),
    inference(resolution,[],[f61,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_pre_topc(k1_tex_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f87,plain,(
    ~ spl2_6 ),
    inference(avatar_split_clause,[],[f27,f85])).

fof(f85,plain,
    ( spl2_6
  <=> v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f27,plain,(
    ~ v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).

fof(f83,plain,
    ( ~ spl2_5
    | spl2_1
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f73,f60,f56,f48,f81])).

fof(f73,plain,
    ( ~ v2_struct_0(k1_tex_2(sK0,sK1))
    | spl2_1
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f72,f49])).

fof(f72,plain,
    ( v2_struct_0(sK0)
    | ~ v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f64,f57])).

fof(f64,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl2_4 ),
    inference(resolution,[],[f61,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v2_struct_0(k1_tex_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f62,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f26,f60])).

fof(f26,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f58,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f30,f56])).

fof(f30,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f54,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f29,f52])).

fof(f29,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f50,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f28,f48])).

fof(f28,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:27:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.48  % (26115)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.48  % (26116)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.48  % (26119)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.48  % (26113)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.49  % (26127)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.49  % (26113)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % (26117)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.49  % (26128)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.50  % (26126)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.50  % (26125)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % (26120)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.50  % (26133)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.50  % (26126)Refutation not found, incomplete strategy% (26126)------------------------------
% 0.22/0.50  % (26126)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (26126)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (26126)Memory used [KB]: 1663
% 0.22/0.50  % (26126)Time elapsed: 0.084 s
% 0.22/0.50  % (26126)------------------------------
% 0.22/0.50  % (26126)------------------------------
% 0.22/0.50  % (26125)Refutation not found, incomplete strategy% (26125)------------------------------
% 0.22/0.50  % (26125)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (26125)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (26125)Memory used [KB]: 6140
% 0.22/0.50  % (26125)Time elapsed: 0.085 s
% 0.22/0.50  % (26125)------------------------------
% 0.22/0.50  % (26125)------------------------------
% 0.22/0.50  % (26114)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f146,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f50,f54,f58,f62,f83,f87,f91,f95,f99,f125,f129,f140,f144,f145])).
% 0.22/0.50  fof(f145,plain,(
% 0.22/0.50    k6_domain_1(u1_struct_0(sK0),sK1) != u1_struct_0(k1_tex_2(sK0,sK1)) | v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK1),sK0) | ~v2_tex_2(u1_struct_0(k1_tex_2(sK0,sK1)),sK0)),
% 0.22/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.50  fof(f144,plain,(
% 0.22/0.50    spl2_14 | spl2_1 | ~spl2_3 | spl2_5 | ~spl2_9 | ~spl2_11 | ~spl2_12),
% 0.22/0.50    inference(avatar_split_clause,[],[f136,f127,f123,f97,f81,f56,f48,f142])).
% 0.22/0.50  fof(f142,plain,(
% 0.22/0.50    spl2_14 <=> v2_tex_2(u1_struct_0(k1_tex_2(sK0,sK1)),sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    spl2_1 <=> v2_struct_0(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.50  fof(f56,plain,(
% 0.22/0.50    spl2_3 <=> l1_pre_topc(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.50  fof(f81,plain,(
% 0.22/0.50    spl2_5 <=> v2_struct_0(k1_tex_2(sK0,sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.50  fof(f97,plain,(
% 0.22/0.50    spl2_9 <=> m1_pre_topc(k1_tex_2(sK0,sK1),sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.22/0.50  fof(f123,plain,(
% 0.22/0.50    spl2_11 <=> v1_tdlat_3(k1_tex_2(sK0,sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.22/0.50  fof(f127,plain,(
% 0.22/0.50    spl2_12 <=> m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.22/0.50  fof(f136,plain,(
% 0.22/0.50    v2_tex_2(u1_struct_0(k1_tex_2(sK0,sK1)),sK0) | (spl2_1 | ~spl2_3 | spl2_5 | ~spl2_9 | ~spl2_11 | ~spl2_12)),
% 0.22/0.50    inference(subsumption_resolution,[],[f135,f124])).
% 0.22/0.50  fof(f124,plain,(
% 0.22/0.50    v1_tdlat_3(k1_tex_2(sK0,sK1)) | ~spl2_11),
% 0.22/0.50    inference(avatar_component_clause,[],[f123])).
% 0.22/0.50  fof(f135,plain,(
% 0.22/0.50    ~v1_tdlat_3(k1_tex_2(sK0,sK1)) | v2_tex_2(u1_struct_0(k1_tex_2(sK0,sK1)),sK0) | (spl2_1 | ~spl2_3 | spl2_5 | ~spl2_9 | ~spl2_12)),
% 0.22/0.50    inference(subsumption_resolution,[],[f134,f49])).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    ~v2_struct_0(sK0) | spl2_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f48])).
% 0.22/0.50  fof(f134,plain,(
% 0.22/0.50    v2_struct_0(sK0) | ~v1_tdlat_3(k1_tex_2(sK0,sK1)) | v2_tex_2(u1_struct_0(k1_tex_2(sK0,sK1)),sK0) | (~spl2_3 | spl2_5 | ~spl2_9 | ~spl2_12)),
% 0.22/0.50    inference(subsumption_resolution,[],[f133,f98])).
% 0.22/0.50  fof(f98,plain,(
% 0.22/0.50    m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~spl2_9),
% 0.22/0.50    inference(avatar_component_clause,[],[f97])).
% 0.22/0.50  fof(f133,plain,(
% 0.22/0.50    ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | v2_struct_0(sK0) | ~v1_tdlat_3(k1_tex_2(sK0,sK1)) | v2_tex_2(u1_struct_0(k1_tex_2(sK0,sK1)),sK0) | (~spl2_3 | spl2_5 | ~spl2_12)),
% 0.22/0.50    inference(subsumption_resolution,[],[f132,f82])).
% 0.22/0.50  fof(f82,plain,(
% 0.22/0.50    ~v2_struct_0(k1_tex_2(sK0,sK1)) | spl2_5),
% 0.22/0.50    inference(avatar_component_clause,[],[f81])).
% 0.22/0.50  fof(f132,plain,(
% 0.22/0.50    v2_struct_0(k1_tex_2(sK0,sK1)) | ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | v2_struct_0(sK0) | ~v1_tdlat_3(k1_tex_2(sK0,sK1)) | v2_tex_2(u1_struct_0(k1_tex_2(sK0,sK1)),sK0) | (~spl2_3 | ~spl2_12)),
% 0.22/0.50    inference(subsumption_resolution,[],[f130,f57])).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    l1_pre_topc(sK0) | ~spl2_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f56])).
% 0.22/0.50  fof(f130,plain,(
% 0.22/0.50    ~l1_pre_topc(sK0) | v2_struct_0(k1_tex_2(sK0,sK1)) | ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | v2_struct_0(sK0) | ~v1_tdlat_3(k1_tex_2(sK0,sK1)) | v2_tex_2(u1_struct_0(k1_tex_2(sK0,sK1)),sK0) | ~spl2_12),
% 0.22/0.50    inference(resolution,[],[f128,f45])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X0) | ~v1_tdlat_3(X1) | v2_tex_2(u1_struct_0(X1),X0)) )),
% 0.22/0.50    inference(equality_resolution,[],[f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X2 | ~v1_tdlat_3(X1) | v2_tex_2(X2,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => (v2_tex_2(X2,X0) <=> v1_tdlat_3(X1))))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_tex_2)).
% 0.22/0.50  fof(f128,plain,(
% 0.22/0.50    m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_12),
% 0.22/0.50    inference(avatar_component_clause,[],[f127])).
% 0.22/0.50  fof(f140,plain,(
% 0.22/0.50    spl2_13 | spl2_1 | ~spl2_3 | ~spl2_4 | spl2_5 | ~spl2_7 | ~spl2_9),
% 0.22/0.50    inference(avatar_split_clause,[],[f108,f97,f89,f81,f60,f56,f48,f138])).
% 0.22/0.50  fof(f138,plain,(
% 0.22/0.50    spl2_13 <=> k6_domain_1(u1_struct_0(sK0),sK1) = u1_struct_0(k1_tex_2(sK0,sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    spl2_4 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.50  fof(f89,plain,(
% 0.22/0.50    spl2_7 <=> v1_pre_topc(k1_tex_2(sK0,sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.22/0.50  fof(f108,plain,(
% 0.22/0.50    k6_domain_1(u1_struct_0(sK0),sK1) = u1_struct_0(k1_tex_2(sK0,sK1)) | (spl2_1 | ~spl2_3 | ~spl2_4 | spl2_5 | ~spl2_7 | ~spl2_9)),
% 0.22/0.50    inference(subsumption_resolution,[],[f107,f49])).
% 0.22/0.50  fof(f107,plain,(
% 0.22/0.50    v2_struct_0(sK0) | k6_domain_1(u1_struct_0(sK0),sK1) = u1_struct_0(k1_tex_2(sK0,sK1)) | (~spl2_3 | ~spl2_4 | spl2_5 | ~spl2_7 | ~spl2_9)),
% 0.22/0.50    inference(subsumption_resolution,[],[f106,f90])).
% 0.22/0.50  fof(f90,plain,(
% 0.22/0.50    v1_pre_topc(k1_tex_2(sK0,sK1)) | ~spl2_7),
% 0.22/0.50    inference(avatar_component_clause,[],[f89])).
% 0.22/0.50  fof(f106,plain,(
% 0.22/0.50    ~v1_pre_topc(k1_tex_2(sK0,sK1)) | v2_struct_0(sK0) | k6_domain_1(u1_struct_0(sK0),sK1) = u1_struct_0(k1_tex_2(sK0,sK1)) | (~spl2_3 | ~spl2_4 | spl2_5 | ~spl2_9)),
% 0.22/0.50    inference(subsumption_resolution,[],[f105,f82])).
% 0.22/0.50  fof(f105,plain,(
% 0.22/0.50    v2_struct_0(k1_tex_2(sK0,sK1)) | ~v1_pre_topc(k1_tex_2(sK0,sK1)) | v2_struct_0(sK0) | k6_domain_1(u1_struct_0(sK0),sK1) = u1_struct_0(k1_tex_2(sK0,sK1)) | (~spl2_3 | ~spl2_4 | ~spl2_9)),
% 0.22/0.50    inference(subsumption_resolution,[],[f104,f61])).
% 0.22/0.50  fof(f61,plain,(
% 0.22/0.50    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl2_4),
% 0.22/0.50    inference(avatar_component_clause,[],[f60])).
% 0.22/0.50  fof(f104,plain,(
% 0.22/0.50    ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(k1_tex_2(sK0,sK1)) | ~v1_pre_topc(k1_tex_2(sK0,sK1)) | v2_struct_0(sK0) | k6_domain_1(u1_struct_0(sK0),sK1) = u1_struct_0(k1_tex_2(sK0,sK1)) | (~spl2_3 | ~spl2_9)),
% 0.22/0.50    inference(subsumption_resolution,[],[f100,f57])).
% 0.22/0.50  fof(f100,plain,(
% 0.22/0.50    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(k1_tex_2(sK0,sK1)) | ~v1_pre_topc(k1_tex_2(sK0,sK1)) | v2_struct_0(sK0) | k6_domain_1(u1_struct_0(sK0),sK1) = u1_struct_0(k1_tex_2(sK0,sK1)) | ~spl2_9),
% 0.22/0.50    inference(resolution,[],[f98,f46])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_pre_topc(k1_tex_2(X0,X1),X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(k1_tex_2(X0,X1)) | ~v1_pre_topc(k1_tex_2(X0,X1)) | v2_struct_0(X0) | k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1))) )),
% 0.22/0.50    inference(equality_resolution,[],[f34])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X2,X0) | u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) | k1_tex_2(X0,X1) != X2) )),
% 0.22/0.50    inference(cnf_transformation,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : ((k1_tex_2(X0,X1) = X2 <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : ((k1_tex_2(X0,X1) = X2 <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)) | (~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => (k1_tex_2(X0,X1) = X2 <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tex_2)).
% 0.22/0.50  fof(f129,plain,(
% 0.22/0.50    spl2_12 | ~spl2_3 | ~spl2_9),
% 0.22/0.50    inference(avatar_split_clause,[],[f109,f97,f56,f127])).
% 0.22/0.50  fof(f109,plain,(
% 0.22/0.50    m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_3 | ~spl2_9)),
% 0.22/0.50    inference(subsumption_resolution,[],[f101,f57])).
% 0.22/0.50  fof(f101,plain,(
% 0.22/0.50    ~l1_pre_topc(sK0) | m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_9),
% 0.22/0.50    inference(resolution,[],[f98,f40])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.22/0.50  fof(f125,plain,(
% 0.22/0.50    spl2_11 | spl2_1 | ~spl2_2 | ~spl2_3 | spl2_5 | ~spl2_8 | ~spl2_9),
% 0.22/0.50    inference(avatar_split_clause,[],[f116,f97,f93,f81,f56,f52,f48,f123])).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    spl2_2 <=> v2_pre_topc(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.50  fof(f93,plain,(
% 0.22/0.50    spl2_8 <=> v7_struct_0(k1_tex_2(sK0,sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.22/0.50  fof(f116,plain,(
% 0.22/0.50    v1_tdlat_3(k1_tex_2(sK0,sK1)) | (spl2_1 | ~spl2_2 | ~spl2_3 | spl2_5 | ~spl2_8 | ~spl2_9)),
% 0.22/0.50    inference(subsumption_resolution,[],[f113,f115])).
% 0.22/0.50  fof(f115,plain,(
% 0.22/0.50    v2_pre_topc(k1_tex_2(sK0,sK1)) | (~spl2_2 | ~spl2_3 | ~spl2_9)),
% 0.22/0.50    inference(subsumption_resolution,[],[f114,f53])).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    v2_pre_topc(sK0) | ~spl2_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f52])).
% 0.22/0.50  fof(f114,plain,(
% 0.22/0.50    ~v2_pre_topc(sK0) | v2_pre_topc(k1_tex_2(sK0,sK1)) | (~spl2_3 | ~spl2_9)),
% 0.22/0.50    inference(subsumption_resolution,[],[f103,f57])).
% 0.22/0.50  fof(f103,plain,(
% 0.22/0.50    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_pre_topc(k1_tex_2(sK0,sK1)) | ~spl2_9),
% 0.22/0.50    inference(resolution,[],[f98,f38])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_pre_topc(X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.50    inference(flattening,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 0.22/0.50  fof(f113,plain,(
% 0.22/0.50    ~v2_pre_topc(k1_tex_2(sK0,sK1)) | v1_tdlat_3(k1_tex_2(sK0,sK1)) | (spl2_1 | ~spl2_3 | spl2_5 | ~spl2_8 | ~spl2_9)),
% 0.22/0.50    inference(subsumption_resolution,[],[f112,f94])).
% 0.22/0.50  fof(f94,plain,(
% 0.22/0.50    v7_struct_0(k1_tex_2(sK0,sK1)) | ~spl2_8),
% 0.22/0.50    inference(avatar_component_clause,[],[f93])).
% 0.22/0.50  fof(f112,plain,(
% 0.22/0.50    ~v7_struct_0(k1_tex_2(sK0,sK1)) | ~v2_pre_topc(k1_tex_2(sK0,sK1)) | v1_tdlat_3(k1_tex_2(sK0,sK1)) | (spl2_1 | ~spl2_3 | spl2_5 | ~spl2_9)),
% 0.22/0.50    inference(subsumption_resolution,[],[f111,f82])).
% 0.22/0.50  fof(f111,plain,(
% 0.22/0.50    v2_struct_0(k1_tex_2(sK0,sK1)) | ~v7_struct_0(k1_tex_2(sK0,sK1)) | ~v2_pre_topc(k1_tex_2(sK0,sK1)) | v1_tdlat_3(k1_tex_2(sK0,sK1)) | (spl2_1 | ~spl2_3 | ~spl2_9)),
% 0.22/0.50    inference(subsumption_resolution,[],[f110,f49])).
% 0.22/0.50  fof(f110,plain,(
% 0.22/0.50    v2_struct_0(sK0) | v2_struct_0(k1_tex_2(sK0,sK1)) | ~v7_struct_0(k1_tex_2(sK0,sK1)) | ~v2_pre_topc(k1_tex_2(sK0,sK1)) | v1_tdlat_3(k1_tex_2(sK0,sK1)) | (~spl2_3 | ~spl2_9)),
% 0.22/0.50    inference(subsumption_resolution,[],[f102,f57])).
% 0.22/0.50  fof(f102,plain,(
% 0.22/0.50    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v2_struct_0(k1_tex_2(sK0,sK1)) | ~v7_struct_0(k1_tex_2(sK0,sK1)) | ~v2_pre_topc(k1_tex_2(sK0,sK1)) | v1_tdlat_3(k1_tex_2(sK0,sK1)) | ~spl2_9),
% 0.22/0.50    inference(resolution,[],[f98,f39])).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v2_struct_0(X1) | ~v7_struct_0(X1) | ~v2_pre_topc(X1) | v1_tdlat_3(X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : ((v1_tdlat_3(X1) & ~v2_struct_0(X1)) | ~v2_pre_topc(X1) | ~v7_struct_0(X1) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (((v1_tdlat_3(X1) & ~v2_struct_0(X1)) | (~v2_pre_topc(X1) | ~v7_struct_0(X1) | v2_struct_0(X1))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f10])).
% 0.22/0.50  fof(f10,plain,(
% 0.22/0.50    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ((v2_pre_topc(X1) & v7_struct_0(X1) & ~v2_struct_0(X1)) => (v1_tdlat_3(X1) & ~v2_struct_0(X1)))))),
% 0.22/0.50    inference(pure_predicate_removal,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ((v2_pre_topc(X1) & v7_struct_0(X1) & ~v2_struct_0(X1)) => (v2_tdlat_3(X1) & v1_tdlat_3(X1) & ~v2_struct_0(X1)))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc25_tex_2)).
% 0.22/0.50  fof(f99,plain,(
% 0.22/0.50    spl2_9 | spl2_1 | ~spl2_3 | ~spl2_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f77,f60,f56,f48,f97])).
% 0.22/0.50  fof(f77,plain,(
% 0.22/0.50    m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | (spl2_1 | ~spl2_3 | ~spl2_4)),
% 0.22/0.50    inference(subsumption_resolution,[],[f76,f49])).
% 0.22/0.50  fof(f76,plain,(
% 0.22/0.50    v2_struct_0(sK0) | m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | (~spl2_3 | ~spl2_4)),
% 0.22/0.50    inference(subsumption_resolution,[],[f66,f57])).
% 0.22/0.50  fof(f66,plain,(
% 0.22/0.50    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~spl2_4),
% 0.22/0.50    inference(resolution,[],[f61,f37])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0) | m1_pre_topc(k1_tex_2(X0,X1),X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f18])).
% 0.22/0.50  % (26114)Refutation not found, incomplete strategy% (26114)------------------------------
% 0.22/0.50  % (26114)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (26114)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (26114)Memory used [KB]: 10490
% 0.22/0.50  % (26114)Time elapsed: 0.079 s
% 0.22/0.50  % (26114)------------------------------
% 0.22/0.50  % (26114)------------------------------
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).
% 0.22/0.50  fof(f95,plain,(
% 0.22/0.50    spl2_8 | spl2_1 | ~spl2_3 | ~spl2_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f79,f60,f56,f48,f93])).
% 0.22/0.50  fof(f79,plain,(
% 0.22/0.50    v7_struct_0(k1_tex_2(sK0,sK1)) | (spl2_1 | ~spl2_3 | ~spl2_4)),
% 0.22/0.50    inference(subsumption_resolution,[],[f78,f49])).
% 0.22/0.50  fof(f78,plain,(
% 0.22/0.50    v2_struct_0(sK0) | v7_struct_0(k1_tex_2(sK0,sK1)) | (~spl2_3 | ~spl2_4)),
% 0.22/0.50    inference(subsumption_resolution,[],[f68,f57])).
% 0.22/0.50  % (26123)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.50  fof(f68,plain,(
% 0.22/0.50    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v7_struct_0(k1_tex_2(sK0,sK1)) | ~spl2_4),
% 0.22/0.50    inference(resolution,[],[f61,f42])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v7_struct_0(k1_tex_2(X0,X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ! [X0,X1] : ((v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ! [X0,X1] : ((v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_tex_2)).
% 0.22/0.50  fof(f91,plain,(
% 0.22/0.50    spl2_7 | spl2_1 | ~spl2_3 | ~spl2_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f75,f60,f56,f48,f89])).
% 0.22/0.50  fof(f75,plain,(
% 0.22/0.50    v1_pre_topc(k1_tex_2(sK0,sK1)) | (spl2_1 | ~spl2_3 | ~spl2_4)),
% 0.22/0.50    inference(subsumption_resolution,[],[f74,f49])).
% 0.22/0.50  fof(f74,plain,(
% 0.22/0.50    v2_struct_0(sK0) | v1_pre_topc(k1_tex_2(sK0,sK1)) | (~spl2_3 | ~spl2_4)),
% 0.22/0.50    inference(subsumption_resolution,[],[f65,f57])).
% 0.22/0.50  fof(f65,plain,(
% 0.22/0.50    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v1_pre_topc(k1_tex_2(sK0,sK1)) | ~spl2_4),
% 0.22/0.50    inference(resolution,[],[f61,f36])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v1_pre_topc(k1_tex_2(X0,X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f18])).
% 0.22/0.50  fof(f87,plain,(
% 0.22/0.50    ~spl2_6),
% 0.22/0.50    inference(avatar_split_clause,[],[f27,f85])).
% 0.22/0.50  fof(f85,plain,(
% 0.22/0.50    spl2_6 <=> v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK1),sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ~v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK1),sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f12])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (~v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f11])).
% 0.22/0.50  fof(f11,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (~v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,negated_conjecture,(
% 0.22/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 0.22/0.50    inference(negated_conjecture,[],[f8])).
% 0.22/0.50  fof(f8,conjecture,(
% 0.22/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).
% 0.22/0.50  fof(f83,plain,(
% 0.22/0.50    ~spl2_5 | spl2_1 | ~spl2_3 | ~spl2_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f73,f60,f56,f48,f81])).
% 0.22/0.50  fof(f73,plain,(
% 0.22/0.50    ~v2_struct_0(k1_tex_2(sK0,sK1)) | (spl2_1 | ~spl2_3 | ~spl2_4)),
% 0.22/0.50    inference(subsumption_resolution,[],[f72,f49])).
% 0.22/0.50  fof(f72,plain,(
% 0.22/0.50    v2_struct_0(sK0) | ~v2_struct_0(k1_tex_2(sK0,sK1)) | (~spl2_3 | ~spl2_4)),
% 0.22/0.50    inference(subsumption_resolution,[],[f64,f57])).
% 0.22/0.50  fof(f64,plain,(
% 0.22/0.50    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~v2_struct_0(k1_tex_2(sK0,sK1)) | ~spl2_4),
% 0.22/0.50    inference(resolution,[],[f61,f35])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~v2_struct_0(k1_tex_2(X0,X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f18])).
% 0.22/0.50  fof(f62,plain,(
% 0.22/0.50    spl2_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f26,f60])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.50    inference(cnf_transformation,[],[f12])).
% 0.22/0.50  fof(f58,plain,(
% 0.22/0.50    spl2_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f30,f56])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    l1_pre_topc(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f12])).
% 0.22/0.50  fof(f54,plain,(
% 0.22/0.50    spl2_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f29,f52])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    v2_pre_topc(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f12])).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    ~spl2_1),
% 0.22/0.50    inference(avatar_split_clause,[],[f28,f48])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ~v2_struct_0(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f12])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (26113)------------------------------
% 0.22/0.50  % (26113)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (26113)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (26113)Memory used [KB]: 6140
% 0.22/0.50  % (26113)Time elapsed: 0.072 s
% 0.22/0.50  % (26113)------------------------------
% 0.22/0.50  % (26113)------------------------------
% 0.22/0.50  % (26109)Success in time 0.137 s
%------------------------------------------------------------------------------
