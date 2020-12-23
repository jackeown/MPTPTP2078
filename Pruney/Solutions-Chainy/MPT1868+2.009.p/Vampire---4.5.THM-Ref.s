%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:20 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 203 expanded)
%              Number of leaves         :   26 (  89 expanded)
%              Depth                    :   11
%              Number of atoms          :  418 ( 772 expanded)
%              Number of equality atoms :   27 (  34 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f136,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f61,f65,f69,f73,f82,f87,f93,f101,f114,f116,f121,f126,f128,f133,f135])).

fof(f135,plain,
    ( ~ spl2_3
    | spl2_15 ),
    inference(avatar_split_clause,[],[f134,f131,f63])).

fof(f63,plain,
    ( spl2_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f131,plain,
    ( spl2_15
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f134,plain,
    ( ~ l1_pre_topc(sK0)
    | spl2_15 ),
    inference(resolution,[],[f132,f39])).

fof(f39,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f132,plain,
    ( ~ l1_struct_0(sK0)
    | spl2_15 ),
    inference(avatar_component_clause,[],[f131])).

fof(f133,plain,
    ( spl2_5
    | ~ spl2_15
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f129,f95,f131,f71])).

fof(f71,plain,
    ( spl2_5
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f95,plain,
    ( spl2_9
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f129,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl2_9 ),
    inference(resolution,[],[f96,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f96,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f95])).

fof(f128,plain,
    ( spl2_5
    | ~ spl2_3
    | ~ spl2_2
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f127,f105,f59,f63,f71])).

fof(f59,plain,
    ( spl2_2
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f105,plain,
    ( spl2_11
  <=> v2_struct_0(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f127,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl2_11 ),
    inference(resolution,[],[f106,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
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
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).

fof(f106,plain,
    ( v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f105])).

fof(f126,plain,
    ( spl2_5
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_3
    | spl2_14 ),
    inference(avatar_split_clause,[],[f124,f119,f63,f67,f59,f71])).

fof(f67,plain,
    ( spl2_4
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f119,plain,
    ( spl2_14
  <=> v2_pre_topc(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f124,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | spl2_14 ),
    inference(duplicate_literal_removal,[],[f123])).

fof(f123,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl2_14 ),
    inference(resolution,[],[f122,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f122,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k1_tex_2(sK0,sK1),X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | spl2_14 ),
    inference(resolution,[],[f120,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
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

fof(f120,plain,
    ( ~ v2_pre_topc(k1_tex_2(sK0,sK1))
    | spl2_14 ),
    inference(avatar_component_clause,[],[f119])).

fof(f121,plain,
    ( spl2_5
    | ~ spl2_3
    | ~ spl2_2
    | ~ spl2_14
    | spl2_13 ),
    inference(avatar_split_clause,[],[f117,f112,f119,f59,f63,f71])).

fof(f112,plain,
    ( spl2_13
  <=> v1_tdlat_3(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f117,plain,
    ( ~ v2_pre_topc(k1_tex_2(sK0,sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl2_13 ),
    inference(resolution,[],[f113,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_tdlat_3(k1_tex_2(X0,X1))
      | ~ v2_pre_topc(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tdlat_3(k1_tex_2(X0,X1))
          | ~ v2_pre_topc(k1_tex_2(X0,X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tdlat_3(k1_tex_2(X0,X1))
          | ~ v2_pre_topc(k1_tex_2(X0,X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v2_pre_topc(k1_tex_2(X0,X1))
           => v1_tdlat_3(k1_tex_2(X0,X1)) ) ) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v2_pre_topc(k1_tex_2(X0,X1))
           => ( v2_tdlat_3(k1_tex_2(X0,X1))
              & v1_tdlat_3(k1_tex_2(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tex_2)).

fof(f113,plain,
    ( ~ v1_tdlat_3(k1_tex_2(sK0,sK1))
    | spl2_13 ),
    inference(avatar_component_clause,[],[f112])).

fof(f116,plain,
    ( spl2_5
    | ~ spl2_3
    | ~ spl2_2
    | spl2_12 ),
    inference(avatar_split_clause,[],[f115,f108,f59,f63,f71])).

fof(f108,plain,
    ( spl2_12
  <=> m1_pre_topc(k1_tex_2(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f115,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl2_12 ),
    inference(resolution,[],[f109,f50])).

fof(f109,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | spl2_12 ),
    inference(avatar_component_clause,[],[f108])).

fof(f114,plain,
    ( spl2_5
    | ~ spl2_3
    | spl2_11
    | ~ spl2_12
    | spl2_8
    | ~ spl2_13
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f102,f99,f112,f91,f108,f105,f63,f71])).

fof(f91,plain,
    ( spl2_8
  <=> v2_tex_2(u1_struct_0(k1_tex_2(sK0,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f99,plain,
    ( spl2_10
  <=> m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f102,plain,
    ( ~ v1_tdlat_3(k1_tex_2(sK0,sK1))
    | v2_tex_2(u1_struct_0(k1_tex_2(sK0,sK1)),sK0)
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl2_10 ),
    inference(resolution,[],[f52,f100])).

fof(f100,plain,
    ( m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f99])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tdlat_3(X1)
      | v2_tex_2(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(X2,X0)
      | ~ v1_tdlat_3(X1)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_tex_2(X2,X0)
                  | ~ v1_tdlat_3(X1) )
                & ( v1_tdlat_3(X1)
                  | ~ v2_tex_2(X2,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f101,plain,
    ( spl2_9
    | ~ spl2_2
    | spl2_10
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f89,f85,f99,f59,f95])).

fof(f85,plain,
    ( spl2_7
  <=> k6_domain_1(u1_struct_0(sK0),sK1) = u1_struct_0(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f89,plain,
    ( m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl2_7 ),
    inference(superposition,[],[f47,f86])).

fof(f86,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = u1_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f85])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f93,plain,
    ( ~ spl2_8
    | spl2_1
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f88,f85,f55,f91])).

fof(f55,plain,
    ( spl2_1
  <=> v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f88,plain,
    ( ~ v2_tex_2(u1_struct_0(k1_tex_2(sK0,sK1)),sK0)
    | spl2_1
    | ~ spl2_7 ),
    inference(superposition,[],[f56,f86])).

fof(f56,plain,
    ( ~ v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK1),sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f55])).

fof(f87,plain,
    ( spl2_7
    | ~ spl2_2
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f83,f80,f59,f85])).

fof(f80,plain,
    ( spl2_6
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k6_domain_1(u1_struct_0(sK0),X0) = u1_struct_0(k1_tex_2(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f83,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = u1_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_6 ),
    inference(resolution,[],[f81,f60])).

fof(f60,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f81,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k6_domain_1(u1_struct_0(sK0),X0) = u1_struct_0(k1_tex_2(sK0,X0)) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f80])).

fof(f82,plain,
    ( spl2_5
    | spl2_6
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f77,f63,f80,f71])).

fof(f77,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k6_domain_1(u1_struct_0(sK0),X0) = u1_struct_0(k1_tex_2(sK0,X0))
        | v2_struct_0(sK0) )
    | ~ spl2_3 ),
    inference(resolution,[],[f76,f64])).

fof(f64,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f63])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1))
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f75,f48])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1))
      | v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f74,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1))
      | ~ v1_pre_topc(k1_tex_2(X0,X1))
      | v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f51,f50])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1))
      | ~ m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ v1_pre_topc(k1_tex_2(X0,X1))
      | v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)
      | k1_tex_2(X0,X1) != X2
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k1_tex_2(X0,X1) = X2
                  | u1_struct_0(X2) != k6_domain_1(u1_struct_0(X0),X1) )
                & ( u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)
                  | k1_tex_2(X0,X1) != X2 ) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f73,plain,(
    ~ spl2_5 ),
    inference(avatar_split_clause,[],[f34,f71])).

fof(f34,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ~ v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK1),sK0)
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f30,f29])).

fof(f29,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ v2_tex_2(k6_domain_1(u1_struct_0(sK0),X1),sK0)
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X1] :
        ( ~ v2_tex_2(k6_domain_1(u1_struct_0(sK0),X1),sK0)
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ~ v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK1),sK0)
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).

fof(f69,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f35,f67])).

fof(f35,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f65,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f36,f63])).

fof(f36,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f61,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f37,f59])).

fof(f37,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f31])).

fof(f57,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f38,f55])).

fof(f38,plain,(
    ~ v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:54:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.46  % (26071)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.46  % (26067)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.46  % (26061)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.46  % (26058)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.46  % (26063)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.47  % (26058)Refutation not found, incomplete strategy% (26058)------------------------------
% 0.21/0.47  % (26058)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (26058)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (26058)Memory used [KB]: 10490
% 0.21/0.47  % (26058)Time elapsed: 0.051 s
% 0.21/0.47  % (26058)------------------------------
% 0.21/0.47  % (26058)------------------------------
% 0.21/0.47  % (26073)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.47  % (26063)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f136,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f57,f61,f65,f69,f73,f82,f87,f93,f101,f114,f116,f121,f126,f128,f133,f135])).
% 0.21/0.47  fof(f135,plain,(
% 0.21/0.47    ~spl2_3 | spl2_15),
% 0.21/0.47    inference(avatar_split_clause,[],[f134,f131,f63])).
% 0.21/0.47  fof(f63,plain,(
% 0.21/0.47    spl2_3 <=> l1_pre_topc(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.47  fof(f131,plain,(
% 0.21/0.47    spl2_15 <=> l1_struct_0(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.21/0.47  fof(f134,plain,(
% 0.21/0.47    ~l1_pre_topc(sK0) | spl2_15),
% 0.21/0.47    inference(resolution,[],[f132,f39])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.47  fof(f132,plain,(
% 0.21/0.47    ~l1_struct_0(sK0) | spl2_15),
% 0.21/0.47    inference(avatar_component_clause,[],[f131])).
% 0.21/0.47  fof(f133,plain,(
% 0.21/0.47    spl2_5 | ~spl2_15 | ~spl2_9),
% 0.21/0.47    inference(avatar_split_clause,[],[f129,f95,f131,f71])).
% 0.21/0.47  fof(f71,plain,(
% 0.21/0.47    spl2_5 <=> v2_struct_0(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.47  fof(f95,plain,(
% 0.21/0.47    spl2_9 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.47  fof(f129,plain,(
% 0.21/0.47    ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~spl2_9),
% 0.21/0.47    inference(resolution,[],[f96,f40])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.47  fof(f96,plain,(
% 0.21/0.47    v1_xboole_0(u1_struct_0(sK0)) | ~spl2_9),
% 0.21/0.47    inference(avatar_component_clause,[],[f95])).
% 0.21/0.47  fof(f128,plain,(
% 0.21/0.47    spl2_5 | ~spl2_3 | ~spl2_2 | ~spl2_11),
% 0.21/0.47    inference(avatar_split_clause,[],[f127,f105,f59,f63,f71])).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    spl2_2 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.47  fof(f105,plain,(
% 0.21/0.47    spl2_11 <=> v2_struct_0(k1_tex_2(sK0,sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.21/0.47  fof(f127,plain,(
% 0.21/0.47    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl2_11),
% 0.21/0.47    inference(resolution,[],[f106,f48])).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v2_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).
% 0.21/0.47  fof(f106,plain,(
% 0.21/0.47    v2_struct_0(k1_tex_2(sK0,sK1)) | ~spl2_11),
% 0.21/0.47    inference(avatar_component_clause,[],[f105])).
% 0.21/0.47  fof(f126,plain,(
% 0.21/0.47    spl2_5 | ~spl2_2 | ~spl2_4 | ~spl2_3 | spl2_14),
% 0.21/0.47    inference(avatar_split_clause,[],[f124,f119,f63,f67,f59,f71])).
% 0.21/0.47  fof(f67,plain,(
% 0.21/0.47    spl2_4 <=> v2_pre_topc(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.47  fof(f119,plain,(
% 0.21/0.47    spl2_14 <=> v2_pre_topc(k1_tex_2(sK0,sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.21/0.47  fof(f124,plain,(
% 0.21/0.47    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | spl2_14),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f123])).
% 0.21/0.47  fof(f123,plain,(
% 0.21/0.47    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | spl2_14),
% 0.21/0.47    inference(resolution,[],[f122,f50])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    ( ! [X0,X1] : (m1_pre_topc(k1_tex_2(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f28])).
% 0.21/0.47  fof(f122,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_pre_topc(k1_tex_2(sK0,sK1),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | spl2_14),
% 0.21/0.47    inference(resolution,[],[f120,f46])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.47    inference(flattening,[],[f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 0.21/0.47  fof(f120,plain,(
% 0.21/0.47    ~v2_pre_topc(k1_tex_2(sK0,sK1)) | spl2_14),
% 0.21/0.47    inference(avatar_component_clause,[],[f119])).
% 0.21/0.47  fof(f121,plain,(
% 0.21/0.47    spl2_5 | ~spl2_3 | ~spl2_2 | ~spl2_14 | spl2_13),
% 0.21/0.47    inference(avatar_split_clause,[],[f117,f112,f119,f59,f63,f71])).
% 0.21/0.47  fof(f112,plain,(
% 0.21/0.47    spl2_13 <=> v1_tdlat_3(k1_tex_2(sK0,sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.21/0.47  fof(f117,plain,(
% 0.21/0.47    ~v2_pre_topc(k1_tex_2(sK0,sK1)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | spl2_13),
% 0.21/0.47    inference(resolution,[],[f113,f41])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v1_tdlat_3(k1_tex_2(X0,X1)) | ~v2_pre_topc(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (v1_tdlat_3(k1_tex_2(X0,X1)) | ~v2_pre_topc(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : ((v1_tdlat_3(k1_tex_2(X0,X1)) | ~v2_pre_topc(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v2_pre_topc(k1_tex_2(X0,X1)) => v1_tdlat_3(k1_tex_2(X0,X1)))))),
% 0.21/0.47    inference(pure_predicate_removal,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v2_pre_topc(k1_tex_2(X0,X1)) => (v2_tdlat_3(k1_tex_2(X0,X1)) & v1_tdlat_3(k1_tex_2(X0,X1))))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tex_2)).
% 0.21/0.47  fof(f113,plain,(
% 0.21/0.47    ~v1_tdlat_3(k1_tex_2(sK0,sK1)) | spl2_13),
% 0.21/0.47    inference(avatar_component_clause,[],[f112])).
% 0.21/0.47  fof(f116,plain,(
% 0.21/0.47    spl2_5 | ~spl2_3 | ~spl2_2 | spl2_12),
% 0.21/0.47    inference(avatar_split_clause,[],[f115,f108,f59,f63,f71])).
% 0.21/0.47  fof(f108,plain,(
% 0.21/0.47    spl2_12 <=> m1_pre_topc(k1_tex_2(sK0,sK1),sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.21/0.47  fof(f115,plain,(
% 0.21/0.47    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | spl2_12),
% 0.21/0.47    inference(resolution,[],[f109,f50])).
% 0.21/0.47  fof(f109,plain,(
% 0.21/0.47    ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | spl2_12),
% 0.21/0.47    inference(avatar_component_clause,[],[f108])).
% 0.21/0.47  fof(f114,plain,(
% 0.21/0.47    spl2_5 | ~spl2_3 | spl2_11 | ~spl2_12 | spl2_8 | ~spl2_13 | ~spl2_10),
% 0.21/0.47    inference(avatar_split_clause,[],[f102,f99,f112,f91,f108,f105,f63,f71])).
% 0.21/0.47  fof(f91,plain,(
% 0.21/0.47    spl2_8 <=> v2_tex_2(u1_struct_0(k1_tex_2(sK0,sK1)),sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.47  fof(f99,plain,(
% 0.21/0.47    spl2_10 <=> m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.47  fof(f102,plain,(
% 0.21/0.47    ~v1_tdlat_3(k1_tex_2(sK0,sK1)) | v2_tex_2(u1_struct_0(k1_tex_2(sK0,sK1)),sK0) | ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | v2_struct_0(k1_tex_2(sK0,sK1)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl2_10),
% 0.21/0.47    inference(resolution,[],[f52,f100])).
% 0.21/0.47  fof(f100,plain,(
% 0.21/0.47    m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_10),
% 0.21/0.47    inference(avatar_component_clause,[],[f99])).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tdlat_3(X1) | v2_tex_2(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(equality_resolution,[],[f45])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (v2_tex_2(X2,X0) | ~v1_tdlat_3(X1) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f33])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) | ~v1_tdlat_3(X1)) & (v1_tdlat_3(X1) | ~v2_tex_2(X2,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(nnf_transformation,[],[f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,axiom,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => (v2_tex_2(X2,X0) <=> v1_tdlat_3(X1))))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_tex_2)).
% 0.21/0.47  fof(f101,plain,(
% 0.21/0.47    spl2_9 | ~spl2_2 | spl2_10 | ~spl2_7),
% 0.21/0.47    inference(avatar_split_clause,[],[f89,f85,f99,f59,f95])).
% 0.21/0.47  fof(f85,plain,(
% 0.21/0.47    spl2_7 <=> k6_domain_1(u1_struct_0(sK0),sK1) = u1_struct_0(k1_tex_2(sK0,sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.47  fof(f89,plain,(
% 0.21/0.47    m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | ~spl2_7),
% 0.21/0.47    inference(superposition,[],[f47,f86])).
% 0.21/0.47  fof(f86,plain,(
% 0.21/0.47    k6_domain_1(u1_struct_0(sK0),sK1) = u1_struct_0(k1_tex_2(sK0,sK1)) | ~spl2_7),
% 0.21/0.47    inference(avatar_component_clause,[],[f85])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.47    inference(flattening,[],[f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.21/0.47  fof(f93,plain,(
% 0.21/0.47    ~spl2_8 | spl2_1 | ~spl2_7),
% 0.21/0.47    inference(avatar_split_clause,[],[f88,f85,f55,f91])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    spl2_1 <=> v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK1),sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.47  fof(f88,plain,(
% 0.21/0.47    ~v2_tex_2(u1_struct_0(k1_tex_2(sK0,sK1)),sK0) | (spl2_1 | ~spl2_7)),
% 0.21/0.47    inference(superposition,[],[f56,f86])).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    ~v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK1),sK0) | spl2_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f55])).
% 0.21/0.47  fof(f87,plain,(
% 0.21/0.47    spl2_7 | ~spl2_2 | ~spl2_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f83,f80,f59,f85])).
% 0.21/0.47  fof(f80,plain,(
% 0.21/0.47    spl2_6 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k6_domain_1(u1_struct_0(sK0),X0) = u1_struct_0(k1_tex_2(sK0,X0)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.47  fof(f83,plain,(
% 0.21/0.47    k6_domain_1(u1_struct_0(sK0),sK1) = u1_struct_0(k1_tex_2(sK0,sK1)) | (~spl2_2 | ~spl2_6)),
% 0.21/0.47    inference(resolution,[],[f81,f60])).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl2_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f59])).
% 0.21/0.47  fof(f81,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k6_domain_1(u1_struct_0(sK0),X0) = u1_struct_0(k1_tex_2(sK0,X0))) ) | ~spl2_6),
% 0.21/0.47    inference(avatar_component_clause,[],[f80])).
% 0.21/0.47  fof(f82,plain,(
% 0.21/0.47    spl2_5 | spl2_6 | ~spl2_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f77,f63,f80,f71])).
% 0.21/0.47  fof(f77,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k6_domain_1(u1_struct_0(sK0),X0) = u1_struct_0(k1_tex_2(sK0,X0)) | v2_struct_0(sK0)) ) | ~spl2_3),
% 0.21/0.47    inference(resolution,[],[f76,f64])).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    l1_pre_topc(sK0) | ~spl2_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f63])).
% 0.21/0.47  fof(f76,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1)) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f75,f48])).
% 0.21/0.47  fof(f75,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1)) | v2_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f74,f49])).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v1_pre_topc(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f28])).
% 0.21/0.47  fof(f74,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1)) | ~v1_pre_topc(k1_tex_2(X0,X1)) | v2_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f51,f50])).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1)) | ~m1_pre_topc(k1_tex_2(X0,X1),X0) | ~v1_pre_topc(k1_tex_2(X0,X1)) | v2_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(equality_resolution,[],[f42])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) | k1_tex_2(X0,X1) != X2 | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f32])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : (((k1_tex_2(X0,X1) = X2 | u1_struct_0(X2) != k6_domain_1(u1_struct_0(X0),X1)) & (u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) | k1_tex_2(X0,X1) != X2)) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(nnf_transformation,[],[f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : ((k1_tex_2(X0,X1) = X2 <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : ((k1_tex_2(X0,X1) = X2 <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)) | (~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => (k1_tex_2(X0,X1) = X2 <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tex_2)).
% 0.21/0.47  fof(f73,plain,(
% 0.21/0.47    ~spl2_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f34,f71])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ~v2_struct_0(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f31])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    (~v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK1),sK0) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f30,f29])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (~v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (~v2_tex_2(k6_domain_1(u1_struct_0(sK0),X1),sK0) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ? [X1] : (~v2_tex_2(k6_domain_1(u1_struct_0(sK0),X1),sK0) & m1_subset_1(X1,u1_struct_0(sK0))) => (~v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK1),sK0) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (~v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (~v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,negated_conjecture,(
% 0.21/0.47    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 0.21/0.47    inference(negated_conjecture,[],[f9])).
% 0.21/0.47  fof(f9,conjecture,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).
% 0.21/0.47  fof(f69,plain,(
% 0.21/0.47    spl2_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f35,f67])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    v2_pre_topc(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f31])).
% 0.21/0.47  fof(f65,plain,(
% 0.21/0.47    spl2_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f36,f63])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    l1_pre_topc(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f31])).
% 0.21/0.47  fof(f61,plain,(
% 0.21/0.47    spl2_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f37,f59])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.47    inference(cnf_transformation,[],[f31])).
% 0.21/0.47  fof(f57,plain,(
% 0.21/0.47    ~spl2_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f38,f55])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    ~v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK1),sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f31])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (26063)------------------------------
% 0.21/0.47  % (26063)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (26063)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (26063)Memory used [KB]: 10618
% 0.21/0.47  % (26063)Time elapsed: 0.055 s
% 0.21/0.47  % (26063)------------------------------
% 0.21/0.47  % (26063)------------------------------
% 0.21/0.47  % (26057)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.47  % (26056)Success in time 0.118 s
%------------------------------------------------------------------------------
