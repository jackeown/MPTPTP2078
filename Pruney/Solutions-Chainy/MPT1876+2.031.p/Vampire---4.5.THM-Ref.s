%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:40 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  185 ( 335 expanded)
%              Number of leaves         :   48 ( 152 expanded)
%              Depth                    :    8
%              Number of atoms          :  679 (1212 expanded)
%              Number of equality atoms :   34 (  55 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1244,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f105,f110,f115,f120,f125,f130,f139,f140,f216,f234,f268,f275,f304,f316,f328,f333,f341,f365,f414,f578,f584,f854,f888,f890,f949,f954,f1170,f1224,f1236,f1243])).

fof(f1243,plain,
    ( k1_tarski(sK2(sK1)) != k6_domain_1(u1_struct_0(sK0),sK2(sK1))
    | k6_domain_1(sK1,sK2(sK1)) != k1_tarski(sK2(sK1))
    | sK1 != k6_domain_1(sK1,sK2(sK1))
    | v2_tex_2(sK1,sK0)
    | ~ v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK2(sK1)),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1236,plain,
    ( spl5_154
    | spl5_4
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f1227,f279,f112,f102,f117,f1233])).

fof(f1233,plain,
    ( spl5_154
  <=> v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK2(sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_154])])).

fof(f117,plain,
    ( spl5_4
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f102,plain,
    ( spl5_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f112,plain,
    ( spl5_3
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f279,plain,
    ( spl5_26
  <=> m1_subset_1(sK2(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f1227,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK2(sK1)),sK0)
    | ~ spl5_26 ),
    inference(resolution,[],[f281,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).

fof(f281,plain,
    ( m1_subset_1(sK2(sK1),u1_struct_0(sK0))
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f279])).

fof(f1224,plain,
    ( spl5_26
    | spl5_27
    | ~ spl5_24 ),
    inference(avatar_split_clause,[],[f1223,f265,f283,f279])).

fof(f283,plain,
    ( spl5_27
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f265,plain,
    ( spl5_24
  <=> r2_hidden(sK2(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f1223,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | m1_subset_1(sK2(sK1),u1_struct_0(sK0))
    | ~ spl5_24 ),
    inference(resolution,[],[f267,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f267,plain,
    ( r2_hidden(sK2(sK1),u1_struct_0(sK0))
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f265])).

fof(f1170,plain,
    ( spl5_11
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f1165,f122,f161])).

fof(f161,plain,
    ( spl5_11
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f122,plain,
    ( spl5_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f1165,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl5_5 ),
    inference(resolution,[],[f124,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f124,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f122])).

fof(f954,plain,
    ( spl5_6
    | spl5_14
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f952,f168,f182,f127])).

fof(f127,plain,
    ( spl5_6
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f182,plain,
    ( spl5_14
  <=> r2_hidden(sK2(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f168,plain,
    ( spl5_12
  <=> m1_subset_1(sK2(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f952,plain,
    ( r2_hidden(sK2(sK1),sK1)
    | v1_xboole_0(sK1)
    | ~ spl5_12 ),
    inference(resolution,[],[f170,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f170,plain,
    ( m1_subset_1(sK2(sK1),sK1)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f168])).

fof(f949,plain,
    ( spl5_6
    | spl5_12
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f946,f136,f168,f127])).

fof(f136,plain,
    ( spl5_8
  <=> v1_zfmisc_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f946,plain,
    ( m1_subset_1(sK2(sK1),sK1)
    | v1_xboole_0(sK1)
    | ~ spl5_8 ),
    inference(resolution,[],[f137,f62])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(X0)
      | m1_subset_1(sK2(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

fof(f137,plain,
    ( v1_zfmisc_1(sK1)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f136])).

fof(f890,plain,
    ( spl5_7
    | spl5_4
    | ~ spl5_1
    | ~ spl5_70
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f260,f122,f581,f102,f117,f132])).

fof(f132,plain,
    ( spl5_7
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f581,plain,
    ( spl5_70
  <=> v1_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_70])])).

fof(f260,plain,
    ( ~ v1_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v2_tex_2(sK1,sK0)
    | ~ spl5_5 ),
    inference(resolution,[],[f141,f124])).

fof(f141,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_tex_2(X1,X0) ) ),
    inference(global_subsumption,[],[f66,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).

fof(f66,plain,(
    ! [X0] :
      ( ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tdlat_3)).

fof(f888,plain,
    ( ~ spl5_36
    | spl5_8
    | ~ spl5_34
    | ~ spl5_39 ),
    inference(avatar_split_clause,[],[f887,f362,f325,f136,f338])).

fof(f338,plain,
    ( spl5_36
  <=> l1_struct_0(sK3(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f325,plain,
    ( spl5_34
  <=> v7_struct_0(sK3(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f362,plain,
    ( spl5_39
  <=> sK1 = u1_struct_0(sK3(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).

fof(f887,plain,
    ( v1_zfmisc_1(sK1)
    | ~ l1_struct_0(sK3(sK0,sK1))
    | ~ spl5_34
    | ~ spl5_39 ),
    inference(forward_demodulation,[],[f886,f364])).

fof(f364,plain,
    ( sK1 = u1_struct_0(sK3(sK0,sK1))
    | ~ spl5_39 ),
    inference(avatar_component_clause,[],[f362])).

fof(f886,plain,
    ( ~ l1_struct_0(sK3(sK0,sK1))
    | v1_zfmisc_1(u1_struct_0(sK3(sK0,sK1)))
    | ~ spl5_34 ),
    inference(resolution,[],[f327,f80])).

fof(f80,plain,(
    ! [X0] :
      ( ~ v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v1_zfmisc_1(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).

fof(f327,plain,
    ( v7_struct_0(sK3(sK0,sK1))
    | ~ spl5_34 ),
    inference(avatar_component_clause,[],[f325])).

fof(f854,plain,
    ( ~ spl5_1
    | ~ spl5_5
    | spl5_4
    | ~ spl5_7
    | ~ spl5_32
    | ~ spl5_48 ),
    inference(avatar_split_clause,[],[f853,f412,f313,f132,f117,f122,f102])).

fof(f313,plain,
    ( spl5_32
  <=> m1_pre_topc(sK3(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f412,plain,
    ( spl5_48
  <=> ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_tex_2(sK1,X0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK3(sK0,sK1),X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).

fof(f853,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl5_32
    | ~ spl5_48 ),
    inference(resolution,[],[f413,f315])).

fof(f315,plain,
    ( m1_pre_topc(sK3(sK0,sK1),sK0)
    | ~ spl5_32 ),
    inference(avatar_component_clause,[],[f313])).

fof(f413,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK3(sK0,sK1),X0)
        | ~ v2_tex_2(sK1,X0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl5_48 ),
    inference(avatar_component_clause,[],[f412])).

fof(f584,plain,
    ( ~ spl5_1
    | spl5_70
    | spl5_4
    | ~ spl5_69 ),
    inference(avatar_split_clause,[],[f579,f575,f117,f581,f102])).

fof(f575,plain,
    ( spl5_69
  <=> v2_tex_2(u1_struct_0(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_69])])).

fof(f579,plain,
    ( v2_struct_0(sK0)
    | v1_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl5_69 ),
    inference(resolution,[],[f577,f342])).

fof(f342,plain,(
    ! [X0] :
      ( ~ v2_tex_2(u1_struct_0(X0),X0)
      | v2_struct_0(X0)
      | v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f95,f156])).

fof(f156,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f92,f99])).

fof(f99,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f95,plain,(
    ! [X0] :
      ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_tdlat_3(X0)
      | ~ v2_tex_2(u1_struct_0(X0),X0) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X0) != X1
      | v1_tdlat_3(X0)
      | ~ v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> v1_tdlat_3(X0) )
          | u1_struct_0(X0) != X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> v1_tdlat_3(X0) )
          | u1_struct_0(X0) != X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( u1_struct_0(X0) = X1
           => ( v2_tex_2(X1,X0)
            <=> v1_tdlat_3(X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_tex_2)).

fof(f577,plain,
    ( v2_tex_2(u1_struct_0(sK0),sK0)
    | ~ spl5_69 ),
    inference(avatar_component_clause,[],[f575])).

fof(f578,plain,
    ( spl5_69
    | spl5_4
    | ~ spl5_3
    | ~ spl5_1
    | ~ spl5_27 ),
    inference(avatar_split_clause,[],[f571,f283,f102,f112,f117,f575])).

fof(f571,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v2_tex_2(u1_struct_0(sK0),sK0)
    | ~ spl5_27 ),
    inference(resolution,[],[f335,f285])).

fof(f285,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f283])).

fof(f335,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_tex_2(u1_struct_0(X0),X0) ) ),
    inference(resolution,[],[f79,f156])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_xboole_0(X1)
      | v2_struct_0(X0)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).

fof(f414,plain,
    ( spl5_33
    | spl5_25
    | spl5_48
    | ~ spl5_39 ),
    inference(avatar_split_clause,[],[f407,f362,f412,f272,f321])).

fof(f321,plain,
    ( spl5_33
  <=> v1_tdlat_3(sK3(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f272,plain,
    ( spl5_25
  <=> v2_struct_0(sK3(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f407,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK3(sK0,sK1))
        | ~ m1_pre_topc(sK3(sK0,sK1),X0)
        | v2_struct_0(X0)
        | v1_tdlat_3(sK3(sK0,sK1))
        | ~ v2_tex_2(sK1,X0) )
    | ~ spl5_39 ),
    inference(superposition,[],[f97,f364])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0)
      | v1_tdlat_3(X1)
      | ~ v2_tex_2(u1_struct_0(X1),X0) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | v1_tdlat_3(X1)
      | ~ v2_tex_2(X2,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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

fof(f365,plain,
    ( spl5_39
    | spl5_4
    | spl5_6
    | ~ spl5_1
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f359,f122,f102,f127,f117,f362])).

fof(f359,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | sK1 = u1_struct_0(sK3(sK0,sK1))
    | ~ spl5_5 ),
    inference(resolution,[],[f73,f124])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | v2_struct_0(X0)
      | u1_struct_0(sK3(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) ) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_tsep_1)).

fof(f341,plain,
    ( spl5_36
    | ~ spl5_35 ),
    inference(avatar_split_clause,[],[f336,f330,f338])).

fof(f330,plain,
    ( spl5_35
  <=> l1_pre_topc(sK3(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f336,plain,
    ( l1_struct_0(sK3(sK0,sK1))
    | ~ spl5_35 ),
    inference(resolution,[],[f332,f65])).

fof(f65,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f332,plain,
    ( l1_pre_topc(sK3(sK0,sK1))
    | ~ spl5_35 ),
    inference(avatar_component_clause,[],[f330])).

fof(f333,plain,
    ( spl5_35
    | ~ spl5_1
    | ~ spl5_32 ),
    inference(avatar_split_clause,[],[f319,f313,f102,f330])).

fof(f319,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK3(sK0,sK1))
    | ~ spl5_32 ),
    inference(resolution,[],[f315,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f328,plain,
    ( ~ spl5_33
    | spl5_34
    | spl5_25
    | spl5_4
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_32 ),
    inference(avatar_split_clause,[],[f318,f313,f107,f102,f117,f272,f325,f321])).

fof(f107,plain,
    ( spl5_2
  <=> v2_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f318,plain,
    ( ~ v2_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(sK3(sK0,sK1))
    | v7_struct_0(sK3(sK0,sK1))
    | ~ v1_tdlat_3(sK3(sK0,sK1))
    | ~ spl5_32 ),
    inference(resolution,[],[f315,f142])).

fof(f142,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | v7_struct_0(X1)
      | ~ v1_tdlat_3(X1) ) ),
    inference(global_subsumption,[],[f67,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | v7_struct_0(X1)
      | ~ v1_tdlat_3(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tdlat_3(X1)
            & ~ v2_struct_0(X1) )
          | v7_struct_0(X1)
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tdlat_3(X1)
            & ~ v2_struct_0(X1) )
          | v7_struct_0(X1)
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( ( ~ v7_struct_0(X1)
              & ~ v2_struct_0(X1) )
           => ( ~ v1_tdlat_3(X1)
              & ~ v2_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc32_tex_2)).

fof(f67,plain,(
    ! [X0] :
      ( ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tdlat_3)).

fof(f316,plain,
    ( spl5_32
    | spl5_4
    | spl5_6
    | ~ spl5_1
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f310,f122,f102,f127,f117,f313])).

fof(f310,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | m1_pre_topc(sK3(sK0,sK1),sK0)
    | ~ spl5_5 ),
    inference(resolution,[],[f72,f124])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | v2_struct_0(X0)
      | m1_pre_topc(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f304,plain,
    ( spl5_30
    | spl5_27
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f288,f279,f283,f301])).

fof(f301,plain,
    ( spl5_30
  <=> k1_tarski(sK2(sK1)) = k6_domain_1(u1_struct_0(sK0),sK2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f288,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k1_tarski(sK2(sK1)) = k6_domain_1(u1_struct_0(sK0),sK2(sK1))
    | ~ spl5_26 ),
    inference(resolution,[],[f281,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f275,plain,
    ( ~ spl5_25
    | spl5_4
    | spl5_6
    | ~ spl5_1
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f269,f122,f102,f127,f117,f272])).

fof(f269,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | ~ v2_struct_0(sK3(sK0,sK1))
    | ~ spl5_5 ),
    inference(resolution,[],[f71,f124])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | v2_struct_0(X0)
      | ~ v2_struct_0(sK3(X0,X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f268,plain,
    ( spl5_24
    | ~ spl5_11
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f262,f182,f161,f265])).

fof(f262,plain,
    ( r2_hidden(sK2(sK1),u1_struct_0(sK0))
    | ~ spl5_11
    | ~ spl5_14 ),
    inference(resolution,[],[f206,f163])).

fof(f163,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f161])).

fof(f206,plain,
    ( ! [X3] :
        ( ~ r1_tarski(sK1,X3)
        | r2_hidden(sK2(sK1),X3) )
    | ~ spl5_14 ),
    inference(resolution,[],[f89,f184])).

fof(f184,plain,
    ( r2_hidden(sK2(sK1),sK1)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f182])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f234,plain,
    ( spl5_19
    | spl5_6
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f231,f168,f127,f226])).

fof(f226,plain,
    ( spl5_19
  <=> k6_domain_1(sK1,sK2(sK1)) = k1_tarski(sK2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f231,plain,
    ( v1_xboole_0(sK1)
    | k6_domain_1(sK1,sK2(sK1)) = k1_tarski(sK2(sK1))
    | ~ spl5_12 ),
    inference(resolution,[],[f170,f85])).

fof(f216,plain,
    ( spl5_6
    | spl5_17
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f211,f136,f213,f127])).

fof(f213,plain,
    ( spl5_17
  <=> sK1 = k6_domain_1(sK1,sK2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f211,plain,
    ( sK1 = k6_domain_1(sK1,sK2(sK1))
    | v1_xboole_0(sK1)
    | ~ spl5_8 ),
    inference(resolution,[],[f63,f137])).

fof(f63,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(X0)
      | k6_domain_1(X0,sK2(X0)) = X0
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f140,plain,
    ( spl5_7
    | spl5_8 ),
    inference(avatar_split_clause,[],[f54,f136,f132])).

fof(f54,plain,
    ( v1_zfmisc_1(sK1)
    | v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X1) )
           => ( v2_tex_2(X1,X0)
            <=> v1_zfmisc_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ( v2_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).

fof(f139,plain,
    ( ~ spl5_7
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f55,f136,f132])).

fof(f55,plain,
    ( ~ v1_zfmisc_1(sK1)
    | ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f130,plain,(
    ~ spl5_6 ),
    inference(avatar_split_clause,[],[f56,f127])).

fof(f56,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f125,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f57,f122])).

fof(f57,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f120,plain,(
    ~ spl5_4 ),
    inference(avatar_split_clause,[],[f58,f117])).

fof(f58,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f115,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f59,f112])).

fof(f59,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f110,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f60,f107])).

fof(f60,plain,(
    v2_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f105,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f61,f102])).

fof(f61,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:45:50 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (14816)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.48  % (14811)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (14816)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f1244,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(avatar_sat_refutation,[],[f105,f110,f115,f120,f125,f130,f139,f140,f216,f234,f268,f275,f304,f316,f328,f333,f341,f365,f414,f578,f584,f854,f888,f890,f949,f954,f1170,f1224,f1236,f1243])).
% 0.22/0.52  fof(f1243,plain,(
% 0.22/0.52    k1_tarski(sK2(sK1)) != k6_domain_1(u1_struct_0(sK0),sK2(sK1)) | k6_domain_1(sK1,sK2(sK1)) != k1_tarski(sK2(sK1)) | sK1 != k6_domain_1(sK1,sK2(sK1)) | v2_tex_2(sK1,sK0) | ~v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK2(sK1)),sK0)),
% 0.22/0.52    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.52  fof(f1236,plain,(
% 0.22/0.52    spl5_154 | spl5_4 | ~spl5_1 | ~spl5_3 | ~spl5_26),
% 0.22/0.52    inference(avatar_split_clause,[],[f1227,f279,f112,f102,f117,f1233])).
% 0.22/0.52  fof(f1233,plain,(
% 0.22/0.52    spl5_154 <=> v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK2(sK1)),sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_154])])).
% 0.22/0.52  fof(f117,plain,(
% 0.22/0.52    spl5_4 <=> v2_struct_0(sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.22/0.52  fof(f102,plain,(
% 0.22/0.52    spl5_1 <=> l1_pre_topc(sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.52  fof(f112,plain,(
% 0.22/0.52    spl5_3 <=> v2_pre_topc(sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.52  fof(f279,plain,(
% 0.22/0.52    spl5_26 <=> m1_subset_1(sK2(sK1),u1_struct_0(sK0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 0.22/0.52  fof(f1227,plain,(
% 0.22/0.52    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK2(sK1)),sK0) | ~spl5_26),
% 0.22/0.52    inference(resolution,[],[f281,f78])).
% 0.22/0.52  fof(f78,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f43])).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f42])).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f18])).
% 0.22/0.52  fof(f18,axiom,(
% 0.22/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).
% 0.22/0.52  fof(f281,plain,(
% 0.22/0.52    m1_subset_1(sK2(sK1),u1_struct_0(sK0)) | ~spl5_26),
% 0.22/0.52    inference(avatar_component_clause,[],[f279])).
% 0.22/0.52  fof(f1224,plain,(
% 0.22/0.52    spl5_26 | spl5_27 | ~spl5_24),
% 0.22/0.52    inference(avatar_split_clause,[],[f1223,f265,f283,f279])).
% 0.22/0.52  fof(f283,plain,(
% 0.22/0.52    spl5_27 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 0.22/0.52  fof(f265,plain,(
% 0.22/0.52    spl5_24 <=> r2_hidden(sK2(sK1),u1_struct_0(sK0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 0.22/0.52  fof(f1223,plain,(
% 0.22/0.52    v1_xboole_0(u1_struct_0(sK0)) | m1_subset_1(sK2(sK1),u1_struct_0(sK0)) | ~spl5_24),
% 0.22/0.52    inference(resolution,[],[f267,f83])).
% 0.22/0.52  fof(f83,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r2_hidden(X1,X0) | v1_xboole_0(X0) | m1_subset_1(X1,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f48])).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.22/0.52  fof(f267,plain,(
% 0.22/0.52    r2_hidden(sK2(sK1),u1_struct_0(sK0)) | ~spl5_24),
% 0.22/0.52    inference(avatar_component_clause,[],[f265])).
% 0.22/0.52  fof(f1170,plain,(
% 0.22/0.52    spl5_11 | ~spl5_5),
% 0.22/0.52    inference(avatar_split_clause,[],[f1165,f122,f161])).
% 0.22/0.52  fof(f161,plain,(
% 0.22/0.52    spl5_11 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.22/0.52  fof(f122,plain,(
% 0.22/0.52    spl5_5 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.22/0.52  fof(f1165,plain,(
% 0.22/0.52    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl5_5),
% 0.22/0.52    inference(resolution,[],[f124,f93])).
% 0.22/0.52  fof(f93,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.52  fof(f124,plain,(
% 0.22/0.52    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_5),
% 0.22/0.52    inference(avatar_component_clause,[],[f122])).
% 0.22/0.52  fof(f954,plain,(
% 0.22/0.52    spl5_6 | spl5_14 | ~spl5_12),
% 0.22/0.52    inference(avatar_split_clause,[],[f952,f168,f182,f127])).
% 0.22/0.52  fof(f127,plain,(
% 0.22/0.52    spl5_6 <=> v1_xboole_0(sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.22/0.52  fof(f182,plain,(
% 0.22/0.52    spl5_14 <=> r2_hidden(sK2(sK1),sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.22/0.52  fof(f168,plain,(
% 0.22/0.52    spl5_12 <=> m1_subset_1(sK2(sK1),sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.22/0.52  fof(f952,plain,(
% 0.22/0.52    r2_hidden(sK2(sK1),sK1) | v1_xboole_0(sK1) | ~spl5_12),
% 0.22/0.52    inference(resolution,[],[f170,f84])).
% 0.22/0.52  fof(f84,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f48])).
% 0.22/0.52  fof(f170,plain,(
% 0.22/0.52    m1_subset_1(sK2(sK1),sK1) | ~spl5_12),
% 0.22/0.52    inference(avatar_component_clause,[],[f168])).
% 0.22/0.52  fof(f949,plain,(
% 0.22/0.52    spl5_6 | spl5_12 | ~spl5_8),
% 0.22/0.52    inference(avatar_split_clause,[],[f946,f136,f168,f127])).
% 0.22/0.52  fof(f136,plain,(
% 0.22/0.52    spl5_8 <=> v1_zfmisc_1(sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.22/0.52  fof(f946,plain,(
% 0.22/0.52    m1_subset_1(sK2(sK1),sK1) | v1_xboole_0(sK1) | ~spl5_8),
% 0.22/0.52    inference(resolution,[],[f137,f62])).
% 0.22/0.52  fof(f62,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_zfmisc_1(X0) | m1_subset_1(sK2(X0),X0) | v1_xboole_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ! [X0] : ((v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))) | v1_xboole_0(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f13])).
% 0.22/0.52  fof(f13,axiom,(
% 0.22/0.52    ! [X0] : (~v1_xboole_0(X0) => (v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).
% 0.22/0.52  fof(f137,plain,(
% 0.22/0.52    v1_zfmisc_1(sK1) | ~spl5_8),
% 0.22/0.52    inference(avatar_component_clause,[],[f136])).
% 0.22/0.52  fof(f890,plain,(
% 0.22/0.52    spl5_7 | spl5_4 | ~spl5_1 | ~spl5_70 | ~spl5_5),
% 0.22/0.52    inference(avatar_split_clause,[],[f260,f122,f581,f102,f117,f132])).
% 0.22/0.52  fof(f132,plain,(
% 0.22/0.52    spl5_7 <=> v2_tex_2(sK1,sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.22/0.52  fof(f581,plain,(
% 0.22/0.52    spl5_70 <=> v1_tdlat_3(sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_70])])).
% 0.22/0.52  fof(f260,plain,(
% 0.22/0.52    ~v1_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v2_tex_2(sK1,sK0) | ~spl5_5),
% 0.22/0.52    inference(resolution,[],[f141,f124])).
% 0.22/0.52  fof(f141,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v2_tex_2(X1,X0)) )),
% 0.22/0.52    inference(global_subsumption,[],[f66,f76])).
% 0.22/0.52  fof(f76,plain,(
% 0.22/0.52    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tex_2(X1,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f39])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f38])).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f19])).
% 0.22/0.52  fof(f19,axiom,(
% 0.22/0.52    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).
% 0.22/0.52  fof(f66,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_pre_topc(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f28])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ! [X0] : (v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(flattening,[],[f27])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ! [X0] : ((v2_pre_topc(X0) | ~v1_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,axiom,(
% 0.22/0.52    ! [X0] : (l1_pre_topc(X0) => (v1_tdlat_3(X0) => v2_pre_topc(X0)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tdlat_3)).
% 0.22/0.52  fof(f888,plain,(
% 0.22/0.52    ~spl5_36 | spl5_8 | ~spl5_34 | ~spl5_39),
% 0.22/0.52    inference(avatar_split_clause,[],[f887,f362,f325,f136,f338])).
% 0.22/0.52  fof(f338,plain,(
% 0.22/0.52    spl5_36 <=> l1_struct_0(sK3(sK0,sK1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).
% 0.22/0.52  fof(f325,plain,(
% 0.22/0.52    spl5_34 <=> v7_struct_0(sK3(sK0,sK1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).
% 0.22/0.52  fof(f362,plain,(
% 0.22/0.52    spl5_39 <=> sK1 = u1_struct_0(sK3(sK0,sK1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).
% 0.22/0.52  fof(f887,plain,(
% 0.22/0.52    v1_zfmisc_1(sK1) | ~l1_struct_0(sK3(sK0,sK1)) | (~spl5_34 | ~spl5_39)),
% 0.22/0.52    inference(forward_demodulation,[],[f886,f364])).
% 0.22/0.52  fof(f364,plain,(
% 0.22/0.52    sK1 = u1_struct_0(sK3(sK0,sK1)) | ~spl5_39),
% 0.22/0.52    inference(avatar_component_clause,[],[f362])).
% 0.22/0.52  fof(f886,plain,(
% 0.22/0.52    ~l1_struct_0(sK3(sK0,sK1)) | v1_zfmisc_1(u1_struct_0(sK3(sK0,sK1))) | ~spl5_34),
% 0.22/0.52    inference(resolution,[],[f327,f80])).
% 0.22/0.52  fof(f80,plain,(
% 0.22/0.52    ( ! [X0] : (~v7_struct_0(X0) | ~l1_struct_0(X0) | v1_zfmisc_1(u1_struct_0(X0))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f47])).
% 0.22/0.52  fof(f47,plain,(
% 0.22/0.52    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f46])).
% 0.22/0.52  fof(f46,plain,(
% 0.22/0.52    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,axiom,(
% 0.22/0.52    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).
% 0.22/0.52  fof(f327,plain,(
% 0.22/0.52    v7_struct_0(sK3(sK0,sK1)) | ~spl5_34),
% 0.22/0.52    inference(avatar_component_clause,[],[f325])).
% 0.22/0.52  fof(f854,plain,(
% 0.22/0.52    ~spl5_1 | ~spl5_5 | spl5_4 | ~spl5_7 | ~spl5_32 | ~spl5_48),
% 0.22/0.52    inference(avatar_split_clause,[],[f853,f412,f313,f132,f117,f122,f102])).
% 0.22/0.52  fof(f313,plain,(
% 0.22/0.52    spl5_32 <=> m1_pre_topc(sK3(sK0,sK1),sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).
% 0.22/0.52  fof(f412,plain,(
% 0.22/0.52    spl5_48 <=> ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(sK1,X0) | v2_struct_0(X0) | ~m1_pre_topc(sK3(sK0,sK1),X0) | ~l1_pre_topc(X0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).
% 0.22/0.52  fof(f853,plain,(
% 0.22/0.52    ~v2_tex_2(sK1,sK0) | v2_struct_0(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl5_32 | ~spl5_48)),
% 0.22/0.52    inference(resolution,[],[f413,f315])).
% 0.22/0.52  fof(f315,plain,(
% 0.22/0.52    m1_pre_topc(sK3(sK0,sK1),sK0) | ~spl5_32),
% 0.22/0.52    inference(avatar_component_clause,[],[f313])).
% 0.22/0.52  fof(f413,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_pre_topc(sK3(sK0,sK1),X0) | ~v2_tex_2(sK1,X0) | v2_struct_0(X0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl5_48),
% 0.22/0.52    inference(avatar_component_clause,[],[f412])).
% 0.22/0.52  fof(f584,plain,(
% 0.22/0.52    ~spl5_1 | spl5_70 | spl5_4 | ~spl5_69),
% 0.22/0.52    inference(avatar_split_clause,[],[f579,f575,f117,f581,f102])).
% 0.22/0.52  fof(f575,plain,(
% 0.22/0.52    spl5_69 <=> v2_tex_2(u1_struct_0(sK0),sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_69])])).
% 0.22/0.53  fof(f579,plain,(
% 0.22/0.53    v2_struct_0(sK0) | v1_tdlat_3(sK0) | ~l1_pre_topc(sK0) | ~spl5_69),
% 0.22/0.53    inference(resolution,[],[f577,f342])).
% 0.22/0.53  fof(f342,plain,(
% 0.22/0.53    ( ! [X0] : (~v2_tex_2(u1_struct_0(X0),X0) | v2_struct_0(X0) | v1_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.53    inference(resolution,[],[f95,f156])).
% 0.22/0.53  fof(f156,plain,(
% 0.22/0.53    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.22/0.53    inference(resolution,[],[f92,f99])).
% 0.22/0.53  fof(f99,plain,(
% 0.22/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.53    inference(equality_resolution,[],[f87])).
% 0.22/0.53  fof(f87,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.53  fof(f92,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f5])).
% 0.22/0.53  fof(f95,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v1_tdlat_3(X0) | ~v2_tex_2(u1_struct_0(X0),X0)) )),
% 0.22/0.53    inference(equality_resolution,[],[f70])).
% 0.22/0.53  fof(f70,plain,(
% 0.22/0.53    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X0) != X1 | v1_tdlat_3(X0) | ~v2_tex_2(X1,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f33])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_tdlat_3(X0)) | u1_struct_0(X0) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f32])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) <=> v1_tdlat_3(X0)) | u1_struct_0(X0) != X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f16])).
% 0.22/0.53  fof(f16,axiom,(
% 0.22/0.53    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X0) = X1 => (v2_tex_2(X1,X0) <=> v1_tdlat_3(X0)))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_tex_2)).
% 0.22/0.53  fof(f577,plain,(
% 0.22/0.53    v2_tex_2(u1_struct_0(sK0),sK0) | ~spl5_69),
% 0.22/0.53    inference(avatar_component_clause,[],[f575])).
% 0.22/0.53  fof(f578,plain,(
% 0.22/0.53    spl5_69 | spl5_4 | ~spl5_3 | ~spl5_1 | ~spl5_27),
% 0.22/0.53    inference(avatar_split_clause,[],[f571,f283,f102,f112,f117,f575])).
% 0.22/0.53  fof(f571,plain,(
% 0.22/0.53    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | v2_tex_2(u1_struct_0(sK0),sK0) | ~spl5_27),
% 0.22/0.53    inference(resolution,[],[f335,f285])).
% 0.22/0.53  fof(f285,plain,(
% 0.22/0.53    v1_xboole_0(u1_struct_0(sK0)) | ~spl5_27),
% 0.22/0.53    inference(avatar_component_clause,[],[f283])).
% 0.22/0.53  fof(f335,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v2_tex_2(u1_struct_0(X0),X0)) )),
% 0.22/0.53    inference(resolution,[],[f79,f156])).
% 0.22/0.53  fof(f79,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_xboole_0(X1) | v2_struct_0(X0) | v2_tex_2(X1,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f45])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f44])).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f17])).
% 0.22/0.53  fof(f17,axiom,(
% 0.22/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).
% 0.22/0.53  fof(f414,plain,(
% 0.22/0.53    spl5_33 | spl5_25 | spl5_48 | ~spl5_39),
% 0.22/0.53    inference(avatar_split_clause,[],[f407,f362,f412,f272,f321])).
% 0.22/0.53  fof(f321,plain,(
% 0.22/0.53    spl5_33 <=> v1_tdlat_3(sK3(sK0,sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).
% 0.22/0.53  fof(f272,plain,(
% 0.22/0.53    spl5_25 <=> v2_struct_0(sK3(sK0,sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 0.22/0.53  fof(f407,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(sK3(sK0,sK1)) | ~m1_pre_topc(sK3(sK0,sK1),X0) | v2_struct_0(X0) | v1_tdlat_3(sK3(sK0,sK1)) | ~v2_tex_2(sK1,X0)) ) | ~spl5_39),
% 0.22/0.53    inference(superposition,[],[f97,f364])).
% 0.22/0.53  fof(f97,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X0) | v1_tdlat_3(X1) | ~v2_tex_2(u1_struct_0(X1),X0)) )),
% 0.22/0.53    inference(equality_resolution,[],[f75])).
% 0.22/0.53  fof(f75,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X2 | v1_tdlat_3(X1) | ~v2_tex_2(X2,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f37])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f36])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f15])).
% 0.22/0.53  fof(f15,axiom,(
% 0.22/0.53    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => (v2_tex_2(X2,X0) <=> v1_tdlat_3(X1))))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_tex_2)).
% 0.22/0.53  fof(f365,plain,(
% 0.22/0.53    spl5_39 | spl5_4 | spl5_6 | ~spl5_1 | ~spl5_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f359,f122,f102,f127,f117,f362])).
% 0.22/0.53  fof(f359,plain,(
% 0.22/0.53    ~l1_pre_topc(sK0) | v1_xboole_0(sK1) | v2_struct_0(sK0) | sK1 = u1_struct_0(sK3(sK0,sK1)) | ~spl5_5),
% 0.22/0.53    inference(resolution,[],[f73,f124])).
% 0.22/0.53  fof(f73,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | v2_struct_0(X0) | u1_struct_0(sK3(X0,X1)) = X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f35])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f34])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2))))),
% 0.22/0.53    inference(pure_predicate_removal,[],[f14])).
% 0.22/0.53  fof(f14,axiom,(
% 0.22/0.53    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_tsep_1)).
% 0.22/0.53  fof(f341,plain,(
% 0.22/0.53    spl5_36 | ~spl5_35),
% 0.22/0.53    inference(avatar_split_clause,[],[f336,f330,f338])).
% 0.22/0.53  fof(f330,plain,(
% 0.22/0.53    spl5_35 <=> l1_pre_topc(sK3(sK0,sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).
% 0.22/0.53  fof(f336,plain,(
% 0.22/0.53    l1_struct_0(sK3(sK0,sK1)) | ~spl5_35),
% 0.22/0.53    inference(resolution,[],[f332,f65])).
% 0.22/0.53  fof(f65,plain,(
% 0.22/0.53    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f26])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.53  fof(f332,plain,(
% 0.22/0.53    l1_pre_topc(sK3(sK0,sK1)) | ~spl5_35),
% 0.22/0.53    inference(avatar_component_clause,[],[f330])).
% 0.22/0.53  fof(f333,plain,(
% 0.22/0.53    spl5_35 | ~spl5_1 | ~spl5_32),
% 0.22/0.53    inference(avatar_split_clause,[],[f319,f313,f102,f330])).
% 0.22/0.53  fof(f319,plain,(
% 0.22/0.53    ~l1_pre_topc(sK0) | l1_pre_topc(sK3(sK0,sK1)) | ~spl5_32),
% 0.22/0.53    inference(resolution,[],[f315,f68])).
% 0.22/0.53  fof(f68,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f31])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.22/0.53  fof(f328,plain,(
% 0.22/0.53    ~spl5_33 | spl5_34 | spl5_25 | spl5_4 | ~spl5_1 | ~spl5_2 | ~spl5_32),
% 0.22/0.53    inference(avatar_split_clause,[],[f318,f313,f107,f102,f117,f272,f325,f321])).
% 0.22/0.53  fof(f107,plain,(
% 0.22/0.53    spl5_2 <=> v2_tdlat_3(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.53  fof(f318,plain,(
% 0.22/0.53    ~v2_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v2_struct_0(sK3(sK0,sK1)) | v7_struct_0(sK3(sK0,sK1)) | ~v1_tdlat_3(sK3(sK0,sK1)) | ~spl5_32),
% 0.22/0.53    inference(resolution,[],[f315,f142])).
% 0.22/0.53  fof(f142,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v2_struct_0(X1) | v7_struct_0(X1) | ~v1_tdlat_3(X1)) )),
% 0.22/0.53    inference(global_subsumption,[],[f67,f77])).
% 0.22/0.53  fof(f77,plain,(
% 0.22/0.53    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | v7_struct_0(X1) | ~v1_tdlat_3(X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f41])).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : ((~v1_tdlat_3(X1) & ~v2_struct_0(X1)) | v7_struct_0(X1) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f40])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (((~v1_tdlat_3(X1) & ~v2_struct_0(X1)) | (v7_struct_0(X1) | v2_struct_0(X1))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f12])).
% 0.22/0.53  fof(f12,axiom,(
% 0.22/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ((~v7_struct_0(X1) & ~v2_struct_0(X1)) => (~v1_tdlat_3(X1) & ~v2_struct_0(X1)))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc32_tex_2)).
% 0.22/0.53  fof(f67,plain,(
% 0.22/0.53    ( ! [X0] : (~v2_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_pre_topc(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(flattening,[],[f29])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ! [X0] : ((v2_pre_topc(X0) | ~v2_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f11])).
% 0.22/0.53  fof(f11,axiom,(
% 0.22/0.53    ! [X0] : (l1_pre_topc(X0) => (v2_tdlat_3(X0) => v2_pre_topc(X0)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tdlat_3)).
% 0.22/0.53  fof(f316,plain,(
% 0.22/0.53    spl5_32 | spl5_4 | spl5_6 | ~spl5_1 | ~spl5_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f310,f122,f102,f127,f117,f313])).
% 0.22/0.53  fof(f310,plain,(
% 0.22/0.53    ~l1_pre_topc(sK0) | v1_xboole_0(sK1) | v2_struct_0(sK0) | m1_pre_topc(sK3(sK0,sK1),sK0) | ~spl5_5),
% 0.22/0.53    inference(resolution,[],[f72,f124])).
% 0.22/0.53  fof(f72,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | v2_struct_0(X0) | m1_pre_topc(sK3(X0,X1),X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f35])).
% 0.22/0.53  fof(f304,plain,(
% 0.22/0.53    spl5_30 | spl5_27 | ~spl5_26),
% 0.22/0.53    inference(avatar_split_clause,[],[f288,f279,f283,f301])).
% 0.22/0.53  fof(f301,plain,(
% 0.22/0.53    spl5_30 <=> k1_tarski(sK2(sK1)) = k6_domain_1(u1_struct_0(sK0),sK2(sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 0.22/0.53  fof(f288,plain,(
% 0.22/0.53    v1_xboole_0(u1_struct_0(sK0)) | k1_tarski(sK2(sK1)) = k6_domain_1(u1_struct_0(sK0),sK2(sK1)) | ~spl5_26),
% 0.22/0.53    inference(resolution,[],[f281,f85])).
% 0.22/0.53  fof(f85,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | v1_xboole_0(X0) | k6_domain_1(X0,X1) = k1_tarski(X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f50])).
% 0.22/0.53  fof(f50,plain,(
% 0.22/0.53    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.22/0.53    inference(flattening,[],[f49])).
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,axiom,(
% 0.22/0.53    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.22/0.53  fof(f275,plain,(
% 0.22/0.53    ~spl5_25 | spl5_4 | spl5_6 | ~spl5_1 | ~spl5_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f269,f122,f102,f127,f117,f272])).
% 0.22/0.53  fof(f269,plain,(
% 0.22/0.53    ~l1_pre_topc(sK0) | v1_xboole_0(sK1) | v2_struct_0(sK0) | ~v2_struct_0(sK3(sK0,sK1)) | ~spl5_5),
% 0.22/0.53    inference(resolution,[],[f71,f124])).
% 0.22/0.53  fof(f71,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | v2_struct_0(X0) | ~v2_struct_0(sK3(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f35])).
% 0.22/0.53  fof(f268,plain,(
% 0.22/0.53    spl5_24 | ~spl5_11 | ~spl5_14),
% 0.22/0.53    inference(avatar_split_clause,[],[f262,f182,f161,f265])).
% 0.22/0.53  fof(f262,plain,(
% 0.22/0.53    r2_hidden(sK2(sK1),u1_struct_0(sK0)) | (~spl5_11 | ~spl5_14)),
% 0.22/0.53    inference(resolution,[],[f206,f163])).
% 0.22/0.53  fof(f163,plain,(
% 0.22/0.53    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl5_11),
% 0.22/0.53    inference(avatar_component_clause,[],[f161])).
% 0.22/0.53  fof(f206,plain,(
% 0.22/0.53    ( ! [X3] : (~r1_tarski(sK1,X3) | r2_hidden(sK2(sK1),X3)) ) | ~spl5_14),
% 0.22/0.53    inference(resolution,[],[f89,f184])).
% 0.22/0.53  fof(f184,plain,(
% 0.22/0.53    r2_hidden(sK2(sK1),sK1) | ~spl5_14),
% 0.22/0.53    inference(avatar_component_clause,[],[f182])).
% 0.22/0.53  fof(f89,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f51])).
% 0.22/0.53  fof(f51,plain,(
% 0.22/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.53  fof(f234,plain,(
% 0.22/0.53    spl5_19 | spl5_6 | ~spl5_12),
% 0.22/0.53    inference(avatar_split_clause,[],[f231,f168,f127,f226])).
% 0.22/0.53  fof(f226,plain,(
% 0.22/0.53    spl5_19 <=> k6_domain_1(sK1,sK2(sK1)) = k1_tarski(sK2(sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.22/0.53  fof(f231,plain,(
% 0.22/0.53    v1_xboole_0(sK1) | k6_domain_1(sK1,sK2(sK1)) = k1_tarski(sK2(sK1)) | ~spl5_12),
% 0.22/0.53    inference(resolution,[],[f170,f85])).
% 0.22/0.53  fof(f216,plain,(
% 0.22/0.53    spl5_6 | spl5_17 | ~spl5_8),
% 0.22/0.53    inference(avatar_split_clause,[],[f211,f136,f213,f127])).
% 0.22/0.53  fof(f213,plain,(
% 0.22/0.53    spl5_17 <=> sK1 = k6_domain_1(sK1,sK2(sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.22/0.53  fof(f211,plain,(
% 0.22/0.53    sK1 = k6_domain_1(sK1,sK2(sK1)) | v1_xboole_0(sK1) | ~spl5_8),
% 0.22/0.53    inference(resolution,[],[f63,f137])).
% 0.22/0.53  fof(f63,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_zfmisc_1(X0) | k6_domain_1(X0,sK2(X0)) = X0 | v1_xboole_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f25])).
% 0.22/0.53  fof(f140,plain,(
% 0.22/0.53    spl5_7 | spl5_8),
% 0.22/0.53    inference(avatar_split_clause,[],[f54,f136,f132])).
% 0.22/0.53  fof(f54,plain,(
% 0.22/0.53    v1_zfmisc_1(sK1) | v2_tex_2(sK1,sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f24])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f21])).
% 0.22/0.53  fof(f21,negated_conjecture,(
% 0.22/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.22/0.53    inference(negated_conjecture,[],[f20])).
% 0.22/0.53  fof(f20,conjecture,(
% 0.22/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).
% 0.22/0.53  fof(f139,plain,(
% 0.22/0.53    ~spl5_7 | ~spl5_8),
% 0.22/0.53    inference(avatar_split_clause,[],[f55,f136,f132])).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    ~v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f24])).
% 0.22/0.53  fof(f130,plain,(
% 0.22/0.53    ~spl5_6),
% 0.22/0.53    inference(avatar_split_clause,[],[f56,f127])).
% 0.22/0.53  fof(f56,plain,(
% 0.22/0.53    ~v1_xboole_0(sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f24])).
% 0.22/0.53  fof(f125,plain,(
% 0.22/0.53    spl5_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f57,f122])).
% 0.22/0.53  fof(f57,plain,(
% 0.22/0.53    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.53    inference(cnf_transformation,[],[f24])).
% 0.22/0.53  fof(f120,plain,(
% 0.22/0.53    ~spl5_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f58,f117])).
% 0.22/0.53  fof(f58,plain,(
% 0.22/0.53    ~v2_struct_0(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f24])).
% 0.22/0.53  fof(f115,plain,(
% 0.22/0.53    spl5_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f59,f112])).
% 0.22/0.53  fof(f59,plain,(
% 0.22/0.53    v2_pre_topc(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f24])).
% 0.22/0.53  fof(f110,plain,(
% 0.22/0.53    spl5_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f60,f107])).
% 0.22/0.53  fof(f60,plain,(
% 0.22/0.53    v2_tdlat_3(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f24])).
% 0.22/0.53  fof(f105,plain,(
% 0.22/0.53    spl5_1),
% 0.22/0.53    inference(avatar_split_clause,[],[f61,f102])).
% 0.22/0.53  fof(f61,plain,(
% 0.22/0.53    l1_pre_topc(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f24])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (14816)------------------------------
% 0.22/0.53  % (14816)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (14816)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (14816)Memory used [KB]: 11513
% 0.22/0.53  % (14816)Time elapsed: 0.087 s
% 0.22/0.53  % (14816)------------------------------
% 0.22/0.53  % (14816)------------------------------
% 0.22/0.53  % (14798)Success in time 0.167 s
%------------------------------------------------------------------------------
