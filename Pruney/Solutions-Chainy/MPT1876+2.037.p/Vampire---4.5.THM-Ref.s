%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:41 EST 2020

% Result     : Theorem 1.57s
% Output     : Refutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :  221 ( 459 expanded)
%              Number of leaves         :   54 ( 200 expanded)
%              Depth                    :   11
%              Number of atoms          :  833 (1921 expanded)
%              Number of equality atoms :   40 (  63 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f875,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f107,f108,f113,f118,f123,f128,f133,f138,f152,f200,f205,f229,f238,f242,f243,f262,f325,f327,f387,f396,f413,f418,f434,f448,f454,f499,f501,f510,f868,f871,f873,f874])).

fof(f874,plain,
    ( k1_tarski(sK3(sK1)) != k6_domain_1(u1_struct_0(sK0),sK3(sK1))
    | sK1 != k1_tarski(sK3(sK1))
    | k1_tarski(sK3(sK1)) != k6_domain_1(sK1,sK3(sK1))
    | v2_tex_2(sK1,sK0)
    | ~ v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK3(sK1)),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f873,plain,
    ( ~ spl5_38
    | spl5_2
    | ~ spl5_14
    | ~ spl5_37 ),
    inference(avatar_split_clause,[],[f872,f410,f221,f104,f426])).

fof(f426,plain,
    ( spl5_38
  <=> v7_struct_0(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f104,plain,
    ( spl5_2
  <=> v1_zfmisc_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f221,plain,
    ( spl5_14
  <=> sK1 = u1_struct_0(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f410,plain,
    ( spl5_37
  <=> l1_struct_0(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).

fof(f872,plain,
    ( v1_zfmisc_1(sK1)
    | ~ v7_struct_0(sK2(sK0,sK1))
    | ~ spl5_14
    | ~ spl5_37 ),
    inference(subsumption_resolution,[],[f334,f412])).

fof(f412,plain,
    ( l1_struct_0(sK2(sK0,sK1))
    | ~ spl5_37 ),
    inference(avatar_component_clause,[],[f410])).

fof(f334,plain,
    ( v1_zfmisc_1(sK1)
    | ~ l1_struct_0(sK2(sK0,sK1))
    | ~ v7_struct_0(sK2(sK0,sK1))
    | ~ spl5_14 ),
    inference(superposition,[],[f86,f223])).

fof(f223,plain,
    ( sK1 = u1_struct_0(sK2(sK0,sK1))
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f221])).

fof(f86,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).

fof(f871,plain,
    ( ~ spl5_2
    | spl5_70
    | spl5_4
    | ~ spl5_46 ),
    inference(avatar_split_clause,[],[f870,f506,f115,f851,f104])).

fof(f851,plain,
    ( spl5_70
  <=> sK1 = k1_tarski(sK3(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_70])])).

fof(f115,plain,
    ( spl5_4
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f506,plain,
    ( spl5_46
  <=> r1_tarski(k1_tarski(sK3(sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).

fof(f870,plain,
    ( sK1 = k1_tarski(sK3(sK1))
    | ~ v1_zfmisc_1(sK1)
    | spl5_4
    | ~ spl5_46 ),
    inference(subsumption_resolution,[],[f869,f71])).

fof(f71,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f869,plain,
    ( sK1 = k1_tarski(sK3(sK1))
    | ~ v1_zfmisc_1(sK1)
    | v1_xboole_0(k1_tarski(sK3(sK1)))
    | spl5_4
    | ~ spl5_46 ),
    inference(subsumption_resolution,[],[f849,f117])).

fof(f117,plain,
    ( ~ v1_xboole_0(sK1)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f115])).

fof(f849,plain,
    ( sK1 = k1_tarski(sK3(sK1))
    | ~ v1_zfmisc_1(sK1)
    | v1_xboole_0(sK1)
    | v1_xboole_0(k1_tarski(sK3(sK1)))
    | ~ spl5_46 ),
    inference(resolution,[],[f508,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X0,X1)
      | ~ v1_zfmisc_1(X1)
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

fof(f508,plain,
    ( r1_tarski(k1_tarski(sK3(sK1)),sK1)
    | ~ spl5_46 ),
    inference(avatar_component_clause,[],[f506])).

fof(f868,plain,
    ( ~ spl5_1
    | ~ spl5_3
    | ~ spl5_5
    | spl5_8
    | ~ spl5_15
    | ~ spl5_35 ),
    inference(avatar_split_clause,[],[f628,f383,f226,f135,f120,f110,f100])).

fof(f100,plain,
    ( spl5_1
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f110,plain,
    ( spl5_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f120,plain,
    ( spl5_5
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f135,plain,
    ( spl5_8
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f226,plain,
    ( spl5_15
  <=> m1_pre_topc(sK2(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f383,plain,
    ( spl5_35
  <=> ! [X9] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X9)))
        | v2_struct_0(X9)
        | ~ l1_pre_topc(X9)
        | ~ m1_pre_topc(sK2(sK0,sK1),X9)
        | ~ v2_tex_2(sK1,X9) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f628,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | ~ spl5_3
    | ~ spl5_5
    | spl5_8
    | ~ spl5_15
    | ~ spl5_35 ),
    inference(unit_resulting_resolution,[],[f122,f137,f112,f228,f384])).

fof(f384,plain,
    ( ! [X9] :
        ( ~ m1_pre_topc(sK2(sK0,sK1),X9)
        | v2_struct_0(X9)
        | ~ l1_pre_topc(X9)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ v2_tex_2(sK1,X9) )
    | ~ spl5_35 ),
    inference(avatar_component_clause,[],[f383])).

fof(f228,plain,
    ( m1_pre_topc(sK2(sK0,sK1),sK0)
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f226])).

fof(f112,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f110])).

fof(f137,plain,
    ( ~ v2_struct_0(sK0)
    | spl5_8 ),
    inference(avatar_component_clause,[],[f135])).

fof(f122,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f120])).

fof(f510,plain,
    ( spl5_46
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f503,f202,f506])).

fof(f202,plain,
    ( spl5_12
  <=> m1_subset_1(k1_tarski(sK3(sK1)),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f503,plain,
    ( r1_tarski(k1_tarski(sK3(sK1)),sK1)
    | ~ spl5_12 ),
    inference(resolution,[],[f204,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f204,plain,
    ( m1_subset_1(k1_tarski(sK3(sK1)),k1_zfmisc_1(sK1))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f202])).

fof(f501,plain,
    ( spl5_44
    | spl5_20
    | ~ spl5_39 ),
    inference(avatar_split_clause,[],[f500,f445,f265,f491])).

fof(f491,plain,
    ( spl5_44
  <=> k1_tarski(sK3(sK1)) = k6_domain_1(u1_struct_0(sK0),sK3(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).

fof(f265,plain,
    ( spl5_20
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f445,plain,
    ( spl5_39
  <=> m1_subset_1(sK3(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).

fof(f500,plain,
    ( k1_tarski(sK3(sK1)) = k6_domain_1(u1_struct_0(sK0),sK3(sK1))
    | spl5_20
    | ~ spl5_39 ),
    inference(subsumption_resolution,[],[f489,f266])).

fof(f266,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl5_20 ),
    inference(avatar_component_clause,[],[f265])).

fof(f489,plain,
    ( k1_tarski(sK3(sK1)) = k6_domain_1(u1_struct_0(sK0),sK3(sK1))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_39 ),
    inference(resolution,[],[f447,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f447,plain,
    ( m1_subset_1(sK3(sK1),u1_struct_0(sK0))
    | ~ spl5_39 ),
    inference(avatar_component_clause,[],[f445])).

fof(f499,plain,
    ( spl5_45
    | ~ spl5_5
    | ~ spl5_7
    | spl5_8
    | ~ spl5_39 ),
    inference(avatar_split_clause,[],[f486,f445,f135,f130,f120,f496])).

fof(f496,plain,
    ( spl5_45
  <=> v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK3(sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).

fof(f130,plain,
    ( spl5_7
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f486,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK3(sK1)),sK0)
    | ~ spl5_5
    | ~ spl5_7
    | spl5_8
    | ~ spl5_39 ),
    inference(unit_resulting_resolution,[],[f137,f132,f122,f447,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
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
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).

fof(f132,plain,
    ( v2_pre_topc(sK0)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f130])).

fof(f454,plain,
    ( ~ spl5_20
    | ~ spl5_19 ),
    inference(avatar_split_clause,[],[f442,f259,f265])).

fof(f259,plain,
    ( spl5_19
  <=> r2_hidden(sK3(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f442,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_19 ),
    inference(resolution,[],[f261,f87])).

fof(f87,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f55,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f261,plain,
    ( r2_hidden(sK3(sK1),u1_struct_0(sK0))
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f259])).

fof(f448,plain,
    ( spl5_39
    | ~ spl5_19 ),
    inference(avatar_split_clause,[],[f437,f259,f445])).

fof(f437,plain,
    ( m1_subset_1(sK3(sK1),u1_struct_0(sK0))
    | ~ spl5_19 ),
    inference(unit_resulting_resolution,[],[f261,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f434,plain,
    ( spl5_38
    | spl5_16
    | ~ spl5_25
    | ~ spl5_26
    | ~ spl5_29
    | ~ spl5_31 ),
    inference(avatar_split_clause,[],[f433,f362,f353,f317,f312,f231,f426])).

fof(f231,plain,
    ( spl5_16
  <=> v2_struct_0(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f312,plain,
    ( spl5_25
  <=> l1_pre_topc(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f317,plain,
    ( spl5_26
  <=> v2_tdlat_3(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f353,plain,
    ( spl5_29
  <=> v2_pre_topc(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f362,plain,
    ( spl5_31
  <=> v1_tdlat_3(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f433,plain,
    ( v7_struct_0(sK2(sK0,sK1))
    | spl5_16
    | ~ spl5_25
    | ~ spl5_26
    | ~ spl5_29
    | ~ spl5_31 ),
    inference(subsumption_resolution,[],[f432,f314])).

fof(f314,plain,
    ( l1_pre_topc(sK2(sK0,sK1))
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f312])).

fof(f432,plain,
    ( v7_struct_0(sK2(sK0,sK1))
    | ~ l1_pre_topc(sK2(sK0,sK1))
    | spl5_16
    | ~ spl5_26
    | ~ spl5_29
    | ~ spl5_31 ),
    inference(subsumption_resolution,[],[f431,f233])).

fof(f233,plain,
    ( ~ v2_struct_0(sK2(sK0,sK1))
    | spl5_16 ),
    inference(avatar_component_clause,[],[f231])).

fof(f431,plain,
    ( v7_struct_0(sK2(sK0,sK1))
    | v2_struct_0(sK2(sK0,sK1))
    | ~ l1_pre_topc(sK2(sK0,sK1))
    | ~ spl5_26
    | ~ spl5_29
    | ~ spl5_31 ),
    inference(subsumption_resolution,[],[f430,f354])).

fof(f354,plain,
    ( v2_pre_topc(sK2(sK0,sK1))
    | ~ spl5_29 ),
    inference(avatar_component_clause,[],[f353])).

fof(f430,plain,
    ( v7_struct_0(sK2(sK0,sK1))
    | ~ v2_pre_topc(sK2(sK0,sK1))
    | v2_struct_0(sK2(sK0,sK1))
    | ~ l1_pre_topc(sK2(sK0,sK1))
    | ~ spl5_26
    | ~ spl5_31 ),
    inference(subsumption_resolution,[],[f424,f319])).

fof(f319,plain,
    ( v2_tdlat_3(sK2(sK0,sK1))
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f317])).

fof(f424,plain,
    ( v7_struct_0(sK2(sK0,sK1))
    | ~ v2_tdlat_3(sK2(sK0,sK1))
    | ~ v2_pre_topc(sK2(sK0,sK1))
    | v2_struct_0(sK2(sK0,sK1))
    | ~ l1_pre_topc(sK2(sK0,sK1))
    | ~ spl5_31 ),
    inference(resolution,[],[f363,f76])).

fof(f76,plain,(
    ! [X0] :
      ( v7_struct_0(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
      | ~ v2_tdlat_3(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
      | ~ v2_tdlat_3(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( ( v2_tdlat_3(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ( v2_pre_topc(X0)
          & v7_struct_0(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_1)).

fof(f363,plain,
    ( v1_tdlat_3(sK2(sK0,sK1))
    | ~ spl5_31 ),
    inference(avatar_component_clause,[],[f362])).

fof(f418,plain,
    ( spl5_29
    | ~ spl5_25
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f414,f317,f312,f353])).

fof(f414,plain,
    ( v2_pre_topc(sK2(sK0,sK1))
    | ~ spl5_25
    | ~ spl5_26 ),
    inference(unit_resulting_resolution,[],[f314,f319,f74])).

fof(f74,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tdlat_3)).

fof(f413,plain,
    ( spl5_37
    | ~ spl5_25 ),
    inference(avatar_split_clause,[],[f397,f312,f410])).

fof(f397,plain,
    ( l1_struct_0(sK2(sK0,sK1))
    | ~ spl5_25 ),
    inference(unit_resulting_resolution,[],[f314,f73])).

fof(f73,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f396,plain,
    ( spl5_36
    | spl5_4
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f395,f197,f115,f391])).

fof(f391,plain,
    ( spl5_36
  <=> k1_tarski(sK3(sK1)) = k6_domain_1(sK1,sK3(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f197,plain,
    ( spl5_11
  <=> m1_subset_1(sK3(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f395,plain,
    ( k1_tarski(sK3(sK1)) = k6_domain_1(sK1,sK3(sK1))
    | spl5_4
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f389,f117])).

fof(f389,plain,
    ( k1_tarski(sK3(sK1)) = k6_domain_1(sK1,sK3(sK1))
    | v1_xboole_0(sK1)
    | ~ spl5_11 ),
    inference(resolution,[],[f199,f91])).

fof(f199,plain,
    ( m1_subset_1(sK3(sK1),sK1)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f197])).

fof(f387,plain,
    ( spl5_31
    | spl5_35
    | ~ spl5_14
    | spl5_16 ),
    inference(avatar_split_clause,[],[f386,f231,f221,f383,f362])).

fof(f386,plain,
    ( ! [X10] :
        ( ~ v2_tex_2(sK1,X10)
        | v1_tdlat_3(sK2(sK0,sK1))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ m1_pre_topc(sK2(sK0,sK1),X10)
        | ~ l1_pre_topc(X10)
        | v2_struct_0(X10) )
    | ~ spl5_14
    | spl5_16 ),
    inference(subsumption_resolution,[],[f340,f233])).

fof(f340,plain,
    ( ! [X10] :
        ( ~ v2_tex_2(sK1,X10)
        | v1_tdlat_3(sK2(sK0,sK1))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ m1_pre_topc(sK2(sK0,sK1),X10)
        | v2_struct_0(sK2(sK0,sK1))
        | ~ l1_pre_topc(X10)
        | v2_struct_0(X10) )
    | ~ spl5_14 ),
    inference(superposition,[],[f98,f223])).

fof(f98,plain,(
    ! [X0,X1] :
      ( v1_tdlat_3(X1)
      | ~ v2_tex_2(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( v1_tdlat_3(X1)
      | ~ v2_tex_2(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
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
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_tex_2)).

fof(f327,plain,
    ( spl5_25
    | ~ spl5_5
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f326,f226,f120,f312])).

fof(f326,plain,
    ( l1_pre_topc(sK2(sK0,sK1))
    | ~ spl5_5
    | ~ spl5_15 ),
    inference(subsumption_resolution,[],[f310,f122])).

fof(f310,plain,
    ( l1_pre_topc(sK2(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl5_15 ),
    inference(resolution,[],[f228,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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

fof(f325,plain,
    ( spl5_26
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | spl5_8
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f324,f226,f135,f130,f125,f120,f317])).

fof(f125,plain,
    ( spl5_6
  <=> v2_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f324,plain,
    ( v2_tdlat_3(sK2(sK0,sK1))
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | spl5_8
    | ~ spl5_15 ),
    inference(subsumption_resolution,[],[f323,f137])).

fof(f323,plain,
    ( v2_tdlat_3(sK2(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_15 ),
    inference(subsumption_resolution,[],[f322,f132])).

fof(f322,plain,
    ( v2_tdlat_3(sK2(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_15 ),
    inference(subsumption_resolution,[],[f321,f127])).

fof(f127,plain,
    ( v2_tdlat_3(sK0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f125])).

fof(f321,plain,
    ( v2_tdlat_3(sK2(sK0,sK1))
    | ~ v2_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_5
    | ~ spl5_15 ),
    inference(subsumption_resolution,[],[f307,f122])).

fof(f307,plain,
    ( v2_tdlat_3(sK2(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_15 ),
    inference(resolution,[],[f228,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( v2_tdlat_3(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_tdlat_3(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_tdlat_3)).

fof(f262,plain,
    ( spl5_19
    | ~ spl5_9
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f254,f216,f149,f259])).

fof(f149,plain,
    ( spl5_9
  <=> r2_hidden(sK3(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f216,plain,
    ( spl5_13
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f254,plain,
    ( r2_hidden(sK3(sK1),u1_struct_0(sK0))
    | ~ spl5_9
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f151,f218,f92])).

fof(f92,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f59,f60])).

fof(f60,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f218,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f216])).

fof(f151,plain,
    ( r2_hidden(sK3(sK1),sK1)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f149])).

fof(f243,plain,
    ( spl5_13
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f213,f110,f216])).

fof(f213,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl5_3 ),
    inference(resolution,[],[f112,f95])).

fof(f242,plain,
    ( spl5_14
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | spl5_8 ),
    inference(avatar_split_clause,[],[f241,f135,f120,f115,f110,f221])).

fof(f241,plain,
    ( sK1 = u1_struct_0(sK2(sK0,sK1))
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | spl5_8 ),
    inference(subsumption_resolution,[],[f240,f137])).

fof(f240,plain,
    ( sK1 = u1_struct_0(sK2(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f239,f122])).

fof(f239,plain,
    ( sK1 = u1_struct_0(sK2(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_3
    | spl5_4 ),
    inference(subsumption_resolution,[],[f212,f117])).

fof(f212,plain,
    ( sK1 = u1_struct_0(sK2(sK0,sK1))
    | v1_xboole_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_3 ),
    inference(resolution,[],[f112,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( u1_struct_0(sK2(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_struct_0(sK2(X0,X1)) = X1
            & m1_pre_topc(sK2(X0,X1),X0)
            & ~ v2_struct_0(sK2(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f32,f51])).

fof(f51,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X1
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( u1_struct_0(sK2(X0,X1)) = X1
        & m1_pre_topc(sK2(X0,X1),X0)
        & ~ v2_struct_0(sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_tsep_1)).

fof(f238,plain,
    ( ~ spl5_16
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | spl5_8 ),
    inference(avatar_split_clause,[],[f237,f135,f120,f115,f110,f231])).

fof(f237,plain,
    ( ~ v2_struct_0(sK2(sK0,sK1))
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | spl5_8 ),
    inference(subsumption_resolution,[],[f236,f137])).

fof(f236,plain,
    ( ~ v2_struct_0(sK2(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f235,f122])).

fof(f235,plain,
    ( ~ v2_struct_0(sK2(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_3
    | spl5_4 ),
    inference(subsumption_resolution,[],[f210,f117])).

fof(f210,plain,
    ( ~ v2_struct_0(sK2(sK0,sK1))
    | v1_xboole_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_3 ),
    inference(resolution,[],[f112,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f229,plain,
    ( spl5_15
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | spl5_8 ),
    inference(avatar_split_clause,[],[f207,f135,f120,f115,f110,f226])).

fof(f207,plain,
    ( m1_pre_topc(sK2(sK0,sK1),sK0)
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | spl5_8 ),
    inference(unit_resulting_resolution,[],[f137,f122,f117,f112,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(sK2(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f205,plain,
    ( spl5_12
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f189,f149,f202])).

fof(f189,plain,
    ( m1_subset_1(k1_tarski(sK3(sK1)),k1_zfmisc_1(sK1))
    | ~ spl5_9 ),
    inference(unit_resulting_resolution,[],[f151,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

fof(f200,plain,
    ( spl5_11
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f190,f149,f197])).

fof(f190,plain,
    ( m1_subset_1(sK3(sK1),sK1)
    | ~ spl5_9 ),
    inference(unit_resulting_resolution,[],[f151,f89])).

fof(f152,plain,
    ( spl5_9
    | spl5_4 ),
    inference(avatar_split_clause,[],[f140,f115,f149])).

fof(f140,plain,
    ( r2_hidden(sK3(sK1),sK1)
    | spl5_4 ),
    inference(unit_resulting_resolution,[],[f117,f88])).

fof(f88,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK3(X0),X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f138,plain,(
    ~ spl5_8 ),
    inference(avatar_split_clause,[],[f63,f135])).

fof(f63,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,
    ( ( ~ v1_zfmisc_1(sK1)
      | ~ v2_tex_2(sK1,sK0) )
    & ( v1_zfmisc_1(sK1)
      | v2_tex_2(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & ~ v1_xboole_0(sK1)
    & l1_pre_topc(sK0)
    & v2_tdlat_3(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f47,f49,f48])).

fof(f48,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v1_zfmisc_1(X1)
              | ~ v2_tex_2(X1,X0) )
            & ( v1_zfmisc_1(X1)
              | v2_tex_2(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v2_tex_2(X1,sK0) )
          & ( v1_zfmisc_1(X1)
            | v2_tex_2(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(sK0)
      & v2_tdlat_3(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ? [X1] :
        ( ( ~ v1_zfmisc_1(X1)
          | ~ v2_tex_2(X1,sK0) )
        & ( v1_zfmisc_1(X1)
          | v2_tex_2(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        & ~ v1_xboole_0(X1) )
   => ( ( ~ v1_zfmisc_1(sK1)
        | ~ v2_tex_2(sK1,sK0) )
      & ( v1_zfmisc_1(sK1)
        | v2_tex_2(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v2_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v2_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v2_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v2_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
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
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tex_2)).

fof(f133,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f64,f130])).

fof(f64,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f128,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f65,f125])).

fof(f65,plain,(
    v2_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f123,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f66,f120])).

fof(f66,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f118,plain,(
    ~ spl5_4 ),
    inference(avatar_split_clause,[],[f67,f115])).

fof(f67,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f113,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f68,f110])).

fof(f68,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f50])).

fof(f108,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f69,f104,f100])).

fof(f69,plain,
    ( v1_zfmisc_1(sK1)
    | v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f107,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f70,f104,f100])).

fof(f70,plain,
    ( ~ v1_zfmisc_1(sK1)
    | ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f50])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:35:20 EST 2020
% 0.21/0.35  % CPUTime    : 
% 0.22/0.50  % (18193)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.50  % (18199)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.51  % (18203)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.51  % (18210)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.52  % (18197)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.52  % (18190)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (18189)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % (18202)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.52  % (18198)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (18186)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.53  % (18206)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.53  % (18187)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (18211)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.53  % (18208)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.53  % (18215)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.54  % (18200)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.54  % (18197)Refutation not found, incomplete strategy% (18197)------------------------------
% 0.22/0.54  % (18197)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (18197)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (18197)Memory used [KB]: 10618
% 0.22/0.54  % (18197)Time elapsed: 0.131 s
% 0.22/0.54  % (18197)------------------------------
% 0.22/0.54  % (18197)------------------------------
% 0.22/0.54  % (18188)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (18191)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  % (18201)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.54  % (18212)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % (18195)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.54  % (18188)Refutation not found, incomplete strategy% (18188)------------------------------
% 0.22/0.54  % (18188)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (18188)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (18188)Memory used [KB]: 10746
% 0.22/0.54  % (18188)Time elapsed: 0.118 s
% 0.22/0.54  % (18188)------------------------------
% 0.22/0.54  % (18188)------------------------------
% 0.22/0.54  % (18213)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.54  % (18208)Refutation not found, incomplete strategy% (18208)------------------------------
% 0.22/0.54  % (18208)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (18204)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.55  % (18209)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.55  % (18205)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.55  % (18194)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.55  % (18196)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.55  % (18214)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.55  % (18192)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.55  % (18208)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (18208)Memory used [KB]: 10746
% 0.22/0.55  % (18208)Time elapsed: 0.096 s
% 0.22/0.55  % (18208)------------------------------
% 0.22/0.55  % (18208)------------------------------
% 0.22/0.56  % (18196)Refutation not found, incomplete strategy% (18196)------------------------------
% 0.22/0.56  % (18196)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.56  % (18207)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.57/0.56  % (18211)Refutation found. Thanks to Tanya!
% 1.57/0.56  % SZS status Theorem for theBenchmark
% 1.57/0.56  % (18196)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.56  
% 1.57/0.56  % (18196)Memory used [KB]: 10618
% 1.57/0.56  % (18196)Time elapsed: 0.152 s
% 1.57/0.56  % (18196)------------------------------
% 1.57/0.56  % (18196)------------------------------
% 1.57/0.57  % SZS output start Proof for theBenchmark
% 1.57/0.57  fof(f875,plain,(
% 1.57/0.57    $false),
% 1.57/0.57    inference(avatar_sat_refutation,[],[f107,f108,f113,f118,f123,f128,f133,f138,f152,f200,f205,f229,f238,f242,f243,f262,f325,f327,f387,f396,f413,f418,f434,f448,f454,f499,f501,f510,f868,f871,f873,f874])).
% 1.57/0.57  fof(f874,plain,(
% 1.57/0.57    k1_tarski(sK3(sK1)) != k6_domain_1(u1_struct_0(sK0),sK3(sK1)) | sK1 != k1_tarski(sK3(sK1)) | k1_tarski(sK3(sK1)) != k6_domain_1(sK1,sK3(sK1)) | v2_tex_2(sK1,sK0) | ~v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK3(sK1)),sK0)),
% 1.57/0.57    introduced(theory_tautology_sat_conflict,[])).
% 1.57/0.57  fof(f873,plain,(
% 1.57/0.57    ~spl5_38 | spl5_2 | ~spl5_14 | ~spl5_37),
% 1.57/0.57    inference(avatar_split_clause,[],[f872,f410,f221,f104,f426])).
% 1.57/0.57  fof(f426,plain,(
% 1.57/0.57    spl5_38 <=> v7_struct_0(sK2(sK0,sK1))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).
% 1.57/0.57  fof(f104,plain,(
% 1.57/0.57    spl5_2 <=> v1_zfmisc_1(sK1)),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.57/0.57  fof(f221,plain,(
% 1.57/0.57    spl5_14 <=> sK1 = u1_struct_0(sK2(sK0,sK1))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 1.57/0.57  fof(f410,plain,(
% 1.57/0.57    spl5_37 <=> l1_struct_0(sK2(sK0,sK1))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).
% 1.57/0.57  fof(f872,plain,(
% 1.57/0.57    v1_zfmisc_1(sK1) | ~v7_struct_0(sK2(sK0,sK1)) | (~spl5_14 | ~spl5_37)),
% 1.57/0.57    inference(subsumption_resolution,[],[f334,f412])).
% 1.57/0.57  fof(f412,plain,(
% 1.57/0.57    l1_struct_0(sK2(sK0,sK1)) | ~spl5_37),
% 1.57/0.57    inference(avatar_component_clause,[],[f410])).
% 1.57/0.57  fof(f334,plain,(
% 1.57/0.57    v1_zfmisc_1(sK1) | ~l1_struct_0(sK2(sK0,sK1)) | ~v7_struct_0(sK2(sK0,sK1)) | ~spl5_14),
% 1.57/0.57    inference(superposition,[],[f86,f223])).
% 1.57/0.57  fof(f223,plain,(
% 1.57/0.57    sK1 = u1_struct_0(sK2(sK0,sK1)) | ~spl5_14),
% 1.57/0.57    inference(avatar_component_clause,[],[f221])).
% 1.57/0.57  fof(f86,plain,(
% 1.57/0.57    ( ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f40])).
% 1.57/0.57  fof(f40,plain,(
% 1.57/0.57    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 1.57/0.57    inference(flattening,[],[f39])).
% 1.57/0.57  fof(f39,plain,(
% 1.57/0.57    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 1.57/0.57    inference(ennf_transformation,[],[f9])).
% 1.57/0.57  fof(f9,axiom,(
% 1.57/0.57    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 1.57/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).
% 1.57/0.57  fof(f871,plain,(
% 1.57/0.57    ~spl5_2 | spl5_70 | spl5_4 | ~spl5_46),
% 1.57/0.57    inference(avatar_split_clause,[],[f870,f506,f115,f851,f104])).
% 1.57/0.57  fof(f851,plain,(
% 1.57/0.57    spl5_70 <=> sK1 = k1_tarski(sK3(sK1))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_70])])).
% 1.57/0.57  fof(f115,plain,(
% 1.57/0.57    spl5_4 <=> v1_xboole_0(sK1)),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.57/0.57  fof(f506,plain,(
% 1.57/0.57    spl5_46 <=> r1_tarski(k1_tarski(sK3(sK1)),sK1)),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).
% 1.57/0.57  fof(f870,plain,(
% 1.57/0.57    sK1 = k1_tarski(sK3(sK1)) | ~v1_zfmisc_1(sK1) | (spl5_4 | ~spl5_46)),
% 1.57/0.57    inference(subsumption_resolution,[],[f869,f71])).
% 1.57/0.57  fof(f71,plain,(
% 1.57/0.57    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 1.57/0.57    inference(cnf_transformation,[],[f3])).
% 1.57/0.57  fof(f3,axiom,(
% 1.57/0.57    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 1.57/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).
% 1.57/0.57  fof(f869,plain,(
% 1.57/0.57    sK1 = k1_tarski(sK3(sK1)) | ~v1_zfmisc_1(sK1) | v1_xboole_0(k1_tarski(sK3(sK1))) | (spl5_4 | ~spl5_46)),
% 1.57/0.57    inference(subsumption_resolution,[],[f849,f117])).
% 1.57/0.57  fof(f117,plain,(
% 1.57/0.57    ~v1_xboole_0(sK1) | spl5_4),
% 1.57/0.57    inference(avatar_component_clause,[],[f115])).
% 1.57/0.57  fof(f849,plain,(
% 1.57/0.57    sK1 = k1_tarski(sK3(sK1)) | ~v1_zfmisc_1(sK1) | v1_xboole_0(sK1) | v1_xboole_0(k1_tarski(sK3(sK1))) | ~spl5_46),
% 1.57/0.57    inference(resolution,[],[f508,f72])).
% 1.57/0.57  fof(f72,plain,(
% 1.57/0.57    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f24])).
% 1.57/0.57  fof(f24,plain,(
% 1.57/0.57    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.57/0.57    inference(flattening,[],[f23])).
% 1.57/0.57  fof(f23,plain,(
% 1.57/0.57    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 1.57/0.57    inference(ennf_transformation,[],[f15])).
% 1.57/0.57  fof(f15,axiom,(
% 1.57/0.57    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 1.57/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).
% 1.57/0.57  fof(f508,plain,(
% 1.57/0.57    r1_tarski(k1_tarski(sK3(sK1)),sK1) | ~spl5_46),
% 1.57/0.57    inference(avatar_component_clause,[],[f506])).
% 1.57/0.57  fof(f868,plain,(
% 1.57/0.57    ~spl5_1 | ~spl5_3 | ~spl5_5 | spl5_8 | ~spl5_15 | ~spl5_35),
% 1.57/0.57    inference(avatar_split_clause,[],[f628,f383,f226,f135,f120,f110,f100])).
% 1.57/0.57  fof(f100,plain,(
% 1.57/0.57    spl5_1 <=> v2_tex_2(sK1,sK0)),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.57/0.57  fof(f110,plain,(
% 1.57/0.57    spl5_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.57/0.57  fof(f120,plain,(
% 1.57/0.57    spl5_5 <=> l1_pre_topc(sK0)),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.57/0.57  fof(f135,plain,(
% 1.57/0.57    spl5_8 <=> v2_struct_0(sK0)),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.57/0.57  fof(f226,plain,(
% 1.57/0.57    spl5_15 <=> m1_pre_topc(sK2(sK0,sK1),sK0)),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 1.57/0.57  fof(f383,plain,(
% 1.57/0.57    spl5_35 <=> ! [X9] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X9))) | v2_struct_0(X9) | ~l1_pre_topc(X9) | ~m1_pre_topc(sK2(sK0,sK1),X9) | ~v2_tex_2(sK1,X9))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).
% 1.57/0.57  fof(f628,plain,(
% 1.57/0.57    ~v2_tex_2(sK1,sK0) | (~spl5_3 | ~spl5_5 | spl5_8 | ~spl5_15 | ~spl5_35)),
% 1.57/0.57    inference(unit_resulting_resolution,[],[f122,f137,f112,f228,f384])).
% 1.57/0.57  fof(f384,plain,(
% 1.57/0.57    ( ! [X9] : (~m1_pre_topc(sK2(sK0,sK1),X9) | v2_struct_0(X9) | ~l1_pre_topc(X9) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X9))) | ~v2_tex_2(sK1,X9)) ) | ~spl5_35),
% 1.57/0.57    inference(avatar_component_clause,[],[f383])).
% 1.57/0.57  fof(f228,plain,(
% 1.57/0.57    m1_pre_topc(sK2(sK0,sK1),sK0) | ~spl5_15),
% 1.57/0.57    inference(avatar_component_clause,[],[f226])).
% 1.57/0.57  fof(f112,plain,(
% 1.57/0.57    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_3),
% 1.57/0.57    inference(avatar_component_clause,[],[f110])).
% 1.57/0.57  fof(f137,plain,(
% 1.57/0.57    ~v2_struct_0(sK0) | spl5_8),
% 1.57/0.57    inference(avatar_component_clause,[],[f135])).
% 1.57/0.57  fof(f122,plain,(
% 1.57/0.57    l1_pre_topc(sK0) | ~spl5_5),
% 1.57/0.57    inference(avatar_component_clause,[],[f120])).
% 1.57/0.57  fof(f510,plain,(
% 1.57/0.57    spl5_46 | ~spl5_12),
% 1.57/0.57    inference(avatar_split_clause,[],[f503,f202,f506])).
% 1.57/0.57  fof(f202,plain,(
% 1.57/0.57    spl5_12 <=> m1_subset_1(k1_tarski(sK3(sK1)),k1_zfmisc_1(sK1))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 1.57/0.57  fof(f503,plain,(
% 1.57/0.57    r1_tarski(k1_tarski(sK3(sK1)),sK1) | ~spl5_12),
% 1.57/0.57    inference(resolution,[],[f204,f95])).
% 1.57/0.57  fof(f95,plain,(
% 1.57/0.57    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.57/0.57    inference(cnf_transformation,[],[f62])).
% 1.57/0.57  fof(f62,plain,(
% 1.57/0.57    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.57/0.57    inference(nnf_transformation,[],[f6])).
% 1.57/0.57  fof(f6,axiom,(
% 1.57/0.57    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.57/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.57/0.57  fof(f204,plain,(
% 1.57/0.57    m1_subset_1(k1_tarski(sK3(sK1)),k1_zfmisc_1(sK1)) | ~spl5_12),
% 1.57/0.57    inference(avatar_component_clause,[],[f202])).
% 1.57/0.57  fof(f501,plain,(
% 1.57/0.57    spl5_44 | spl5_20 | ~spl5_39),
% 1.57/0.57    inference(avatar_split_clause,[],[f500,f445,f265,f491])).
% 1.57/0.57  fof(f491,plain,(
% 1.57/0.57    spl5_44 <=> k1_tarski(sK3(sK1)) = k6_domain_1(u1_struct_0(sK0),sK3(sK1))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).
% 1.57/0.57  fof(f265,plain,(
% 1.57/0.57    spl5_20 <=> v1_xboole_0(u1_struct_0(sK0))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 1.57/0.57  fof(f445,plain,(
% 1.57/0.57    spl5_39 <=> m1_subset_1(sK3(sK1),u1_struct_0(sK0))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).
% 1.57/0.57  fof(f500,plain,(
% 1.57/0.57    k1_tarski(sK3(sK1)) = k6_domain_1(u1_struct_0(sK0),sK3(sK1)) | (spl5_20 | ~spl5_39)),
% 1.57/0.57    inference(subsumption_resolution,[],[f489,f266])).
% 1.57/0.57  fof(f266,plain,(
% 1.57/0.57    ~v1_xboole_0(u1_struct_0(sK0)) | spl5_20),
% 1.57/0.57    inference(avatar_component_clause,[],[f265])).
% 1.57/0.57  fof(f489,plain,(
% 1.57/0.57    k1_tarski(sK3(sK1)) = k6_domain_1(u1_struct_0(sK0),sK3(sK1)) | v1_xboole_0(u1_struct_0(sK0)) | ~spl5_39),
% 1.57/0.57    inference(resolution,[],[f447,f91])).
% 1.57/0.57  fof(f91,plain,(
% 1.57/0.57    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f44])).
% 1.57/0.57  fof(f44,plain,(
% 1.57/0.57    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.57/0.57    inference(flattening,[],[f43])).
% 1.57/0.57  fof(f43,plain,(
% 1.57/0.57    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.57/0.57    inference(ennf_transformation,[],[f10])).
% 1.57/0.57  fof(f10,axiom,(
% 1.57/0.57    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 1.57/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 1.57/0.57  fof(f447,plain,(
% 1.57/0.57    m1_subset_1(sK3(sK1),u1_struct_0(sK0)) | ~spl5_39),
% 1.57/0.57    inference(avatar_component_clause,[],[f445])).
% 1.57/0.57  fof(f499,plain,(
% 1.57/0.57    spl5_45 | ~spl5_5 | ~spl5_7 | spl5_8 | ~spl5_39),
% 1.57/0.57    inference(avatar_split_clause,[],[f486,f445,f135,f130,f120,f496])).
% 1.57/0.57  fof(f496,plain,(
% 1.57/0.57    spl5_45 <=> v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK3(sK1)),sK0)),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).
% 1.57/0.57  fof(f130,plain,(
% 1.57/0.57    spl5_7 <=> v2_pre_topc(sK0)),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.57/0.57  fof(f486,plain,(
% 1.57/0.57    v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK3(sK1)),sK0) | (~spl5_5 | ~spl5_7 | spl5_8 | ~spl5_39)),
% 1.57/0.57    inference(unit_resulting_resolution,[],[f137,f132,f122,f447,f85])).
% 1.57/0.57  fof(f85,plain,(
% 1.57/0.57    ( ! [X0,X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f38])).
% 1.57/0.57  fof(f38,plain,(
% 1.57/0.57    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.57/0.57    inference(flattening,[],[f37])).
% 1.57/0.57  fof(f37,plain,(
% 1.57/0.57    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.57/0.57    inference(ennf_transformation,[],[f17])).
% 1.57/0.57  fof(f17,axiom,(
% 1.57/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 1.57/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).
% 1.57/0.57  fof(f132,plain,(
% 1.57/0.57    v2_pre_topc(sK0) | ~spl5_7),
% 1.57/0.57    inference(avatar_component_clause,[],[f130])).
% 1.57/0.57  fof(f454,plain,(
% 1.57/0.57    ~spl5_20 | ~spl5_19),
% 1.57/0.57    inference(avatar_split_clause,[],[f442,f259,f265])).
% 1.57/0.57  fof(f259,plain,(
% 1.57/0.57    spl5_19 <=> r2_hidden(sK3(sK1),u1_struct_0(sK0))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 1.57/0.57  fof(f442,plain,(
% 1.57/0.57    ~v1_xboole_0(u1_struct_0(sK0)) | ~spl5_19),
% 1.57/0.57    inference(resolution,[],[f261,f87])).
% 1.57/0.57  fof(f87,plain,(
% 1.57/0.57    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f57])).
% 1.57/0.57  fof(f57,plain,(
% 1.57/0.57    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.57/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f55,f56])).
% 1.57/0.57  fof(f56,plain,(
% 1.57/0.57    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 1.57/0.57    introduced(choice_axiom,[])).
% 1.57/0.57  fof(f55,plain,(
% 1.57/0.57    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.57/0.57    inference(rectify,[],[f54])).
% 1.57/0.57  fof(f54,plain,(
% 1.57/0.57    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.57/0.57    inference(nnf_transformation,[],[f1])).
% 1.57/0.57  fof(f1,axiom,(
% 1.57/0.57    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.57/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.57/0.57  fof(f261,plain,(
% 1.57/0.57    r2_hidden(sK3(sK1),u1_struct_0(sK0)) | ~spl5_19),
% 1.57/0.57    inference(avatar_component_clause,[],[f259])).
% 1.57/0.57  fof(f448,plain,(
% 1.57/0.57    spl5_39 | ~spl5_19),
% 1.57/0.57    inference(avatar_split_clause,[],[f437,f259,f445])).
% 1.57/0.57  fof(f437,plain,(
% 1.57/0.57    m1_subset_1(sK3(sK1),u1_struct_0(sK0)) | ~spl5_19),
% 1.57/0.57    inference(unit_resulting_resolution,[],[f261,f89])).
% 1.57/0.57  fof(f89,plain,(
% 1.57/0.57    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f41])).
% 1.57/0.57  fof(f41,plain,(
% 1.57/0.57    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.57/0.57    inference(ennf_transformation,[],[f5])).
% 1.57/0.57  fof(f5,axiom,(
% 1.57/0.57    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.57/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 1.57/0.57  fof(f434,plain,(
% 1.57/0.57    spl5_38 | spl5_16 | ~spl5_25 | ~spl5_26 | ~spl5_29 | ~spl5_31),
% 1.57/0.57    inference(avatar_split_clause,[],[f433,f362,f353,f317,f312,f231,f426])).
% 1.57/0.57  fof(f231,plain,(
% 1.57/0.57    spl5_16 <=> v2_struct_0(sK2(sK0,sK1))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 1.57/0.57  fof(f312,plain,(
% 1.57/0.57    spl5_25 <=> l1_pre_topc(sK2(sK0,sK1))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 1.57/0.57  fof(f317,plain,(
% 1.57/0.57    spl5_26 <=> v2_tdlat_3(sK2(sK0,sK1))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 1.57/0.57  fof(f353,plain,(
% 1.57/0.57    spl5_29 <=> v2_pre_topc(sK2(sK0,sK1))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).
% 1.57/0.57  fof(f362,plain,(
% 1.57/0.57    spl5_31 <=> v1_tdlat_3(sK2(sK0,sK1))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).
% 1.57/0.57  fof(f433,plain,(
% 1.57/0.57    v7_struct_0(sK2(sK0,sK1)) | (spl5_16 | ~spl5_25 | ~spl5_26 | ~spl5_29 | ~spl5_31)),
% 1.57/0.57    inference(subsumption_resolution,[],[f432,f314])).
% 1.57/0.57  fof(f314,plain,(
% 1.57/0.57    l1_pre_topc(sK2(sK0,sK1)) | ~spl5_25),
% 1.57/0.57    inference(avatar_component_clause,[],[f312])).
% 1.57/0.57  fof(f432,plain,(
% 1.57/0.57    v7_struct_0(sK2(sK0,sK1)) | ~l1_pre_topc(sK2(sK0,sK1)) | (spl5_16 | ~spl5_26 | ~spl5_29 | ~spl5_31)),
% 1.57/0.57    inference(subsumption_resolution,[],[f431,f233])).
% 1.57/0.57  fof(f233,plain,(
% 1.57/0.57    ~v2_struct_0(sK2(sK0,sK1)) | spl5_16),
% 1.57/0.57    inference(avatar_component_clause,[],[f231])).
% 1.57/0.57  fof(f431,plain,(
% 1.57/0.57    v7_struct_0(sK2(sK0,sK1)) | v2_struct_0(sK2(sK0,sK1)) | ~l1_pre_topc(sK2(sK0,sK1)) | (~spl5_26 | ~spl5_29 | ~spl5_31)),
% 1.57/0.57    inference(subsumption_resolution,[],[f430,f354])).
% 1.57/0.57  fof(f354,plain,(
% 1.57/0.57    v2_pre_topc(sK2(sK0,sK1)) | ~spl5_29),
% 1.57/0.57    inference(avatar_component_clause,[],[f353])).
% 1.57/0.57  fof(f430,plain,(
% 1.57/0.57    v7_struct_0(sK2(sK0,sK1)) | ~v2_pre_topc(sK2(sK0,sK1)) | v2_struct_0(sK2(sK0,sK1)) | ~l1_pre_topc(sK2(sK0,sK1)) | (~spl5_26 | ~spl5_31)),
% 1.57/0.57    inference(subsumption_resolution,[],[f424,f319])).
% 1.57/0.57  fof(f319,plain,(
% 1.57/0.57    v2_tdlat_3(sK2(sK0,sK1)) | ~spl5_26),
% 1.57/0.57    inference(avatar_component_clause,[],[f317])).
% 1.57/0.57  fof(f424,plain,(
% 1.57/0.57    v7_struct_0(sK2(sK0,sK1)) | ~v2_tdlat_3(sK2(sK0,sK1)) | ~v2_pre_topc(sK2(sK0,sK1)) | v2_struct_0(sK2(sK0,sK1)) | ~l1_pre_topc(sK2(sK0,sK1)) | ~spl5_31),
% 1.57/0.57    inference(resolution,[],[f363,f76])).
% 1.57/0.57  fof(f76,plain,(
% 1.57/0.57    ( ! [X0] : (v7_struct_0(X0) | ~v2_tdlat_3(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f29])).
% 1.57/0.57  fof(f29,plain,(
% 1.57/0.57    ! [X0] : ((v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) | ~v2_tdlat_3(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.57/0.57    inference(flattening,[],[f28])).
% 1.57/0.57  fof(f28,plain,(
% 1.57/0.57    ! [X0] : (((v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) | (~v2_tdlat_3(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.57/0.57    inference(ennf_transformation,[],[f12])).
% 1.57/0.57  fof(f12,axiom,(
% 1.57/0.57    ! [X0] : (l1_pre_topc(X0) => ((v2_tdlat_3(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0))))),
% 1.57/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_1)).
% 1.57/0.57  fof(f363,plain,(
% 1.57/0.57    v1_tdlat_3(sK2(sK0,sK1)) | ~spl5_31),
% 1.57/0.57    inference(avatar_component_clause,[],[f362])).
% 1.57/0.57  fof(f418,plain,(
% 1.57/0.57    spl5_29 | ~spl5_25 | ~spl5_26),
% 1.57/0.57    inference(avatar_split_clause,[],[f414,f317,f312,f353])).
% 1.57/0.57  fof(f414,plain,(
% 1.57/0.57    v2_pre_topc(sK2(sK0,sK1)) | (~spl5_25 | ~spl5_26)),
% 1.57/0.57    inference(unit_resulting_resolution,[],[f314,f319,f74])).
% 1.57/0.57  fof(f74,plain,(
% 1.57/0.57    ( ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f27])).
% 1.57/0.57  fof(f27,plain,(
% 1.57/0.57    ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 1.57/0.57    inference(flattening,[],[f26])).
% 1.57/0.57  fof(f26,plain,(
% 1.57/0.57    ! [X0] : ((v2_pre_topc(X0) | ~v2_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 1.57/0.57    inference(ennf_transformation,[],[f11])).
% 1.57/0.57  fof(f11,axiom,(
% 1.57/0.57    ! [X0] : (l1_pre_topc(X0) => (v2_tdlat_3(X0) => v2_pre_topc(X0)))),
% 1.57/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tdlat_3)).
% 1.57/0.57  fof(f413,plain,(
% 1.57/0.57    spl5_37 | ~spl5_25),
% 1.57/0.57    inference(avatar_split_clause,[],[f397,f312,f410])).
% 1.57/0.57  fof(f397,plain,(
% 1.57/0.57    l1_struct_0(sK2(sK0,sK1)) | ~spl5_25),
% 1.57/0.57    inference(unit_resulting_resolution,[],[f314,f73])).
% 1.57/0.57  fof(f73,plain,(
% 1.57/0.57    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f25])).
% 1.57/0.57  fof(f25,plain,(
% 1.57/0.57    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.57/0.57    inference(ennf_transformation,[],[f7])).
% 1.57/0.57  fof(f7,axiom,(
% 1.57/0.57    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.57/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.57/0.57  fof(f396,plain,(
% 1.57/0.57    spl5_36 | spl5_4 | ~spl5_11),
% 1.57/0.57    inference(avatar_split_clause,[],[f395,f197,f115,f391])).
% 1.57/0.57  fof(f391,plain,(
% 1.57/0.57    spl5_36 <=> k1_tarski(sK3(sK1)) = k6_domain_1(sK1,sK3(sK1))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).
% 1.57/0.57  fof(f197,plain,(
% 1.57/0.57    spl5_11 <=> m1_subset_1(sK3(sK1),sK1)),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 1.57/0.57  fof(f395,plain,(
% 1.57/0.57    k1_tarski(sK3(sK1)) = k6_domain_1(sK1,sK3(sK1)) | (spl5_4 | ~spl5_11)),
% 1.57/0.57    inference(subsumption_resolution,[],[f389,f117])).
% 1.57/0.57  fof(f389,plain,(
% 1.57/0.57    k1_tarski(sK3(sK1)) = k6_domain_1(sK1,sK3(sK1)) | v1_xboole_0(sK1) | ~spl5_11),
% 1.57/0.57    inference(resolution,[],[f199,f91])).
% 1.57/0.57  fof(f199,plain,(
% 1.57/0.57    m1_subset_1(sK3(sK1),sK1) | ~spl5_11),
% 1.57/0.57    inference(avatar_component_clause,[],[f197])).
% 1.57/0.57  fof(f387,plain,(
% 1.57/0.57    spl5_31 | spl5_35 | ~spl5_14 | spl5_16),
% 1.57/0.57    inference(avatar_split_clause,[],[f386,f231,f221,f383,f362])).
% 1.57/0.57  fof(f386,plain,(
% 1.57/0.57    ( ! [X10] : (~v2_tex_2(sK1,X10) | v1_tdlat_3(sK2(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X10))) | ~m1_pre_topc(sK2(sK0,sK1),X10) | ~l1_pre_topc(X10) | v2_struct_0(X10)) ) | (~spl5_14 | spl5_16)),
% 1.57/0.57    inference(subsumption_resolution,[],[f340,f233])).
% 1.57/0.57  fof(f340,plain,(
% 1.57/0.57    ( ! [X10] : (~v2_tex_2(sK1,X10) | v1_tdlat_3(sK2(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X10))) | ~m1_pre_topc(sK2(sK0,sK1),X10) | v2_struct_0(sK2(sK0,sK1)) | ~l1_pre_topc(X10) | v2_struct_0(X10)) ) | ~spl5_14),
% 1.57/0.57    inference(superposition,[],[f98,f223])).
% 1.57/0.57  fof(f98,plain,(
% 1.57/0.57    ( ! [X0,X1] : (v1_tdlat_3(X1) | ~v2_tex_2(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.57/0.57    inference(equality_resolution,[],[f82])).
% 1.57/0.57  fof(f82,plain,(
% 1.57/0.57    ( ! [X2,X0,X1] : (v1_tdlat_3(X1) | ~v2_tex_2(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f53])).
% 1.57/0.57  fof(f53,plain,(
% 1.57/0.57    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) | ~v1_tdlat_3(X1)) & (v1_tdlat_3(X1) | ~v2_tex_2(X2,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.57/0.57    inference(nnf_transformation,[],[f34])).
% 1.57/0.57  fof(f34,plain,(
% 1.57/0.57    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.57/0.57    inference(flattening,[],[f33])).
% 1.57/0.57  fof(f33,plain,(
% 1.57/0.57    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.57/0.57    inference(ennf_transformation,[],[f16])).
% 1.57/0.57  fof(f16,axiom,(
% 1.57/0.57    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => (v2_tex_2(X2,X0) <=> v1_tdlat_3(X1))))))),
% 1.57/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_tex_2)).
% 1.57/0.57  fof(f327,plain,(
% 1.57/0.57    spl5_25 | ~spl5_5 | ~spl5_15),
% 1.57/0.57    inference(avatar_split_clause,[],[f326,f226,f120,f312])).
% 1.57/0.57  fof(f326,plain,(
% 1.57/0.57    l1_pre_topc(sK2(sK0,sK1)) | (~spl5_5 | ~spl5_15)),
% 1.57/0.57    inference(subsumption_resolution,[],[f310,f122])).
% 1.57/0.57  fof(f310,plain,(
% 1.57/0.57    l1_pre_topc(sK2(sK0,sK1)) | ~l1_pre_topc(sK0) | ~spl5_15),
% 1.57/0.57    inference(resolution,[],[f228,f78])).
% 1.57/0.57  fof(f78,plain,(
% 1.57/0.57    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f30])).
% 1.57/0.57  fof(f30,plain,(
% 1.57/0.57    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.57/0.57    inference(ennf_transformation,[],[f8])).
% 1.57/0.57  fof(f8,axiom,(
% 1.57/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.57/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.57/0.57  fof(f325,plain,(
% 1.57/0.57    spl5_26 | ~spl5_5 | ~spl5_6 | ~spl5_7 | spl5_8 | ~spl5_15),
% 1.57/0.57    inference(avatar_split_clause,[],[f324,f226,f135,f130,f125,f120,f317])).
% 1.57/0.57  fof(f125,plain,(
% 1.57/0.57    spl5_6 <=> v2_tdlat_3(sK0)),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.57/0.57  fof(f324,plain,(
% 1.57/0.57    v2_tdlat_3(sK2(sK0,sK1)) | (~spl5_5 | ~spl5_6 | ~spl5_7 | spl5_8 | ~spl5_15)),
% 1.57/0.57    inference(subsumption_resolution,[],[f323,f137])).
% 1.57/0.57  fof(f323,plain,(
% 1.57/0.57    v2_tdlat_3(sK2(sK0,sK1)) | v2_struct_0(sK0) | (~spl5_5 | ~spl5_6 | ~spl5_7 | ~spl5_15)),
% 1.57/0.57    inference(subsumption_resolution,[],[f322,f132])).
% 1.57/0.57  fof(f322,plain,(
% 1.57/0.57    v2_tdlat_3(sK2(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_5 | ~spl5_6 | ~spl5_15)),
% 1.57/0.57    inference(subsumption_resolution,[],[f321,f127])).
% 1.57/0.57  fof(f127,plain,(
% 1.57/0.57    v2_tdlat_3(sK0) | ~spl5_6),
% 1.57/0.57    inference(avatar_component_clause,[],[f125])).
% 1.57/0.58  fof(f321,plain,(
% 1.57/0.58    v2_tdlat_3(sK2(sK0,sK1)) | ~v2_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_5 | ~spl5_15)),
% 1.57/0.58    inference(subsumption_resolution,[],[f307,f122])).
% 1.57/0.58  fof(f307,plain,(
% 1.57/0.58    v2_tdlat_3(sK2(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_15),
% 1.57/0.58    inference(resolution,[],[f228,f84])).
% 1.57/0.58  fof(f84,plain,(
% 1.57/0.58    ( ! [X0,X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.57/0.58    inference(cnf_transformation,[],[f36])).
% 1.57/0.58  fof(f36,plain,(
% 1.57/0.58    ! [X0] : (! [X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.57/0.58    inference(flattening,[],[f35])).
% 1.57/0.58  fof(f35,plain,(
% 1.57/0.58    ! [X0] : (! [X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.57/0.58    inference(ennf_transformation,[],[f13])).
% 1.57/0.58  fof(f13,axiom,(
% 1.57/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_tdlat_3(X1)))),
% 1.57/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_tdlat_3)).
% 1.57/0.58  fof(f262,plain,(
% 1.57/0.58    spl5_19 | ~spl5_9 | ~spl5_13),
% 1.57/0.58    inference(avatar_split_clause,[],[f254,f216,f149,f259])).
% 1.57/0.58  fof(f149,plain,(
% 1.57/0.58    spl5_9 <=> r2_hidden(sK3(sK1),sK1)),
% 1.57/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 1.57/0.58  fof(f216,plain,(
% 1.57/0.58    spl5_13 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 1.57/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 1.57/0.58  fof(f254,plain,(
% 1.57/0.58    r2_hidden(sK3(sK1),u1_struct_0(sK0)) | (~spl5_9 | ~spl5_13)),
% 1.57/0.58    inference(unit_resulting_resolution,[],[f151,f218,f92])).
% 1.57/0.58  fof(f92,plain,(
% 1.57/0.58    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.57/0.58    inference(cnf_transformation,[],[f61])).
% 1.57/0.58  fof(f61,plain,(
% 1.57/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.57/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f59,f60])).
% 1.57/0.58  fof(f60,plain,(
% 1.57/0.58    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.57/0.58    introduced(choice_axiom,[])).
% 1.57/0.58  fof(f59,plain,(
% 1.57/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.57/0.58    inference(rectify,[],[f58])).
% 1.57/0.58  fof(f58,plain,(
% 1.57/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.57/0.58    inference(nnf_transformation,[],[f45])).
% 1.57/0.58  fof(f45,plain,(
% 1.57/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.57/0.58    inference(ennf_transformation,[],[f2])).
% 1.57/0.58  fof(f2,axiom,(
% 1.57/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.57/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.57/0.58  fof(f218,plain,(
% 1.57/0.58    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl5_13),
% 1.57/0.58    inference(avatar_component_clause,[],[f216])).
% 1.57/0.58  fof(f151,plain,(
% 1.57/0.58    r2_hidden(sK3(sK1),sK1) | ~spl5_9),
% 1.57/0.58    inference(avatar_component_clause,[],[f149])).
% 1.57/0.58  fof(f243,plain,(
% 1.57/0.58    spl5_13 | ~spl5_3),
% 1.57/0.58    inference(avatar_split_clause,[],[f213,f110,f216])).
% 1.57/0.58  fof(f213,plain,(
% 1.57/0.58    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl5_3),
% 1.57/0.58    inference(resolution,[],[f112,f95])).
% 1.57/0.58  fof(f242,plain,(
% 1.57/0.58    spl5_14 | ~spl5_3 | spl5_4 | ~spl5_5 | spl5_8),
% 1.57/0.58    inference(avatar_split_clause,[],[f241,f135,f120,f115,f110,f221])).
% 1.57/0.58  fof(f241,plain,(
% 1.57/0.58    sK1 = u1_struct_0(sK2(sK0,sK1)) | (~spl5_3 | spl5_4 | ~spl5_5 | spl5_8)),
% 1.57/0.58    inference(subsumption_resolution,[],[f240,f137])).
% 1.57/0.58  fof(f240,plain,(
% 1.57/0.58    sK1 = u1_struct_0(sK2(sK0,sK1)) | v2_struct_0(sK0) | (~spl5_3 | spl5_4 | ~spl5_5)),
% 1.57/0.58    inference(subsumption_resolution,[],[f239,f122])).
% 1.57/0.58  fof(f239,plain,(
% 1.57/0.58    sK1 = u1_struct_0(sK2(sK0,sK1)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_3 | spl5_4)),
% 1.57/0.58    inference(subsumption_resolution,[],[f212,f117])).
% 1.57/0.58  fof(f212,plain,(
% 1.57/0.58    sK1 = u1_struct_0(sK2(sK0,sK1)) | v1_xboole_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_3),
% 1.57/0.58    inference(resolution,[],[f112,f81])).
% 1.57/0.58  fof(f81,plain,(
% 1.57/0.58    ( ! [X0,X1] : (u1_struct_0(sK2(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.57/0.58    inference(cnf_transformation,[],[f52])).
% 1.57/0.58  fof(f52,plain,(
% 1.57/0.58    ! [X0] : (! [X1] : ((u1_struct_0(sK2(X0,X1)) = X1 & m1_pre_topc(sK2(X0,X1),X0) & ~v2_struct_0(sK2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.57/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f32,f51])).
% 1.57/0.58  fof(f51,plain,(
% 1.57/0.58    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (u1_struct_0(sK2(X0,X1)) = X1 & m1_pre_topc(sK2(X0,X1),X0) & ~v2_struct_0(sK2(X0,X1))))),
% 1.57/0.58    introduced(choice_axiom,[])).
% 1.57/0.58  fof(f32,plain,(
% 1.57/0.58    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.57/0.58    inference(flattening,[],[f31])).
% 1.57/0.58  fof(f31,plain,(
% 1.57/0.58    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.57/0.58    inference(ennf_transformation,[],[f20])).
% 1.57/0.58  fof(f20,plain,(
% 1.57/0.58    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2))))),
% 1.57/0.58    inference(pure_predicate_removal,[],[f14])).
% 1.57/0.58  fof(f14,axiom,(
% 1.57/0.58    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2))))),
% 1.57/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_tsep_1)).
% 1.57/0.58  fof(f238,plain,(
% 1.57/0.58    ~spl5_16 | ~spl5_3 | spl5_4 | ~spl5_5 | spl5_8),
% 1.57/0.58    inference(avatar_split_clause,[],[f237,f135,f120,f115,f110,f231])).
% 1.57/0.58  fof(f237,plain,(
% 1.57/0.58    ~v2_struct_0(sK2(sK0,sK1)) | (~spl5_3 | spl5_4 | ~spl5_5 | spl5_8)),
% 1.57/0.58    inference(subsumption_resolution,[],[f236,f137])).
% 1.57/0.58  fof(f236,plain,(
% 1.57/0.58    ~v2_struct_0(sK2(sK0,sK1)) | v2_struct_0(sK0) | (~spl5_3 | spl5_4 | ~spl5_5)),
% 1.57/0.58    inference(subsumption_resolution,[],[f235,f122])).
% 1.57/0.58  fof(f235,plain,(
% 1.57/0.58    ~v2_struct_0(sK2(sK0,sK1)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_3 | spl5_4)),
% 1.57/0.58    inference(subsumption_resolution,[],[f210,f117])).
% 1.57/0.58  fof(f210,plain,(
% 1.57/0.58    ~v2_struct_0(sK2(sK0,sK1)) | v1_xboole_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_3),
% 1.57/0.58    inference(resolution,[],[f112,f79])).
% 1.57/0.58  fof(f79,plain,(
% 1.57/0.58    ( ! [X0,X1] : (~v2_struct_0(sK2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.57/0.58    inference(cnf_transformation,[],[f52])).
% 1.57/0.58  fof(f229,plain,(
% 1.57/0.58    spl5_15 | ~spl5_3 | spl5_4 | ~spl5_5 | spl5_8),
% 1.57/0.58    inference(avatar_split_clause,[],[f207,f135,f120,f115,f110,f226])).
% 1.57/0.58  fof(f207,plain,(
% 1.57/0.58    m1_pre_topc(sK2(sK0,sK1),sK0) | (~spl5_3 | spl5_4 | ~spl5_5 | spl5_8)),
% 1.57/0.58    inference(unit_resulting_resolution,[],[f137,f122,f117,f112,f80])).
% 1.57/0.58  fof(f80,plain,(
% 1.57/0.58    ( ! [X0,X1] : (m1_pre_topc(sK2(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.57/0.58    inference(cnf_transformation,[],[f52])).
% 1.57/0.58  fof(f205,plain,(
% 1.57/0.58    spl5_12 | ~spl5_9),
% 1.57/0.58    inference(avatar_split_clause,[],[f189,f149,f202])).
% 1.57/0.58  fof(f189,plain,(
% 1.57/0.58    m1_subset_1(k1_tarski(sK3(sK1)),k1_zfmisc_1(sK1)) | ~spl5_9),
% 1.57/0.58    inference(unit_resulting_resolution,[],[f151,f90])).
% 1.57/0.58  fof(f90,plain,(
% 1.57/0.58    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 1.57/0.58    inference(cnf_transformation,[],[f42])).
% 1.57/0.58  fof(f42,plain,(
% 1.57/0.58    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 1.57/0.58    inference(ennf_transformation,[],[f4])).
% 1.57/0.58  fof(f4,axiom,(
% 1.57/0.58    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 1.57/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).
% 1.57/0.58  fof(f200,plain,(
% 1.57/0.58    spl5_11 | ~spl5_9),
% 1.57/0.58    inference(avatar_split_clause,[],[f190,f149,f197])).
% 1.57/0.58  fof(f190,plain,(
% 1.57/0.58    m1_subset_1(sK3(sK1),sK1) | ~spl5_9),
% 1.57/0.58    inference(unit_resulting_resolution,[],[f151,f89])).
% 1.57/0.58  fof(f152,plain,(
% 1.57/0.58    spl5_9 | spl5_4),
% 1.57/0.58    inference(avatar_split_clause,[],[f140,f115,f149])).
% 1.57/0.58  fof(f140,plain,(
% 1.57/0.58    r2_hidden(sK3(sK1),sK1) | spl5_4),
% 1.57/0.58    inference(unit_resulting_resolution,[],[f117,f88])).
% 1.57/0.58  fof(f88,plain,(
% 1.57/0.58    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) )),
% 1.57/0.58    inference(cnf_transformation,[],[f57])).
% 1.57/0.58  fof(f138,plain,(
% 1.57/0.58    ~spl5_8),
% 1.57/0.58    inference(avatar_split_clause,[],[f63,f135])).
% 1.57/0.58  fof(f63,plain,(
% 1.57/0.58    ~v2_struct_0(sK0)),
% 1.57/0.58    inference(cnf_transformation,[],[f50])).
% 1.57/0.58  fof(f50,plain,(
% 1.57/0.58    ((~v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0)) & (v1_zfmisc_1(sK1) | v2_tex_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(sK1)) & l1_pre_topc(sK0) & v2_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.57/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f47,f49,f48])).
% 1.57/0.58  fof(f48,plain,(
% 1.57/0.58    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,sK0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK0) & v2_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.57/0.58    introduced(choice_axiom,[])).
% 1.57/0.58  fof(f49,plain,(
% 1.57/0.58    ? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,sK0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(X1)) => ((~v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0)) & (v1_zfmisc_1(sK1) | v2_tex_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(sK1))),
% 1.57/0.58    introduced(choice_axiom,[])).
% 1.57/0.58  fof(f47,plain,(
% 1.57/0.58    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.57/0.58    inference(flattening,[],[f46])).
% 1.57/0.58  fof(f46,plain,(
% 1.57/0.58    ? [X0] : (? [X1] : (((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.57/0.58    inference(nnf_transformation,[],[f22])).
% 1.57/0.58  fof(f22,plain,(
% 1.57/0.58    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.57/0.58    inference(flattening,[],[f21])).
% 1.57/0.58  fof(f21,plain,(
% 1.57/0.58    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.57/0.58    inference(ennf_transformation,[],[f19])).
% 1.57/0.58  fof(f19,negated_conjecture,(
% 1.57/0.58    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 1.57/0.58    inference(negated_conjecture,[],[f18])).
% 1.57/0.58  fof(f18,conjecture,(
% 1.57/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 1.57/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tex_2)).
% 1.57/0.58  fof(f133,plain,(
% 1.57/0.58    spl5_7),
% 1.57/0.58    inference(avatar_split_clause,[],[f64,f130])).
% 1.57/0.58  fof(f64,plain,(
% 1.57/0.58    v2_pre_topc(sK0)),
% 1.57/0.58    inference(cnf_transformation,[],[f50])).
% 1.57/0.58  fof(f128,plain,(
% 1.57/0.58    spl5_6),
% 1.57/0.58    inference(avatar_split_clause,[],[f65,f125])).
% 1.57/0.58  fof(f65,plain,(
% 1.57/0.58    v2_tdlat_3(sK0)),
% 1.57/0.58    inference(cnf_transformation,[],[f50])).
% 1.57/0.58  fof(f123,plain,(
% 1.57/0.58    spl5_5),
% 1.57/0.58    inference(avatar_split_clause,[],[f66,f120])).
% 1.71/0.58  fof(f66,plain,(
% 1.71/0.58    l1_pre_topc(sK0)),
% 1.71/0.58    inference(cnf_transformation,[],[f50])).
% 1.71/0.58  fof(f118,plain,(
% 1.71/0.58    ~spl5_4),
% 1.71/0.58    inference(avatar_split_clause,[],[f67,f115])).
% 1.71/0.58  fof(f67,plain,(
% 1.71/0.58    ~v1_xboole_0(sK1)),
% 1.71/0.58    inference(cnf_transformation,[],[f50])).
% 1.71/0.58  fof(f113,plain,(
% 1.71/0.58    spl5_3),
% 1.71/0.58    inference(avatar_split_clause,[],[f68,f110])).
% 1.71/0.58  fof(f68,plain,(
% 1.71/0.58    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.71/0.58    inference(cnf_transformation,[],[f50])).
% 1.71/0.58  fof(f108,plain,(
% 1.71/0.58    spl5_1 | spl5_2),
% 1.71/0.58    inference(avatar_split_clause,[],[f69,f104,f100])).
% 1.71/0.58  fof(f69,plain,(
% 1.71/0.58    v1_zfmisc_1(sK1) | v2_tex_2(sK1,sK0)),
% 1.71/0.58    inference(cnf_transformation,[],[f50])).
% 1.71/0.58  fof(f107,plain,(
% 1.71/0.58    ~spl5_1 | ~spl5_2),
% 1.71/0.58    inference(avatar_split_clause,[],[f70,f104,f100])).
% 1.71/0.58  fof(f70,plain,(
% 1.71/0.58    ~v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0)),
% 1.71/0.58    inference(cnf_transformation,[],[f50])).
% 1.71/0.58  % SZS output end Proof for theBenchmark
% 1.71/0.58  % (18211)------------------------------
% 1.71/0.58  % (18211)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.71/0.58  % (18211)Termination reason: Refutation
% 1.71/0.58  
% 1.71/0.58  % (18211)Memory used [KB]: 6652
% 1.71/0.58  % (18211)Time elapsed: 0.160 s
% 1.71/0.58  % (18211)------------------------------
% 1.71/0.58  % (18211)------------------------------
% 1.71/0.58  % (18185)Success in time 0.222 s
%------------------------------------------------------------------------------
