%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:07 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 311 expanded)
%              Number of leaves         :   37 ( 136 expanded)
%              Depth                    :    8
%              Number of atoms          :  543 (1091 expanded)
%              Number of equality atoms :    9 (  15 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f363,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f81,f86,f91,f96,f103,f108,f143,f152,f159,f164,f172,f195,f200,f213,f234,f240,f272,f278,f289,f298,f304,f312,f315,f319,f362])).

fof(f362,plain,
    ( ~ spl6_23
    | spl6_22 ),
    inference(avatar_split_clause,[],[f361,f210,f219])).

fof(f219,plain,
    ( spl6_23
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f210,plain,
    ( spl6_22
  <=> m1_subset_1(k1_setfam_1(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f361,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_22 ),
    inference(duplicate_literal_removal,[],[f354])).

fof(f354,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_22 ),
    inference(resolution,[],[f330,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f330,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k9_subset_1(X0,sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(X0)) )
    | spl6_22 ),
    inference(superposition,[],[f212,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f56,f48])).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f212,plain,
    ( ~ m1_subset_1(k1_setfam_1(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_22 ),
    inference(avatar_component_clause,[],[f210])).

fof(f319,plain,
    ( ~ spl6_15
    | ~ spl6_33 ),
    inference(avatar_contradiction_clause,[],[f317])).

fof(f317,plain,
    ( $false
    | ~ spl6_15
    | ~ spl6_33 ),
    inference(unit_resulting_resolution,[],[f163,f310,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f310,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl6_33 ),
    inference(avatar_component_clause,[],[f309])).

fof(f309,plain,
    ( spl6_33
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f163,plain,
    ( v1_xboole_0(sK2)
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f161])).

fof(f161,plain,
    ( spl6_15
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f315,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_19
    | ~ spl6_25
    | spl6_33 ),
    inference(avatar_contradiction_clause,[],[f313])).

fof(f313,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_19
    | ~ spl6_25
    | spl6_33 ),
    inference(unit_resulting_resolution,[],[f85,f80,f90,f199,f95,f228,f311,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_connsp_2(X1,X0,X2)
      | r2_hidden(X2,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,X1)
              | ~ m1_connsp_2(X1,X0,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,X1)
              | ~ m1_connsp_2(X1,X0,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( m1_connsp_2(X1,X0,X2)
               => r2_hidden(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_connsp_2)).

fof(f311,plain,
    ( ~ r2_hidden(sK1,sK2)
    | spl6_33 ),
    inference(avatar_component_clause,[],[f309])).

fof(f228,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f227])).

fof(f227,plain,
    ( spl6_25
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f95,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl6_4
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f199,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f197])).

fof(f197,plain,
    ( spl6_19
  <=> m1_connsp_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f90,plain,
    ( l1_pre_topc(sK0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl6_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f80,plain,
    ( ~ v2_struct_0(sK0)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl6_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f85,plain,
    ( v2_pre_topc(sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl6_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f312,plain,
    ( ~ spl6_33
    | ~ spl6_32
    | spl6_21 ),
    inference(avatar_split_clause,[],[f306,f206,f275,f309])).

fof(f275,plain,
    ( spl6_32
  <=> r2_hidden(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f206,plain,
    ( spl6_21
  <=> r2_hidden(sK1,k1_setfam_1(k2_tarski(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f306,plain,
    ( ~ r2_hidden(sK1,sK3)
    | ~ r2_hidden(sK1,sK2)
    | spl6_21 ),
    inference(resolution,[],[f208,f74])).

fof(f74,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k1_setfam_1(k2_tarski(X0,X1)))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k1_setfam_1(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f64,f48])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f208,plain,
    ( ~ r2_hidden(sK1,k1_setfam_1(k2_tarski(sK2,sK3)))
    | spl6_21 ),
    inference(avatar_component_clause,[],[f206])).

fof(f304,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_16
    | ~ spl6_25
    | spl6_26 ),
    inference(avatar_contradiction_clause,[],[f299])).

fof(f299,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_16
    | ~ spl6_25
    | spl6_26 ),
    inference(unit_resulting_resolution,[],[f80,f90,f85,f233,f95,f171,f228,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(X2,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
              <=> ( v3_pre_topc(X2,X0)
                  & r2_hidden(X1,X2) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
              <=> ( v3_pre_topc(X2,X0)
                  & r2_hidden(X1,X2) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
              <=> ( v3_pre_topc(X2,X0)
                  & r2_hidden(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_yellow_6)).

fof(f171,plain,
    ( r2_hidden(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f169])).

fof(f169,plain,
    ( spl6_16
  <=> r2_hidden(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f233,plain,
    ( ~ v3_pre_topc(sK2,sK0)
    | spl6_26 ),
    inference(avatar_component_clause,[],[f231])).

fof(f231,plain,
    ( spl6_26
  <=> v3_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f298,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_19
    | spl6_25 ),
    inference(avatar_contradiction_clause,[],[f293])).

fof(f293,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_19
    | spl6_25 ),
    inference(unit_resulting_resolution,[],[f80,f90,f85,f199,f95,f229,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_connsp_2(X2,X0,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).

fof(f229,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_25 ),
    inference(avatar_component_clause,[],[f227])).

fof(f289,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_14
    | ~ spl6_23
    | spl6_24 ),
    inference(avatar_contradiction_clause,[],[f285])).

fof(f285,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_14
    | ~ spl6_23
    | spl6_24 ),
    inference(unit_resulting_resolution,[],[f80,f90,f85,f225,f95,f220,f158,f42])).

fof(f158,plain,
    ( r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl6_14
  <=> r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f220,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f219])).

fof(f225,plain,
    ( ~ v3_pre_topc(sK3,sK0)
    | spl6_24 ),
    inference(avatar_component_clause,[],[f223])).

fof(f223,plain,
    ( spl6_24
  <=> v3_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f278,plain,
    ( ~ spl6_4
    | spl6_32
    | ~ spl6_18
    | ~ spl6_31 ),
    inference(avatar_split_clause,[],[f273,f270,f192,f275,f93])).

fof(f192,plain,
    ( spl6_18
  <=> m1_connsp_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f270,plain,
    ( spl6_31
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,sK3)
        | ~ m1_connsp_2(sK3,sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f273,plain,
    ( r2_hidden(sK1,sK3)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl6_18
    | ~ spl6_31 ),
    inference(resolution,[],[f271,f194])).

fof(f194,plain,
    ( m1_connsp_2(sK3,sK0,sK1)
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f192])).

fof(f271,plain,
    ( ! [X0] :
        ( ~ m1_connsp_2(sK3,sK0,X0)
        | r2_hidden(X0,sK3)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl6_31 ),
    inference(avatar_component_clause,[],[f270])).

fof(f272,plain,
    ( spl6_31
    | spl6_1
    | ~ spl6_3
    | ~ spl6_2
    | ~ spl6_23 ),
    inference(avatar_split_clause,[],[f241,f219,f83,f88,f78,f270])).

fof(f241,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_connsp_2(sK3,sK0,X0)
        | r2_hidden(X0,sK3) )
    | ~ spl6_23 ),
    inference(resolution,[],[f220,f45])).

fof(f240,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_18
    | spl6_23 ),
    inference(avatar_contradiction_clause,[],[f235])).

fof(f235,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_18
    | spl6_23 ),
    inference(unit_resulting_resolution,[],[f80,f90,f85,f194,f95,f221,f54])).

fof(f221,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_23 ),
    inference(avatar_component_clause,[],[f219])).

fof(f234,plain,
    ( ~ spl6_2
    | ~ spl6_23
    | ~ spl6_24
    | ~ spl6_25
    | ~ spl6_26
    | ~ spl6_3
    | spl6_20 ),
    inference(avatar_split_clause,[],[f214,f202,f88,f231,f227,f223,f219,f83])).

fof(f202,plain,
    ( spl6_20
  <=> v3_pre_topc(k1_setfam_1(k2_tarski(sK2,sK3)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f214,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v3_pre_topc(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(sK3,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | spl6_20 ),
    inference(resolution,[],[f204,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(k1_setfam_1(k2_tarski(X1,X2)),X0)
      | ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f57,f48])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(k3_xboole_0(X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k3_xboole_0(X1,X2),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_tops_1)).

fof(f204,plain,
    ( ~ v3_pre_topc(k1_setfam_1(k2_tarski(sK2,sK3)),sK0)
    | spl6_20 ),
    inference(avatar_component_clause,[],[f202])).

fof(f213,plain,
    ( spl6_1
    | ~ spl6_20
    | ~ spl6_21
    | ~ spl6_22
    | ~ spl6_4
    | ~ spl6_3
    | ~ spl6_2
    | spl6_13 ),
    inference(avatar_split_clause,[],[f153,f149,f83,f88,f93,f210,f206,f202,f78])).

fof(f149,plain,
    ( spl6_13
  <=> r2_hidden(k1_setfam_1(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f153,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k1_setfam_1(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1,k1_setfam_1(k2_tarski(sK2,sK3)))
    | ~ v3_pre_topc(k1_setfam_1(k2_tarski(sK2,sK3)),sK0)
    | v2_struct_0(sK0)
    | spl6_13 ),
    inference(resolution,[],[f151,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,X2)
      | ~ v3_pre_topc(X2,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f151,plain,
    ( ~ r2_hidden(k1_setfam_1(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1)))
    | spl6_13 ),
    inference(avatar_component_clause,[],[f149])).

fof(f200,plain,
    ( spl6_19
    | spl6_1
    | ~ spl6_4
    | ~ spl6_3
    | ~ spl6_2
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f121,f105,f83,f88,f93,f78,f197])).

fof(f105,plain,
    ( spl6_6
  <=> m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f121,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | m1_connsp_2(sK2,sK0,sK1)
    | ~ spl6_6 ),
    inference(resolution,[],[f107,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | m1_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
             => m1_connsp_2(X2,X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_waybel_9)).

fof(f107,plain,
    ( m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f105])).

fof(f195,plain,
    ( spl6_18
    | spl6_1
    | ~ spl6_4
    | ~ spl6_3
    | ~ spl6_2
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f118,f100,f83,f88,f93,f78,f192])).

fof(f100,plain,
    ( spl6_5
  <=> m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f118,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | m1_connsp_2(sK3,sK0,sK1)
    | ~ spl6_5 ),
    inference(resolution,[],[f102,f44])).

fof(f102,plain,
    ( m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f100])).

fof(f172,plain,
    ( spl6_10
    | spl6_16
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f123,f105,f169,f131])).

fof(f131,plain,
    ( spl6_10
  <=> v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f123,plain,
    ( r2_hidden(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1)))
    | ~ spl6_6 ),
    inference(resolution,[],[f107,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f164,plain,
    ( ~ spl6_10
    | spl6_15
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f122,f105,f161,f131])).

fof(f122,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1)))
    | ~ spl6_6 ),
    inference(resolution,[],[f107,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f159,plain,
    ( spl6_10
    | spl6_14
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f120,f100,f156,f131])).

fof(f120,plain,
    ( r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1)))
    | ~ spl6_5 ),
    inference(resolution,[],[f102,f52])).

fof(f152,plain,
    ( ~ spl6_13
    | spl6_12 ),
    inference(avatar_split_clause,[],[f144,f140,f149])).

fof(f140,plain,
    ( spl6_12
  <=> m1_subset_1(k1_setfam_1(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f144,plain,
    ( ~ r2_hidden(k1_setfam_1(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1)))
    | spl6_12 ),
    inference(resolution,[],[f142,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f142,plain,
    ( ~ m1_subset_1(k1_setfam_1(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1)))
    | spl6_12 ),
    inference(avatar_component_clause,[],[f140])).

fof(f143,plain,(
    ~ spl6_12 ),
    inference(avatar_split_clause,[],[f65,f140])).

fof(f65,plain,(
    ~ m1_subset_1(k1_setfam_1(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(definition_unfolding,[],[f35,f48])).

fof(f35,plain,(
    ~ m1_subset_1(k3_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
                  & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
                  & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))
                   => m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))
                 => m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_waybel_9)).

fof(f108,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f36,f105])).

fof(f36,plain,(
    m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(cnf_transformation,[],[f17])).

fof(f103,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f34,f100])).

fof(f34,plain,(
    m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(cnf_transformation,[],[f17])).

fof(f96,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f37,f93])).

fof(f37,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f91,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f40,f88])).

fof(f40,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f86,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f39,f83])).

fof(f39,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f81,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f38,f78])).

fof(f38,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:31:47 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (14536)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.51  % (14528)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.51  % (14520)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (14515)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (14517)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (14516)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (14519)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (14531)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.53  % (14542)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.53  % (14518)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (14513)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (14525)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (14538)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (14514)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (14521)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (14532)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  % (14533)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (14523)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  % (14534)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (14523)Refutation not found, incomplete strategy% (14523)------------------------------
% 0.21/0.54  % (14523)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (14523)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (14523)Memory used [KB]: 10618
% 0.21/0.54  % (14523)Time elapsed: 0.147 s
% 0.21/0.54  % (14523)------------------------------
% 0.21/0.54  % (14523)------------------------------
% 0.21/0.54  % (14540)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (14541)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (14522)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (14537)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.55  % (14526)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.55  % (14535)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.55  % (14530)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (14524)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (14527)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.55  % (14529)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (14530)Refutation not found, incomplete strategy% (14530)------------------------------
% 0.21/0.55  % (14530)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (14530)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (14530)Memory used [KB]: 10618
% 0.21/0.55  % (14530)Time elapsed: 0.159 s
% 0.21/0.55  % (14530)------------------------------
% 0.21/0.55  % (14530)------------------------------
% 0.21/0.55  % (14524)Refutation not found, incomplete strategy% (14524)------------------------------
% 0.21/0.55  % (14524)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (14524)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (14524)Memory used [KB]: 10618
% 0.21/0.55  % (14524)Time elapsed: 0.153 s
% 0.21/0.55  % (14524)------------------------------
% 0.21/0.55  % (14524)------------------------------
% 0.21/0.56  % (14539)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.58  % (14535)Refutation found. Thanks to Tanya!
% 0.21/0.58  % SZS status Theorem for theBenchmark
% 0.21/0.58  % SZS output start Proof for theBenchmark
% 0.21/0.58  fof(f363,plain,(
% 0.21/0.58    $false),
% 0.21/0.58    inference(avatar_sat_refutation,[],[f81,f86,f91,f96,f103,f108,f143,f152,f159,f164,f172,f195,f200,f213,f234,f240,f272,f278,f289,f298,f304,f312,f315,f319,f362])).
% 0.21/0.58  fof(f362,plain,(
% 0.21/0.58    ~spl6_23 | spl6_22),
% 0.21/0.58    inference(avatar_split_clause,[],[f361,f210,f219])).
% 0.21/0.58  fof(f219,plain,(
% 0.21/0.58    spl6_23 <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 0.21/0.58  fof(f210,plain,(
% 0.21/0.58    spl6_22 <=> m1_subset_1(k1_setfam_1(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 0.21/0.58  fof(f361,plain,(
% 0.21/0.58    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | spl6_22),
% 0.21/0.58    inference(duplicate_literal_removal,[],[f354])).
% 0.21/0.58  fof(f354,plain,(
% 0.21/0.58    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | spl6_22),
% 0.21/0.58    inference(resolution,[],[f330,f55])).
% 0.21/0.58  fof(f55,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f28])).
% 0.21/0.58  fof(f28,plain,(
% 0.21/0.58    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f4])).
% 0.21/0.58  fof(f4,axiom,(
% 0.21/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).
% 0.21/0.58  fof(f330,plain,(
% 0.21/0.58    ( ! [X0] : (~m1_subset_1(k9_subset_1(X0,sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(X0))) ) | spl6_22),
% 0.21/0.58    inference(superposition,[],[f212,f66])).
% 0.21/0.58  fof(f66,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.21/0.58    inference(definition_unfolding,[],[f56,f48])).
% 0.21/0.58  fof(f48,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f6])).
% 0.21/0.58  fof(f6,axiom,(
% 0.21/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.58  fof(f56,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f29])).
% 0.21/0.58  fof(f29,plain,(
% 0.21/0.58    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f5])).
% 0.21/0.58  fof(f5,axiom,(
% 0.21/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.21/0.58  fof(f212,plain,(
% 0.21/0.58    ~m1_subset_1(k1_setfam_1(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0))) | spl6_22),
% 0.21/0.58    inference(avatar_component_clause,[],[f210])).
% 0.21/0.58  fof(f319,plain,(
% 0.21/0.58    ~spl6_15 | ~spl6_33),
% 0.21/0.58    inference(avatar_contradiction_clause,[],[f317])).
% 0.21/0.58  fof(f317,plain,(
% 0.21/0.58    $false | (~spl6_15 | ~spl6_33)),
% 0.21/0.58    inference(unit_resulting_resolution,[],[f163,f310,f47])).
% 0.21/0.58  fof(f47,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f1])).
% 0.21/0.58  fof(f1,axiom,(
% 0.21/0.58    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.58  fof(f310,plain,(
% 0.21/0.58    r2_hidden(sK1,sK2) | ~spl6_33),
% 0.21/0.58    inference(avatar_component_clause,[],[f309])).
% 0.21/0.58  fof(f309,plain,(
% 0.21/0.58    spl6_33 <=> r2_hidden(sK1,sK2)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).
% 0.21/0.58  fof(f163,plain,(
% 0.21/0.58    v1_xboole_0(sK2) | ~spl6_15),
% 0.21/0.58    inference(avatar_component_clause,[],[f161])).
% 0.21/0.58  fof(f161,plain,(
% 0.21/0.58    spl6_15 <=> v1_xboole_0(sK2)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.21/0.58  fof(f315,plain,(
% 0.21/0.58    spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_19 | ~spl6_25 | spl6_33),
% 0.21/0.58    inference(avatar_contradiction_clause,[],[f313])).
% 0.21/0.58  fof(f313,plain,(
% 0.21/0.58    $false | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_19 | ~spl6_25 | spl6_33)),
% 0.21/0.58    inference(unit_resulting_resolution,[],[f85,f80,f90,f199,f95,f228,f311,f45])).
% 0.21/0.58  fof(f45,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_connsp_2(X1,X0,X2) | r2_hidden(X2,X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f23])).
% 0.21/0.58  fof(f23,plain,(
% 0.21/0.58    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.58    inference(flattening,[],[f22])).
% 0.21/0.58  fof(f22,plain,(
% 0.21/0.58    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f11])).
% 0.21/0.58  fof(f11,axiom,(
% 0.21/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (m1_connsp_2(X1,X0,X2) => r2_hidden(X2,X1)))))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_connsp_2)).
% 0.21/0.58  fof(f311,plain,(
% 0.21/0.58    ~r2_hidden(sK1,sK2) | spl6_33),
% 0.21/0.58    inference(avatar_component_clause,[],[f309])).
% 0.21/0.58  fof(f228,plain,(
% 0.21/0.58    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_25),
% 0.21/0.58    inference(avatar_component_clause,[],[f227])).
% 0.21/0.58  fof(f227,plain,(
% 0.21/0.58    spl6_25 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 0.21/0.58  fof(f95,plain,(
% 0.21/0.58    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl6_4),
% 0.21/0.58    inference(avatar_component_clause,[],[f93])).
% 0.21/0.58  fof(f93,plain,(
% 0.21/0.58    spl6_4 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.58  fof(f199,plain,(
% 0.21/0.58    m1_connsp_2(sK2,sK0,sK1) | ~spl6_19),
% 0.21/0.58    inference(avatar_component_clause,[],[f197])).
% 0.21/0.58  fof(f197,plain,(
% 0.21/0.58    spl6_19 <=> m1_connsp_2(sK2,sK0,sK1)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 0.21/0.58  fof(f90,plain,(
% 0.21/0.58    l1_pre_topc(sK0) | ~spl6_3),
% 0.21/0.58    inference(avatar_component_clause,[],[f88])).
% 0.21/0.58  fof(f88,plain,(
% 0.21/0.58    spl6_3 <=> l1_pre_topc(sK0)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.58  fof(f80,plain,(
% 0.21/0.58    ~v2_struct_0(sK0) | spl6_1),
% 0.21/0.58    inference(avatar_component_clause,[],[f78])).
% 0.21/0.58  fof(f78,plain,(
% 0.21/0.58    spl6_1 <=> v2_struct_0(sK0)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.58  fof(f85,plain,(
% 0.21/0.58    v2_pre_topc(sK0) | ~spl6_2),
% 0.21/0.58    inference(avatar_component_clause,[],[f83])).
% 0.21/0.58  fof(f83,plain,(
% 0.21/0.58    spl6_2 <=> v2_pre_topc(sK0)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.58  fof(f312,plain,(
% 0.21/0.58    ~spl6_33 | ~spl6_32 | spl6_21),
% 0.21/0.58    inference(avatar_split_clause,[],[f306,f206,f275,f309])).
% 0.21/0.58  fof(f275,plain,(
% 0.21/0.58    spl6_32 <=> r2_hidden(sK1,sK3)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).
% 0.21/0.58  fof(f206,plain,(
% 0.21/0.58    spl6_21 <=> r2_hidden(sK1,k1_setfam_1(k2_tarski(sK2,sK3)))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 0.21/0.58  fof(f306,plain,(
% 0.21/0.58    ~r2_hidden(sK1,sK3) | ~r2_hidden(sK1,sK2) | spl6_21),
% 0.21/0.58    inference(resolution,[],[f208,f74])).
% 0.21/0.58  fof(f74,plain,(
% 0.21/0.58    ( ! [X0,X3,X1] : (r2_hidden(X3,k1_setfam_1(k2_tarski(X0,X1))) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) )),
% 0.21/0.58    inference(equality_resolution,[],[f68])).
% 0.21/0.58  fof(f68,plain,(
% 0.21/0.58    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | r2_hidden(X3,X2) | k1_setfam_1(k2_tarski(X0,X1)) != X2) )),
% 0.21/0.58    inference(definition_unfolding,[],[f64,f48])).
% 0.21/0.58  fof(f64,plain,(
% 0.21/0.58    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.21/0.58    inference(cnf_transformation,[],[f2])).
% 0.21/0.58  fof(f2,axiom,(
% 0.21/0.58    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 0.21/0.58  fof(f208,plain,(
% 0.21/0.58    ~r2_hidden(sK1,k1_setfam_1(k2_tarski(sK2,sK3))) | spl6_21),
% 0.21/0.58    inference(avatar_component_clause,[],[f206])).
% 0.21/0.58  fof(f304,plain,(
% 0.21/0.58    spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_16 | ~spl6_25 | spl6_26),
% 0.21/0.58    inference(avatar_contradiction_clause,[],[f299])).
% 0.21/0.58  fof(f299,plain,(
% 0.21/0.58    $false | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_16 | ~spl6_25 | spl6_26)),
% 0.21/0.58    inference(unit_resulting_resolution,[],[f80,f90,f85,f233,f95,f171,f228,f42])).
% 0.21/0.58  fof(f42,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(X2,X0) | v2_struct_0(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f19])).
% 0.21/0.58  fof(f19,plain,(
% 0.21/0.58    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.58    inference(flattening,[],[f18])).
% 0.21/0.58  fof(f18,plain,(
% 0.21/0.58    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f12])).
% 0.21/0.58  fof(f12,axiom,(
% 0.21/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))))))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_yellow_6)).
% 0.21/0.58  fof(f171,plain,(
% 0.21/0.58    r2_hidden(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) | ~spl6_16),
% 0.21/0.58    inference(avatar_component_clause,[],[f169])).
% 0.21/0.58  fof(f169,plain,(
% 0.21/0.58    spl6_16 <=> r2_hidden(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.21/0.58  fof(f233,plain,(
% 0.21/0.58    ~v3_pre_topc(sK2,sK0) | spl6_26),
% 0.21/0.58    inference(avatar_component_clause,[],[f231])).
% 0.21/0.58  fof(f231,plain,(
% 0.21/0.58    spl6_26 <=> v3_pre_topc(sK2,sK0)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 0.21/0.58  fof(f298,plain,(
% 0.21/0.58    spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_19 | spl6_25),
% 0.21/0.58    inference(avatar_contradiction_clause,[],[f293])).
% 0.21/0.58  fof(f293,plain,(
% 0.21/0.58    $false | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_19 | spl6_25)),
% 0.21/0.58    inference(unit_resulting_resolution,[],[f80,f90,f85,f199,f95,f229,f54])).
% 0.21/0.58  fof(f54,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_connsp_2(X2,X0,X1) | v2_struct_0(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f27])).
% 0.21/0.58  fof(f27,plain,(
% 0.21/0.58    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.58    inference(flattening,[],[f26])).
% 0.21/0.58  fof(f26,plain,(
% 0.21/0.58    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f10])).
% 0.21/0.58  fof(f10,axiom,(
% 0.21/0.58    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).
% 0.21/0.58  fof(f229,plain,(
% 0.21/0.58    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | spl6_25),
% 0.21/0.58    inference(avatar_component_clause,[],[f227])).
% 0.21/0.58  fof(f289,plain,(
% 0.21/0.58    spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_14 | ~spl6_23 | spl6_24),
% 0.21/0.58    inference(avatar_contradiction_clause,[],[f285])).
% 0.21/0.58  fof(f285,plain,(
% 0.21/0.58    $false | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_14 | ~spl6_23 | spl6_24)),
% 0.21/0.58    inference(unit_resulting_resolution,[],[f80,f90,f85,f225,f95,f220,f158,f42])).
% 0.21/0.58  fof(f158,plain,(
% 0.21/0.58    r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))) | ~spl6_14),
% 0.21/0.58    inference(avatar_component_clause,[],[f156])).
% 0.21/0.58  fof(f156,plain,(
% 0.21/0.58    spl6_14 <=> r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.21/0.58  fof(f220,plain,(
% 0.21/0.58    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_23),
% 0.21/0.58    inference(avatar_component_clause,[],[f219])).
% 0.21/0.58  fof(f225,plain,(
% 0.21/0.58    ~v3_pre_topc(sK3,sK0) | spl6_24),
% 0.21/0.58    inference(avatar_component_clause,[],[f223])).
% 0.21/0.58  fof(f223,plain,(
% 0.21/0.58    spl6_24 <=> v3_pre_topc(sK3,sK0)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 0.21/0.58  fof(f278,plain,(
% 0.21/0.58    ~spl6_4 | spl6_32 | ~spl6_18 | ~spl6_31),
% 0.21/0.58    inference(avatar_split_clause,[],[f273,f270,f192,f275,f93])).
% 0.21/0.58  fof(f192,plain,(
% 0.21/0.58    spl6_18 <=> m1_connsp_2(sK3,sK0,sK1)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.21/0.58  fof(f270,plain,(
% 0.21/0.58    spl6_31 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,sK3) | ~m1_connsp_2(sK3,sK0,X0))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).
% 0.21/0.58  fof(f273,plain,(
% 0.21/0.58    r2_hidden(sK1,sK3) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | (~spl6_18 | ~spl6_31)),
% 0.21/0.58    inference(resolution,[],[f271,f194])).
% 0.21/0.58  fof(f194,plain,(
% 0.21/0.58    m1_connsp_2(sK3,sK0,sK1) | ~spl6_18),
% 0.21/0.58    inference(avatar_component_clause,[],[f192])).
% 0.21/0.58  fof(f271,plain,(
% 0.21/0.58    ( ! [X0] : (~m1_connsp_2(sK3,sK0,X0) | r2_hidden(X0,sK3) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl6_31),
% 0.21/0.58    inference(avatar_component_clause,[],[f270])).
% 0.21/0.58  fof(f272,plain,(
% 0.21/0.58    spl6_31 | spl6_1 | ~spl6_3 | ~spl6_2 | ~spl6_23),
% 0.21/0.58    inference(avatar_split_clause,[],[f241,f219,f83,f88,f78,f270])).
% 0.21/0.58  fof(f241,plain,(
% 0.21/0.58    ( ! [X0] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_connsp_2(sK3,sK0,X0) | r2_hidden(X0,sK3)) ) | ~spl6_23),
% 0.21/0.58    inference(resolution,[],[f220,f45])).
% 0.21/0.58  fof(f240,plain,(
% 0.21/0.58    spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_18 | spl6_23),
% 0.21/0.58    inference(avatar_contradiction_clause,[],[f235])).
% 0.21/0.58  fof(f235,plain,(
% 0.21/0.58    $false | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_18 | spl6_23)),
% 0.21/0.58    inference(unit_resulting_resolution,[],[f80,f90,f85,f194,f95,f221,f54])).
% 0.21/0.58  fof(f221,plain,(
% 0.21/0.58    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | spl6_23),
% 0.21/0.58    inference(avatar_component_clause,[],[f219])).
% 0.21/0.58  fof(f234,plain,(
% 0.21/0.58    ~spl6_2 | ~spl6_23 | ~spl6_24 | ~spl6_25 | ~spl6_26 | ~spl6_3 | spl6_20),
% 0.21/0.58    inference(avatar_split_clause,[],[f214,f202,f88,f231,f227,f223,f219,f83])).
% 0.21/0.58  fof(f202,plain,(
% 0.21/0.58    spl6_20 <=> v3_pre_topc(k1_setfam_1(k2_tarski(sK2,sK3)),sK0)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 0.21/0.58  fof(f214,plain,(
% 0.21/0.58    ~l1_pre_topc(sK0) | ~v3_pre_topc(sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(sK3,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | spl6_20),
% 0.21/0.58    inference(resolution,[],[f204,f67])).
% 0.21/0.58  fof(f67,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (v3_pre_topc(k1_setfam_1(k2_tarski(X1,X2)),X0) | ~l1_pre_topc(X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0)) )),
% 0.21/0.58    inference(definition_unfolding,[],[f57,f48])).
% 0.21/0.58  fof(f57,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k3_xboole_0(X1,X2),X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f31])).
% 0.21/0.58  fof(f31,plain,(
% 0.21/0.58    ! [X0,X1,X2] : (v3_pre_topc(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.58    inference(flattening,[],[f30])).
% 0.21/0.58  fof(f30,plain,(
% 0.21/0.58    ! [X0,X1,X2] : (v3_pre_topc(k3_xboole_0(X1,X2),X0) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f9])).
% 0.21/0.58  fof(f9,axiom,(
% 0.21/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X2,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k3_xboole_0(X1,X2),X0))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_tops_1)).
% 0.21/0.58  fof(f204,plain,(
% 0.21/0.58    ~v3_pre_topc(k1_setfam_1(k2_tarski(sK2,sK3)),sK0) | spl6_20),
% 0.21/0.58    inference(avatar_component_clause,[],[f202])).
% 0.21/0.58  fof(f213,plain,(
% 0.21/0.58    spl6_1 | ~spl6_20 | ~spl6_21 | ~spl6_22 | ~spl6_4 | ~spl6_3 | ~spl6_2 | spl6_13),
% 0.21/0.58    inference(avatar_split_clause,[],[f153,f149,f83,f88,f93,f210,f206,f202,f78])).
% 0.21/0.58  fof(f149,plain,(
% 0.21/0.58    spl6_13 <=> r2_hidden(k1_setfam_1(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.21/0.58  fof(f153,plain,(
% 0.21/0.58    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k1_setfam_1(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK1,k1_setfam_1(k2_tarski(sK2,sK3))) | ~v3_pre_topc(k1_setfam_1(k2_tarski(sK2,sK3)),sK0) | v2_struct_0(sK0) | spl6_13),
% 0.21/0.58    inference(resolution,[],[f151,f43])).
% 0.21/0.58  fof(f43,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X1,X2) | ~v3_pre_topc(X2,X0) | v2_struct_0(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f19])).
% 0.21/0.58  fof(f151,plain,(
% 0.21/0.58    ~r2_hidden(k1_setfam_1(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1))) | spl6_13),
% 0.21/0.58    inference(avatar_component_clause,[],[f149])).
% 0.21/0.58  fof(f200,plain,(
% 0.21/0.58    spl6_19 | spl6_1 | ~spl6_4 | ~spl6_3 | ~spl6_2 | ~spl6_6),
% 0.21/0.58    inference(avatar_split_clause,[],[f121,f105,f83,f88,f93,f78,f197])).
% 0.21/0.58  fof(f105,plain,(
% 0.21/0.58    spl6_6 <=> m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.58  fof(f121,plain,(
% 0.21/0.58    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | m1_connsp_2(sK2,sK0,sK1) | ~spl6_6),
% 0.21/0.58    inference(resolution,[],[f107,f44])).
% 0.21/0.58  fof(f44,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | m1_connsp_2(X2,X0,X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f21])).
% 0.21/0.58  fof(f21,plain,(
% 0.21/0.58    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.58    inference(flattening,[],[f20])).
% 0.21/0.58  fof(f20,plain,(
% 0.21/0.58    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f13])).
% 0.21/0.58  fof(f13,axiom,(
% 0.21/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => m1_connsp_2(X2,X0,X1))))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_waybel_9)).
% 0.21/0.58  fof(f107,plain,(
% 0.21/0.58    m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) | ~spl6_6),
% 0.21/0.58    inference(avatar_component_clause,[],[f105])).
% 0.21/0.58  fof(f195,plain,(
% 0.21/0.58    spl6_18 | spl6_1 | ~spl6_4 | ~spl6_3 | ~spl6_2 | ~spl6_5),
% 0.21/0.58    inference(avatar_split_clause,[],[f118,f100,f83,f88,f93,f78,f192])).
% 0.21/0.58  fof(f100,plain,(
% 0.21/0.58    spl6_5 <=> m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.58  fof(f118,plain,(
% 0.21/0.58    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | m1_connsp_2(sK3,sK0,sK1) | ~spl6_5),
% 0.21/0.58    inference(resolution,[],[f102,f44])).
% 0.21/0.58  fof(f102,plain,(
% 0.21/0.58    m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))) | ~spl6_5),
% 0.21/0.58    inference(avatar_component_clause,[],[f100])).
% 0.21/0.58  fof(f172,plain,(
% 0.21/0.58    spl6_10 | spl6_16 | ~spl6_6),
% 0.21/0.58    inference(avatar_split_clause,[],[f123,f105,f169,f131])).
% 0.21/0.58  fof(f131,plain,(
% 0.21/0.58    spl6_10 <=> v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.21/0.58  fof(f123,plain,(
% 0.21/0.58    r2_hidden(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) | v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1))) | ~spl6_6),
% 0.21/0.58    inference(resolution,[],[f107,f52])).
% 0.21/0.58  fof(f52,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f24])).
% 0.21/0.58  fof(f24,plain,(
% 0.21/0.58    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f3])).
% 0.21/0.58  fof(f3,axiom,(
% 0.21/0.58    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.21/0.58  fof(f164,plain,(
% 0.21/0.58    ~spl6_10 | spl6_15 | ~spl6_6),
% 0.21/0.58    inference(avatar_split_clause,[],[f122,f105,f161,f131])).
% 0.21/0.58  fof(f122,plain,(
% 0.21/0.58    v1_xboole_0(sK2) | ~v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1))) | ~spl6_6),
% 0.21/0.58    inference(resolution,[],[f107,f50])).
% 0.21/0.58  fof(f50,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f24])).
% 0.21/0.58  fof(f159,plain,(
% 0.21/0.58    spl6_10 | spl6_14 | ~spl6_5),
% 0.21/0.58    inference(avatar_split_clause,[],[f120,f100,f156,f131])).
% 0.21/0.58  fof(f120,plain,(
% 0.21/0.58    r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))) | v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1))) | ~spl6_5),
% 0.21/0.58    inference(resolution,[],[f102,f52])).
% 0.21/0.58  fof(f152,plain,(
% 0.21/0.58    ~spl6_13 | spl6_12),
% 0.21/0.58    inference(avatar_split_clause,[],[f144,f140,f149])).
% 0.21/0.58  fof(f140,plain,(
% 0.21/0.58    spl6_12 <=> m1_subset_1(k1_setfam_1(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.21/0.58  fof(f144,plain,(
% 0.21/0.58    ~r2_hidden(k1_setfam_1(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1))) | spl6_12),
% 0.21/0.58    inference(resolution,[],[f142,f53])).
% 0.21/0.58  fof(f53,plain,(
% 0.21/0.58    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f25])).
% 0.21/0.58  fof(f25,plain,(
% 0.21/0.58    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.21/0.58    inference(ennf_transformation,[],[f7])).
% 0.21/0.58  fof(f7,axiom,(
% 0.21/0.58    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.21/0.58  fof(f142,plain,(
% 0.21/0.58    ~m1_subset_1(k1_setfam_1(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1))) | spl6_12),
% 0.21/0.58    inference(avatar_component_clause,[],[f140])).
% 0.21/0.58  fof(f143,plain,(
% 0.21/0.58    ~spl6_12),
% 0.21/0.58    inference(avatar_split_clause,[],[f65,f140])).
% 0.21/0.58  fof(f65,plain,(
% 0.21/0.58    ~m1_subset_1(k1_setfam_1(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 0.21/0.58    inference(definition_unfolding,[],[f35,f48])).
% 0.21/0.58  fof(f35,plain,(
% 0.21/0.58    ~m1_subset_1(k3_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 0.21/0.58    inference(cnf_transformation,[],[f17])).
% 0.21/0.58  fof(f17,plain,(
% 0.21/0.58    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.58    inference(flattening,[],[f16])).
% 0.21/0.58  fof(f16,plain,(
% 0.21/0.58    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f15])).
% 0.21/0.58  fof(f15,negated_conjecture,(
% 0.21/0.58    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 0.21/0.58    inference(negated_conjecture,[],[f14])).
% 0.21/0.58  fof(f14,conjecture,(
% 0.21/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_waybel_9)).
% 0.21/0.58  fof(f108,plain,(
% 0.21/0.58    spl6_6),
% 0.21/0.58    inference(avatar_split_clause,[],[f36,f105])).
% 0.21/0.58  fof(f36,plain,(
% 0.21/0.58    m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 0.21/0.58    inference(cnf_transformation,[],[f17])).
% 0.21/0.58  fof(f103,plain,(
% 0.21/0.58    spl6_5),
% 0.21/0.58    inference(avatar_split_clause,[],[f34,f100])).
% 0.21/0.58  fof(f34,plain,(
% 0.21/0.58    m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 0.21/0.58    inference(cnf_transformation,[],[f17])).
% 0.21/0.58  fof(f96,plain,(
% 0.21/0.58    spl6_4),
% 0.21/0.58    inference(avatar_split_clause,[],[f37,f93])).
% 0.21/0.58  fof(f37,plain,(
% 0.21/0.58    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.58    inference(cnf_transformation,[],[f17])).
% 0.21/0.58  fof(f91,plain,(
% 0.21/0.58    spl6_3),
% 0.21/0.58    inference(avatar_split_clause,[],[f40,f88])).
% 0.21/0.58  fof(f40,plain,(
% 0.21/0.58    l1_pre_topc(sK0)),
% 0.21/0.58    inference(cnf_transformation,[],[f17])).
% 0.21/0.58  fof(f86,plain,(
% 0.21/0.58    spl6_2),
% 0.21/0.58    inference(avatar_split_clause,[],[f39,f83])).
% 0.21/0.58  fof(f39,plain,(
% 0.21/0.58    v2_pre_topc(sK0)),
% 0.21/0.58    inference(cnf_transformation,[],[f17])).
% 0.21/0.58  fof(f81,plain,(
% 0.21/0.58    ~spl6_1),
% 0.21/0.58    inference(avatar_split_clause,[],[f38,f78])).
% 0.21/0.58  fof(f38,plain,(
% 0.21/0.58    ~v2_struct_0(sK0)),
% 0.21/0.58    inference(cnf_transformation,[],[f17])).
% 0.21/0.58  % SZS output end Proof for theBenchmark
% 0.21/0.58  % (14535)------------------------------
% 0.21/0.58  % (14535)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (14535)Termination reason: Refutation
% 0.21/0.58  
% 0.21/0.58  % (14535)Memory used [KB]: 11001
% 0.21/0.58  % (14535)Time elapsed: 0.146 s
% 0.21/0.58  % (14535)------------------------------
% 0.21/0.58  % (14535)------------------------------
% 0.21/0.58  % (14512)Success in time 0.226 s
%------------------------------------------------------------------------------
