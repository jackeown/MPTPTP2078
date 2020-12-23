%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:08 EST 2020

% Result     : Theorem 1.47s
% Output     : Refutation 1.47s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 421 expanded)
%              Number of leaves         :   39 ( 209 expanded)
%              Depth                    :    8
%              Number of atoms          :  584 (1630 expanded)
%              Number of equality atoms :   22 (  76 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1342,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f72,f77,f82,f87,f92,f97,f102,f116,f137,f142,f151,f170,f176,f189,f195,f208,f301,f335,f1047,f1340,f1341])).

fof(f1341,plain,
    ( ~ spl6_45
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | spl6_8
    | ~ spl6_11
    | spl6_20
    | ~ spl6_34 ),
    inference(avatar_split_clause,[],[f963,f295,f205,f148,f112,f99,f94,f89,f84,f440])).

fof(f440,plain,
    ( spl6_45
  <=> m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).

fof(f84,plain,
    ( spl6_4
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f89,plain,
    ( spl6_5
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f94,plain,
    ( spl6_6
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f99,plain,
    ( spl6_7
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f112,plain,
    ( spl6_8
  <=> r2_hidden(k2_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f148,plain,
    ( spl6_11
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f205,plain,
    ( spl6_20
  <=> sP5(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f295,plain,
    ( spl6_34
  <=> v3_pre_topc(k2_xboole_0(sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f963,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | spl6_8
    | ~ spl6_11
    | spl6_20
    | ~ spl6_34 ),
    inference(unit_resulting_resolution,[],[f101,f96,f91,f86,f297,f114,f432,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_pre_topc(X2,X0)
      | r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
                  | ~ v3_pre_topc(X2,X0)
                  | ~ r2_hidden(X1,X2) )
                & ( ( v3_pre_topc(X2,X0)
                    & r2_hidden(X1,X2) )
                  | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
                  | ~ v3_pre_topc(X2,X0)
                  | ~ r2_hidden(X1,X2) )
                & ( ( v3_pre_topc(X2,X0)
                    & r2_hidden(X1,X2) )
                  | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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

fof(f432,plain,
    ( ! [X0] : r2_hidden(sK1,k2_xboole_0(sK2,X0))
    | ~ spl6_11
    | spl6_20 ),
    inference(unit_resulting_resolution,[],[f200,f228,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f228,plain,
    ( ! [X0] : ~ v1_xboole_0(k2_xboole_0(sK2,X0))
    | spl6_20 ),
    inference(unit_resulting_resolution,[],[f107,f207,f66])).

fof(f66,plain,(
    ! [X2,X1] :
      ( sP5(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f66_D])).

fof(f66_D,plain,(
    ! [X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
          | ~ v1_xboole_0(X2) )
    <=> ~ sP5(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP5])])).

fof(f207,plain,
    ( ~ sP5(sK2)
    | spl6_20 ),
    inference(avatar_component_clause,[],[f205])).

fof(f107,plain,(
    ! [X0,X1] : m1_subset_1(X0,k1_zfmisc_1(k2_xboole_0(X0,X1))) ),
    inference(unit_resulting_resolution,[],[f52,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f52,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f200,plain,
    ( ! [X0] : m1_subset_1(sK1,k2_xboole_0(sK2,X0))
    | ~ spl6_11 ),
    inference(unit_resulting_resolution,[],[f107,f150,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f150,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f148])).

fof(f114,plain,
    ( ~ r2_hidden(k2_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1)))
    | spl6_8 ),
    inference(avatar_component_clause,[],[f112])).

fof(f297,plain,
    ( v3_pre_topc(k2_xboole_0(sK2,sK3),sK0)
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f295])).

fof(f86,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f84])).

fof(f91,plain,
    ( l1_pre_topc(sK0)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f89])).

fof(f96,plain,
    ( v2_pre_topc(sK0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f94])).

fof(f101,plain,
    ( ~ v2_struct_0(sK0)
    | spl6_7 ),
    inference(avatar_component_clause,[],[f99])).

fof(f1340,plain,
    ( spl6_62
    | ~ spl6_17
    | ~ spl6_36 ),
    inference(avatar_split_clause,[],[f1339,f325,f186,f1043])).

fof(f1043,plain,
    ( spl6_62
  <=> r1_tarski(k2_xboole_0(sK2,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).

fof(f186,plain,
    ( spl6_17
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f325,plain,
    ( spl6_36
  <=> u1_struct_0(sK0) = k2_xboole_0(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f1339,plain,
    ( r1_tarski(k2_xboole_0(sK2,sK3),u1_struct_0(sK0))
    | ~ spl6_17
    | ~ spl6_36 ),
    inference(superposition,[],[f565,f327])).

fof(f327,plain,
    ( u1_struct_0(sK0) = k2_xboole_0(sK3,u1_struct_0(sK0))
    | ~ spl6_36 ),
    inference(avatar_component_clause,[],[f325])).

fof(f565,plain,
    ( ! [X0] : r1_tarski(k2_xboole_0(sK2,X0),k2_xboole_0(X0,u1_struct_0(sK0)))
    | ~ spl6_17 ),
    inference(superposition,[],[f356,f51])).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f356,plain,
    ( ! [X0] : r1_tarski(k2_xboole_0(sK2,X0),k2_xboole_0(u1_struct_0(sK0),X0))
    | ~ spl6_17 ),
    inference(unit_resulting_resolution,[],[f188,f130])).

fof(f130,plain,(
    ! [X6,X8,X7] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(X8))
      | r1_tarski(k2_xboole_0(X6,X7),k2_xboole_0(X8,X7)) ) ),
    inference(resolution,[],[f49,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_xboole_1)).

fof(f188,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f186])).

fof(f1047,plain,
    ( ~ spl6_62
    | spl6_45 ),
    inference(avatar_split_clause,[],[f1035,f440,f1043])).

fof(f1035,plain,
    ( ~ r1_tarski(k2_xboole_0(sK2,sK3),u1_struct_0(sK0))
    | spl6_45 ),
    inference(resolution,[],[f442,f63])).

fof(f442,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_45 ),
    inference(avatar_component_clause,[],[f440])).

fof(f335,plain,
    ( spl6_36
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f322,f192,f325])).

fof(f192,plain,
    ( spl6_18
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f322,plain,
    ( u1_struct_0(sK0) = k2_xboole_0(sK3,u1_struct_0(sK0))
    | ~ spl6_18 ),
    inference(resolution,[],[f121,f194])).

fof(f194,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f192])).

fof(f121,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(X5))
      | k2_xboole_0(X4,X5) = X5 ) ),
    inference(resolution,[],[f50,f62])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f301,plain,
    ( spl6_34
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_17
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f300,f192,f186,f173,f167,f94,f89,f295])).

fof(f167,plain,
    ( spl6_14
  <=> v3_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f173,plain,
    ( spl6_15
  <=> v3_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f300,plain,
    ( v3_pre_topc(k2_xboole_0(sK2,sK3),sK0)
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_17
    | ~ spl6_18 ),
    inference(forward_demodulation,[],[f278,f51])).

fof(f278,plain,
    ( v3_pre_topc(k2_xboole_0(sK3,sK2),sK0)
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_17
    | ~ spl6_18 ),
    inference(unit_resulting_resolution,[],[f96,f91,f175,f169,f188,f194,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_xboole_0(X1,X2),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_tops_1)).

fof(f169,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f167])).

fof(f175,plain,
    ( v3_pre_topc(sK3,sK0)
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f173])).

fof(f208,plain,
    ( ~ spl6_20
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f202,f148,f205])).

fof(f202,plain,
    ( ~ sP5(sK2)
    | ~ spl6_11 ),
    inference(unit_resulting_resolution,[],[f150,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ sP5(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(general_splitting,[],[f60,f66_D])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f195,plain,
    ( spl6_18
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f190,f139,f99,f94,f89,f84,f74,f192])).

fof(f74,plain,
    ( spl6_2
  <=> m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f139,plain,
    ( spl6_10
  <=> sK3 = sK4(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f190,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f181,f141])).

fof(f141,plain,
    ( sK3 = sK4(sK0,sK1,sK3)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f139])).

fof(f181,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7 ),
    inference(unit_resulting_resolution,[],[f101,f96,f91,f86,f76,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_pre_topc(sK4(X0,X1,X2),X0)
                & r2_hidden(X1,sK4(X0,X1,X2))
                & sK4(X0,X1,X2) = X2
                & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f36])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( v3_pre_topc(X3,X0)
          & r2_hidden(X1,X3)
          & X2 = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( v3_pre_topc(sK4(X0,X1,X2),X0)
        & r2_hidden(X1,sK4(X0,X1,X2))
        & sK4(X0,X1,X2) = X2
        & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( v3_pre_topc(X3,X0)
                  & r2_hidden(X1,X3)
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( v3_pre_topc(X3,X0)
                  & r2_hidden(X1,X3)
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
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
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
             => ? [X3] :
                  ( v3_pre_topc(X3,X0)
                  & r2_hidden(X1,X3)
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_yellow_6)).

fof(f76,plain,
    ( m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f74])).

fof(f189,plain,
    ( spl6_17
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f184,f134,f99,f94,f89,f84,f79,f186])).

fof(f79,plain,
    ( spl6_3
  <=> m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f134,plain,
    ( spl6_9
  <=> sK2 = sK4(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f184,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | ~ spl6_9 ),
    inference(forward_demodulation,[],[f182,f136])).

fof(f136,plain,
    ( sK2 = sK4(sK0,sK1,sK2)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f134])).

fof(f182,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7 ),
    inference(unit_resulting_resolution,[],[f101,f96,f91,f86,f81,f53])).

fof(f81,plain,
    ( m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f79])).

fof(f176,plain,
    ( spl6_15
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f171,f139,f99,f94,f89,f84,f74,f173])).

fof(f171,plain,
    ( v3_pre_topc(sK3,sK0)
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f162,f141])).

fof(f162,plain,
    ( v3_pre_topc(sK4(sK0,sK1,sK3),sK0)
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7 ),
    inference(unit_resulting_resolution,[],[f101,f96,f91,f86,f76,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v3_pre_topc(sK4(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f170,plain,
    ( spl6_14
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f165,f134,f99,f94,f89,f84,f79,f167])).

fof(f165,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | ~ spl6_9 ),
    inference(forward_demodulation,[],[f163,f136])).

fof(f163,plain,
    ( v3_pre_topc(sK4(sK0,sK1,sK2),sK0)
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7 ),
    inference(unit_resulting_resolution,[],[f101,f96,f91,f86,f81,f56])).

fof(f151,plain,
    ( spl6_11
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f146,f134,f99,f94,f89,f84,f79,f148])).

fof(f146,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | ~ spl6_9 ),
    inference(forward_demodulation,[],[f144,f136])).

fof(f144,plain,
    ( r2_hidden(sK1,sK4(sK0,sK1,sK2))
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7 ),
    inference(unit_resulting_resolution,[],[f101,f96,f91,f86,f81,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | r2_hidden(X1,sK4(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f142,plain,
    ( spl6_10
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7 ),
    inference(avatar_split_clause,[],[f131,f99,f94,f89,f84,f74,f139])).

fof(f131,plain,
    ( sK3 = sK4(sK0,sK1,sK3)
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7 ),
    inference(unit_resulting_resolution,[],[f101,f96,f91,f86,f76,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( sK4(X0,X1,X2) = X2
      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f137,plain,
    ( spl6_9
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7 ),
    inference(avatar_split_clause,[],[f132,f99,f94,f89,f84,f79,f134])).

fof(f132,plain,
    ( sK2 = sK4(sK0,sK1,sK2)
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7 ),
    inference(unit_resulting_resolution,[],[f101,f96,f91,f86,f81,f54])).

fof(f116,plain,
    ( ~ spl6_8
    | spl6_1 ),
    inference(avatar_split_clause,[],[f110,f69,f112])).

fof(f69,plain,
    ( spl6_1
  <=> m1_subset_1(k2_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f110,plain,
    ( ~ r2_hidden(k2_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1)))
    | spl6_1 ),
    inference(resolution,[],[f71,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f71,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1)))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f69])).

fof(f102,plain,(
    ~ spl6_7 ),
    inference(avatar_split_clause,[],[f41,f99])).

fof(f41,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1)))
    & m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))
    & m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f34,f33,f32,f31])).

fof(f31,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
                    & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
                & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK0,X1)))
                  & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK0,X1))) )
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK0,X1))) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK0,X1)))
                & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK0,X1))) )
            & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK0,X1))) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK0,sK1)))
              & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK0,sK1))) )
          & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK0,sK1))) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK0,sK1)))
            & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK0,sK1))) )
        & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK0,sK1))) )
   => ( ? [X3] :
          ( ~ m1_subset_1(k2_xboole_0(sK2,X3),u1_struct_0(k9_yellow_6(sK0,sK1)))
          & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK0,sK1))) )
      & m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X3] :
        ( ~ m1_subset_1(k2_xboole_0(sK2,X3),u1_struct_0(k9_yellow_6(sK0,sK1)))
        & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK0,sK1))) )
   => ( ~ m1_subset_1(k2_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1)))
      & m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
                  & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
                  & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
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
                   => m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
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
                 => m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_waybel_9)).

fof(f97,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f42,f94])).

fof(f42,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f92,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f43,f89])).

fof(f43,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f87,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f44,f84])).

fof(f44,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f35])).

fof(f82,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f45,f79])).

fof(f45,plain,(
    m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(cnf_transformation,[],[f35])).

fof(f77,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f46,f74])).

fof(f46,plain,(
    m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(cnf_transformation,[],[f35])).

fof(f72,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f47,f69])).

fof(f47,plain,(
    ~ m1_subset_1(k2_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.36  % Computer   : n024.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 17:24:21 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.50  % (8384)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.52  % (8399)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.22/0.52  % (8380)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.52  % (8398)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.22/0.52  % (8383)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.52  % (8401)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.22/0.52  % (8400)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.22/0.52  % (8388)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.22/0.52  % (8382)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.52  % (8381)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.52  % (8390)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.22/0.53  % (8393)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.22/0.53  % (8394)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.22/0.53  % (8402)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.22/0.53  % (8385)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.53  % (8391)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.22/0.53  % (8392)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.22/0.53  % (8382)Refutation not found, incomplete strategy% (8382)------------------------------
% 0.22/0.53  % (8382)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (8382)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (8382)Memory used [KB]: 10618
% 0.22/0.53  % (8382)Time elapsed: 0.099 s
% 0.22/0.53  % (8382)------------------------------
% 0.22/0.53  % (8382)------------------------------
% 0.22/0.53  % (8386)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.26/0.54  % (8395)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 1.26/0.55  % (8389)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 1.26/0.55  % (8379)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 1.26/0.55  % (8387)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 1.26/0.55  % (8387)Refutation not found, incomplete strategy% (8387)------------------------------
% 1.26/0.55  % (8387)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.55  % (8387)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.55  
% 1.26/0.55  % (8387)Memory used [KB]: 10618
% 1.26/0.55  % (8387)Time elapsed: 0.100 s
% 1.26/0.55  % (8387)------------------------------
% 1.26/0.55  % (8387)------------------------------
% 1.47/0.57  % (8397)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 1.47/0.57  % (8389)Refutation not found, incomplete strategy% (8389)------------------------------
% 1.47/0.57  % (8389)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.57  % (8389)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.57  
% 1.47/0.57  % (8389)Memory used [KB]: 10618
% 1.47/0.57  % (8389)Time elapsed: 0.126 s
% 1.47/0.57  % (8389)------------------------------
% 1.47/0.57  % (8389)------------------------------
% 1.47/0.57  % (8396)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 1.47/0.58  % (8385)Refutation found. Thanks to Tanya!
% 1.47/0.58  % SZS status Theorem for theBenchmark
% 1.47/0.58  % SZS output start Proof for theBenchmark
% 1.47/0.58  fof(f1342,plain,(
% 1.47/0.58    $false),
% 1.47/0.58    inference(avatar_sat_refutation,[],[f72,f77,f82,f87,f92,f97,f102,f116,f137,f142,f151,f170,f176,f189,f195,f208,f301,f335,f1047,f1340,f1341])).
% 1.47/0.58  fof(f1341,plain,(
% 1.47/0.58    ~spl6_45 | ~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7 | spl6_8 | ~spl6_11 | spl6_20 | ~spl6_34),
% 1.47/0.58    inference(avatar_split_clause,[],[f963,f295,f205,f148,f112,f99,f94,f89,f84,f440])).
% 1.47/0.58  fof(f440,plain,(
% 1.47/0.58    spl6_45 <=> m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.47/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).
% 1.47/0.58  fof(f84,plain,(
% 1.47/0.58    spl6_4 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 1.47/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.47/0.58  fof(f89,plain,(
% 1.47/0.58    spl6_5 <=> l1_pre_topc(sK0)),
% 1.47/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.47/0.58  fof(f94,plain,(
% 1.47/0.58    spl6_6 <=> v2_pre_topc(sK0)),
% 1.47/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 1.47/0.58  fof(f99,plain,(
% 1.47/0.58    spl6_7 <=> v2_struct_0(sK0)),
% 1.47/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 1.47/0.58  fof(f112,plain,(
% 1.47/0.58    spl6_8 <=> r2_hidden(k2_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 1.47/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 1.47/0.58  fof(f148,plain,(
% 1.47/0.58    spl6_11 <=> r2_hidden(sK1,sK2)),
% 1.47/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 1.47/0.58  fof(f205,plain,(
% 1.47/0.58    spl6_20 <=> sP5(sK2)),
% 1.47/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 1.47/0.58  fof(f295,plain,(
% 1.47/0.58    spl6_34 <=> v3_pre_topc(k2_xboole_0(sK2,sK3),sK0)),
% 1.47/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).
% 1.47/0.58  fof(f963,plain,(
% 1.47/0.58    ~m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7 | spl6_8 | ~spl6_11 | spl6_20 | ~spl6_34)),
% 1.47/0.58    inference(unit_resulting_resolution,[],[f101,f96,f91,f86,f297,f114,f432,f59])).
% 1.47/0.58  fof(f59,plain,(
% 1.47/0.58    ( ! [X2,X0,X1] : (~v3_pre_topc(X2,X0) | r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.47/0.58    inference(cnf_transformation,[],[f39])).
% 1.47/0.58  fof(f39,plain,(
% 1.47/0.58    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2)) & ((v3_pre_topc(X2,X0) & r2_hidden(X1,X2)) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.47/0.58    inference(flattening,[],[f38])).
% 1.47/0.58  fof(f38,plain,(
% 1.47/0.58    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | (~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2))) & ((v3_pre_topc(X2,X0) & r2_hidden(X1,X2)) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.47/0.58    inference(nnf_transformation,[],[f24])).
% 1.47/0.58  fof(f24,plain,(
% 1.47/0.58    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.47/0.58    inference(flattening,[],[f23])).
% 1.47/0.58  fof(f23,plain,(
% 1.47/0.58    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.47/0.58    inference(ennf_transformation,[],[f12])).
% 1.47/0.58  fof(f12,axiom,(
% 1.47/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))))))),
% 1.47/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_yellow_6)).
% 1.47/0.58  fof(f432,plain,(
% 1.47/0.58    ( ! [X0] : (r2_hidden(sK1,k2_xboole_0(sK2,X0))) ) | (~spl6_11 | spl6_20)),
% 1.47/0.58    inference(unit_resulting_resolution,[],[f200,f228,f64])).
% 1.47/0.58  fof(f64,plain,(
% 1.47/0.58    ( ! [X0,X1] : (v1_xboole_0(X1) | r2_hidden(X0,X1) | ~m1_subset_1(X0,X1)) )),
% 1.47/0.58    inference(cnf_transformation,[],[f29])).
% 1.47/0.58  fof(f29,plain,(
% 1.47/0.58    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.47/0.58    inference(flattening,[],[f28])).
% 1.47/0.58  fof(f28,plain,(
% 1.47/0.58    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.47/0.58    inference(ennf_transformation,[],[f6])).
% 1.47/0.58  fof(f6,axiom,(
% 1.47/0.58    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.47/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 1.47/0.58  fof(f228,plain,(
% 1.47/0.58    ( ! [X0] : (~v1_xboole_0(k2_xboole_0(sK2,X0))) ) | spl6_20),
% 1.47/0.58    inference(unit_resulting_resolution,[],[f107,f207,f66])).
% 1.47/0.58  fof(f66,plain,(
% 1.47/0.58    ( ! [X2,X1] : (sP5(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) )),
% 1.47/0.58    inference(cnf_transformation,[],[f66_D])).
% 1.47/0.58  fof(f66_D,plain,(
% 1.47/0.58    ( ! [X1] : (( ! [X2] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) ) <=> ~sP5(X1)) )),
% 1.47/0.58    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP5])])).
% 1.47/0.58  fof(f207,plain,(
% 1.47/0.58    ~sP5(sK2) | spl6_20),
% 1.47/0.58    inference(avatar_component_clause,[],[f205])).
% 1.47/0.58  fof(f107,plain,(
% 1.47/0.58    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(k2_xboole_0(X0,X1)))) )),
% 1.47/0.58    inference(unit_resulting_resolution,[],[f52,f63])).
% 1.47/0.58  fof(f63,plain,(
% 1.47/0.58    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.47/0.58    inference(cnf_transformation,[],[f40])).
% 1.47/0.58  fof(f40,plain,(
% 1.47/0.58    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.47/0.58    inference(nnf_transformation,[],[f7])).
% 1.47/0.58  fof(f7,axiom,(
% 1.47/0.58    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.47/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.47/0.58  fof(f52,plain,(
% 1.47/0.58    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.47/0.58    inference(cnf_transformation,[],[f3])).
% 1.47/0.58  fof(f3,axiom,(
% 1.47/0.58    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.47/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.47/0.58  fof(f200,plain,(
% 1.47/0.58    ( ! [X0] : (m1_subset_1(sK1,k2_xboole_0(sK2,X0))) ) | ~spl6_11),
% 1.47/0.58    inference(unit_resulting_resolution,[],[f107,f150,f61])).
% 1.47/0.58  fof(f61,plain,(
% 1.47/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 1.47/0.58    inference(cnf_transformation,[],[f27])).
% 1.47/0.58  fof(f27,plain,(
% 1.47/0.58    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.47/0.58    inference(flattening,[],[f26])).
% 1.47/0.58  fof(f26,plain,(
% 1.47/0.58    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.47/0.58    inference(ennf_transformation,[],[f8])).
% 1.47/0.58  fof(f8,axiom,(
% 1.47/0.58    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.47/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 1.47/0.58  fof(f150,plain,(
% 1.47/0.58    r2_hidden(sK1,sK2) | ~spl6_11),
% 1.47/0.58    inference(avatar_component_clause,[],[f148])).
% 1.47/0.58  fof(f114,plain,(
% 1.47/0.58    ~r2_hidden(k2_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1))) | spl6_8),
% 1.47/0.58    inference(avatar_component_clause,[],[f112])).
% 1.47/0.58  fof(f297,plain,(
% 1.47/0.58    v3_pre_topc(k2_xboole_0(sK2,sK3),sK0) | ~spl6_34),
% 1.47/0.58    inference(avatar_component_clause,[],[f295])).
% 1.47/0.58  fof(f86,plain,(
% 1.47/0.58    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl6_4),
% 1.47/0.58    inference(avatar_component_clause,[],[f84])).
% 1.47/0.58  fof(f91,plain,(
% 1.47/0.58    l1_pre_topc(sK0) | ~spl6_5),
% 1.47/0.58    inference(avatar_component_clause,[],[f89])).
% 1.47/0.58  fof(f96,plain,(
% 1.47/0.58    v2_pre_topc(sK0) | ~spl6_6),
% 1.47/0.58    inference(avatar_component_clause,[],[f94])).
% 1.47/0.58  fof(f101,plain,(
% 1.47/0.58    ~v2_struct_0(sK0) | spl6_7),
% 1.47/0.58    inference(avatar_component_clause,[],[f99])).
% 1.47/0.58  fof(f1340,plain,(
% 1.47/0.58    spl6_62 | ~spl6_17 | ~spl6_36),
% 1.47/0.58    inference(avatar_split_clause,[],[f1339,f325,f186,f1043])).
% 1.47/0.58  fof(f1043,plain,(
% 1.47/0.58    spl6_62 <=> r1_tarski(k2_xboole_0(sK2,sK3),u1_struct_0(sK0))),
% 1.47/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).
% 1.47/0.58  fof(f186,plain,(
% 1.47/0.58    spl6_17 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.47/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 1.47/0.58  fof(f325,plain,(
% 1.47/0.58    spl6_36 <=> u1_struct_0(sK0) = k2_xboole_0(sK3,u1_struct_0(sK0))),
% 1.47/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).
% 1.47/0.58  fof(f1339,plain,(
% 1.47/0.58    r1_tarski(k2_xboole_0(sK2,sK3),u1_struct_0(sK0)) | (~spl6_17 | ~spl6_36)),
% 1.47/0.58    inference(superposition,[],[f565,f327])).
% 1.47/0.58  fof(f327,plain,(
% 1.47/0.58    u1_struct_0(sK0) = k2_xboole_0(sK3,u1_struct_0(sK0)) | ~spl6_36),
% 1.47/0.58    inference(avatar_component_clause,[],[f325])).
% 1.47/0.58  fof(f565,plain,(
% 1.47/0.58    ( ! [X0] : (r1_tarski(k2_xboole_0(sK2,X0),k2_xboole_0(X0,u1_struct_0(sK0)))) ) | ~spl6_17),
% 1.47/0.58    inference(superposition,[],[f356,f51])).
% 1.47/0.58  fof(f51,plain,(
% 1.47/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.47/0.58    inference(cnf_transformation,[],[f1])).
% 1.47/0.58  fof(f1,axiom,(
% 1.47/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.47/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.47/0.58  fof(f356,plain,(
% 1.47/0.58    ( ! [X0] : (r1_tarski(k2_xboole_0(sK2,X0),k2_xboole_0(u1_struct_0(sK0),X0))) ) | ~spl6_17),
% 1.47/0.58    inference(unit_resulting_resolution,[],[f188,f130])).
% 1.47/0.58  fof(f130,plain,(
% 1.47/0.58    ( ! [X6,X8,X7] : (~m1_subset_1(X6,k1_zfmisc_1(X8)) | r1_tarski(k2_xboole_0(X6,X7),k2_xboole_0(X8,X7))) )),
% 1.47/0.58    inference(resolution,[],[f49,f62])).
% 1.47/0.58  fof(f62,plain,(
% 1.47/0.58    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.47/0.58    inference(cnf_transformation,[],[f40])).
% 1.47/0.58  fof(f49,plain,(
% 1.47/0.58    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))) )),
% 1.47/0.58    inference(cnf_transformation,[],[f19])).
% 1.47/0.58  fof(f19,plain,(
% 1.47/0.58    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) | ~r1_tarski(X0,X1))),
% 1.47/0.58    inference(ennf_transformation,[],[f4])).
% 1.47/0.58  fof(f4,axiom,(
% 1.47/0.58    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)))),
% 1.47/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_xboole_1)).
% 1.47/0.58  fof(f188,plain,(
% 1.47/0.58    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_17),
% 1.47/0.58    inference(avatar_component_clause,[],[f186])).
% 1.47/0.58  fof(f1047,plain,(
% 1.47/0.58    ~spl6_62 | spl6_45),
% 1.47/0.58    inference(avatar_split_clause,[],[f1035,f440,f1043])).
% 1.47/0.58  fof(f1035,plain,(
% 1.47/0.58    ~r1_tarski(k2_xboole_0(sK2,sK3),u1_struct_0(sK0)) | spl6_45),
% 1.47/0.58    inference(resolution,[],[f442,f63])).
% 1.47/0.58  fof(f442,plain,(
% 1.47/0.58    ~m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) | spl6_45),
% 1.47/0.58    inference(avatar_component_clause,[],[f440])).
% 1.47/0.58  fof(f335,plain,(
% 1.47/0.58    spl6_36 | ~spl6_18),
% 1.47/0.58    inference(avatar_split_clause,[],[f322,f192,f325])).
% 1.47/0.58  fof(f192,plain,(
% 1.47/0.58    spl6_18 <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.47/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 1.47/0.58  fof(f322,plain,(
% 1.47/0.58    u1_struct_0(sK0) = k2_xboole_0(sK3,u1_struct_0(sK0)) | ~spl6_18),
% 1.47/0.58    inference(resolution,[],[f121,f194])).
% 1.47/0.58  fof(f194,plain,(
% 1.47/0.58    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_18),
% 1.47/0.58    inference(avatar_component_clause,[],[f192])).
% 1.47/0.58  fof(f121,plain,(
% 1.47/0.58    ( ! [X4,X5] : (~m1_subset_1(X4,k1_zfmisc_1(X5)) | k2_xboole_0(X4,X5) = X5) )),
% 1.47/0.58    inference(resolution,[],[f50,f62])).
% 1.47/0.58  fof(f50,plain,(
% 1.47/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.47/0.58    inference(cnf_transformation,[],[f20])).
% 1.47/0.58  fof(f20,plain,(
% 1.47/0.58    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.47/0.58    inference(ennf_transformation,[],[f2])).
% 1.47/0.58  fof(f2,axiom,(
% 1.47/0.58    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.47/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.47/0.58  fof(f301,plain,(
% 1.47/0.58    spl6_34 | ~spl6_5 | ~spl6_6 | ~spl6_14 | ~spl6_15 | ~spl6_17 | ~spl6_18),
% 1.47/0.58    inference(avatar_split_clause,[],[f300,f192,f186,f173,f167,f94,f89,f295])).
% 1.47/0.58  fof(f167,plain,(
% 1.47/0.58    spl6_14 <=> v3_pre_topc(sK2,sK0)),
% 1.47/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 1.47/0.58  fof(f173,plain,(
% 1.47/0.58    spl6_15 <=> v3_pre_topc(sK3,sK0)),
% 1.47/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 1.47/0.58  fof(f300,plain,(
% 1.47/0.58    v3_pre_topc(k2_xboole_0(sK2,sK3),sK0) | (~spl6_5 | ~spl6_6 | ~spl6_14 | ~spl6_15 | ~spl6_17 | ~spl6_18)),
% 1.47/0.58    inference(forward_demodulation,[],[f278,f51])).
% 1.47/0.58  fof(f278,plain,(
% 1.47/0.58    v3_pre_topc(k2_xboole_0(sK3,sK2),sK0) | (~spl6_5 | ~spl6_6 | ~spl6_14 | ~spl6_15 | ~spl6_17 | ~spl6_18)),
% 1.47/0.58    inference(unit_resulting_resolution,[],[f96,f91,f175,f169,f188,f194,f48])).
% 1.47/0.58  fof(f48,plain,(
% 1.47/0.58    ( ! [X2,X0,X1] : (~v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k2_xboole_0(X1,X2),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.47/0.58    inference(cnf_transformation,[],[f18])).
% 1.47/0.58  fof(f18,plain,(
% 1.47/0.58    ! [X0,X1,X2] : (v3_pre_topc(k2_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.47/0.58    inference(flattening,[],[f17])).
% 1.47/0.58  fof(f17,plain,(
% 1.47/0.58    ! [X0,X1,X2] : (v3_pre_topc(k2_xboole_0(X1,X2),X0) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.47/0.58    inference(ennf_transformation,[],[f10])).
% 1.47/0.58  fof(f10,axiom,(
% 1.47/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X2,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_xboole_0(X1,X2),X0))),
% 1.47/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_tops_1)).
% 1.47/0.58  fof(f169,plain,(
% 1.47/0.58    v3_pre_topc(sK2,sK0) | ~spl6_14),
% 1.47/0.58    inference(avatar_component_clause,[],[f167])).
% 1.47/0.58  fof(f175,plain,(
% 1.47/0.58    v3_pre_topc(sK3,sK0) | ~spl6_15),
% 1.47/0.58    inference(avatar_component_clause,[],[f173])).
% 1.47/0.58  fof(f208,plain,(
% 1.47/0.58    ~spl6_20 | ~spl6_11),
% 1.47/0.58    inference(avatar_split_clause,[],[f202,f148,f205])).
% 1.47/0.58  fof(f202,plain,(
% 1.47/0.58    ~sP5(sK2) | ~spl6_11),
% 1.47/0.58    inference(unit_resulting_resolution,[],[f150,f67])).
% 1.47/0.58  fof(f67,plain,(
% 1.47/0.58    ( ! [X0,X1] : (~sP5(X1) | ~r2_hidden(X0,X1)) )),
% 1.47/0.58    inference(general_splitting,[],[f60,f66_D])).
% 1.47/0.58  fof(f60,plain,(
% 1.47/0.58    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.47/0.58    inference(cnf_transformation,[],[f25])).
% 1.47/0.58  fof(f25,plain,(
% 1.47/0.58    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.47/0.58    inference(ennf_transformation,[],[f9])).
% 1.47/0.58  fof(f9,axiom,(
% 1.47/0.58    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.47/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 1.47/0.58  fof(f195,plain,(
% 1.47/0.58    spl6_18 | ~spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7 | ~spl6_10),
% 1.47/0.58    inference(avatar_split_clause,[],[f190,f139,f99,f94,f89,f84,f74,f192])).
% 1.47/0.58  fof(f74,plain,(
% 1.47/0.58    spl6_2 <=> m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 1.47/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.47/0.58  fof(f139,plain,(
% 1.47/0.58    spl6_10 <=> sK3 = sK4(sK0,sK1,sK3)),
% 1.47/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 1.47/0.58  fof(f190,plain,(
% 1.47/0.58    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7 | ~spl6_10)),
% 1.47/0.58    inference(forward_demodulation,[],[f181,f141])).
% 1.47/0.58  fof(f141,plain,(
% 1.47/0.58    sK3 = sK4(sK0,sK1,sK3) | ~spl6_10),
% 1.47/0.58    inference(avatar_component_clause,[],[f139])).
% 1.47/0.58  fof(f181,plain,(
% 1.47/0.58    m1_subset_1(sK4(sK0,sK1,sK3),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7)),
% 1.47/0.58    inference(unit_resulting_resolution,[],[f101,f96,f91,f86,f76,f53])).
% 1.47/0.58  fof(f53,plain,(
% 1.47/0.58    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 1.47/0.58    inference(cnf_transformation,[],[f37])).
% 1.47/0.58  fof(f37,plain,(
% 1.47/0.58    ! [X0] : (! [X1] : (! [X2] : ((v3_pre_topc(sK4(X0,X1,X2),X0) & r2_hidden(X1,sK4(X0,X1,X2)) & sK4(X0,X1,X2) = X2 & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.47/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f36])).
% 1.47/0.58  fof(f36,plain,(
% 1.47/0.58    ! [X2,X1,X0] : (? [X3] : (v3_pre_topc(X3,X0) & r2_hidden(X1,X3) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (v3_pre_topc(sK4(X0,X1,X2),X0) & r2_hidden(X1,sK4(X0,X1,X2)) & sK4(X0,X1,X2) = X2 & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.47/0.58    introduced(choice_axiom,[])).
% 1.47/0.58  fof(f22,plain,(
% 1.47/0.58    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (v3_pre_topc(X3,X0) & r2_hidden(X1,X3) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.47/0.58    inference(flattening,[],[f21])).
% 1.47/0.58  fof(f21,plain,(
% 1.47/0.58    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (v3_pre_topc(X3,X0) & r2_hidden(X1,X3) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.47/0.58    inference(ennf_transformation,[],[f11])).
% 1.47/0.58  fof(f11,axiom,(
% 1.47/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ? [X3] : (v3_pre_topc(X3,X0) & r2_hidden(X1,X3) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))))),
% 1.47/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_yellow_6)).
% 1.47/0.58  fof(f76,plain,(
% 1.47/0.58    m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))) | ~spl6_2),
% 1.47/0.58    inference(avatar_component_clause,[],[f74])).
% 1.47/0.58  fof(f189,plain,(
% 1.47/0.58    spl6_17 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7 | ~spl6_9),
% 1.47/0.58    inference(avatar_split_clause,[],[f184,f134,f99,f94,f89,f84,f79,f186])).
% 1.47/0.58  fof(f79,plain,(
% 1.47/0.58    spl6_3 <=> m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 1.47/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.47/0.58  fof(f134,plain,(
% 1.47/0.58    spl6_9 <=> sK2 = sK4(sK0,sK1,sK2)),
% 1.47/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 1.47/0.58  fof(f184,plain,(
% 1.47/0.58    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7 | ~spl6_9)),
% 1.47/0.58    inference(forward_demodulation,[],[f182,f136])).
% 1.47/0.58  fof(f136,plain,(
% 1.47/0.58    sK2 = sK4(sK0,sK1,sK2) | ~spl6_9),
% 1.47/0.58    inference(avatar_component_clause,[],[f134])).
% 1.47/0.58  fof(f182,plain,(
% 1.47/0.58    m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7)),
% 1.47/0.58    inference(unit_resulting_resolution,[],[f101,f96,f91,f86,f81,f53])).
% 1.47/0.58  fof(f81,plain,(
% 1.47/0.58    m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) | ~spl6_3),
% 1.47/0.58    inference(avatar_component_clause,[],[f79])).
% 1.47/0.58  fof(f176,plain,(
% 1.47/0.58    spl6_15 | ~spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7 | ~spl6_10),
% 1.47/0.58    inference(avatar_split_clause,[],[f171,f139,f99,f94,f89,f84,f74,f173])).
% 1.47/0.58  fof(f171,plain,(
% 1.47/0.58    v3_pre_topc(sK3,sK0) | (~spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7 | ~spl6_10)),
% 1.47/0.58    inference(forward_demodulation,[],[f162,f141])).
% 1.47/0.58  fof(f162,plain,(
% 1.47/0.58    v3_pre_topc(sK4(sK0,sK1,sK3),sK0) | (~spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7)),
% 1.47/0.58    inference(unit_resulting_resolution,[],[f101,f96,f91,f86,f76,f56])).
% 1.47/0.58  fof(f56,plain,(
% 1.47/0.58    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v3_pre_topc(sK4(X0,X1,X2),X0)) )),
% 1.47/0.58    inference(cnf_transformation,[],[f37])).
% 1.47/0.58  fof(f170,plain,(
% 1.47/0.58    spl6_14 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7 | ~spl6_9),
% 1.47/0.58    inference(avatar_split_clause,[],[f165,f134,f99,f94,f89,f84,f79,f167])).
% 1.47/0.58  fof(f165,plain,(
% 1.47/0.58    v3_pre_topc(sK2,sK0) | (~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7 | ~spl6_9)),
% 1.47/0.58    inference(forward_demodulation,[],[f163,f136])).
% 1.47/0.58  fof(f163,plain,(
% 1.47/0.58    v3_pre_topc(sK4(sK0,sK1,sK2),sK0) | (~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7)),
% 1.47/0.58    inference(unit_resulting_resolution,[],[f101,f96,f91,f86,f81,f56])).
% 1.47/0.58  fof(f151,plain,(
% 1.47/0.58    spl6_11 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7 | ~spl6_9),
% 1.47/0.58    inference(avatar_split_clause,[],[f146,f134,f99,f94,f89,f84,f79,f148])).
% 1.47/0.58  fof(f146,plain,(
% 1.47/0.58    r2_hidden(sK1,sK2) | (~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7 | ~spl6_9)),
% 1.47/0.58    inference(forward_demodulation,[],[f144,f136])).
% 1.47/0.58  fof(f144,plain,(
% 1.47/0.58    r2_hidden(sK1,sK4(sK0,sK1,sK2)) | (~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7)),
% 1.47/0.58    inference(unit_resulting_resolution,[],[f101,f96,f91,f86,f81,f55])).
% 1.47/0.58  fof(f55,plain,(
% 1.47/0.58    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | r2_hidden(X1,sK4(X0,X1,X2))) )),
% 1.47/0.58    inference(cnf_transformation,[],[f37])).
% 1.47/0.58  fof(f142,plain,(
% 1.47/0.58    spl6_10 | ~spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7),
% 1.47/0.58    inference(avatar_split_clause,[],[f131,f99,f94,f89,f84,f74,f139])).
% 1.47/0.58  fof(f131,plain,(
% 1.47/0.58    sK3 = sK4(sK0,sK1,sK3) | (~spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7)),
% 1.47/0.58    inference(unit_resulting_resolution,[],[f101,f96,f91,f86,f76,f54])).
% 1.47/0.58  fof(f54,plain,(
% 1.47/0.58    ( ! [X2,X0,X1] : (sK4(X0,X1,X2) = X2 | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.47/0.58    inference(cnf_transformation,[],[f37])).
% 1.47/0.58  fof(f137,plain,(
% 1.47/0.58    spl6_9 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7),
% 1.47/0.58    inference(avatar_split_clause,[],[f132,f99,f94,f89,f84,f79,f134])).
% 1.47/0.58  fof(f132,plain,(
% 1.47/0.58    sK2 = sK4(sK0,sK1,sK2) | (~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7)),
% 1.47/0.58    inference(unit_resulting_resolution,[],[f101,f96,f91,f86,f81,f54])).
% 1.47/0.58  fof(f116,plain,(
% 1.47/0.58    ~spl6_8 | spl6_1),
% 1.47/0.58    inference(avatar_split_clause,[],[f110,f69,f112])).
% 1.47/0.58  fof(f69,plain,(
% 1.47/0.58    spl6_1 <=> m1_subset_1(k2_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 1.47/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.47/0.58  fof(f110,plain,(
% 1.47/0.58    ~r2_hidden(k2_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1))) | spl6_1),
% 1.47/0.58    inference(resolution,[],[f71,f65])).
% 1.47/0.58  fof(f65,plain,(
% 1.47/0.58    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 1.47/0.58    inference(cnf_transformation,[],[f30])).
% 1.47/0.58  fof(f30,plain,(
% 1.47/0.58    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.47/0.58    inference(ennf_transformation,[],[f5])).
% 1.47/0.58  fof(f5,axiom,(
% 1.47/0.58    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.47/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 1.47/0.58  fof(f71,plain,(
% 1.47/0.58    ~m1_subset_1(k2_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1))) | spl6_1),
% 1.47/0.58    inference(avatar_component_clause,[],[f69])).
% 1.47/0.58  fof(f102,plain,(
% 1.47/0.58    ~spl6_7),
% 1.47/0.58    inference(avatar_split_clause,[],[f41,f99])).
% 1.47/0.58  fof(f41,plain,(
% 1.47/0.58    ~v2_struct_0(sK0)),
% 1.47/0.58    inference(cnf_transformation,[],[f35])).
% 1.47/0.58  fof(f35,plain,(
% 1.47/0.58    (((~m1_subset_1(k2_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1))) & m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))) & m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.47/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f34,f33,f32,f31])).
% 1.47/0.58  fof(f31,plain,(
% 1.47/0.58    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK0,X1)))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.47/0.58    introduced(choice_axiom,[])).
% 1.47/0.58  fof(f32,plain,(
% 1.47/0.58    ? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK0,X1)))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK0,sK1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK0,sK1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK0,sK1)))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 1.47/0.58    introduced(choice_axiom,[])).
% 1.47/0.58  fof(f33,plain,(
% 1.47/0.58    ? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK0,sK1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK0,sK1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK0,sK1)))) => (? [X3] : (~m1_subset_1(k2_xboole_0(sK2,X3),u1_struct_0(k9_yellow_6(sK0,sK1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK0,sK1)))) & m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))))),
% 1.47/0.58    introduced(choice_axiom,[])).
% 1.47/0.58  fof(f34,plain,(
% 1.47/0.58    ? [X3] : (~m1_subset_1(k2_xboole_0(sK2,X3),u1_struct_0(k9_yellow_6(sK0,sK1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK0,sK1)))) => (~m1_subset_1(k2_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1))) & m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))))),
% 1.47/0.58    introduced(choice_axiom,[])).
% 1.47/0.58  fof(f16,plain,(
% 1.47/0.58    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.47/0.58    inference(flattening,[],[f15])).
% 1.47/0.58  fof(f15,plain,(
% 1.47/0.58    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.47/0.58    inference(ennf_transformation,[],[f14])).
% 1.47/0.58  fof(f14,negated_conjecture,(
% 1.47/0.58    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 1.47/0.58    inference(negated_conjecture,[],[f13])).
% 1.47/0.58  fof(f13,conjecture,(
% 1.47/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 1.47/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_waybel_9)).
% 1.47/0.58  fof(f97,plain,(
% 1.47/0.58    spl6_6),
% 1.47/0.58    inference(avatar_split_clause,[],[f42,f94])).
% 1.47/0.58  fof(f42,plain,(
% 1.47/0.58    v2_pre_topc(sK0)),
% 1.47/0.58    inference(cnf_transformation,[],[f35])).
% 1.47/0.58  fof(f92,plain,(
% 1.47/0.58    spl6_5),
% 1.47/0.58    inference(avatar_split_clause,[],[f43,f89])).
% 1.47/0.58  fof(f43,plain,(
% 1.47/0.58    l1_pre_topc(sK0)),
% 1.47/0.58    inference(cnf_transformation,[],[f35])).
% 1.47/0.58  fof(f87,plain,(
% 1.47/0.58    spl6_4),
% 1.47/0.58    inference(avatar_split_clause,[],[f44,f84])).
% 1.47/0.58  fof(f44,plain,(
% 1.47/0.58    m1_subset_1(sK1,u1_struct_0(sK0))),
% 1.47/0.58    inference(cnf_transformation,[],[f35])).
% 1.47/0.58  fof(f82,plain,(
% 1.47/0.58    spl6_3),
% 1.47/0.58    inference(avatar_split_clause,[],[f45,f79])).
% 1.47/0.58  fof(f45,plain,(
% 1.47/0.58    m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 1.47/0.58    inference(cnf_transformation,[],[f35])).
% 1.47/0.58  fof(f77,plain,(
% 1.47/0.58    spl6_2),
% 1.47/0.58    inference(avatar_split_clause,[],[f46,f74])).
% 1.47/0.58  fof(f46,plain,(
% 1.47/0.58    m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 1.47/0.58    inference(cnf_transformation,[],[f35])).
% 1.47/0.58  fof(f72,plain,(
% 1.47/0.58    ~spl6_1),
% 1.47/0.58    inference(avatar_split_clause,[],[f47,f69])).
% 1.47/0.58  fof(f47,plain,(
% 1.47/0.58    ~m1_subset_1(k2_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 1.47/0.58    inference(cnf_transformation,[],[f35])).
% 1.47/0.58  % SZS output end Proof for theBenchmark
% 1.47/0.58  % (8385)------------------------------
% 1.47/0.58  % (8385)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.58  % (8385)Termination reason: Refutation
% 1.47/0.58  
% 1.47/0.58  % (8385)Memory used [KB]: 11513
% 1.47/0.58  % (8385)Time elapsed: 0.143 s
% 1.47/0.58  % (8385)------------------------------
% 1.47/0.58  % (8385)------------------------------
% 1.47/0.59  % (8378)Success in time 0.214 s
%------------------------------------------------------------------------------
