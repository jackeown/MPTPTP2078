%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1383+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:20 EST 2020

% Result     : Theorem 3.43s
% Output     : Refutation 3.43s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 379 expanded)
%              Number of leaves         :   31 ( 163 expanded)
%              Depth                    :   10
%              Number of atoms          :  718 (2845 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6686,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f3993,f3998,f4003,f4008,f4013,f4037,f4042,f4047,f4057,f4061,f4494,f4873,f4891,f4896,f5046,f5081,f5455,f6672])).

fof(f6672,plain,
    ( ~ spl126_5
    | ~ spl126_11
    | ~ spl126_39
    | spl126_67 ),
    inference(avatar_contradiction_clause,[],[f6671])).

fof(f6671,plain,
    ( $false
    | ~ spl126_5
    | ~ spl126_11
    | ~ spl126_39
    | spl126_67 ),
    inference(subsumption_resolution,[],[f6670,f4413])).

fof(f4413,plain,
    ( m1_connsp_2(sK3,sK0,sK1)
    | ~ spl126_39 ),
    inference(avatar_component_clause,[],[f4412])).

fof(f4412,plain,
    ( spl126_39
  <=> m1_connsp_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl126_39])])).

fof(f6670,plain,
    ( ~ m1_connsp_2(sK3,sK0,sK1)
    | ~ spl126_5
    | ~ spl126_11
    | spl126_67 ),
    inference(forward_demodulation,[],[f6660,f5554])).

fof(f5554,plain,
    ( sK3 = k3_xboole_0(sK3,sK2)
    | ~ spl126_11 ),
    inference(unit_resulting_resolution,[],[f4041,f3386])).

fof(f3386,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f2637])).

fof(f2637,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f86])).

fof(f86,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f4041,plain,
    ( r1_tarski(sK3,sK2)
    | ~ spl126_11 ),
    inference(avatar_component_clause,[],[f4039])).

fof(f4039,plain,
    ( spl126_11
  <=> r1_tarski(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl126_11])])).

fof(f6660,plain,
    ( ~ m1_connsp_2(k3_xboole_0(sK3,sK2),sK0,sK1)
    | ~ spl126_5
    | spl126_67 ),
    inference(backward_demodulation,[],[f5454,f6599])).

fof(f6599,plain,
    ( ! [X0] : k3_xboole_0(X0,sK2) = k9_subset_1(u1_struct_0(sK0),X0,sK2)
    | ~ spl126_5 ),
    inference(unit_resulting_resolution,[],[f4012,f3463])).

fof(f3463,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f2665])).

fof(f2665,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f496])).

fof(f496,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f4012,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl126_5 ),
    inference(avatar_component_clause,[],[f4010])).

fof(f4010,plain,
    ( spl126_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl126_5])])).

fof(f5454,plain,
    ( ~ m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK3,sK2),sK0,sK1)
    | spl126_67 ),
    inference(avatar_component_clause,[],[f5452])).

fof(f5452,plain,
    ( spl126_67
  <=> m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK3,sK2),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl126_67])])).

fof(f5455,plain,
    ( ~ spl126_67
    | spl126_1
    | ~ spl126_2
    | ~ spl126_3
    | ~ spl126_4
    | ~ spl126_5
    | spl126_9
    | ~ spl126_14 ),
    inference(avatar_split_clause,[],[f5130,f4054,f4030,f4010,f4005,f4000,f3995,f3990,f5452])).

fof(f3990,plain,
    ( spl126_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl126_1])])).

fof(f3995,plain,
    ( spl126_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl126_2])])).

fof(f4000,plain,
    ( spl126_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl126_3])])).

fof(f4005,plain,
    ( spl126_4
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl126_4])])).

fof(f4030,plain,
    ( spl126_9
  <=> m1_connsp_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl126_9])])).

fof(f4054,plain,
    ( spl126_14
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl126_14])])).

fof(f5130,plain,
    ( ~ m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK3,sK2),sK0,sK1)
    | spl126_1
    | ~ spl126_2
    | ~ spl126_3
    | ~ spl126_4
    | ~ spl126_5
    | spl126_9
    | ~ spl126_14 ),
    inference(unit_resulting_resolution,[],[f3992,f3997,f4002,f4007,f4056,f4012,f4031,f3292])).

fof(f3292,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | m1_connsp_2(X3,X0,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3021])).

fof(f3021,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( ( m1_connsp_2(X3,X0,X1)
                        & m1_connsp_2(X2,X0,X1) )
                      | ~ m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1) )
                    & ( m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
                      | ~ m1_connsp_2(X3,X0,X1)
                      | ~ m1_connsp_2(X2,X0,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3020])).

fof(f3020,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( ( m1_connsp_2(X3,X0,X1)
                        & m1_connsp_2(X2,X0,X1) )
                      | ~ m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1) )
                    & ( m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
                      | ~ m1_connsp_2(X3,X0,X1)
                      | ~ m1_connsp_2(X2,X0,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f2582])).

fof(f2582,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( m1_connsp_2(X3,X0,X1)
                      & m1_connsp_2(X2,X0,X1) )
                  <=> m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2581])).

fof(f2581,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( m1_connsp_2(X3,X0,X1)
                      & m1_connsp_2(X2,X0,X1) )
                  <=> m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2519])).

fof(f2519,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( m1_connsp_2(X3,X0,X1)
                      & m1_connsp_2(X2,X0,X1) )
                  <=> m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_connsp_2)).

fof(f4031,plain,
    ( ~ m1_connsp_2(sK2,sK0,sK1)
    | spl126_9 ),
    inference(avatar_component_clause,[],[f4030])).

fof(f4056,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl126_14 ),
    inference(avatar_component_clause,[],[f4054])).

fof(f4007,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl126_4 ),
    inference(avatar_component_clause,[],[f4005])).

fof(f4002,plain,
    ( l1_pre_topc(sK0)
    | ~ spl126_3 ),
    inference(avatar_component_clause,[],[f4000])).

fof(f3997,plain,
    ( v2_pre_topc(sK0)
    | ~ spl126_2 ),
    inference(avatar_component_clause,[],[f3995])).

fof(f3992,plain,
    ( ~ v2_struct_0(sK0)
    | spl126_1 ),
    inference(avatar_component_clause,[],[f3990])).

fof(f5081,plain,
    ( spl126_1
    | ~ spl126_2
    | ~ spl126_3
    | ~ spl126_4
    | ~ spl126_15
    | ~ spl126_48
    | ~ spl126_49
    | ~ spl126_50
    | ~ spl126_57 ),
    inference(avatar_contradiction_clause,[],[f5080])).

fof(f5080,plain,
    ( $false
    | spl126_1
    | ~ spl126_2
    | ~ spl126_3
    | ~ spl126_4
    | ~ spl126_15
    | ~ spl126_48
    | ~ spl126_49
    | ~ spl126_50
    | ~ spl126_57 ),
    inference(subsumption_resolution,[],[f5047,f4903])).

fof(f4903,plain,
    ( r2_hidden(sK1,sK19(sK0,sK1,sK2))
    | spl126_1
    | ~ spl126_2
    | ~ spl126_3
    | ~ spl126_4
    | ~ spl126_50 ),
    inference(unit_resulting_resolution,[],[f3992,f3997,f4002,f4007,f4895,f3944])).

fof(f3944,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_connsp_2(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | r2_hidden(X2,X1)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f3289,f3287])).

fof(f3287,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2576])).

fof(f2576,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2575])).

fof(f2575,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2515])).

fof(f2515,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).

fof(f3289,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ m1_connsp_2(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2580])).

fof(f2580,plain,(
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
    inference(flattening,[],[f2579])).

fof(f2579,plain,(
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
    inference(ennf_transformation,[],[f2521])).

fof(f2521,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_connsp_2)).

fof(f4895,plain,
    ( m1_connsp_2(sK19(sK0,sK1,sK2),sK0,sK1)
    | ~ spl126_50 ),
    inference(avatar_component_clause,[],[f4893])).

fof(f4893,plain,
    ( spl126_50
  <=> m1_connsp_2(sK19(sK0,sK1,sK2),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl126_50])])).

fof(f5047,plain,
    ( ~ r2_hidden(sK1,sK19(sK0,sK1,sK2))
    | ~ spl126_15
    | ~ spl126_48
    | ~ spl126_49
    | ~ spl126_57 ),
    inference(unit_resulting_resolution,[],[f4890,f4872,f5045,f4060])).

fof(f4060,plain,
    ( ! [X3] :
        ( ~ r1_tarski(X3,sK2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X3,sK0)
        | ~ r2_hidden(sK1,X3) )
    | ~ spl126_15 ),
    inference(avatar_component_clause,[],[f4059])).

fof(f4059,plain,
    ( spl126_15
  <=> ! [X3] :
        ( ~ r2_hidden(sK1,X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X3,sK0)
        | ~ r1_tarski(X3,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl126_15])])).

fof(f5045,plain,
    ( m1_subset_1(sK19(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl126_57 ),
    inference(avatar_component_clause,[],[f5043])).

fof(f5043,plain,
    ( spl126_57
  <=> m1_subset_1(sK19(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl126_57])])).

fof(f4872,plain,
    ( r1_tarski(sK19(sK0,sK1,sK2),sK2)
    | ~ spl126_48 ),
    inference(avatar_component_clause,[],[f4870])).

fof(f4870,plain,
    ( spl126_48
  <=> r1_tarski(sK19(sK0,sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl126_48])])).

fof(f4890,plain,
    ( v3_pre_topc(sK19(sK0,sK1,sK2),sK0)
    | ~ spl126_49 ),
    inference(avatar_component_clause,[],[f4888])).

fof(f4888,plain,
    ( spl126_49
  <=> v3_pre_topc(sK19(sK0,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl126_49])])).

fof(f5046,plain,
    ( spl126_57
    | spl126_1
    | ~ spl126_2
    | ~ spl126_3
    | ~ spl126_4
    | ~ spl126_9 ),
    inference(avatar_split_clause,[],[f4518,f4030,f4005,f4000,f3995,f3990,f5043])).

fof(f4518,plain,
    ( m1_subset_1(sK19(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl126_1
    | ~ spl126_2
    | ~ spl126_3
    | ~ spl126_4
    | ~ spl126_9 ),
    inference(unit_resulting_resolution,[],[f3992,f3997,f4002,f4007,f4032,f3952])).

fof(f3952,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(sK19(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f3295,f3287])).

fof(f3295,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK19(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3023])).

fof(f3023,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(sK19(X0,X1,X2),X2)
                & v3_pre_topc(sK19(X0,X1,X2),X0)
                & m1_connsp_2(sK19(X0,X1,X2),X0,X1)
                & m1_subset_1(sK19(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                & ~ v1_xboole_0(sK19(X0,X1,X2)) )
              | ~ m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK19])],[f2586,f3022])).

fof(f3022,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r1_tarski(X3,X2)
          & v3_pre_topc(X3,X0)
          & m1_connsp_2(X3,X0,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X3) )
     => ( r1_tarski(sK19(X0,X1,X2),X2)
        & v3_pre_topc(sK19(X0,X1,X2),X0)
        & m1_connsp_2(sK19(X0,X1,X2),X0,X1)
        & m1_subset_1(sK19(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(sK19(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f2586,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r1_tarski(X3,X2)
                  & v3_pre_topc(X3,X0)
                  & m1_connsp_2(X3,X0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  & ~ v1_xboole_0(X3) )
              | ~ m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2585])).

fof(f2585,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r1_tarski(X3,X2)
                  & v3_pre_topc(X3,X0)
                  & m1_connsp_2(X3,X0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  & ~ v1_xboole_0(X3) )
              | ~ m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2522])).

fof(f2522,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ~ ( ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                        & ~ v1_xboole_0(X3) )
                     => ~ ( r1_tarski(X3,X2)
                          & v3_pre_topc(X3,X0)
                          & m1_connsp_2(X3,X0,X1) ) )
                  & m1_connsp_2(X2,X0,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_connsp_2)).

fof(f4032,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ spl126_9 ),
    inference(avatar_component_clause,[],[f4030])).

fof(f4896,plain,
    ( spl126_50
    | spl126_1
    | ~ spl126_2
    | ~ spl126_3
    | ~ spl126_4
    | ~ spl126_9 ),
    inference(avatar_split_clause,[],[f4517,f4030,f4005,f4000,f3995,f3990,f4893])).

fof(f4517,plain,
    ( m1_connsp_2(sK19(sK0,sK1,sK2),sK0,sK1)
    | spl126_1
    | ~ spl126_2
    | ~ spl126_3
    | ~ spl126_4
    | ~ spl126_9 ),
    inference(unit_resulting_resolution,[],[f3992,f3997,f4002,f4007,f4032,f3951])).

fof(f3951,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(sK19(X0,X1,X2),X0,X1)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f3296,f3287])).

fof(f3296,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(sK19(X0,X1,X2),X0,X1)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3023])).

fof(f4891,plain,
    ( spl126_49
    | spl126_1
    | ~ spl126_2
    | ~ spl126_3
    | ~ spl126_4
    | ~ spl126_9 ),
    inference(avatar_split_clause,[],[f4516,f4030,f4005,f4000,f3995,f3990,f4888])).

fof(f4516,plain,
    ( v3_pre_topc(sK19(sK0,sK1,sK2),sK0)
    | spl126_1
    | ~ spl126_2
    | ~ spl126_3
    | ~ spl126_4
    | ~ spl126_9 ),
    inference(unit_resulting_resolution,[],[f3992,f3997,f4002,f4007,f4032,f3950])).

fof(f3950,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(sK19(X0,X1,X2),X0)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f3297,f3287])).

fof(f3297,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(sK19(X0,X1,X2),X0)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3023])).

fof(f4873,plain,
    ( spl126_48
    | spl126_1
    | ~ spl126_2
    | ~ spl126_3
    | ~ spl126_4
    | ~ spl126_9 ),
    inference(avatar_split_clause,[],[f4515,f4030,f4005,f4000,f3995,f3990,f4870])).

fof(f4515,plain,
    ( r1_tarski(sK19(sK0,sK1,sK2),sK2)
    | spl126_1
    | ~ spl126_2
    | ~ spl126_3
    | ~ spl126_4
    | ~ spl126_9 ),
    inference(unit_resulting_resolution,[],[f3992,f3997,f4002,f4007,f4032,f3949])).

fof(f3949,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | r1_tarski(sK19(X0,X1,X2),X2)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f3298,f3287])).

fof(f3298,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(sK19(X0,X1,X2),X2)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3023])).

fof(f4494,plain,
    ( spl126_1
    | ~ spl126_2
    | ~ spl126_3
    | ~ spl126_10
    | ~ spl126_12
    | ~ spl126_14
    | spl126_39 ),
    inference(avatar_contradiction_clause,[],[f4493])).

fof(f4493,plain,
    ( $false
    | spl126_1
    | ~ spl126_2
    | ~ spl126_3
    | ~ spl126_10
    | ~ spl126_12
    | ~ spl126_14
    | spl126_39 ),
    inference(subsumption_resolution,[],[f4492,f4056])).

fof(f4492,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl126_1
    | ~ spl126_2
    | ~ spl126_3
    | ~ spl126_10
    | ~ spl126_12
    | spl126_39 ),
    inference(unit_resulting_resolution,[],[f3992,f3997,f4002,f4036,f4414,f4046,f3943])).

fof(f3943,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ r2_hidden(X2,X1)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | m1_connsp_2(X1,X0,X2)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f3288,f3233])).

fof(f3233,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f2540])).

fof(f2540,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f2539])).

fof(f2539,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f618])).

fof(f618,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f3288,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X1,X0,X2)
      | ~ r2_hidden(X2,X1)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2578])).

fof(f2578,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2577])).

fof(f2577,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2520])).

fof(f2520,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r2_hidden(X2,X1)
                  & v3_pre_topc(X1,X0) )
               => m1_connsp_2(X1,X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_connsp_2)).

fof(f4046,plain,
    ( r2_hidden(sK1,sK3)
    | ~ spl126_12 ),
    inference(avatar_component_clause,[],[f4044])).

fof(f4044,plain,
    ( spl126_12
  <=> r2_hidden(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl126_12])])).

fof(f4414,plain,
    ( ~ m1_connsp_2(sK3,sK0,sK1)
    | spl126_39 ),
    inference(avatar_component_clause,[],[f4412])).

fof(f4036,plain,
    ( v3_pre_topc(sK3,sK0)
    | ~ spl126_10 ),
    inference(avatar_component_clause,[],[f4034])).

fof(f4034,plain,
    ( spl126_10
  <=> v3_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl126_10])])).

fof(f4061,plain,
    ( ~ spl126_9
    | spl126_15 ),
    inference(avatar_split_clause,[],[f3228,f4059,f4030])).

fof(f3228,plain,(
    ! [X3] :
      ( ~ r2_hidden(sK1,X3)
      | ~ r1_tarski(X3,sK2)
      | ~ v3_pre_topc(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_connsp_2(sK2,sK0,sK1) ) ),
    inference(cnf_transformation,[],[f2977])).

fof(f2977,plain,
    ( ( ! [X3] :
          ( ~ r2_hidden(sK1,X3)
          | ~ r1_tarski(X3,sK2)
          | ~ v3_pre_topc(X3,sK0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
      | ~ m1_connsp_2(sK2,sK0,sK1) )
    & ( ( r2_hidden(sK1,sK3)
        & r1_tarski(sK3,sK2)
        & v3_pre_topc(sK3,sK0)
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) )
      | m1_connsp_2(sK2,sK0,sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f2972,f2976,f2975,f2974,f2973])).

fof(f2973,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ! [X3] :
                      ( ~ r2_hidden(X1,X3)
                      | ~ r1_tarski(X3,X2)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_connsp_2(X2,X0,X1) )
                & ( ? [X4] :
                      ( r2_hidden(X1,X4)
                      & r1_tarski(X4,X2)
                      & v3_pre_topc(X4,X0)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | m1_connsp_2(X2,X0,X1) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( ~ r2_hidden(X1,X3)
                    | ~ r1_tarski(X3,X2)
                    | ~ v3_pre_topc(X3,sK0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
                | ~ m1_connsp_2(X2,sK0,X1) )
              & ( ? [X4] :
                    ( r2_hidden(X1,X4)
                    & r1_tarski(X4,X2)
                    & v3_pre_topc(X4,sK0)
                    & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
                | m1_connsp_2(X2,sK0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f2974,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X1,X3)
                  | ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,sK0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
              | ~ m1_connsp_2(X2,sK0,X1) )
            & ( ? [X4] :
                  ( r2_hidden(X1,X4)
                  & r1_tarski(X4,X2)
                  & v3_pre_topc(X4,sK0)
                  & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
              | m1_connsp_2(X2,sK0,X1) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(sK1,X3)
                | ~ r1_tarski(X3,X2)
                | ~ v3_pre_topc(X3,sK0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
            | ~ m1_connsp_2(X2,sK0,sK1) )
          & ( ? [X4] :
                ( r2_hidden(sK1,X4)
                & r1_tarski(X4,X2)
                & v3_pre_topc(X4,sK0)
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
            | m1_connsp_2(X2,sK0,sK1) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f2975,plain,
    ( ? [X2] :
        ( ( ! [X3] :
              ( ~ r2_hidden(sK1,X3)
              | ~ r1_tarski(X3,X2)
              | ~ v3_pre_topc(X3,sK0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
          | ~ m1_connsp_2(X2,sK0,sK1) )
        & ( ? [X4] :
              ( r2_hidden(sK1,X4)
              & r1_tarski(X4,X2)
              & v3_pre_topc(X4,sK0)
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
          | m1_connsp_2(X2,sK0,sK1) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ! [X3] :
            ( ~ r2_hidden(sK1,X3)
            | ~ r1_tarski(X3,sK2)
            | ~ v3_pre_topc(X3,sK0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
        | ~ m1_connsp_2(sK2,sK0,sK1) )
      & ( ? [X4] :
            ( r2_hidden(sK1,X4)
            & r1_tarski(X4,sK2)
            & v3_pre_topc(X4,sK0)
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
        | m1_connsp_2(sK2,sK0,sK1) )
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f2976,plain,
    ( ? [X4] :
        ( r2_hidden(sK1,X4)
        & r1_tarski(X4,sK2)
        & v3_pre_topc(X4,sK0)
        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( r2_hidden(sK1,sK3)
      & r1_tarski(sK3,sK2)
      & v3_pre_topc(sK3,sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f2972,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( ~ r2_hidden(X1,X3)
                    | ~ r1_tarski(X3,X2)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ m1_connsp_2(X2,X0,X1) )
              & ( ? [X4] :
                    ( r2_hidden(X1,X4)
                    & r1_tarski(X4,X2)
                    & v3_pre_topc(X4,X0)
                    & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                | m1_connsp_2(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f2971])).

fof(f2971,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( ~ r2_hidden(X1,X3)
                    | ~ r1_tarski(X3,X2)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ m1_connsp_2(X2,X0,X1) )
              & ( ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | m1_connsp_2(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f2970])).

fof(f2970,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( ~ r2_hidden(X1,X3)
                    | ~ r1_tarski(X3,X2)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ m1_connsp_2(X2,X0,X1) )
              & ( ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | m1_connsp_2(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f2534])).

fof(f2534,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <~> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f2533])).

fof(f2533,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <~> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2524])).

fof(f2524,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( m1_connsp_2(X2,X0,X1)
                <=> ? [X3] :
                      ( r2_hidden(X1,X3)
                      & r1_tarski(X3,X2)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f2523])).

fof(f2523,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_connsp_2)).

fof(f4057,plain,
    ( spl126_9
    | spl126_14 ),
    inference(avatar_split_clause,[],[f3224,f4054,f4030])).

fof(f3224,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f2977])).

fof(f4047,plain,
    ( spl126_9
    | spl126_12 ),
    inference(avatar_split_clause,[],[f3227,f4044,f4030])).

fof(f3227,plain,
    ( r2_hidden(sK1,sK3)
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f2977])).

fof(f4042,plain,
    ( spl126_9
    | spl126_11 ),
    inference(avatar_split_clause,[],[f3226,f4039,f4030])).

fof(f3226,plain,
    ( r1_tarski(sK3,sK2)
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f2977])).

fof(f4037,plain,
    ( spl126_9
    | spl126_10 ),
    inference(avatar_split_clause,[],[f3225,f4034,f4030])).

fof(f3225,plain,
    ( v3_pre_topc(sK3,sK0)
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f2977])).

fof(f4013,plain,(
    spl126_5 ),
    inference(avatar_split_clause,[],[f3223,f4010])).

fof(f3223,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f2977])).

fof(f4008,plain,(
    spl126_4 ),
    inference(avatar_split_clause,[],[f3222,f4005])).

fof(f3222,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f2977])).

fof(f4003,plain,(
    spl126_3 ),
    inference(avatar_split_clause,[],[f3221,f4000])).

fof(f3221,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f2977])).

fof(f3998,plain,(
    spl126_2 ),
    inference(avatar_split_clause,[],[f3220,f3995])).

fof(f3220,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f2977])).

fof(f3993,plain,(
    ~ spl126_1 ),
    inference(avatar_split_clause,[],[f3219,f3990])).

fof(f3219,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f2977])).
%------------------------------------------------------------------------------
