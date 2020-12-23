%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1732+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:31 EST 2020

% Result     : Theorem 5.27s
% Output     : Refutation 5.27s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 479 expanded)
%              Number of leaves         :   31 ( 223 expanded)
%              Depth                    :    7
%              Number of atoms          :  763 (3513 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6623,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f5248,f5253,f5258,f5263,f5268,f5273,f5278,f5283,f5288,f5293,f5302,f5326,f5363,f5431,f5446,f5695,f6039,f6348,f6500,f6502,f6541,f6616,f6622])).

fof(f6622,plain,
    ( spl205_1
    | ~ spl205_2
    | ~ spl205_3
    | spl205_6
    | ~ spl205_9
    | spl205_11
    | ~ spl205_12
    | ~ spl205_46
    | spl205_64
    | ~ spl205_81 ),
    inference(avatar_contradiction_clause,[],[f6621])).

fof(f6621,plain,
    ( $false
    | spl205_1
    | ~ spl205_2
    | ~ spl205_3
    | spl205_6
    | ~ spl205_9
    | spl205_11
    | ~ spl205_12
    | ~ spl205_46
    | spl205_64
    | ~ spl205_81 ),
    inference(subsumption_resolution,[],[f5300,f6468])).

fof(f6468,plain,
    ( ~ r1_tsep_1(sK3,k2_tsep_1(sK0,sK1,sK2))
    | spl205_1
    | ~ spl205_2
    | ~ spl205_3
    | spl205_6
    | ~ spl205_9
    | spl205_11
    | ~ spl205_46
    | spl205_64
    | ~ spl205_81 ),
    inference(unit_resulting_resolution,[],[f5247,f5252,f5257,f5272,f5272,f5694,f5287,f5287,f6038,f5297,f6347,f4206])).

fof(f4206,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | r1_tsep_1(X3,X1)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ r1_tsep_1(X2,X3)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3440])).

fof(f3440,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ~ r1_tsep_1(X3,X2)
                    & ~ r1_tsep_1(X2,X3) )
                  | ( r1_tsep_1(X3,X1)
                    & r1_tsep_1(X1,X3) )
                  | ~ m1_pre_topc(X1,X2)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3439])).

fof(f3439,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ~ r1_tsep_1(X3,X2)
                    & ~ r1_tsep_1(X2,X3) )
                  | ( r1_tsep_1(X3,X1)
                    & r1_tsep_1(X1,X3) )
                  | ~ m1_pre_topc(X1,X2)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3358])).

fof(f3358,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( m1_pre_topc(X1,X2)
                   => ( ( ~ r1_tsep_1(X3,X2)
                        & ~ r1_tsep_1(X2,X3) )
                      | ( r1_tsep_1(X3,X1)
                        & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tmap_1)).

fof(f6347,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | ~ spl205_81 ),
    inference(avatar_component_clause,[],[f6345])).

fof(f6345,plain,
    ( spl205_81
  <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl205_81])])).

fof(f5297,plain,
    ( ~ r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3)
    | spl205_11 ),
    inference(avatar_component_clause,[],[f5295])).

fof(f5295,plain,
    ( spl205_11
  <=> r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl205_11])])).

fof(f6038,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | spl205_64 ),
    inference(avatar_component_clause,[],[f6036])).

fof(f6036,plain,
    ( spl205_64
  <=> v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl205_64])])).

fof(f5287,plain,
    ( m1_pre_topc(sK3,sK0)
    | ~ spl205_9 ),
    inference(avatar_component_clause,[],[f5285])).

fof(f5285,plain,
    ( spl205_9
  <=> m1_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl205_9])])).

fof(f5694,plain,
    ( m1_pre_topc(sK3,sK3)
    | ~ spl205_46 ),
    inference(avatar_component_clause,[],[f5692])).

fof(f5692,plain,
    ( spl205_46
  <=> m1_pre_topc(sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl205_46])])).

fof(f5272,plain,
    ( ~ v2_struct_0(sK3)
    | spl205_6 ),
    inference(avatar_component_clause,[],[f5270])).

fof(f5270,plain,
    ( spl205_6
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl205_6])])).

fof(f5257,plain,
    ( l1_pre_topc(sK0)
    | ~ spl205_3 ),
    inference(avatar_component_clause,[],[f5255])).

fof(f5255,plain,
    ( spl205_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl205_3])])).

fof(f5252,plain,
    ( v2_pre_topc(sK0)
    | ~ spl205_2 ),
    inference(avatar_component_clause,[],[f5250])).

fof(f5250,plain,
    ( spl205_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl205_2])])).

fof(f5247,plain,
    ( ~ v2_struct_0(sK0)
    | spl205_1 ),
    inference(avatar_component_clause,[],[f5245])).

fof(f5245,plain,
    ( spl205_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl205_1])])).

fof(f5300,plain,
    ( r1_tsep_1(sK3,k2_tsep_1(sK0,sK1,sK2))
    | ~ spl205_12 ),
    inference(avatar_component_clause,[],[f5299])).

fof(f5299,plain,
    ( spl205_12
  <=> r1_tsep_1(sK3,k2_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl205_12])])).

fof(f6616,plain,
    ( spl205_1
    | ~ spl205_2
    | ~ spl205_3
    | spl205_4
    | spl205_5
    | spl205_6
    | ~ spl205_7
    | ~ spl205_8
    | ~ spl205_9
    | spl205_10
    | spl205_12
    | ~ spl205_15
    | spl205_64
    | ~ spl205_81 ),
    inference(avatar_contradiction_clause,[],[f6615])).

fof(f6615,plain,
    ( $false
    | spl205_1
    | ~ spl205_2
    | ~ spl205_3
    | spl205_4
    | spl205_5
    | spl205_6
    | ~ spl205_7
    | ~ spl205_8
    | ~ spl205_9
    | spl205_10
    | spl205_12
    | ~ spl205_15
    | spl205_64
    | ~ spl205_81 ),
    inference(subsumption_resolution,[],[f6608,f5413])).

fof(f5413,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK2)
    | spl205_1
    | ~ spl205_2
    | ~ spl205_3
    | spl205_4
    | spl205_5
    | ~ spl205_7
    | ~ spl205_8
    | spl205_10 ),
    inference(unit_resulting_resolution,[],[f5247,f5252,f5257,f5262,f5267,f5277,f5282,f5292,f4200])).

fof(f4200,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X2)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3432])).

fof(f3432,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X2)
                & m1_pre_topc(k2_tsep_1(X0,X1,X2),X1) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3431])).

fof(f3431,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X2)
                & m1_pre_topc(k2_tsep_1(X0,X1,X2),X1) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3369])).

fof(f3369,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( ~ r1_tsep_1(X1,X2)
               => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X2)
                  & m1_pre_topc(k2_tsep_1(X0,X1,X2),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_tsep_1)).

fof(f5292,plain,
    ( ~ r1_tsep_1(sK1,sK2)
    | spl205_10 ),
    inference(avatar_component_clause,[],[f5290])).

fof(f5290,plain,
    ( spl205_10
  <=> r1_tsep_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl205_10])])).

fof(f5282,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl205_8 ),
    inference(avatar_component_clause,[],[f5280])).

fof(f5280,plain,
    ( spl205_8
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl205_8])])).

fof(f5277,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl205_7 ),
    inference(avatar_component_clause,[],[f5275])).

fof(f5275,plain,
    ( spl205_7
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl205_7])])).

fof(f5267,plain,
    ( ~ v2_struct_0(sK2)
    | spl205_5 ),
    inference(avatar_component_clause,[],[f5265])).

fof(f5265,plain,
    ( spl205_5
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl205_5])])).

fof(f5262,plain,
    ( ~ v2_struct_0(sK1)
    | spl205_4 ),
    inference(avatar_component_clause,[],[f5260])).

fof(f5260,plain,
    ( spl205_4
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl205_4])])).

fof(f6608,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK2)
    | spl205_1
    | ~ spl205_2
    | ~ spl205_3
    | spl205_5
    | spl205_6
    | ~ spl205_8
    | ~ spl205_9
    | spl205_12
    | ~ spl205_15
    | spl205_64
    | ~ spl205_81 ),
    inference(unit_resulting_resolution,[],[f5247,f5252,f5257,f5272,f5267,f5287,f5282,f6038,f6347,f5301,f5315,f4206])).

fof(f5315,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ spl205_15 ),
    inference(avatar_component_clause,[],[f5313])).

fof(f5313,plain,
    ( spl205_15
  <=> r1_tsep_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl205_15])])).

fof(f5301,plain,
    ( ~ r1_tsep_1(sK3,k2_tsep_1(sK0,sK1,sK2))
    | spl205_12 ),
    inference(avatar_component_clause,[],[f5299])).

fof(f6541,plain,
    ( spl205_1
    | ~ spl205_2
    | ~ spl205_3
    | spl205_5
    | spl205_6
    | ~ spl205_8
    | ~ spl205_9
    | spl205_15
    | ~ spl205_17
    | ~ spl205_46 ),
    inference(avatar_contradiction_clause,[],[f6540])).

fof(f6540,plain,
    ( $false
    | spl205_1
    | ~ spl205_2
    | ~ spl205_3
    | spl205_5
    | spl205_6
    | ~ spl205_8
    | ~ spl205_9
    | spl205_15
    | ~ spl205_17
    | ~ spl205_46 ),
    inference(subsumption_resolution,[],[f5324,f6101])).

fof(f6101,plain,
    ( ~ r1_tsep_1(sK3,sK2)
    | spl205_1
    | ~ spl205_2
    | ~ spl205_3
    | spl205_5
    | spl205_6
    | ~ spl205_8
    | ~ spl205_9
    | spl205_15
    | ~ spl205_46 ),
    inference(unit_resulting_resolution,[],[f5247,f5252,f5257,f5272,f5267,f5272,f5287,f5287,f5282,f5314,f5694,f4206])).

fof(f5314,plain,
    ( ~ r1_tsep_1(sK2,sK3)
    | spl205_15 ),
    inference(avatar_component_clause,[],[f5313])).

fof(f5324,plain,
    ( r1_tsep_1(sK3,sK2)
    | ~ spl205_17 ),
    inference(avatar_component_clause,[],[f5322])).

fof(f5322,plain,
    ( spl205_17
  <=> r1_tsep_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl205_17])])).

fof(f6502,plain,
    ( spl205_1
    | ~ spl205_2
    | ~ spl205_3
    | spl205_4
    | spl205_5
    | spl205_6
    | ~ spl205_7
    | ~ spl205_8
    | ~ spl205_9
    | spl205_10
    | spl205_11
    | ~ spl205_16
    | spl205_64
    | ~ spl205_81 ),
    inference(avatar_contradiction_clause,[],[f6501])).

fof(f6501,plain,
    ( $false
    | spl205_1
    | ~ spl205_2
    | ~ spl205_3
    | spl205_4
    | spl205_5
    | spl205_6
    | ~ spl205_7
    | ~ spl205_8
    | ~ spl205_9
    | spl205_10
    | spl205_11
    | ~ spl205_16
    | spl205_64
    | ~ spl205_81 ),
    inference(subsumption_resolution,[],[f6470,f5405])).

fof(f5405,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK1)
    | spl205_1
    | ~ spl205_2
    | ~ spl205_3
    | spl205_4
    | spl205_5
    | ~ spl205_7
    | ~ spl205_8
    | spl205_10 ),
    inference(unit_resulting_resolution,[],[f5247,f5252,f5257,f5262,f5267,f5277,f5282,f5292,f4199])).

fof(f4199,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X1)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3432])).

fof(f6470,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK1)
    | spl205_1
    | ~ spl205_2
    | ~ spl205_3
    | spl205_4
    | spl205_6
    | ~ spl205_7
    | ~ spl205_9
    | spl205_11
    | ~ spl205_16
    | spl205_64
    | ~ spl205_81 ),
    inference(unit_resulting_resolution,[],[f5247,f5262,f5257,f5272,f5252,f5320,f5277,f5287,f6038,f5297,f6347,f4207])).

fof(f4207,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | r1_tsep_1(X1,X3)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ r1_tsep_1(X3,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3440])).

fof(f5320,plain,
    ( r1_tsep_1(sK3,sK1)
    | ~ spl205_16 ),
    inference(avatar_component_clause,[],[f5318])).

fof(f5318,plain,
    ( spl205_16
  <=> r1_tsep_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl205_16])])).

fof(f6500,plain,
    ( spl205_1
    | ~ spl205_2
    | ~ spl205_3
    | spl205_4
    | spl205_5
    | spl205_6
    | ~ spl205_7
    | ~ spl205_8
    | ~ spl205_9
    | spl205_10
    | spl205_12
    | ~ spl205_16
    | spl205_64
    | ~ spl205_81 ),
    inference(avatar_contradiction_clause,[],[f6499])).

fof(f6499,plain,
    ( $false
    | spl205_1
    | ~ spl205_2
    | ~ spl205_3
    | spl205_4
    | spl205_5
    | spl205_6
    | ~ spl205_7
    | ~ spl205_8
    | ~ spl205_9
    | spl205_10
    | spl205_12
    | ~ spl205_16
    | spl205_64
    | ~ spl205_81 ),
    inference(subsumption_resolution,[],[f6475,f5405])).

fof(f6475,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK1)
    | spl205_1
    | ~ spl205_2
    | ~ spl205_3
    | spl205_4
    | spl205_6
    | ~ spl205_7
    | ~ spl205_9
    | spl205_12
    | ~ spl205_16
    | spl205_64
    | ~ spl205_81 ),
    inference(unit_resulting_resolution,[],[f5247,f5262,f5257,f5272,f5252,f5320,f5277,f5287,f6038,f5301,f6347,f4208])).

fof(f4208,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | r1_tsep_1(X3,X1)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ r1_tsep_1(X3,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3440])).

fof(f6348,plain,
    ( spl205_81
    | spl205_1
    | ~ spl205_3
    | spl205_4
    | spl205_5
    | ~ spl205_7
    | ~ spl205_8 ),
    inference(avatar_split_clause,[],[f5389,f5280,f5275,f5265,f5260,f5255,f5245,f6345])).

fof(f5389,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | spl205_1
    | ~ spl205_3
    | spl205_4
    | spl205_5
    | ~ spl205_7
    | ~ spl205_8 ),
    inference(unit_resulting_resolution,[],[f5247,f5257,f5262,f5277,f5267,f5282,f4149])).

fof(f4149,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3404])).

fof(f3404,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3403])).

fof(f3403,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3331])).

fof(f3331,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tsep_1)).

fof(f6039,plain,
    ( ~ spl205_64
    | spl205_1
    | ~ spl205_3
    | spl205_4
    | spl205_5
    | ~ spl205_7
    | ~ spl205_8 ),
    inference(avatar_split_clause,[],[f5367,f5280,f5275,f5265,f5260,f5255,f5245,f6036])).

fof(f5367,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | spl205_1
    | ~ spl205_3
    | spl205_4
    | spl205_5
    | ~ spl205_7
    | ~ spl205_8 ),
    inference(unit_resulting_resolution,[],[f5247,f5257,f5262,f5277,f5267,f5282,f4147])).

fof(f4147,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3404])).

fof(f5695,plain,
    ( spl205_46
    | ~ spl205_23 ),
    inference(avatar_split_clause,[],[f5448,f5443,f5692])).

fof(f5443,plain,
    ( spl205_23
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl205_23])])).

fof(f5448,plain,
    ( m1_pre_topc(sK3,sK3)
    | ~ spl205_23 ),
    inference(unit_resulting_resolution,[],[f5445,f4228])).

fof(f4228,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3459])).

fof(f3459,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3367])).

fof(f3367,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f5445,plain,
    ( l1_pre_topc(sK3)
    | ~ spl205_23 ),
    inference(avatar_component_clause,[],[f5443])).

fof(f5446,plain,
    ( spl205_23
    | ~ spl205_3
    | ~ spl205_9 ),
    inference(avatar_split_clause,[],[f5340,f5285,f5255,f5443])).

fof(f5340,plain,
    ( l1_pre_topc(sK3)
    | ~ spl205_3
    | ~ spl205_9 ),
    inference(unit_resulting_resolution,[],[f5287,f5257,f4227])).

fof(f4227,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f3458])).

fof(f3458,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1784])).

fof(f1784,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f5431,plain,
    ( spl205_1
    | ~ spl205_2
    | ~ spl205_3
    | spl205_4
    | spl205_6
    | ~ spl205_7
    | ~ spl205_9
    | ~ spl205_14
    | spl205_16
    | ~ spl205_21 ),
    inference(avatar_contradiction_clause,[],[f5430])).

fof(f5430,plain,
    ( $false
    | spl205_1
    | ~ spl205_2
    | ~ spl205_3
    | spl205_4
    | spl205_6
    | ~ spl205_7
    | ~ spl205_9
    | ~ spl205_14
    | spl205_16
    | ~ spl205_21 ),
    inference(subsumption_resolution,[],[f5426,f5374])).

fof(f5374,plain,
    ( m1_pre_topc(sK1,sK1)
    | ~ spl205_21 ),
    inference(unit_resulting_resolution,[],[f5362,f4228])).

fof(f5362,plain,
    ( l1_pre_topc(sK1)
    | ~ spl205_21 ),
    inference(avatar_component_clause,[],[f5360])).

fof(f5360,plain,
    ( spl205_21
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl205_21])])).

fof(f5426,plain,
    ( ~ m1_pre_topc(sK1,sK1)
    | spl205_1
    | ~ spl205_2
    | ~ spl205_3
    | spl205_4
    | spl205_6
    | ~ spl205_7
    | ~ spl205_9
    | ~ spl205_14
    | spl205_16 ),
    inference(unit_resulting_resolution,[],[f5247,f5252,f5257,f5262,f5272,f5262,f5277,f5277,f5287,f5319,f5311,f4206])).

fof(f5311,plain,
    ( r1_tsep_1(sK1,sK3)
    | ~ spl205_14 ),
    inference(avatar_component_clause,[],[f5309])).

fof(f5309,plain,
    ( spl205_14
  <=> r1_tsep_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl205_14])])).

fof(f5319,plain,
    ( ~ r1_tsep_1(sK3,sK1)
    | spl205_16 ),
    inference(avatar_component_clause,[],[f5318])).

fof(f5363,plain,
    ( spl205_21
    | ~ spl205_3
    | ~ spl205_7 ),
    inference(avatar_split_clause,[],[f5338,f5275,f5255,f5360])).

fof(f5338,plain,
    ( l1_pre_topc(sK1)
    | ~ spl205_3
    | ~ spl205_7 ),
    inference(unit_resulting_resolution,[],[f5277,f5257,f4227])).

fof(f5326,plain,
    ( spl205_14
    | spl205_15
    | spl205_16
    | spl205_17 ),
    inference(avatar_split_clause,[],[f4146,f5322,f5318,f5313,f5309])).

fof(f4146,plain,
    ( r1_tsep_1(sK3,sK2)
    | r1_tsep_1(sK3,sK1)
    | r1_tsep_1(sK2,sK3)
    | r1_tsep_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f3860])).

fof(f3860,plain,
    ( ( ( ( r1_tsep_1(sK3,sK2)
          | r1_tsep_1(sK3,sK1) )
        & ~ r1_tsep_1(sK3,k2_tsep_1(sK0,sK1,sK2)) )
      | ( ( r1_tsep_1(sK2,sK3)
          | r1_tsep_1(sK1,sK3) )
        & ~ r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3) ) )
    & ~ r1_tsep_1(sK1,sK2)
    & m1_pre_topc(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f3402,f3859,f3858,f3857,f3856])).

fof(f3856,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ( ( r1_tsep_1(X3,X2)
                          | r1_tsep_1(X3,X1) )
                        & ~ r1_tsep_1(X3,k2_tsep_1(X0,X1,X2)) )
                      | ( ( r1_tsep_1(X2,X3)
                          | r1_tsep_1(X1,X3) )
                        & ~ r1_tsep_1(k2_tsep_1(X0,X1,X2),X3) ) )
                    & ~ r1_tsep_1(X1,X2)
                    & m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( r1_tsep_1(X3,X2)
                        | r1_tsep_1(X3,X1) )
                      & ~ r1_tsep_1(X3,k2_tsep_1(sK0,X1,X2)) )
                    | ( ( r1_tsep_1(X2,X3)
                        | r1_tsep_1(X1,X3) )
                      & ~ r1_tsep_1(k2_tsep_1(sK0,X1,X2),X3) ) )
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X3,sK0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f3857,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ( ( r1_tsep_1(X3,X2)
                      | r1_tsep_1(X3,X1) )
                    & ~ r1_tsep_1(X3,k2_tsep_1(sK0,X1,X2)) )
                  | ( ( r1_tsep_1(X2,X3)
                      | r1_tsep_1(X1,X3) )
                    & ~ r1_tsep_1(k2_tsep_1(sK0,X1,X2),X3) ) )
                & ~ r1_tsep_1(X1,X2)
                & m1_pre_topc(X3,sK0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ( ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X3,sK1) )
                  & ~ r1_tsep_1(X3,k2_tsep_1(sK0,sK1,X2)) )
                | ( ( r1_tsep_1(X2,X3)
                    | r1_tsep_1(sK1,X3) )
                  & ~ r1_tsep_1(k2_tsep_1(sK0,sK1,X2),X3) ) )
              & ~ r1_tsep_1(sK1,X2)
              & m1_pre_topc(X3,sK0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f3858,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ( ( r1_tsep_1(X3,X2)
                  | r1_tsep_1(X3,sK1) )
                & ~ r1_tsep_1(X3,k2_tsep_1(sK0,sK1,X2)) )
              | ( ( r1_tsep_1(X2,X3)
                  | r1_tsep_1(sK1,X3) )
                & ~ r1_tsep_1(k2_tsep_1(sK0,sK1,X2),X3) ) )
            & ~ r1_tsep_1(sK1,X2)
            & m1_pre_topc(X3,sK0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ( ( ( r1_tsep_1(X3,sK2)
                | r1_tsep_1(X3,sK1) )
              & ~ r1_tsep_1(X3,k2_tsep_1(sK0,sK1,sK2)) )
            | ( ( r1_tsep_1(sK2,X3)
                | r1_tsep_1(sK1,X3) )
              & ~ r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),X3) ) )
          & ~ r1_tsep_1(sK1,sK2)
          & m1_pre_topc(X3,sK0)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f3859,plain,
    ( ? [X3] :
        ( ( ( ( r1_tsep_1(X3,sK2)
              | r1_tsep_1(X3,sK1) )
            & ~ r1_tsep_1(X3,k2_tsep_1(sK0,sK1,sK2)) )
          | ( ( r1_tsep_1(sK2,X3)
              | r1_tsep_1(sK1,X3) )
            & ~ r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),X3) ) )
        & ~ r1_tsep_1(sK1,sK2)
        & m1_pre_topc(X3,sK0)
        & ~ v2_struct_0(X3) )
   => ( ( ( ( r1_tsep_1(sK3,sK2)
            | r1_tsep_1(sK3,sK1) )
          & ~ r1_tsep_1(sK3,k2_tsep_1(sK0,sK1,sK2)) )
        | ( ( r1_tsep_1(sK2,sK3)
            | r1_tsep_1(sK1,sK3) )
          & ~ r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3) ) )
      & ~ r1_tsep_1(sK1,sK2)
      & m1_pre_topc(sK3,sK0)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f3402,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( r1_tsep_1(X3,X2)
                        | r1_tsep_1(X3,X1) )
                      & ~ r1_tsep_1(X3,k2_tsep_1(X0,X1,X2)) )
                    | ( ( r1_tsep_1(X2,X3)
                        | r1_tsep_1(X1,X3) )
                      & ~ r1_tsep_1(k2_tsep_1(X0,X1,X2),X3) ) )
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3401])).

fof(f3401,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( r1_tsep_1(X3,X2)
                        | r1_tsep_1(X3,X1) )
                      & ~ r1_tsep_1(X3,k2_tsep_1(X0,X1,X2)) )
                    | ( ( r1_tsep_1(X2,X3)
                        | r1_tsep_1(X1,X3) )
                      & ~ r1_tsep_1(k2_tsep_1(X0,X1,X2),X3) ) )
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3382])).

fof(f3382,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ( ~ r1_tsep_1(X1,X2)
                     => ( ( ~ r1_tsep_1(X3,k2_tsep_1(X0,X1,X2))
                         => ( ~ r1_tsep_1(X3,X2)
                            & ~ r1_tsep_1(X3,X1) ) )
                        & ( ~ r1_tsep_1(k2_tsep_1(X0,X1,X2),X3)
                         => ( ~ r1_tsep_1(X2,X3)
                            & ~ r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f3381])).

fof(f3381,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( ~ r1_tsep_1(X1,X2)
                   => ( ( ~ r1_tsep_1(X3,k2_tsep_1(X0,X1,X2))
                       => ( ~ r1_tsep_1(X3,X2)
                          & ~ r1_tsep_1(X3,X1) ) )
                      & ( ~ r1_tsep_1(k2_tsep_1(X0,X1,X2),X3)
                       => ( ~ r1_tsep_1(X2,X3)
                          & ~ r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tmap_1)).

fof(f5302,plain,
    ( ~ spl205_11
    | ~ spl205_12 ),
    inference(avatar_split_clause,[],[f4143,f5299,f5295])).

fof(f4143,plain,
    ( ~ r1_tsep_1(sK3,k2_tsep_1(sK0,sK1,sK2))
    | ~ r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f3860])).

fof(f5293,plain,(
    ~ spl205_10 ),
    inference(avatar_split_clause,[],[f4142,f5290])).

fof(f4142,plain,(
    ~ r1_tsep_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f3860])).

fof(f5288,plain,(
    spl205_9 ),
    inference(avatar_split_clause,[],[f4141,f5285])).

fof(f4141,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f3860])).

fof(f5283,plain,(
    spl205_8 ),
    inference(avatar_split_clause,[],[f4139,f5280])).

fof(f4139,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f3860])).

fof(f5278,plain,(
    spl205_7 ),
    inference(avatar_split_clause,[],[f4137,f5275])).

fof(f4137,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f3860])).

fof(f5273,plain,(
    ~ spl205_6 ),
    inference(avatar_split_clause,[],[f4140,f5270])).

fof(f4140,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f3860])).

fof(f5268,plain,(
    ~ spl205_5 ),
    inference(avatar_split_clause,[],[f4138,f5265])).

fof(f4138,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f3860])).

fof(f5263,plain,(
    ~ spl205_4 ),
    inference(avatar_split_clause,[],[f4136,f5260])).

fof(f4136,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f3860])).

fof(f5258,plain,(
    spl205_3 ),
    inference(avatar_split_clause,[],[f4135,f5255])).

fof(f4135,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f3860])).

fof(f5253,plain,(
    spl205_2 ),
    inference(avatar_split_clause,[],[f4134,f5250])).

fof(f4134,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f3860])).

fof(f5248,plain,(
    ~ spl205_1 ),
    inference(avatar_split_clause,[],[f4133,f5245])).

fof(f4133,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f3860])).
%------------------------------------------------------------------------------
