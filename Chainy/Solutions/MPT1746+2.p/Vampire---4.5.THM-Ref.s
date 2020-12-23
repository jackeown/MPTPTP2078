%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1746+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:31 EST 2020

% Result     : Theorem 2.60s
% Output     : Refutation 2.60s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 333 expanded)
%              Number of leaves         :   22 ( 146 expanded)
%              Depth                    :   18
%              Number of atoms          :  756 (3910 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4472,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f3626,f3630,f3637,f3642,f3643,f3644,f3648,f3652,f3656,f3660,f3664,f3668,f4348,f4375,f4461,f4469])).

fof(f4469,plain,
    ( ~ spl18_1
    | ~ spl18_2
    | ~ spl18_3
    | ~ spl18_4
    | spl18_5
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_9
    | spl18_10
    | ~ spl18_11
    | ~ spl18_12
    | spl18_13 ),
    inference(avatar_contradiction_clause,[],[f4465])).

fof(f4465,plain,
    ( $false
    | ~ spl18_1
    | ~ spl18_2
    | ~ spl18_3
    | ~ spl18_4
    | spl18_5
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_9
    | spl18_10
    | ~ spl18_11
    | ~ spl18_12
    | spl18_13 ),
    inference(unit_resulting_resolution,[],[f3655,f3651,f3647,f3667,f3663,f3659,f3640,f3636,f3629,f3638,f3631,f3625,f3538])).

fof(f3538,plain,(
    ! [X4,X2,X0,X1] :
      ( v2_struct_0(X1)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ v5_pre_topc(X2,X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | r1_tmap_1(X1,X0,X2,X4)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3480])).

fof(f3480,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X1,X0)
                  | ( ~ r1_tmap_1(X1,X0,X2,sK9(X0,X1,X2))
                    & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1)) ) )
                & ( ! [X4] :
                      ( r1_tmap_1(X1,X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ v5_pre_topc(X2,X1,X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f3478,f3479])).

fof(f3479,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tmap_1(X1,X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_tmap_1(X1,X0,X2,sK9(X0,X1,X2))
        & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3478,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X1,X0)
                  | ? [X3] :
                      ( ~ r1_tmap_1(X1,X0,X2,X3)
                      & m1_subset_1(X3,u1_struct_0(X1)) ) )
                & ( ! [X4] :
                      ( r1_tmap_1(X1,X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ v5_pre_topc(X2,X1,X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f3477])).

fof(f3477,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X1,X0)
                  | ? [X3] :
                      ( ~ r1_tmap_1(X1,X0,X2,X3)
                      & m1_subset_1(X3,u1_struct_0(X1)) ) )
                & ( ! [X3] :
                      ( r1_tmap_1(X1,X0,X2,X3)
                      | ~ m1_subset_1(X3,u1_struct_0(X1)) )
                  | ~ v5_pre_topc(X2,X1,X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f3420])).

fof(f3420,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X1,X0)
              <=> ! [X3] :
                    ( r1_tmap_1(X1,X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3419])).

fof(f3419,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X1,X0)
              <=> ! [X3] :
                    ( r1_tmap_1(X1,X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3393])).

fof(f3393,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ( v5_pre_topc(X2,X1,X0)
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X1))
                   => r1_tmap_1(X1,X0,X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tmap_1)).

fof(f3625,plain,
    ( ~ r1_tmap_1(sK0,sK1,sK2,sK3)
    | spl18_5 ),
    inference(avatar_component_clause,[],[f3624])).

fof(f3624,plain,
    ( spl18_5
  <=> r1_tmap_1(sK0,sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_5])])).

fof(f3631,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl18_4 ),
    inference(avatar_component_clause,[],[f3621])).

fof(f3621,plain,
    ( spl18_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_4])])).

fof(f3638,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl18_2 ),
    inference(avatar_component_clause,[],[f3615])).

fof(f3615,plain,
    ( spl18_2
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_2])])).

fof(f3629,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl18_6 ),
    inference(avatar_component_clause,[],[f3628])).

fof(f3628,plain,
    ( spl18_6
  <=> m1_subset_1(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_6])])).

fof(f3636,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ spl18_3 ),
    inference(avatar_component_clause,[],[f3618])).

fof(f3618,plain,
    ( spl18_3
  <=> v5_pre_topc(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_3])])).

fof(f3640,plain,
    ( v1_funct_1(sK2)
    | ~ spl18_1 ),
    inference(avatar_component_clause,[],[f3612])).

fof(f3612,plain,
    ( spl18_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_1])])).

fof(f3659,plain,
    ( l1_pre_topc(sK0)
    | ~ spl18_11 ),
    inference(avatar_component_clause,[],[f3658])).

fof(f3658,plain,
    ( spl18_11
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_11])])).

fof(f3663,plain,
    ( v2_pre_topc(sK0)
    | ~ spl18_12 ),
    inference(avatar_component_clause,[],[f3662])).

fof(f3662,plain,
    ( spl18_12
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_12])])).

fof(f3667,plain,
    ( ~ v2_struct_0(sK0)
    | spl18_13 ),
    inference(avatar_component_clause,[],[f3666])).

fof(f3666,plain,
    ( spl18_13
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_13])])).

fof(f3647,plain,
    ( l1_pre_topc(sK1)
    | ~ spl18_8 ),
    inference(avatar_component_clause,[],[f3646])).

fof(f3646,plain,
    ( spl18_8
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_8])])).

fof(f3651,plain,
    ( v2_pre_topc(sK1)
    | ~ spl18_9 ),
    inference(avatar_component_clause,[],[f3650])).

fof(f3650,plain,
    ( spl18_9
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_9])])).

fof(f3655,plain,
    ( ~ v2_struct_0(sK1)
    | spl18_10 ),
    inference(avatar_component_clause,[],[f3654])).

fof(f3654,plain,
    ( spl18_10
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_10])])).

fof(f4461,plain,
    ( spl18_3
    | ~ spl18_1
    | ~ spl18_2
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_9
    | spl18_10
    | ~ spl18_11
    | ~ spl18_12
    | spl18_13
    | spl18_59 ),
    inference(avatar_split_clause,[],[f4460,f4373,f3666,f3662,f3658,f3654,f3650,f3646,f3621,f3615,f3612,f3618])).

fof(f4373,plain,
    ( spl18_59
  <=> m1_subset_1(sK9(sK1,sK0,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_59])])).

fof(f4460,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ spl18_1
    | ~ spl18_2
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_9
    | spl18_10
    | ~ spl18_11
    | ~ spl18_12
    | spl18_13
    | spl18_59 ),
    inference(subsumption_resolution,[],[f4459,f3655])).

fof(f4459,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | v2_struct_0(sK1)
    | ~ spl18_1
    | ~ spl18_2
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_9
    | ~ spl18_11
    | ~ spl18_12
    | spl18_13
    | spl18_59 ),
    inference(subsumption_resolution,[],[f4458,f3651])).

fof(f4458,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl18_1
    | ~ spl18_2
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_11
    | ~ spl18_12
    | spl18_13
    | spl18_59 ),
    inference(subsumption_resolution,[],[f4457,f3647])).

fof(f4457,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl18_1
    | ~ spl18_2
    | ~ spl18_4
    | ~ spl18_11
    | ~ spl18_12
    | spl18_13
    | spl18_59 ),
    inference(subsumption_resolution,[],[f4456,f3667])).

fof(f4456,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl18_1
    | ~ spl18_2
    | ~ spl18_4
    | ~ spl18_11
    | ~ spl18_12
    | spl18_59 ),
    inference(subsumption_resolution,[],[f4455,f3663])).

fof(f4455,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl18_1
    | ~ spl18_2
    | ~ spl18_4
    | ~ spl18_11
    | spl18_59 ),
    inference(subsumption_resolution,[],[f4454,f3659])).

fof(f4454,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl18_1
    | ~ spl18_2
    | ~ spl18_4
    | spl18_59 ),
    inference(subsumption_resolution,[],[f4453,f3640])).

fof(f4453,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl18_2
    | ~ spl18_4
    | spl18_59 ),
    inference(subsumption_resolution,[],[f4452,f3638])).

fof(f4452,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl18_4
    | spl18_59 ),
    inference(subsumption_resolution,[],[f4439,f3631])).

fof(f4439,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | spl18_59 ),
    inference(resolution,[],[f4374,f3539])).

fof(f3539,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1))
      | v5_pre_topc(X2,X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3480])).

fof(f4374,plain,
    ( ~ m1_subset_1(sK9(sK1,sK0,sK2),u1_struct_0(sK0))
    | spl18_59 ),
    inference(avatar_component_clause,[],[f4373])).

fof(f4375,plain,
    ( ~ spl18_59
    | ~ spl18_7
    | spl18_53 ),
    inference(avatar_split_clause,[],[f4371,f4346,f3633,f4373])).

fof(f3633,plain,
    ( spl18_7
  <=> ! [X4] :
        ( r1_tmap_1(sK0,sK1,sK2,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_7])])).

fof(f4346,plain,
    ( spl18_53
  <=> r1_tmap_1(sK0,sK1,sK2,sK9(sK1,sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_53])])).

fof(f4371,plain,
    ( ~ m1_subset_1(sK9(sK1,sK0,sK2),u1_struct_0(sK0))
    | ~ spl18_7
    | spl18_53 ),
    inference(resolution,[],[f4347,f3634])).

fof(f3634,plain,
    ( ! [X4] :
        ( r1_tmap_1(sK0,sK1,sK2,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
    | ~ spl18_7 ),
    inference(avatar_component_clause,[],[f3633])).

fof(f4347,plain,
    ( ~ r1_tmap_1(sK0,sK1,sK2,sK9(sK1,sK0,sK2))
    | spl18_53 ),
    inference(avatar_component_clause,[],[f4346])).

fof(f4348,plain,
    ( ~ spl18_53
    | ~ spl18_1
    | ~ spl18_2
    | spl18_3
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_9
    | spl18_10
    | ~ spl18_11
    | ~ spl18_12
    | spl18_13 ),
    inference(avatar_split_clause,[],[f4344,f3666,f3662,f3658,f3654,f3650,f3646,f3621,f3618,f3615,f3612,f4346])).

fof(f4344,plain,
    ( ~ r1_tmap_1(sK0,sK1,sK2,sK9(sK1,sK0,sK2))
    | ~ spl18_1
    | ~ spl18_2
    | spl18_3
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_9
    | spl18_10
    | ~ spl18_11
    | ~ spl18_12
    | spl18_13 ),
    inference(subsumption_resolution,[],[f4343,f3619])).

fof(f3619,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | spl18_3 ),
    inference(avatar_component_clause,[],[f3618])).

fof(f4343,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ r1_tmap_1(sK0,sK1,sK2,sK9(sK1,sK0,sK2))
    | ~ spl18_1
    | ~ spl18_2
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_9
    | spl18_10
    | ~ spl18_11
    | ~ spl18_12
    | spl18_13 ),
    inference(subsumption_resolution,[],[f4342,f3640])).

fof(f4342,plain,
    ( ~ v1_funct_1(sK2)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ r1_tmap_1(sK0,sK1,sK2,sK9(sK1,sK0,sK2))
    | ~ spl18_2
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_9
    | spl18_10
    | ~ spl18_11
    | ~ spl18_12
    | spl18_13 ),
    inference(subsumption_resolution,[],[f4338,f3638])).

fof(f4338,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ r1_tmap_1(sK0,sK1,sK2,sK9(sK1,sK0,sK2))
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_9
    | spl18_10
    | ~ spl18_11
    | ~ spl18_12
    | spl18_13 ),
    inference(resolution,[],[f4297,f3631])).

fof(f4297,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(X0)
        | v5_pre_topc(X0,sK0,sK1)
        | ~ r1_tmap_1(sK0,sK1,X0,sK9(sK1,sK0,X0)) )
    | ~ spl18_8
    | ~ spl18_9
    | spl18_10
    | ~ spl18_11
    | ~ spl18_12
    | spl18_13 ),
    inference(subsumption_resolution,[],[f4296,f3651])).

fof(f4296,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(X0)
        | v5_pre_topc(X0,sK0,sK1)
        | ~ v2_pre_topc(sK1)
        | ~ r1_tmap_1(sK0,sK1,X0,sK9(sK1,sK0,X0)) )
    | ~ spl18_8
    | spl18_10
    | ~ spl18_11
    | ~ spl18_12
    | spl18_13 ),
    inference(subsumption_resolution,[],[f4294,f3647])).

fof(f4294,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(X0)
        | v5_pre_topc(X0,sK0,sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ r1_tmap_1(sK0,sK1,X0,sK9(sK1,sK0,X0)) )
    | spl18_10
    | ~ spl18_11
    | ~ spl18_12
    | spl18_13 ),
    inference(resolution,[],[f3849,f3655])).

fof(f3849,plain,
    ( ! [X2,X3] :
        ( v2_struct_0(X2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X2))))
        | ~ v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X2))
        | ~ v1_funct_1(X3)
        | v5_pre_topc(X3,sK0,X2)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | ~ r1_tmap_1(sK0,X2,X3,sK9(X2,sK0,X3)) )
    | ~ spl18_11
    | ~ spl18_12
    | spl18_13 ),
    inference(subsumption_resolution,[],[f3848,f3663])).

fof(f3848,plain,
    ( ! [X2,X3] :
        ( ~ r1_tmap_1(sK0,X2,X3,sK9(X2,sK0,X3))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X2))))
        | ~ v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X2))
        | ~ v1_funct_1(X3)
        | ~ v2_pre_topc(sK0)
        | v5_pre_topc(X3,sK0,X2)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2) )
    | ~ spl18_11
    | spl18_13 ),
    inference(subsumption_resolution,[],[f3843,f3659])).

fof(f3843,plain,
    ( ! [X2,X3] :
        ( ~ r1_tmap_1(sK0,X2,X3,sK9(X2,sK0,X3))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X2))))
        | ~ v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X2))
        | ~ v1_funct_1(X3)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v5_pre_topc(X3,sK0,X2)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2) )
    | spl18_13 ),
    inference(resolution,[],[f3540,f3667])).

fof(f3540,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X1)
      | ~ r1_tmap_1(X1,X0,X2,sK9(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v5_pre_topc(X2,X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3480])).

fof(f3668,plain,(
    ~ spl18_13 ),
    inference(avatar_split_clause,[],[f3508,f3666])).

fof(f3508,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f3462])).

fof(f3462,plain,
    ( ( ( ~ r1_tmap_1(sK0,sK1,sK2,sK3)
        & m1_subset_1(sK3,u1_struct_0(sK0)) )
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(sK2,sK0,sK1)
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(sK2) )
    & ( ! [X4] :
          ( r1_tmap_1(sK0,sK1,sK2,X4)
          | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
      | ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v5_pre_topc(sK2,sK0,sK1)
        & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(sK2) ) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f3457,f3461,f3460,f3459,f3458])).

fof(f3458,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ? [X3] :
                      ( ~ r1_tmap_1(X0,X1,X2,X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  | ~ v5_pre_topc(X2,X0,X1)
                  | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  | ~ v1_funct_1(X2) )
                & ( ! [X4] :
                      ( r1_tmap_1(X0,X1,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                    & v5_pre_topc(X2,X0,X1)
                    & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                    & v1_funct_1(X2) ) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r1_tmap_1(sK0,X1,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(sK0)) )
                | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
                | ~ v5_pre_topc(X2,sK0,X1)
                | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
                | ~ v1_funct_1(X2) )
              & ( ! [X4] :
                    ( r1_tmap_1(sK0,X1,X2,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
                | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
                  & v5_pre_topc(X2,sK0,X1)
                  & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
                  & v1_funct_1(X2) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f3459,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ? [X3] :
                  ( ~ r1_tmap_1(sK0,X1,X2,X3)
                  & m1_subset_1(X3,u1_struct_0(sK0)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              | ~ v5_pre_topc(X2,sK0,X1)
              | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
            & ( ! [X4] :
                  ( r1_tmap_1(sK0,X1,X2,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
              | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
                & v5_pre_topc(X2,sK0,X1)
                & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
                & v1_funct_1(X2) ) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ( ? [X3] :
                ( ~ r1_tmap_1(sK0,sK1,X2,X3)
                & m1_subset_1(X3,u1_struct_0(sK0)) )
            | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
            | ~ v5_pre_topc(X2,sK0,sK1)
            | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
            | ~ v1_funct_1(X2) )
          & ( ! [X4] :
                ( r1_tmap_1(sK0,sK1,X2,X4)
                | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
            | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
              & v5_pre_topc(X2,sK0,sK1)
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
              & v1_funct_1(X2) ) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f3460,plain,
    ( ? [X2] :
        ( ( ? [X3] :
              ( ~ r1_tmap_1(sK0,sK1,X2,X3)
              & m1_subset_1(X3,u1_struct_0(sK0)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          | ~ v5_pre_topc(X2,sK0,sK1)
          | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          | ~ v1_funct_1(X2) )
        & ( ! [X4] :
              ( r1_tmap_1(sK0,sK1,X2,X4)
              | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
          | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
            & v5_pre_topc(X2,sK0,sK1)
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
            & v1_funct_1(X2) ) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( ( ? [X3] :
            ( ~ r1_tmap_1(sK0,sK1,sK2,X3)
            & m1_subset_1(X3,u1_struct_0(sK0)) )
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(sK2) )
      & ( ! [X4] :
            ( r1_tmap_1(sK0,sK1,sK2,X4)
            | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
        | ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v5_pre_topc(sK2,sK0,sK1)
          & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(sK2) ) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f3461,plain,
    ( ? [X3] :
        ( ~ r1_tmap_1(sK0,sK1,sK2,X3)
        & m1_subset_1(X3,u1_struct_0(sK0)) )
   => ( ~ r1_tmap_1(sK0,sK1,sK2,sK3)
      & m1_subset_1(sK3,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f3457,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r1_tmap_1(X0,X1,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                | ~ v5_pre_topc(X2,X0,X1)
                | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                | ~ v1_funct_1(X2) )
              & ( ! [X4] :
                    ( r1_tmap_1(X0,X1,X2,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v5_pre_topc(X2,X0,X1)
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f3456])).

fof(f3456,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r1_tmap_1(X0,X1,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                | ~ v5_pre_topc(X2,X0,X1)
                | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                | ~ v1_funct_1(X2) )
              & ( ! [X3] :
                    ( r1_tmap_1(X0,X1,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v5_pre_topc(X2,X0,X1)
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3455])).

fof(f3455,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r1_tmap_1(X0,X1,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                | ~ v5_pre_topc(X2,X0,X1)
                | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                | ~ v1_funct_1(X2) )
              & ( ! [X3] :
                    ( r1_tmap_1(X0,X1,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v5_pre_topc(X2,X0,X1)
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f3412])).

fof(f3412,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v5_pre_topc(X2,X0,X1)
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
              <~> ! [X3] :
                    ( r1_tmap_1(X0,X1,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3411])).

fof(f3411,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v5_pre_topc(X2,X0,X1)
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
              <~> ! [X3] :
                    ( r1_tmap_1(X0,X1,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3401])).

fof(f3401,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                    & v5_pre_topc(X2,X0,X1)
                    & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                    & v1_funct_1(X2) )
                <=> ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => r1_tmap_1(X0,X1,X2,X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f3400])).

fof(f3400,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v5_pre_topc(X2,X0,X1)
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => r1_tmap_1(X0,X1,X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tmap_1)).

fof(f3664,plain,(
    spl18_12 ),
    inference(avatar_split_clause,[],[f3509,f3662])).

fof(f3509,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f3462])).

fof(f3660,plain,(
    spl18_11 ),
    inference(avatar_split_clause,[],[f3510,f3658])).

fof(f3510,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f3462])).

fof(f3656,plain,(
    ~ spl18_10 ),
    inference(avatar_split_clause,[],[f3511,f3654])).

fof(f3511,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f3462])).

fof(f3652,plain,(
    spl18_9 ),
    inference(avatar_split_clause,[],[f3512,f3650])).

fof(f3512,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f3462])).

fof(f3648,plain,(
    spl18_8 ),
    inference(avatar_split_clause,[],[f3513,f3646])).

fof(f3513,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f3462])).

fof(f3644,plain,(
    spl18_1 ),
    inference(avatar_split_clause,[],[f3514,f3612])).

fof(f3514,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f3462])).

fof(f3643,plain,(
    spl18_2 ),
    inference(avatar_split_clause,[],[f3515,f3615])).

fof(f3515,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f3462])).

fof(f3642,plain,(
    spl18_4 ),
    inference(avatar_split_clause,[],[f3516,f3621])).

fof(f3516,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f3462])).

fof(f3637,plain,
    ( spl18_3
    | spl18_7 ),
    inference(avatar_split_clause,[],[f3519,f3633,f3618])).

fof(f3519,plain,(
    ! [X4] :
      ( r1_tmap_1(sK0,sK1,sK2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | v5_pre_topc(sK2,sK0,sK1) ) ),
    inference(cnf_transformation,[],[f3462])).

fof(f3630,plain,
    ( ~ spl18_1
    | ~ spl18_2
    | ~ spl18_3
    | ~ spl18_4
    | spl18_6 ),
    inference(avatar_split_clause,[],[f3521,f3628,f3621,f3618,f3615,f3612])).

fof(f3521,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f3462])).

fof(f3626,plain,
    ( ~ spl18_1
    | ~ spl18_2
    | ~ spl18_3
    | ~ spl18_4
    | ~ spl18_5 ),
    inference(avatar_split_clause,[],[f3522,f3624,f3621,f3618,f3615,f3612])).

fof(f3522,plain,
    ( ~ r1_tmap_1(sK0,sK1,sK2,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f3462])).
%------------------------------------------------------------------------------
