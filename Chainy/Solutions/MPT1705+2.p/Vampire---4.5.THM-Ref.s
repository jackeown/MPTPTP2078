%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1705+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:29 EST 2020

% Result     : Theorem 1.64s
% Output     : Refutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 334 expanded)
%              Number of leaves         :   30 ( 129 expanded)
%              Depth                    :   15
%              Number of atoms          :  660 (2375 expanded)
%              Number of equality atoms :   55 ( 197 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4611,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f3683,f3686,f3691,f3695,f3699,f3703,f3707,f3715,f3719,f3797,f3804,f3900,f4003,f4034,f4496,f4501,f4503,f4514,f4529,f4610])).

fof(f4610,plain,
    ( spl25_2
    | ~ spl25_4
    | ~ spl25_5
    | ~ spl25_7
    | ~ spl25_8
    | ~ spl25_10 ),
    inference(avatar_contradiction_clause,[],[f4609])).

fof(f4609,plain,
    ( $false
    | spl25_2
    | ~ spl25_4
    | ~ spl25_5
    | ~ spl25_7
    | ~ spl25_8
    | ~ spl25_10 ),
    inference(subsumption_resolution,[],[f4608,f3714])).

fof(f3714,plain,
    ( l1_pre_topc(sK0)
    | ~ spl25_10 ),
    inference(avatar_component_clause,[],[f3713])).

fof(f3713,plain,
    ( spl25_10
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl25_10])])).

fof(f4608,plain,
    ( ~ l1_pre_topc(sK0)
    | spl25_2
    | ~ spl25_4
    | ~ spl25_5
    | ~ spl25_7
    | ~ spl25_8 ),
    inference(subsumption_resolution,[],[f4593,f3685])).

fof(f3685,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl25_4 ),
    inference(avatar_component_clause,[],[f3681])).

fof(f3681,plain,
    ( spl25_4
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl25_4])])).

fof(f4593,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | spl25_2
    | ~ spl25_5
    | ~ spl25_7
    | ~ spl25_8 ),
    inference(resolution,[],[f4590,f3676])).

fof(f3676,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | spl25_2 ),
    inference(avatar_component_clause,[],[f3675])).

fof(f3675,plain,
    ( spl25_2
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl25_2])])).

fof(f4590,plain,
    ( ! [X0] :
        ( m1_pre_topc(sK1,X0)
        | ~ m1_pre_topc(sK2,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl25_5
    | ~ spl25_7
    | ~ spl25_8 ),
    inference(subsumption_resolution,[],[f4589,f3706])).

fof(f3706,plain,
    ( l1_pre_topc(sK1)
    | ~ spl25_8 ),
    inference(avatar_component_clause,[],[f3705])).

fof(f3705,plain,
    ( spl25_8
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl25_8])])).

fof(f4589,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | ~ l1_pre_topc(sK1)
        | m1_pre_topc(sK1,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl25_5
    | ~ spl25_7 ),
    inference(subsumption_resolution,[],[f4575,f3702])).

fof(f3702,plain,
    ( v2_pre_topc(sK2)
    | ~ spl25_7 ),
    inference(avatar_component_clause,[],[f3701])).

fof(f3701,plain,
    ( spl25_7
  <=> v2_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl25_7])])).

fof(f4575,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK2)
        | ~ m1_pre_topc(sK2,X0)
        | ~ l1_pre_topc(sK1)
        | m1_pre_topc(sK1,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl25_5 ),
    inference(superposition,[],[f4570,f3694])).

fof(f3694,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2
    | ~ spl25_5 ),
    inference(avatar_component_clause,[],[f3693])).

fof(f3693,plain,
    ( spl25_5
  <=> g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl25_5])])).

fof(f4570,plain,(
    ! [X2,X0] :
      ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0)
      | ~ l1_pre_topc(X2)
      | m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f4569,f3508])).

fof(f3508,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3372])).

fof(f3372,plain,(
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

fof(f4569,plain,(
    ! [X2,X0] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0)
      | ~ l1_pre_topc(X2)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f3622,f3548])).

fof(f3548,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3401])).

fof(f3401,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f3400])).

fof(f3400,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1849])).

fof(f1849,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_pre_topc)).

fof(f3622,plain,(
    ! [X2,X0] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f3539])).

fof(f3539,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3447])).

fof(f3447,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  | ~ m1_pre_topc(X2,X0) )
                & ( m1_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0) ) )
              | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f3392])).

fof(f3392,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X0)
              <=> m1_pre_topc(X2,X0) )
              | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f3391])).

fof(f3391,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X0)
              <=> m1_pre_topc(X2,X0) )
              | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3333])).

fof(f3333,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2) )
             => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1
               => ( m1_pre_topc(X1,X0)
                <=> m1_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_tmap_1)).

fof(f4529,plain,
    ( spl25_1
    | ~ spl25_2
    | ~ spl25_10
    | ~ spl25_11
    | ~ spl25_69 ),
    inference(avatar_split_clause,[],[f4523,f4492,f3717,f3713,f3675,f3672])).

fof(f3672,plain,
    ( spl25_1
  <=> v1_tsep_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl25_1])])).

fof(f3717,plain,
    ( spl25_11
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl25_11])])).

fof(f4492,plain,
    ( spl25_69
  <=> v3_pre_topc(u1_struct_0(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl25_69])])).

fof(f4523,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v1_tsep_1(sK1,sK0)
    | ~ spl25_10
    | ~ spl25_11
    | ~ spl25_69 ),
    inference(resolution,[],[f4493,f3976])).

fof(f3976,plain,
    ( ! [X5] :
        ( ~ v3_pre_topc(u1_struct_0(X5),sK0)
        | ~ m1_pre_topc(X5,sK0)
        | v1_tsep_1(X5,sK0) )
    | ~ spl25_10
    | ~ spl25_11 ),
    inference(subsumption_resolution,[],[f3970,f3714])).

fof(f3970,plain,
    ( ! [X5] :
        ( ~ v3_pre_topc(u1_struct_0(X5),sK0)
        | ~ m1_pre_topc(X5,sK0)
        | ~ l1_pre_topc(sK0)
        | v1_tsep_1(X5,sK0) )
    | ~ spl25_11 ),
    inference(resolution,[],[f3720,f3718])).

fof(f3718,plain,
    ( v2_pre_topc(sK0)
    | ~ spl25_11 ),
    inference(avatar_component_clause,[],[f3717])).

fof(f3720,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v1_tsep_1(X1,X0) ) ),
    inference(global_subsumption,[],[f3507,f3619])).

fof(f3619,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f3514])).

fof(f3514,plain,(
    ! [X2,X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3440])).

fof(f3440,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                  | ~ v3_pre_topc(X2,X0) )
                & ( v3_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_tsep_1(X1,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f3439])).

fof(f3439,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                  | ~ v3_pre_topc(X2,X0) )
                & ( v3_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_tsep_1(X1,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f3376])).

fof(f3376,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f3375])).

fof(f3375,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3337])).

fof(f3337,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                <=> v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tsep_1)).

fof(f3507,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3371])).

fof(f3371,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3338])).

fof(f3338,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f4493,plain,
    ( v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ spl25_69 ),
    inference(avatar_component_clause,[],[f4492])).

fof(f4514,plain,
    ( ~ spl25_1
    | ~ spl25_2
    | ~ spl25_10
    | ~ spl25_11
    | spl25_69 ),
    inference(avatar_contradiction_clause,[],[f4513])).

fof(f4513,plain,
    ( $false
    | ~ spl25_1
    | ~ spl25_2
    | ~ spl25_10
    | ~ spl25_11
    | spl25_69 ),
    inference(subsumption_resolution,[],[f4512,f3684])).

fof(f3684,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl25_2 ),
    inference(avatar_component_clause,[],[f3675])).

fof(f4512,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ spl25_1
    | ~ spl25_10
    | ~ spl25_11
    | spl25_69 ),
    inference(subsumption_resolution,[],[f4509,f3687])).

fof(f3687,plain,
    ( v1_tsep_1(sK1,sK0)
    | ~ spl25_1 ),
    inference(avatar_component_clause,[],[f3672])).

fof(f4509,plain,
    ( ~ v1_tsep_1(sK1,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ spl25_10
    | ~ spl25_11
    | spl25_69 ),
    inference(resolution,[],[f4502,f4205])).

fof(f4205,plain,
    ( ! [X5] :
        ( v3_pre_topc(u1_struct_0(X5),sK0)
        | ~ v1_tsep_1(X5,sK0)
        | ~ m1_pre_topc(X5,sK0) )
    | ~ spl25_10
    | ~ spl25_11 ),
    inference(subsumption_resolution,[],[f4199,f3714])).

fof(f4199,plain,
    ( ! [X5] :
        ( ~ m1_pre_topc(X5,sK0)
        | ~ v1_tsep_1(X5,sK0)
        | ~ l1_pre_topc(sK0)
        | v3_pre_topc(u1_struct_0(X5),sK0) )
    | ~ spl25_11 ),
    inference(resolution,[],[f4184,f3718])).

fof(f4184,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | v3_pre_topc(u1_struct_0(X1),X0) ) ),
    inference(subsumption_resolution,[],[f3669,f3507])).

fof(f3669,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f3620])).

fof(f3620,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f3513])).

fof(f3513,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3440])).

fof(f4502,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK1),sK0)
    | spl25_69 ),
    inference(avatar_component_clause,[],[f4492])).

fof(f4503,plain,
    ( spl25_3
    | ~ spl25_4
    | ~ spl25_69
    | ~ spl25_10
    | ~ spl25_11
    | ~ spl25_44 ),
    inference(avatar_split_clause,[],[f4455,f4032,f3717,f3713,f4492,f3681,f3678])).

fof(f3678,plain,
    ( spl25_3
  <=> v1_tsep_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl25_3])])).

fof(f4032,plain,
    ( spl25_44
  <=> u1_struct_0(sK1) = u1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl25_44])])).

fof(f4455,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v1_tsep_1(sK2,sK0)
    | ~ spl25_10
    | ~ spl25_11
    | ~ spl25_44 ),
    inference(superposition,[],[f3976,f4033])).

fof(f4033,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK2)
    | ~ spl25_44 ),
    inference(avatar_component_clause,[],[f4032])).

fof(f4501,plain,
    ( ~ spl25_4
    | ~ spl25_3
    | spl25_69
    | ~ spl25_10
    | ~ spl25_11
    | ~ spl25_44 ),
    inference(avatar_split_clause,[],[f4487,f4032,f3717,f3713,f4492,f3678,f3681])).

fof(f4487,plain,
    ( v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ v1_tsep_1(sK2,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ spl25_10
    | ~ spl25_11
    | ~ spl25_44 ),
    inference(superposition,[],[f4205,f4033])).

fof(f4496,plain,
    ( ~ spl25_2
    | spl25_4
    | ~ spl25_5
    | ~ spl25_10 ),
    inference(avatar_split_clause,[],[f4380,f3713,f3693,f3681,f3675])).

fof(f4380,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ spl25_5
    | ~ spl25_10 ),
    inference(superposition,[],[f3911,f3694])).

fof(f3911,plain,
    ( ! [X6] :
        ( m1_pre_topc(g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6)),sK0)
        | ~ m1_pre_topc(X6,sK0) )
    | ~ spl25_10 ),
    inference(resolution,[],[f3544,f3714])).

fof(f3544,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) ) ),
    inference(cnf_transformation,[],[f3396])).

fof(f3396,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3331])).

fof(f3331,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tmap_1)).

fof(f4034,plain,
    ( spl25_44
    | ~ spl25_34
    | ~ spl25_40 ),
    inference(avatar_split_clause,[],[f4030,f4001,f3898,f4032])).

fof(f3898,plain,
    ( spl25_34
  <=> sK2 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl25_34])])).

fof(f4001,plain,
    ( spl25_40
  <=> ! [X1,X0] :
        ( g1_pre_topc(X0,X1) != sK2
        | u1_struct_0(sK1) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl25_40])])).

fof(f4030,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK2)
    | ~ spl25_34
    | ~ spl25_40 ),
    inference(trivial_inequality_removal,[],[f4029])).

fof(f4029,plain,
    ( sK2 != sK2
    | u1_struct_0(sK1) = u1_struct_0(sK2)
    | ~ spl25_34
    | ~ spl25_40 ),
    inference(superposition,[],[f4002,f3899])).

fof(f3899,plain,
    ( sK2 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | ~ spl25_34 ),
    inference(avatar_component_clause,[],[f3898])).

fof(f4002,plain,
    ( ! [X0,X1] :
        ( g1_pre_topc(X0,X1) != sK2
        | u1_struct_0(sK1) = X0 )
    | ~ spl25_40 ),
    inference(avatar_component_clause,[],[f4001])).

fof(f4003,plain,
    ( ~ spl25_23
    | spl25_40
    | ~ spl25_5 ),
    inference(avatar_split_clause,[],[f3995,f3693,f4001,f3792])).

fof(f3792,plain,
    ( spl25_23
  <=> m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl25_23])])).

fof(f3995,plain,
    ( ! [X0,X1] :
        ( g1_pre_topc(X0,X1) != sK2
        | u1_struct_0(sK1) = X0
        | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) )
    | ~ spl25_5 ),
    inference(superposition,[],[f3523,f3694])).

fof(f3523,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f3381])).

fof(f3381,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f1808])).

fof(f1808,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(f3900,plain,
    ( spl25_34
    | ~ spl25_6
    | ~ spl25_24 ),
    inference(avatar_split_clause,[],[f3896,f3795,f3697,f3898])).

fof(f3697,plain,
    ( spl25_6
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl25_6])])).

fof(f3795,plain,
    ( spl25_24
  <=> v1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl25_24])])).

fof(f3896,plain,
    ( sK2 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | ~ spl25_6
    | ~ spl25_24 ),
    inference(subsumption_resolution,[],[f3892,f3698])).

fof(f3698,plain,
    ( l1_pre_topc(sK2)
    | ~ spl25_6 ),
    inference(avatar_component_clause,[],[f3697])).

fof(f3892,plain,
    ( sK2 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | ~ l1_pre_topc(sK2)
    | ~ spl25_24 ),
    inference(resolution,[],[f3549,f3796])).

fof(f3796,plain,
    ( v1_pre_topc(sK2)
    | ~ spl25_24 ),
    inference(avatar_component_clause,[],[f3795])).

fof(f3549,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3403])).

fof(f3403,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f3402])).

fof(f3402,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1759])).

fof(f1759,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(f3804,plain,
    ( ~ spl25_8
    | spl25_23 ),
    inference(avatar_contradiction_clause,[],[f3803])).

fof(f3803,plain,
    ( $false
    | ~ spl25_8
    | spl25_23 ),
    inference(subsumption_resolution,[],[f3801,f3706])).

fof(f3801,plain,
    ( ~ l1_pre_topc(sK1)
    | spl25_23 ),
    inference(resolution,[],[f3608,f3793])).

fof(f3793,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | spl25_23 ),
    inference(avatar_component_clause,[],[f3792])).

fof(f3608,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3414])).

fof(f3414,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1786])).

fof(f1786,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f3797,plain,
    ( ~ spl25_23
    | spl25_24
    | ~ spl25_5 ),
    inference(avatar_split_clause,[],[f3790,f3693,f3795,f3792])).

fof(f3790,plain,
    ( v1_pre_topc(sK2)
    | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl25_5 ),
    inference(superposition,[],[f3525,f3694])).

fof(f3525,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f3382])).

fof(f3382,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f1777])).

fof(f1777,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(f3719,plain,(
    spl25_11 ),
    inference(avatar_split_clause,[],[f3473,f3717])).

fof(f3473,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f3421])).

fof(f3421,plain,
    ( ( ~ m1_pre_topc(sK2,sK0)
      | ~ v1_tsep_1(sK2,sK0)
      | ~ m1_pre_topc(sK1,sK0)
      | ~ v1_tsep_1(sK1,sK0) )
    & ( ( m1_pre_topc(sK2,sK0)
        & v1_tsep_1(sK2,sK0) )
      | ( m1_pre_topc(sK1,sK0)
        & v1_tsep_1(sK1,sK0) ) )
    & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f3417,f3420,f3419,f3418])).

fof(f3418,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ m1_pre_topc(X2,X0)
                  | ~ v1_tsep_1(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_tsep_1(X1,X0) )
                & ( ( m1_pre_topc(X2,X0)
                    & v1_tsep_1(X2,X0) )
                  | ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) ) )
                & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
                & l1_pre_topc(X2)
                & v2_pre_topc(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,sK0)
                | ~ v1_tsep_1(X2,sK0)
                | ~ m1_pre_topc(X1,sK0)
                | ~ v1_tsep_1(X1,sK0) )
              & ( ( m1_pre_topc(X2,sK0)
                  & v1_tsep_1(X2,sK0) )
                | ( m1_pre_topc(X1,sK0)
                  & v1_tsep_1(X1,sK0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f3419,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ m1_pre_topc(X2,sK0)
              | ~ v1_tsep_1(X2,sK0)
              | ~ m1_pre_topc(X1,sK0)
              | ~ v1_tsep_1(X1,sK0) )
            & ( ( m1_pre_topc(X2,sK0)
                & v1_tsep_1(X2,sK0) )
              | ( m1_pre_topc(X1,sK0)
                & v1_tsep_1(X1,sK0) ) )
            & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
            & l1_pre_topc(X2)
            & v2_pre_topc(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1) )
   => ( ? [X2] :
          ( ( ~ m1_pre_topc(X2,sK0)
            | ~ v1_tsep_1(X2,sK0)
            | ~ m1_pre_topc(sK1,sK0)
            | ~ v1_tsep_1(sK1,sK0) )
          & ( ( m1_pre_topc(X2,sK0)
              & v1_tsep_1(X2,sK0) )
            | ( m1_pre_topc(sK1,sK0)
              & v1_tsep_1(sK1,sK0) ) )
          & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = X2
          & l1_pre_topc(X2)
          & v2_pre_topc(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f3420,plain,
    ( ? [X2] :
        ( ( ~ m1_pre_topc(X2,sK0)
          | ~ v1_tsep_1(X2,sK0)
          | ~ m1_pre_topc(sK1,sK0)
          | ~ v1_tsep_1(sK1,sK0) )
        & ( ( m1_pre_topc(X2,sK0)
            & v1_tsep_1(X2,sK0) )
          | ( m1_pre_topc(sK1,sK0)
            & v1_tsep_1(sK1,sK0) ) )
        & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = X2
        & l1_pre_topc(X2)
        & v2_pre_topc(X2) )
   => ( ( ~ m1_pre_topc(sK2,sK0)
        | ~ v1_tsep_1(sK2,sK0)
        | ~ m1_pre_topc(sK1,sK0)
        | ~ v1_tsep_1(sK1,sK0) )
      & ( ( m1_pre_topc(sK2,sK0)
          & v1_tsep_1(sK2,sK0) )
        | ( m1_pre_topc(sK1,sK0)
          & v1_tsep_1(sK1,sK0) ) )
      & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f3417,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,X0)
                | ~ v1_tsep_1(X2,X0)
                | ~ m1_pre_topc(X1,X0)
                | ~ v1_tsep_1(X1,X0) )
              & ( ( m1_pre_topc(X2,X0)
                  & v1_tsep_1(X2,X0) )
                | ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f3416])).

fof(f3416,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,X0)
                | ~ v1_tsep_1(X2,X0)
                | ~ m1_pre_topc(X1,X0)
                | ~ v1_tsep_1(X1,X0) )
              & ( ( m1_pre_topc(X2,X0)
                  & v1_tsep_1(X2,X0) )
                | ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f3353])).

fof(f3353,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <~> ( m1_pre_topc(X2,X0)
                  & v1_tsep_1(X2,X0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f3352])).

fof(f3352,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <~> ( m1_pre_topc(X2,X0)
                  & v1_tsep_1(X2,X0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3336])).

fof(f3336,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1) )
           => ! [X2] :
                ( ( l1_pre_topc(X2)
                  & v2_pre_topc(X2) )
               => ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
                 => ( ( m1_pre_topc(X1,X0)
                      & v1_tsep_1(X1,X0) )
                  <=> ( m1_pre_topc(X2,X0)
                      & v1_tsep_1(X2,X0) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f3335])).

fof(f3335,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2) )
             => ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                <=> ( m1_pre_topc(X2,X0)
                    & v1_tsep_1(X2,X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_tmap_1)).

fof(f3715,plain,(
    spl25_10 ),
    inference(avatar_split_clause,[],[f3474,f3713])).

fof(f3474,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f3421])).

fof(f3707,plain,(
    spl25_8 ),
    inference(avatar_split_clause,[],[f3476,f3705])).

fof(f3476,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f3421])).

fof(f3703,plain,(
    spl25_7 ),
    inference(avatar_split_clause,[],[f3477,f3701])).

fof(f3477,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f3421])).

fof(f3699,plain,(
    spl25_6 ),
    inference(avatar_split_clause,[],[f3478,f3697])).

fof(f3478,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f3421])).

fof(f3695,plain,(
    spl25_5 ),
    inference(avatar_split_clause,[],[f3479,f3693])).

fof(f3479,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2 ),
    inference(cnf_transformation,[],[f3421])).

fof(f3691,plain,
    ( spl25_1
    | spl25_3 ),
    inference(avatar_split_clause,[],[f3480,f3678,f3672])).

fof(f3480,plain,
    ( v1_tsep_1(sK2,sK0)
    | v1_tsep_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f3421])).

fof(f3686,plain,
    ( spl25_2
    | spl25_4 ),
    inference(avatar_split_clause,[],[f3483,f3681,f3675])).

fof(f3483,plain,
    ( m1_pre_topc(sK2,sK0)
    | m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f3421])).

fof(f3683,plain,
    ( ~ spl25_1
    | ~ spl25_2
    | ~ spl25_3
    | ~ spl25_4 ),
    inference(avatar_split_clause,[],[f3484,f3681,f3678,f3675,f3672])).

fof(f3484,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ v1_tsep_1(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v1_tsep_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f3421])).
%------------------------------------------------------------------------------
