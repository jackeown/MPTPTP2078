%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1773+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:32 EST 2020

% Result     : Theorem 17.76s
% Output     : Refutation 17.76s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 292 expanded)
%              Number of leaves         :   33 ( 122 expanded)
%              Depth                    :    7
%              Number of atoms          :  604 (3047 expanded)
%              Number of equality atoms :   13 ( 116 expanded)
%              Maximal formula depth    :   31 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8450,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f4454,f4459,f4464,f4469,f4474,f4479,f4484,f4489,f4494,f4499,f4504,f4509,f4514,f4519,f4524,f4529,f4534,f4539,f4544,f4549,f4558,f4559,f4578,f4583,f4688,f6537,f6541,f7264,f8449])).

fof(f8449,plain,
    ( ~ spl85_18
    | ~ spl85_16
    | ~ spl85_39
    | spl85_399 ),
    inference(avatar_split_clause,[],[f8448,f7261,f4686,f4526,f4536])).

fof(f4536,plain,
    ( spl85_18
  <=> r2_hidden(sK7,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl85_18])])).

fof(f4526,plain,
    ( spl85_16
  <=> m1_subset_1(sK7,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl85_16])])).

fof(f4686,plain,
    ( spl85_39
  <=> ! [X5] :
        ( ~ m1_subset_1(X5,u1_struct_0(sK3))
        | m1_connsp_2(sK5,sK3,X5)
        | ~ r2_hidden(X5,sK5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl85_39])])).

fof(f7261,plain,
    ( spl85_399
  <=> m1_connsp_2(sK5,sK3,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl85_399])])).

fof(f8448,plain,
    ( ~ m1_subset_1(sK7,u1_struct_0(sK3))
    | ~ r2_hidden(sK7,sK5)
    | ~ spl85_39
    | spl85_399 ),
    inference(resolution,[],[f7263,f4687])).

fof(f4687,plain,
    ( ! [X5] :
        ( m1_connsp_2(sK5,sK3,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK3))
        | ~ r2_hidden(X5,sK5) )
    | ~ spl85_39 ),
    inference(avatar_component_clause,[],[f4686])).

fof(f7263,plain,
    ( ~ m1_connsp_2(sK5,sK3,sK7)
    | spl85_399 ),
    inference(avatar_component_clause,[],[f7261])).

fof(f7264,plain,
    ( ~ spl85_17
    | ~ spl85_399
    | ~ spl85_15
    | ~ spl85_321 ),
    inference(avatar_split_clause,[],[f7200,f6535,f4521,f7261,f4531])).

fof(f4531,plain,
    ( spl85_17
  <=> r1_tarski(sK5,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl85_17])])).

fof(f4521,plain,
    ( spl85_15
  <=> m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl85_15])])).

fof(f6535,plain,
    ( spl85_321
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_connsp_2(X0,sK3,sK7)
        | ~ r1_tarski(X0,u1_struct_0(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl85_321])])).

fof(f7200,plain,
    ( ~ m1_connsp_2(sK5,sK3,sK7)
    | ~ r1_tarski(sK5,u1_struct_0(sK2))
    | ~ spl85_15
    | ~ spl85_321 ),
    inference(resolution,[],[f6536,f4523])).

fof(f4523,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl85_15 ),
    inference(avatar_component_clause,[],[f4521])).

fof(f6536,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_connsp_2(X0,sK3,sK7)
        | ~ r1_tarski(X0,u1_struct_0(sK2)) )
    | ~ spl85_321 ),
    inference(avatar_component_clause,[],[f6535])).

fof(f6541,plain,
    ( spl85_3
    | ~ spl85_21
    | ~ spl85_11
    | ~ spl85_20
    | ~ spl85_16
    | ~ spl85_12
    | ~ spl85_13
    | ~ spl85_14
    | ~ spl85_7
    | spl85_8
    | ~ spl85_9
    | spl85_10
    | ~ spl85_4
    | ~ spl85_5
    | spl85_6
    | ~ spl85_1
    | ~ spl85_2
    | spl85_22 ),
    inference(avatar_split_clause,[],[f6539,f4555,f4456,f4451,f4476,f4471,f4466,f4496,f4491,f4486,f4481,f4516,f4511,f4506,f4526,f4546,f4501,f4551,f4461])).

fof(f4461,plain,
    ( spl85_3
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl85_3])])).

fof(f4551,plain,
    ( spl85_21
  <=> r1_tmap_1(sK3,sK1,sK4,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl85_21])])).

fof(f4501,plain,
    ( spl85_11
  <=> m1_pre_topc(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl85_11])])).

fof(f4546,plain,
    ( spl85_20
  <=> m1_subset_1(sK7,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl85_20])])).

fof(f4506,plain,
    ( spl85_12
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl85_12])])).

fof(f4511,plain,
    ( spl85_13
  <=> v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl85_13])])).

fof(f4516,plain,
    ( spl85_14
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl85_14])])).

fof(f4481,plain,
    ( spl85_7
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl85_7])])).

fof(f4486,plain,
    ( spl85_8
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl85_8])])).

fof(f4491,plain,
    ( spl85_9
  <=> m1_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl85_9])])).

fof(f4496,plain,
    ( spl85_10
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl85_10])])).

fof(f4466,plain,
    ( spl85_4
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl85_4])])).

fof(f4471,plain,
    ( spl85_5
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl85_5])])).

fof(f4476,plain,
    ( spl85_6
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl85_6])])).

fof(f4451,plain,
    ( spl85_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl85_1])])).

fof(f4456,plain,
    ( spl85_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl85_2])])).

fof(f4555,plain,
    ( spl85_22
  <=> r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl85_22])])).

fof(f6539,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK7,u1_struct_0(sK3))
    | ~ m1_subset_1(sK7,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tmap_1(sK3,sK1,sK4,sK7)
    | v2_struct_0(sK0)
    | spl85_22 ),
    inference(resolution,[],[f4557,f4384])).

fof(f4384,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_pre_topc(X3,X2)
      | ~ r1_tmap_1(X2,X1,X4,X6)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f3868])).

fof(f3868,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | X5 != X6
      | ~ m1_pre_topc(X3,X2)
      | ~ r1_tmap_1(X2,X1,X4,X5)
      | r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) ) ),
    inference(cnf_transformation,[],[f3464])).

fof(f3464,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
                              | ~ r1_tmap_1(X2,X1,X4,X5)
                              | ~ m1_pre_topc(X3,X2)
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X2)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3463])).

fof(f3463,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
                              | ~ r1_tmap_1(X2,X1,X4,X5)
                              | ~ m1_pre_topc(X3,X2)
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X2)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3434])).

fof(f3434,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X2))
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X3))
                             => ( ( r1_tmap_1(X2,X1,X4,X5)
                                  & m1_pre_topc(X3,X2)
                                  & X5 = X6 )
                               => r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_tmap_1)).

fof(f4557,plain,
    ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7)
    | spl85_22 ),
    inference(avatar_component_clause,[],[f4555])).

fof(f6537,plain,
    ( spl85_21
    | spl85_3
    | ~ spl85_20
    | ~ spl85_16
    | spl85_321
    | ~ spl85_11
    | ~ spl85_12
    | ~ spl85_13
    | ~ spl85_14
    | ~ spl85_9
    | spl85_10
    | ~ spl85_7
    | spl85_8
    | ~ spl85_4
    | ~ spl85_5
    | spl85_6
    | ~ spl85_1
    | ~ spl85_2
    | ~ spl85_22 ),
    inference(avatar_split_clause,[],[f4973,f4555,f4456,f4451,f4476,f4471,f4466,f4486,f4481,f4496,f4491,f4516,f4511,f4506,f4501,f6535,f4526,f4546,f4461,f4551])).

fof(f4973,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ m1_pre_topc(sK2,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(sK7,u1_struct_0(sK3))
        | ~ m1_subset_1(sK7,u1_struct_0(sK2))
        | ~ r1_tarski(X0,u1_struct_0(sK2))
        | ~ m1_connsp_2(X0,sK3,sK7)
        | v2_struct_0(sK0)
        | r1_tmap_1(sK3,sK1,sK4,sK7) )
    | ~ spl85_22 ),
    inference(resolution,[],[f4556,f4386])).

fof(f4386,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ m1_connsp_2(X5,X3,X7)
      | v2_struct_0(X0)
      | r1_tmap_1(X3,X1,X4,X7) ) ),
    inference(equality_resolution,[],[f3872])).

fof(f3872,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ m1_connsp_2(X5,X3,X6)
      | X6 != X7
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | r1_tmap_1(X3,X1,X4,X6) ) ),
    inference(cnf_transformation,[],[f3468])).

fof(f3468,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( r1_tmap_1(X3,X1,X4,X6)
                                  <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) )
                                  | X6 != X7
                                  | ~ m1_connsp_2(X5,X3,X6)
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ m1_subset_1(X7,u1_struct_0(X2)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3467])).

fof(f3467,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( r1_tmap_1(X3,X1,X4,X6)
                                  <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) )
                                  | X6 != X7
                                  | ~ m1_connsp_2(X5,X3,X6)
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ m1_subset_1(X7,u1_struct_0(X2)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3436])).

fof(f3436,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X2,X3)
                       => ! [X5] :
                            ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X3))
                               => ! [X7] :
                                    ( m1_subset_1(X7,u1_struct_0(X2))
                                   => ( ( X6 = X7
                                        & m1_connsp_2(X5,X3,X6)
                                        & r1_tarski(X5,u1_struct_0(X2)) )
                                     => ( r1_tmap_1(X3,X1,X4,X6)
                                      <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_tmap_1)).

fof(f4556,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7)
    | ~ spl85_22 ),
    inference(avatar_component_clause,[],[f4555])).

fof(f4688,plain,
    ( ~ spl85_19
    | spl85_39
    | spl85_10
    | ~ spl85_25
    | ~ spl85_26
    | ~ spl85_15 ),
    inference(avatar_split_clause,[],[f4657,f4521,f4580,f4575,f4496,f4686,f4541])).

fof(f4541,plain,
    ( spl85_19
  <=> v3_pre_topc(sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl85_19])])).

fof(f4575,plain,
    ( spl85_25
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl85_25])])).

fof(f4580,plain,
    ( spl85_26
  <=> v2_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl85_26])])).

fof(f4657,plain,
    ( ! [X5] :
        ( ~ v2_pre_topc(sK3)
        | ~ l1_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ m1_subset_1(X5,u1_struct_0(sK3))
        | ~ v3_pre_topc(sK5,sK3)
        | ~ r2_hidden(X5,sK5)
        | m1_connsp_2(sK5,sK3,X5) )
    | ~ spl85_15 ),
    inference(resolution,[],[f4523,f4096])).

fof(f4096,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ r2_hidden(X2,X1)
      | m1_connsp_2(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f3648])).

fof(f3648,plain,(
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
    inference(flattening,[],[f3647])).

fof(f3647,plain,(
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
    inference(ennf_transformation,[],[f2565])).

fof(f2565,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_connsp_2)).

fof(f4583,plain,
    ( spl85_26
    | ~ spl85_2
    | ~ spl85_1
    | ~ spl85_9 ),
    inference(avatar_split_clause,[],[f4573,f4491,f4451,f4456,f4580])).

fof(f4573,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK3)
    | ~ spl85_9 ),
    inference(resolution,[],[f4493,f3991])).

fof(f3991,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f3567])).

fof(f3567,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f3566])).

fof(f3566,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1760])).

fof(f1760,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f4493,plain,
    ( m1_pre_topc(sK3,sK0)
    | ~ spl85_9 ),
    inference(avatar_component_clause,[],[f4491])).

fof(f4578,plain,
    ( spl85_25
    | ~ spl85_1
    | ~ spl85_9 ),
    inference(avatar_split_clause,[],[f4572,f4491,f4451,f4575])).

fof(f4572,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK3)
    | ~ spl85_9 ),
    inference(resolution,[],[f4493,f4000])).

fof(f4000,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f3577])).

fof(f3577,plain,(
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

fof(f4559,plain,
    ( spl85_21
    | spl85_22 ),
    inference(avatar_split_clause,[],[f4383,f4555,f4551])).

fof(f4383,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7)
    | r1_tmap_1(sK3,sK1,sK4,sK7) ),
    inference(definition_unfolding,[],[f3840,f3846])).

fof(f3846,plain,(
    sK6 = sK7 ),
    inference(cnf_transformation,[],[f3456])).

fof(f3456,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( r1_tmap_1(X3,X1,X4,X6)
                                  <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) )
                                  & X6 = X7
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & r2_hidden(X6,X5)
                                  & v3_pre_topc(X5,X3)
                                  & m1_subset_1(X7,u1_struct_0(X2)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
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
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( r1_tmap_1(X3,X1,X4,X6)
                                  <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) )
                                  & X6 = X7
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & r2_hidden(X6,X5)
                                  & v3_pre_topc(X5,X3)
                                  & m1_subset_1(X7,u1_struct_0(X2)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3438])).

fof(f3438,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ( m1_pre_topc(X2,X3)
                         => ! [X5] :
                              ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
                             => ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X3))
                                 => ! [X7] :
                                      ( m1_subset_1(X7,u1_struct_0(X2))
                                     => ( ( X6 = X7
                                          & r1_tarski(X5,u1_struct_0(X2))
                                          & r2_hidden(X6,X5)
                                          & v3_pre_topc(X5,X3) )
                                       => ( r1_tmap_1(X3,X1,X4,X6)
                                        <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) ) ) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f3437])).

fof(f3437,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X2,X3)
                       => ! [X5] :
                            ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X3))
                               => ! [X7] :
                                    ( m1_subset_1(X7,u1_struct_0(X2))
                                   => ( ( X6 = X7
                                        & r1_tarski(X5,u1_struct_0(X2))
                                        & r2_hidden(X6,X5)
                                        & v3_pre_topc(X5,X3) )
                                     => ( r1_tmap_1(X3,X1,X4,X6)
                                      <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tmap_1)).

fof(f3840,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7)
    | r1_tmap_1(sK3,sK1,sK4,sK6) ),
    inference(cnf_transformation,[],[f3456])).

fof(f4558,plain,
    ( ~ spl85_21
    | ~ spl85_22 ),
    inference(avatar_split_clause,[],[f4382,f4555,f4551])).

fof(f4382,plain,
    ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7)
    | ~ r1_tmap_1(sK3,sK1,sK4,sK7) ),
    inference(definition_unfolding,[],[f3841,f3846])).

fof(f3841,plain,
    ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7)
    | ~ r1_tmap_1(sK3,sK1,sK4,sK6) ),
    inference(cnf_transformation,[],[f3456])).

fof(f4549,plain,(
    spl85_20 ),
    inference(avatar_split_clause,[],[f3842,f4546])).

fof(f3842,plain,(
    m1_subset_1(sK7,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f3456])).

fof(f4544,plain,(
    spl85_19 ),
    inference(avatar_split_clause,[],[f3843,f4541])).

fof(f3843,plain,(
    v3_pre_topc(sK5,sK3) ),
    inference(cnf_transformation,[],[f3456])).

fof(f4539,plain,(
    spl85_18 ),
    inference(avatar_split_clause,[],[f4381,f4536])).

fof(f4381,plain,(
    r2_hidden(sK7,sK5) ),
    inference(definition_unfolding,[],[f3844,f3846])).

fof(f3844,plain,(
    r2_hidden(sK6,sK5) ),
    inference(cnf_transformation,[],[f3456])).

fof(f4534,plain,(
    spl85_17 ),
    inference(avatar_split_clause,[],[f3845,f4531])).

fof(f3845,plain,(
    r1_tarski(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f3456])).

fof(f4529,plain,(
    spl85_16 ),
    inference(avatar_split_clause,[],[f4380,f4526])).

fof(f4380,plain,(
    m1_subset_1(sK7,u1_struct_0(sK3)) ),
    inference(definition_unfolding,[],[f3847,f3846])).

fof(f3847,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f3456])).

fof(f4524,plain,(
    spl85_15 ),
    inference(avatar_split_clause,[],[f3848,f4521])).

fof(f3848,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f3456])).

fof(f4519,plain,(
    spl85_14 ),
    inference(avatar_split_clause,[],[f3849,f4516])).

fof(f3849,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f3456])).

fof(f4514,plain,(
    spl85_13 ),
    inference(avatar_split_clause,[],[f3850,f4511])).

fof(f3850,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f3456])).

fof(f4509,plain,(
    spl85_12 ),
    inference(avatar_split_clause,[],[f3851,f4506])).

fof(f3851,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f3456])).

fof(f4504,plain,(
    spl85_11 ),
    inference(avatar_split_clause,[],[f3852,f4501])).

fof(f3852,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f3456])).

fof(f4499,plain,(
    ~ spl85_10 ),
    inference(avatar_split_clause,[],[f3853,f4496])).

fof(f3853,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f3456])).

fof(f4494,plain,(
    spl85_9 ),
    inference(avatar_split_clause,[],[f3854,f4491])).

fof(f3854,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f3456])).

fof(f4489,plain,(
    ~ spl85_8 ),
    inference(avatar_split_clause,[],[f3855,f4486])).

fof(f3855,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f3456])).

fof(f4484,plain,(
    spl85_7 ),
    inference(avatar_split_clause,[],[f3856,f4481])).

fof(f3856,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f3456])).

fof(f4479,plain,(
    ~ spl85_6 ),
    inference(avatar_split_clause,[],[f3857,f4476])).

fof(f3857,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f3456])).

fof(f4474,plain,(
    spl85_5 ),
    inference(avatar_split_clause,[],[f3858,f4471])).

fof(f3858,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f3456])).

fof(f4469,plain,(
    spl85_4 ),
    inference(avatar_split_clause,[],[f3859,f4466])).

fof(f3859,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f3456])).

fof(f4464,plain,(
    ~ spl85_3 ),
    inference(avatar_split_clause,[],[f3860,f4461])).

fof(f3860,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f3456])).

fof(f4459,plain,(
    spl85_2 ),
    inference(avatar_split_clause,[],[f3861,f4456])).

fof(f3861,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f3456])).

fof(f4454,plain,(
    spl85_1 ),
    inference(avatar_split_clause,[],[f3862,f4451])).

fof(f3862,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f3456])).
%------------------------------------------------------------------------------
