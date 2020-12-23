%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1776+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:32 EST 2020

% Result     : Theorem 8.74s
% Output     : Refutation 8.74s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 517 expanded)
%              Number of leaves         :   35 ( 284 expanded)
%              Depth                    :   10
%              Number of atoms          :  866 (8503 expanded)
%              Number of equality atoms :   31 ( 474 expanded)
%              Maximal formula depth    :   28 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11966,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f4730,f4731,f4736,f4741,f4746,f4756,f4761,f4766,f4771,f4776,f4781,f4782,f4787,f4792,f4797,f4802,f4807,f4812,f4817,f5172,f6299,f11886,f11938,f11943])).

fof(f11943,plain,
    ( ~ spl145_204
    | ~ spl145_6
    | ~ spl145_7
    | ~ spl145_11
    | spl145_12
    | ~ spl145_14
    | ~ spl145_15
    | spl145_16
    | spl145_738 ),
    inference(avatar_split_clause,[],[f11939,f11934,f4799,f4794,f4789,f4778,f4773,f4753,f4748,f6296])).

fof(f6296,plain,
    ( spl145_204
  <=> r1_tarski(u1_struct_0(sK8),u1_struct_0(sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl145_204])])).

fof(f4748,plain,
    ( spl145_6
  <=> m1_pre_topc(sK8,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl145_6])])).

fof(f4753,plain,
    ( spl145_7
  <=> v1_tsep_1(sK8,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl145_7])])).

fof(f4773,plain,
    ( spl145_11
  <=> m1_pre_topc(sK9,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl145_11])])).

fof(f4778,plain,
    ( spl145_12
  <=> v2_struct_0(sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl145_12])])).

fof(f4789,plain,
    ( spl145_14
  <=> l1_pre_topc(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl145_14])])).

fof(f4794,plain,
    ( spl145_15
  <=> v2_pre_topc(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl145_15])])).

fof(f4799,plain,
    ( spl145_16
  <=> v2_struct_0(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl145_16])])).

fof(f11934,plain,
    ( spl145_738
  <=> v1_tsep_1(sK8,sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl145_738])])).

fof(f11939,plain,
    ( ~ r1_tarski(u1_struct_0(sK8),u1_struct_0(sK9))
    | ~ spl145_6
    | ~ spl145_7
    | ~ spl145_11
    | spl145_12
    | ~ spl145_14
    | ~ spl145_15
    | spl145_16
    | spl145_738 ),
    inference(unit_resulting_resolution,[],[f4801,f4796,f4791,f4780,f4755,f4750,f4775,f11936,f4175])).

fof(f4175,plain,(
    ! [X2,X0,X1] :
      ( v1_tsep_1(X1,X2)
      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3544])).

fof(f3544,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X2)
                & v1_tsep_1(X1,X2) )
              | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_tsep_1(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3543])).

fof(f3543,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X2)
                & v1_tsep_1(X1,X2) )
              | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_tsep_1(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3362])).

fof(f3362,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & v1_tsep_1(X1,X0) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
               => ( m1_pre_topc(X1,X2)
                  & v1_tsep_1(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_tsep_1)).

fof(f11936,plain,
    ( ~ v1_tsep_1(sK8,sK9)
    | spl145_738 ),
    inference(avatar_component_clause,[],[f11934])).

fof(f4775,plain,
    ( m1_pre_topc(sK9,sK7)
    | ~ spl145_11 ),
    inference(avatar_component_clause,[],[f4773])).

fof(f4750,plain,
    ( m1_pre_topc(sK8,sK7)
    | ~ spl145_6 ),
    inference(avatar_component_clause,[],[f4748])).

fof(f4755,plain,
    ( v1_tsep_1(sK8,sK7)
    | ~ spl145_7 ),
    inference(avatar_component_clause,[],[f4753])).

fof(f4780,plain,
    ( ~ v2_struct_0(sK9)
    | spl145_12 ),
    inference(avatar_component_clause,[],[f4778])).

fof(f4791,plain,
    ( l1_pre_topc(sK7)
    | ~ spl145_14 ),
    inference(avatar_component_clause,[],[f4789])).

fof(f4796,plain,
    ( v2_pre_topc(sK7)
    | ~ spl145_15 ),
    inference(avatar_component_clause,[],[f4794])).

fof(f4801,plain,
    ( ~ v2_struct_0(sK7)
    | spl145_16 ),
    inference(avatar_component_clause,[],[f4799])).

fof(f11938,plain,
    ( spl145_16
    | ~ spl145_15
    | ~ spl145_14
    | spl145_19
    | ~ spl145_18
    | ~ spl145_17
    | spl145_13
    | ~ spl145_6
    | spl145_12
    | ~ spl145_11
    | ~ spl145_10
    | ~ spl145_9
    | ~ spl145_8
    | ~ spl145_738
    | ~ spl145_5
    | ~ spl145_4
    | ~ spl145_3
    | spl145_1
    | ~ spl145_2 ),
    inference(avatar_split_clause,[],[f11930,f4727,f4723,f4733,f4738,f4743,f11934,f4758,f4763,f4768,f4773,f4778,f4748,f4784,f4804,f4809,f4814,f4789,f4794,f4799])).

fof(f4814,plain,
    ( spl145_19
  <=> v2_struct_0(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl145_19])])).

fof(f4809,plain,
    ( spl145_18
  <=> v2_pre_topc(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl145_18])])).

fof(f4804,plain,
    ( spl145_17
  <=> l1_pre_topc(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl145_17])])).

fof(f4784,plain,
    ( spl145_13
  <=> v2_struct_0(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl145_13])])).

fof(f4768,plain,
    ( spl145_10
  <=> v1_funct_1(sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl145_10])])).

fof(f4763,plain,
    ( spl145_9
  <=> v1_funct_2(sK10,u1_struct_0(sK9),u1_struct_0(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl145_9])])).

fof(f4758,plain,
    ( spl145_8
  <=> m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK6)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl145_8])])).

fof(f4743,plain,
    ( spl145_5
  <=> m1_pre_topc(sK8,sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl145_5])])).

fof(f4738,plain,
    ( spl145_4
  <=> m1_subset_1(sK12,u1_struct_0(sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl145_4])])).

fof(f4733,plain,
    ( spl145_3
  <=> m1_subset_1(sK12,u1_struct_0(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl145_3])])).

fof(f4723,plain,
    ( spl145_1
  <=> r1_tmap_1(sK9,sK6,sK10,sK12) ),
    introduced(avatar_definition,[new_symbols(naming,[spl145_1])])).

fof(f4727,plain,
    ( spl145_2
  <=> r1_tmap_1(sK8,sK6,k3_tmap_1(sK7,sK6,sK9,sK8,sK10),sK12) ),
    introduced(avatar_definition,[new_symbols(naming,[spl145_2])])).

fof(f11930,plain,
    ( r1_tmap_1(sK9,sK6,sK10,sK12)
    | ~ m1_subset_1(sK12,u1_struct_0(sK8))
    | ~ m1_subset_1(sK12,u1_struct_0(sK9))
    | ~ m1_pre_topc(sK8,sK9)
    | ~ v1_tsep_1(sK8,sK9)
    | ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK6))))
    | ~ v1_funct_2(sK10,u1_struct_0(sK9),u1_struct_0(sK6))
    | ~ v1_funct_1(sK10)
    | ~ m1_pre_topc(sK9,sK7)
    | v2_struct_0(sK9)
    | ~ m1_pre_topc(sK8,sK7)
    | v2_struct_0(sK8)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK7)
    | ~ v2_pre_topc(sK7)
    | v2_struct_0(sK7)
    | ~ spl145_2 ),
    inference(resolution,[],[f4559,f4728])).

fof(f4728,plain,
    ( r1_tmap_1(sK8,sK6,k3_tmap_1(sK7,sK6,sK9,sK8,sK10),sK12)
    | ~ spl145_2 ),
    inference(avatar_component_clause,[],[f4727])).

fof(f4559,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
      | r1_tmap_1(X3,X1,X4,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_pre_topc(X2,X3)
      | ~ v1_tsep_1(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f4062])).

fof(f4062,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X5)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
      | X5 != X6
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_pre_topc(X2,X3)
      | ~ v1_tsep_1(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3800])).

fof(f3800,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( ( r1_tmap_1(X3,X1,X4,X5)
                                  | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                                & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                  | ~ r1_tmap_1(X3,X1,X4,X5) ) )
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ v1_tsep_1(X2,X3)
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
    inference(nnf_transformation,[],[f3462])).

fof(f3462,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X3,X1,X4,X5)
                              <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ v1_tsep_1(X2,X3)
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
    inference(flattening,[],[f3461])).

fof(f3461,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X3,X1,X4,X5)
                              <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ v1_tsep_1(X2,X3)
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
    inference(ennf_transformation,[],[f3440])).

fof(f3440,axiom,(
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
                     => ( ( m1_pre_topc(X2,X3)
                          & v1_tsep_1(X2,X3) )
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( X5 = X6
                                 => ( r1_tmap_1(X3,X1,X4,X5)
                                  <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tmap_1)).

fof(f11886,plain,
    ( ~ spl145_8
    | ~ spl145_1
    | spl145_2
    | ~ spl145_3
    | ~ spl145_4
    | ~ spl145_5
    | ~ spl145_6
    | ~ spl145_9
    | ~ spl145_10
    | ~ spl145_11
    | spl145_12
    | spl145_13
    | ~ spl145_14
    | ~ spl145_15
    | spl145_16
    | ~ spl145_17
    | ~ spl145_18
    | spl145_19 ),
    inference(avatar_split_clause,[],[f11836,f4814,f4809,f4804,f4799,f4794,f4789,f4784,f4778,f4773,f4768,f4763,f4748,f4743,f4738,f4733,f4727,f4723,f4758])).

fof(f11836,plain,
    ( ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK6))))
    | ~ spl145_1
    | spl145_2
    | ~ spl145_3
    | ~ spl145_4
    | ~ spl145_5
    | ~ spl145_6
    | ~ spl145_9
    | ~ spl145_10
    | ~ spl145_11
    | spl145_12
    | spl145_13
    | ~ spl145_14
    | ~ spl145_15
    | spl145_16
    | ~ spl145_17
    | ~ spl145_18
    | spl145_19 ),
    inference(unit_resulting_resolution,[],[f4801,f4796,f4791,f4816,f4811,f4806,f4780,f4770,f4786,f4775,f4750,f4745,f4735,f4740,f4724,f4765,f4729,f4558])).

fof(f4558,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( ~ r1_tmap_1(X2,X1,X4,X6)
      | r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f4060])).

fof(f4060,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
      | ~ r1_tmap_1(X2,X1,X4,X5)
      | ~ m1_pre_topc(X3,X2)
      | X5 != X6
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3460])).

fof(f3460,plain,(
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
    inference(flattening,[],[f3459])).

fof(f3459,plain,(
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
    inference(ennf_transformation,[],[f3435])).

fof(f3435,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_tmap_1)).

fof(f4729,plain,
    ( ~ r1_tmap_1(sK8,sK6,k3_tmap_1(sK7,sK6,sK9,sK8,sK10),sK12)
    | spl145_2 ),
    inference(avatar_component_clause,[],[f4727])).

fof(f4765,plain,
    ( v1_funct_2(sK10,u1_struct_0(sK9),u1_struct_0(sK6))
    | ~ spl145_9 ),
    inference(avatar_component_clause,[],[f4763])).

fof(f4724,plain,
    ( r1_tmap_1(sK9,sK6,sK10,sK12)
    | ~ spl145_1 ),
    inference(avatar_component_clause,[],[f4723])).

fof(f4740,plain,
    ( m1_subset_1(sK12,u1_struct_0(sK9))
    | ~ spl145_4 ),
    inference(avatar_component_clause,[],[f4738])).

fof(f4735,plain,
    ( m1_subset_1(sK12,u1_struct_0(sK8))
    | ~ spl145_3 ),
    inference(avatar_component_clause,[],[f4733])).

fof(f4745,plain,
    ( m1_pre_topc(sK8,sK9)
    | ~ spl145_5 ),
    inference(avatar_component_clause,[],[f4743])).

fof(f4786,plain,
    ( ~ v2_struct_0(sK8)
    | spl145_13 ),
    inference(avatar_component_clause,[],[f4784])).

fof(f4770,plain,
    ( v1_funct_1(sK10)
    | ~ spl145_10 ),
    inference(avatar_component_clause,[],[f4768])).

fof(f4806,plain,
    ( l1_pre_topc(sK6)
    | ~ spl145_17 ),
    inference(avatar_component_clause,[],[f4804])).

fof(f4811,plain,
    ( v2_pre_topc(sK6)
    | ~ spl145_18 ),
    inference(avatar_component_clause,[],[f4809])).

fof(f4816,plain,
    ( ~ v2_struct_0(sK6)
    | spl145_19 ),
    inference(avatar_component_clause,[],[f4814])).

fof(f6299,plain,
    ( spl145_204
    | ~ spl145_5
    | ~ spl145_63 ),
    inference(avatar_split_clause,[],[f6281,f5169,f4743,f6296])).

fof(f5169,plain,
    ( spl145_63
  <=> l1_pre_topc(sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl145_63])])).

fof(f6281,plain,
    ( r1_tarski(u1_struct_0(sK8),u1_struct_0(sK9))
    | ~ spl145_5
    | ~ spl145_63 ),
    inference(unit_resulting_resolution,[],[f5171,f4745,f4487])).

fof(f4487,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3739])).

fof(f3739,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3385])).

fof(f3385,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_borsuk_1)).

fof(f5171,plain,
    ( l1_pre_topc(sK9)
    | ~ spl145_63 ),
    inference(avatar_component_clause,[],[f5169])).

fof(f5172,plain,
    ( spl145_63
    | ~ spl145_11
    | ~ spl145_14 ),
    inference(avatar_split_clause,[],[f5167,f4789,f4773,f5169])).

fof(f5167,plain,
    ( l1_pre_topc(sK9)
    | ~ spl145_11
    | ~ spl145_14 ),
    inference(unit_resulting_resolution,[],[f4791,f4775,f4488])).

fof(f4488,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3740])).

fof(f3740,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f4817,plain,(
    ~ spl145_19 ),
    inference(avatar_split_clause,[],[f4034,f4814])).

fof(f4034,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f3799])).

fof(f3799,plain,
    ( ( ~ r1_tmap_1(sK8,sK6,k3_tmap_1(sK7,sK6,sK9,sK8,sK10),sK12)
      | ~ r1_tmap_1(sK9,sK6,sK10,sK11) )
    & ( r1_tmap_1(sK8,sK6,k3_tmap_1(sK7,sK6,sK9,sK8,sK10),sK12)
      | r1_tmap_1(sK9,sK6,sK10,sK11) )
    & sK11 = sK12
    & m1_subset_1(sK12,u1_struct_0(sK8))
    & m1_subset_1(sK11,u1_struct_0(sK9))
    & m1_pre_topc(sK8,sK9)
    & m1_pre_topc(sK8,sK7)
    & v1_tsep_1(sK8,sK7)
    & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK6))))
    & v1_funct_2(sK10,u1_struct_0(sK9),u1_struct_0(sK6))
    & v1_funct_1(sK10)
    & m1_pre_topc(sK9,sK7)
    & ~ v2_struct_0(sK9)
    & m1_pre_topc(sK8,sK7)
    & ~ v2_struct_0(sK8)
    & l1_pre_topc(sK7)
    & v2_pre_topc(sK7)
    & ~ v2_struct_0(sK7)
    & l1_pre_topc(sK6)
    & v2_pre_topc(sK6)
    & ~ v2_struct_0(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9,sK10,sK11,sK12])],[f3791,f3798,f3797,f3796,f3795,f3794,f3793,f3792])).

fof(f3792,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ? [X6] :
                                ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                                  | ~ r1_tmap_1(X3,X0,X4,X5) )
                                & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                                  | r1_tmap_1(X3,X0,X4,X5) )
                                & X5 = X6
                                & m1_subset_1(X6,u1_struct_0(X2)) )
                            & m1_subset_1(X5,u1_struct_0(X3)) )
                        & m1_pre_topc(X2,X3)
                        & m1_pre_topc(X2,X1)
                        & v1_tsep_1(X2,X1)
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                        & v1_funct_1(X4) )
                    & m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X1)
                & ~ v2_struct_0(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( ~ r1_tmap_1(X2,sK6,k3_tmap_1(X1,sK6,X3,X2,X4),X6)
                                | ~ r1_tmap_1(X3,sK6,X4,X5) )
                              & ( r1_tmap_1(X2,sK6,k3_tmap_1(X1,sK6,X3,X2,X4),X6)
                                | r1_tmap_1(X3,sK6,X4,X5) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & m1_pre_topc(X2,X1)
                      & v1_tsep_1(X2,X1)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK6))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK6))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK6)
      & v2_pre_topc(sK6)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f3793,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ( ~ r1_tmap_1(X2,sK6,k3_tmap_1(X1,sK6,X3,X2,X4),X6)
                              | ~ r1_tmap_1(X3,sK6,X4,X5) )
                            & ( r1_tmap_1(X2,sK6,k3_tmap_1(X1,sK6,X3,X2,X4),X6)
                              | r1_tmap_1(X3,sK6,X4,X5) )
                            & X5 = X6
                            & m1_subset_1(X6,u1_struct_0(X2)) )
                        & m1_subset_1(X5,u1_struct_0(X3)) )
                    & m1_pre_topc(X2,X3)
                    & m1_pre_topc(X2,X1)
                    & v1_tsep_1(X2,X1)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK6))))
                    & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK6))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,X1)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X1)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ( ~ r1_tmap_1(X2,sK6,k3_tmap_1(sK7,sK6,X3,X2,X4),X6)
                            | ~ r1_tmap_1(X3,sK6,X4,X5) )
                          & ( r1_tmap_1(X2,sK6,k3_tmap_1(sK7,sK6,X3,X2,X4),X6)
                            | r1_tmap_1(X3,sK6,X4,X5) )
                          & X5 = X6
                          & m1_subset_1(X6,u1_struct_0(X2)) )
                      & m1_subset_1(X5,u1_struct_0(X3)) )
                  & m1_pre_topc(X2,X3)
                  & m1_pre_topc(X2,sK7)
                  & v1_tsep_1(X2,sK7)
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK6))))
                  & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK6))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,sK7)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK7)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK7)
      & v2_pre_topc(sK7)
      & ~ v2_struct_0(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f3794,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ( ~ r1_tmap_1(X2,sK6,k3_tmap_1(sK7,sK6,X3,X2,X4),X6)
                          | ~ r1_tmap_1(X3,sK6,X4,X5) )
                        & ( r1_tmap_1(X2,sK6,k3_tmap_1(sK7,sK6,X3,X2,X4),X6)
                          | r1_tmap_1(X3,sK6,X4,X5) )
                        & X5 = X6
                        & m1_subset_1(X6,u1_struct_0(X2)) )
                    & m1_subset_1(X5,u1_struct_0(X3)) )
                & m1_pre_topc(X2,X3)
                & m1_pre_topc(X2,sK7)
                & v1_tsep_1(X2,sK7)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK6))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK6))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,sK7)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK7)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ( ~ r1_tmap_1(sK8,sK6,k3_tmap_1(sK7,sK6,X3,sK8,X4),X6)
                        | ~ r1_tmap_1(X3,sK6,X4,X5) )
                      & ( r1_tmap_1(sK8,sK6,k3_tmap_1(sK7,sK6,X3,sK8,X4),X6)
                        | r1_tmap_1(X3,sK6,X4,X5) )
                      & X5 = X6
                      & m1_subset_1(X6,u1_struct_0(sK8)) )
                  & m1_subset_1(X5,u1_struct_0(X3)) )
              & m1_pre_topc(sK8,X3)
              & m1_pre_topc(sK8,sK7)
              & v1_tsep_1(sK8,sK7)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK6))))
              & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK6))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,sK7)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK8,sK7)
      & ~ v2_struct_0(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f3795,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ( ~ r1_tmap_1(sK8,sK6,k3_tmap_1(sK7,sK6,X3,sK8,X4),X6)
                      | ~ r1_tmap_1(X3,sK6,X4,X5) )
                    & ( r1_tmap_1(sK8,sK6,k3_tmap_1(sK7,sK6,X3,sK8,X4),X6)
                      | r1_tmap_1(X3,sK6,X4,X5) )
                    & X5 = X6
                    & m1_subset_1(X6,u1_struct_0(sK8)) )
                & m1_subset_1(X5,u1_struct_0(X3)) )
            & m1_pre_topc(sK8,X3)
            & m1_pre_topc(sK8,sK7)
            & v1_tsep_1(sK8,sK7)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK6))))
            & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK6))
            & v1_funct_1(X4) )
        & m1_pre_topc(X3,sK7)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r1_tmap_1(sK8,sK6,k3_tmap_1(sK7,sK6,sK9,sK8,X4),X6)
                    | ~ r1_tmap_1(sK9,sK6,X4,X5) )
                  & ( r1_tmap_1(sK8,sK6,k3_tmap_1(sK7,sK6,sK9,sK8,X4),X6)
                    | r1_tmap_1(sK9,sK6,X4,X5) )
                  & X5 = X6
                  & m1_subset_1(X6,u1_struct_0(sK8)) )
              & m1_subset_1(X5,u1_struct_0(sK9)) )
          & m1_pre_topc(sK8,sK9)
          & m1_pre_topc(sK8,sK7)
          & v1_tsep_1(sK8,sK7)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK6))))
          & v1_funct_2(X4,u1_struct_0(sK9),u1_struct_0(sK6))
          & v1_funct_1(X4) )
      & m1_pre_topc(sK9,sK7)
      & ~ v2_struct_0(sK9) ) ),
    introduced(choice_axiom,[])).

fof(f3796,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ? [X6] :
                ( ( ~ r1_tmap_1(sK8,sK6,k3_tmap_1(sK7,sK6,sK9,sK8,X4),X6)
                  | ~ r1_tmap_1(sK9,sK6,X4,X5) )
                & ( r1_tmap_1(sK8,sK6,k3_tmap_1(sK7,sK6,sK9,sK8,X4),X6)
                  | r1_tmap_1(sK9,sK6,X4,X5) )
                & X5 = X6
                & m1_subset_1(X6,u1_struct_0(sK8)) )
            & m1_subset_1(X5,u1_struct_0(sK9)) )
        & m1_pre_topc(sK8,sK9)
        & m1_pre_topc(sK8,sK7)
        & v1_tsep_1(sK8,sK7)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK6))))
        & v1_funct_2(X4,u1_struct_0(sK9),u1_struct_0(sK6))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( ? [X6] :
              ( ( ~ r1_tmap_1(sK8,sK6,k3_tmap_1(sK7,sK6,sK9,sK8,sK10),X6)
                | ~ r1_tmap_1(sK9,sK6,sK10,X5) )
              & ( r1_tmap_1(sK8,sK6,k3_tmap_1(sK7,sK6,sK9,sK8,sK10),X6)
                | r1_tmap_1(sK9,sK6,sK10,X5) )
              & X5 = X6
              & m1_subset_1(X6,u1_struct_0(sK8)) )
          & m1_subset_1(X5,u1_struct_0(sK9)) )
      & m1_pre_topc(sK8,sK9)
      & m1_pre_topc(sK8,sK7)
      & v1_tsep_1(sK8,sK7)
      & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK6))))
      & v1_funct_2(sK10,u1_struct_0(sK9),u1_struct_0(sK6))
      & v1_funct_1(sK10) ) ),
    introduced(choice_axiom,[])).

fof(f3797,plain,
    ( ? [X5] :
        ( ? [X6] :
            ( ( ~ r1_tmap_1(sK8,sK6,k3_tmap_1(sK7,sK6,sK9,sK8,sK10),X6)
              | ~ r1_tmap_1(sK9,sK6,sK10,X5) )
            & ( r1_tmap_1(sK8,sK6,k3_tmap_1(sK7,sK6,sK9,sK8,sK10),X6)
              | r1_tmap_1(sK9,sK6,sK10,X5) )
            & X5 = X6
            & m1_subset_1(X6,u1_struct_0(sK8)) )
        & m1_subset_1(X5,u1_struct_0(sK9)) )
   => ( ? [X6] :
          ( ( ~ r1_tmap_1(sK8,sK6,k3_tmap_1(sK7,sK6,sK9,sK8,sK10),X6)
            | ~ r1_tmap_1(sK9,sK6,sK10,sK11) )
          & ( r1_tmap_1(sK8,sK6,k3_tmap_1(sK7,sK6,sK9,sK8,sK10),X6)
            | r1_tmap_1(sK9,sK6,sK10,sK11) )
          & sK11 = X6
          & m1_subset_1(X6,u1_struct_0(sK8)) )
      & m1_subset_1(sK11,u1_struct_0(sK9)) ) ),
    introduced(choice_axiom,[])).

fof(f3798,plain,
    ( ? [X6] :
        ( ( ~ r1_tmap_1(sK8,sK6,k3_tmap_1(sK7,sK6,sK9,sK8,sK10),X6)
          | ~ r1_tmap_1(sK9,sK6,sK10,sK11) )
        & ( r1_tmap_1(sK8,sK6,k3_tmap_1(sK7,sK6,sK9,sK8,sK10),X6)
          | r1_tmap_1(sK9,sK6,sK10,sK11) )
        & sK11 = X6
        & m1_subset_1(X6,u1_struct_0(sK8)) )
   => ( ( ~ r1_tmap_1(sK8,sK6,k3_tmap_1(sK7,sK6,sK9,sK8,sK10),sK12)
        | ~ r1_tmap_1(sK9,sK6,sK10,sK11) )
      & ( r1_tmap_1(sK8,sK6,k3_tmap_1(sK7,sK6,sK9,sK8,sK10),sK12)
        | r1_tmap_1(sK9,sK6,sK10,sK11) )
      & sK11 = sK12
      & m1_subset_1(sK12,u1_struct_0(sK8)) ) ),
    introduced(choice_axiom,[])).

fof(f3791,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                                | ~ r1_tmap_1(X3,X0,X4,X5) )
                              & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                                | r1_tmap_1(X3,X0,X4,X5) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & m1_pre_topc(X2,X1)
                      & v1_tsep_1(X2,X1)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3790])).

fof(f3790,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                                | ~ r1_tmap_1(X3,X0,X4,X5) )
                              & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                                | r1_tmap_1(X3,X0,X4,X5) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & m1_pre_topc(X2,X1)
                      & v1_tsep_1(X2,X1)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f3452])).

fof(f3452,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r1_tmap_1(X3,X0,X4,X5)
                              <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & m1_pre_topc(X2,X1)
                      & v1_tsep_1(X2,X1)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3451])).

fof(f3451,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r1_tmap_1(X3,X0,X4,X5)
                              <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & m1_pre_topc(X2,X1)
                      & v1_tsep_1(X2,X1)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3442])).

fof(f3442,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X1)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X1)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                          & v1_funct_1(X4) )
                       => ( ( m1_pre_topc(X2,X3)
                            & m1_pre_topc(X2,X1)
                            & v1_tsep_1(X2,X1) )
                         => ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X3))
                             => ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X2))
                                 => ( X5 = X6
                                   => ( r1_tmap_1(X3,X0,X4,X5)
                                    <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) ) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f3441])).

fof(f3441,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X1)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                        & v1_funct_1(X4) )
                     => ( ( m1_pre_topc(X2,X3)
                          & m1_pre_topc(X2,X1)
                          & v1_tsep_1(X2,X1) )
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( X5 = X6
                                 => ( r1_tmap_1(X3,X0,X4,X5)
                                  <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_tmap_1)).

fof(f4812,plain,(
    spl145_18 ),
    inference(avatar_split_clause,[],[f4035,f4809])).

fof(f4035,plain,(
    v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f3799])).

fof(f4807,plain,(
    spl145_17 ),
    inference(avatar_split_clause,[],[f4036,f4804])).

fof(f4036,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f3799])).

fof(f4802,plain,(
    ~ spl145_16 ),
    inference(avatar_split_clause,[],[f4037,f4799])).

fof(f4037,plain,(
    ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f3799])).

fof(f4797,plain,(
    spl145_15 ),
    inference(avatar_split_clause,[],[f4038,f4794])).

fof(f4038,plain,(
    v2_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f3799])).

fof(f4792,plain,(
    spl145_14 ),
    inference(avatar_split_clause,[],[f4039,f4789])).

fof(f4039,plain,(
    l1_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f3799])).

fof(f4787,plain,(
    ~ spl145_13 ),
    inference(avatar_split_clause,[],[f4040,f4784])).

fof(f4040,plain,(
    ~ v2_struct_0(sK8) ),
    inference(cnf_transformation,[],[f3799])).

fof(f4782,plain,(
    spl145_6 ),
    inference(avatar_split_clause,[],[f4041,f4748])).

fof(f4041,plain,(
    m1_pre_topc(sK8,sK7) ),
    inference(cnf_transformation,[],[f3799])).

fof(f4781,plain,(
    ~ spl145_12 ),
    inference(avatar_split_clause,[],[f4042,f4778])).

fof(f4042,plain,(
    ~ v2_struct_0(sK9) ),
    inference(cnf_transformation,[],[f3799])).

fof(f4776,plain,(
    spl145_11 ),
    inference(avatar_split_clause,[],[f4043,f4773])).

fof(f4043,plain,(
    m1_pre_topc(sK9,sK7) ),
    inference(cnf_transformation,[],[f3799])).

fof(f4771,plain,(
    spl145_10 ),
    inference(avatar_split_clause,[],[f4044,f4768])).

fof(f4044,plain,(
    v1_funct_1(sK10) ),
    inference(cnf_transformation,[],[f3799])).

fof(f4766,plain,(
    spl145_9 ),
    inference(avatar_split_clause,[],[f4045,f4763])).

fof(f4045,plain,(
    v1_funct_2(sK10,u1_struct_0(sK9),u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f3799])).

fof(f4761,plain,(
    spl145_8 ),
    inference(avatar_split_clause,[],[f4046,f4758])).

fof(f4046,plain,(
    m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK6)))) ),
    inference(cnf_transformation,[],[f3799])).

fof(f4756,plain,(
    spl145_7 ),
    inference(avatar_split_clause,[],[f4047,f4753])).

fof(f4047,plain,(
    v1_tsep_1(sK8,sK7) ),
    inference(cnf_transformation,[],[f3799])).

fof(f4746,plain,(
    spl145_5 ),
    inference(avatar_split_clause,[],[f4049,f4743])).

fof(f4049,plain,(
    m1_pre_topc(sK8,sK9) ),
    inference(cnf_transformation,[],[f3799])).

fof(f4741,plain,(
    spl145_4 ),
    inference(avatar_split_clause,[],[f4557,f4738])).

fof(f4557,plain,(
    m1_subset_1(sK12,u1_struct_0(sK9)) ),
    inference(definition_unfolding,[],[f4050,f4052])).

fof(f4052,plain,(
    sK11 = sK12 ),
    inference(cnf_transformation,[],[f3799])).

fof(f4050,plain,(
    m1_subset_1(sK11,u1_struct_0(sK9)) ),
    inference(cnf_transformation,[],[f3799])).

fof(f4736,plain,(
    spl145_3 ),
    inference(avatar_split_clause,[],[f4051,f4733])).

fof(f4051,plain,(
    m1_subset_1(sK12,u1_struct_0(sK8)) ),
    inference(cnf_transformation,[],[f3799])).

fof(f4731,plain,
    ( spl145_1
    | spl145_2 ),
    inference(avatar_split_clause,[],[f4556,f4727,f4723])).

fof(f4556,plain,
    ( r1_tmap_1(sK8,sK6,k3_tmap_1(sK7,sK6,sK9,sK8,sK10),sK12)
    | r1_tmap_1(sK9,sK6,sK10,sK12) ),
    inference(definition_unfolding,[],[f4053,f4052])).

fof(f4053,plain,
    ( r1_tmap_1(sK8,sK6,k3_tmap_1(sK7,sK6,sK9,sK8,sK10),sK12)
    | r1_tmap_1(sK9,sK6,sK10,sK11) ),
    inference(cnf_transformation,[],[f3799])).

fof(f4730,plain,
    ( ~ spl145_1
    | ~ spl145_2 ),
    inference(avatar_split_clause,[],[f4555,f4727,f4723])).

fof(f4555,plain,
    ( ~ r1_tmap_1(sK8,sK6,k3_tmap_1(sK7,sK6,sK9,sK8,sK10),sK12)
    | ~ r1_tmap_1(sK9,sK6,sK10,sK12) ),
    inference(definition_unfolding,[],[f4054,f4052])).

fof(f4054,plain,
    ( ~ r1_tmap_1(sK8,sK6,k3_tmap_1(sK7,sK6,sK9,sK8,sK10),sK12)
    | ~ r1_tmap_1(sK9,sK6,sK10,sK11) ),
    inference(cnf_transformation,[],[f3799])).
%------------------------------------------------------------------------------
