%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT2066+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:07 EST 2020

% Result     : Theorem 0.11s
% Output     : Refutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :  198 ( 584 expanded)
%              Number of leaves         :   42 ( 249 expanded)
%              Depth                    :   26
%              Number of atoms          : 1301 (5985 expanded)
%              Number of equality atoms :   19 (  30 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1040,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f83,f88,f93,f98,f103,f108,f113,f118,f123,f127,f132,f137,f142,f147,f199,f211,f303,f313,f332,f352,f353,f645,f721,f726,f978,f1031,f1038,f1039])).

fof(f1039,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | r2_hidden(sK3,sK1)
    | ~ r2_hidden(sK3,k2_pre_topc(sK0,k2_pre_topc(sK0,sK1))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1038,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | r1_waybel_0(sK0,sK2,k2_pre_topc(sK0,sK1))
    | ~ r1_waybel_0(sK0,sK2,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1031,plain,
    ( ~ spl6_47
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_14
    | spl6_15
    | ~ spl6_16
    | spl6_20
    | ~ spl6_21
    | ~ spl6_46 ),
    inference(avatar_split_clause,[],[f1030,f718,f260,f255,f196,f144,f139,f134,f129,f125,f723])).

fof(f723,plain,
    ( spl6_47
  <=> v3_yellow_6(sK4(sK0,sK1,sK5(k2_pre_topc(sK0,sK1),sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_47])])).

fof(f125,plain,
    ( spl6_11
  <=> ! [X5,X4] :
        ( r2_hidden(X5,sK1)
        | v2_struct_0(X4)
        | ~ v4_orders_2(X4)
        | ~ v7_waybel_0(X4)
        | ~ v3_yellow_6(X4,sK0)
        | ~ l1_waybel_0(X4,sK0)
        | ~ r1_waybel_0(sK0,X4,sK1)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ r2_hidden(X5,k10_yellow_6(sK0,X4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f129,plain,
    ( spl6_12
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f134,plain,
    ( spl6_13
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f139,plain,
    ( spl6_14
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f144,plain,
    ( spl6_15
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f196,plain,
    ( spl6_16
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f255,plain,
    ( spl6_20
  <=> r2_hidden(sK5(k2_pre_topc(sK0,sK1),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f260,plain,
    ( spl6_21
  <=> r2_hidden(sK5(k2_pre_topc(sK0,sK1),sK1),k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f718,plain,
    ( spl6_46
  <=> l1_waybel_0(sK4(sK0,sK1,sK5(k2_pre_topc(sK0,sK1),sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).

fof(f1030,plain,
    ( ~ v3_yellow_6(sK4(sK0,sK1,sK5(k2_pre_topc(sK0,sK1),sK1)),sK0)
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_14
    | spl6_15
    | ~ spl6_16
    | spl6_20
    | ~ spl6_21
    | ~ spl6_46 ),
    inference(subsumption_resolution,[],[f1029,f262])).

fof(f262,plain,
    ( r2_hidden(sK5(k2_pre_topc(sK0,sK1),sK1),k2_pre_topc(sK0,sK1))
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f260])).

fof(f1029,plain,
    ( ~ v3_yellow_6(sK4(sK0,sK1,sK5(k2_pre_topc(sK0,sK1),sK1)),sK0)
    | ~ r2_hidden(sK5(k2_pre_topc(sK0,sK1),sK1),k2_pre_topc(sK0,sK1))
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_14
    | spl6_15
    | ~ spl6_16
    | spl6_20
    | ~ spl6_46 ),
    inference(subsumption_resolution,[],[f1025,f257])).

fof(f257,plain,
    ( ~ r2_hidden(sK5(k2_pre_topc(sK0,sK1),sK1),sK1)
    | spl6_20 ),
    inference(avatar_component_clause,[],[f255])).

fof(f1025,plain,
    ( ~ v3_yellow_6(sK4(sK0,sK1,sK5(k2_pre_topc(sK0,sK1),sK1)),sK0)
    | r2_hidden(sK5(k2_pre_topc(sK0,sK1),sK1),sK1)
    | ~ r2_hidden(sK5(k2_pre_topc(sK0,sK1),sK1),k2_pre_topc(sK0,sK1))
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_14
    | spl6_15
    | ~ spl6_16
    | ~ spl6_46 ),
    inference(resolution,[],[f720,f921])).

fof(f921,plain,
    ( ! [X0] :
        ( ~ l1_waybel_0(sK4(sK0,sK1,X0),sK0)
        | ~ v3_yellow_6(sK4(sK0,sK1,X0),sK0)
        | r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,k2_pre_topc(sK0,sK1)) )
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_14
    | spl6_15
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f506,f377])).

fof(f377,plain,
    ( ! [X9] :
        ( ~ r2_hidden(X9,k2_pre_topc(sK0,sK1))
        | m1_subset_1(X9,u1_struct_0(sK0)) )
    | ~ spl6_16 ),
    inference(resolution,[],[f198,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f198,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f196])).

fof(f506,plain,
    ( ! [X0] :
        ( ~ v3_yellow_6(sK4(sK0,sK1,X0),sK0)
        | ~ l1_waybel_0(sK4(sK0,sK1,X0),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,k2_pre_topc(sK0,sK1)) )
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_14
    | spl6_15 ),
    inference(subsumption_resolution,[],[f505,f218])).

fof(f218,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_pre_topc(sK0,sK1))
        | ~ v2_struct_0(sK4(sK0,sK1,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_14
    | spl6_15 ),
    inference(subsumption_resolution,[],[f217,f146])).

fof(f146,plain,
    ( ~ v2_struct_0(sK0)
    | spl6_15 ),
    inference(avatar_component_clause,[],[f144])).

fof(f217,plain,
    ( ! [X0] :
        ( ~ v2_struct_0(sK4(sK0,sK1,X0))
        | ~ r2_hidden(X0,k2_pre_topc(sK0,sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f216,f141])).

fof(f141,plain,
    ( v2_pre_topc(sK0)
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f139])).

fof(f216,plain,
    ( ! [X0] :
        ( ~ v2_struct_0(sK4(sK0,sK1,X0))
        | ~ r2_hidden(X0,k2_pre_topc(sK0,sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_12
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f185,f136])).

fof(f136,plain,
    ( l1_pre_topc(sK0)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f134])).

fof(f185,plain,
    ( ! [X0] :
        ( ~ v2_struct_0(sK4(sK0,sK1,X0))
        | ~ r2_hidden(X0,k2_pre_topc(sK0,sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_12 ),
    inference(resolution,[],[f131,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(sK4(X0,X1,X2))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ! [X3] :
                      ( ~ r2_hidden(X2,k10_yellow_6(X0,X3))
                      | ~ r1_waybel_0(X0,X3,X1)
                      | ~ l1_waybel_0(X3,X0)
                      | ~ v3_yellow_6(X3,X0)
                      | ~ v7_waybel_0(X3)
                      | ~ v4_orders_2(X3)
                      | v2_struct_0(X3) ) )
                & ( ( r2_hidden(X2,k10_yellow_6(X0,sK4(X0,X1,X2)))
                    & r1_waybel_0(X0,sK4(X0,X1,X2),X1)
                    & l1_waybel_0(sK4(X0,X1,X2),X0)
                    & v3_yellow_6(sK4(X0,X1,X2),X0)
                    & v7_waybel_0(sK4(X0,X1,X2))
                    & v4_orders_2(sK4(X0,X1,X2))
                    & ~ v2_struct_0(sK4(X0,X1,X2)) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f31,f32])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X2,k10_yellow_6(X0,X4))
          & r1_waybel_0(X0,X4,X1)
          & l1_waybel_0(X4,X0)
          & v3_yellow_6(X4,X0)
          & v7_waybel_0(X4)
          & v4_orders_2(X4)
          & ~ v2_struct_0(X4) )
     => ( r2_hidden(X2,k10_yellow_6(X0,sK4(X0,X1,X2)))
        & r1_waybel_0(X0,sK4(X0,X1,X2),X1)
        & l1_waybel_0(sK4(X0,X1,X2),X0)
        & v3_yellow_6(sK4(X0,X1,X2),X0)
        & v7_waybel_0(sK4(X0,X1,X2))
        & v4_orders_2(sK4(X0,X1,X2))
        & ~ v2_struct_0(sK4(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ! [X3] :
                      ( ~ r2_hidden(X2,k10_yellow_6(X0,X3))
                      | ~ r1_waybel_0(X0,X3,X1)
                      | ~ l1_waybel_0(X3,X0)
                      | ~ v3_yellow_6(X3,X0)
                      | ~ v7_waybel_0(X3)
                      | ~ v4_orders_2(X3)
                      | v2_struct_0(X3) ) )
                & ( ? [X4] :
                      ( r2_hidden(X2,k10_yellow_6(X0,X4))
                      & r1_waybel_0(X0,X4,X1)
                      & l1_waybel_0(X4,X0)
                      & v3_yellow_6(X4,X0)
                      & v7_waybel_0(X4)
                      & v4_orders_2(X4)
                      & ~ v2_struct_0(X4) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ! [X3] :
                      ( ~ r2_hidden(X2,k10_yellow_6(X0,X3))
                      | ~ r1_waybel_0(X0,X3,X1)
                      | ~ l1_waybel_0(X3,X0)
                      | ~ v3_yellow_6(X3,X0)
                      | ~ v7_waybel_0(X3)
                      | ~ v4_orders_2(X3)
                      | v2_struct_0(X3) ) )
                & ( ? [X3] :
                      ( r2_hidden(X2,k10_yellow_6(X0,X3))
                      & r1_waybel_0(X0,X3,X1)
                      & l1_waybel_0(X3,X0)
                      & v3_yellow_6(X3,X0)
                      & v7_waybel_0(X3)
                      & v4_orders_2(X3)
                      & ~ v2_struct_0(X3) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ? [X3] :
                    ( r2_hidden(X2,k10_yellow_6(X0,X3))
                    & r1_waybel_0(X0,X3,X1)
                    & l1_waybel_0(X3,X0)
                    & v3_yellow_6(X3,X0)
                    & v7_waybel_0(X3)
                    & v4_orders_2(X3)
                    & ~ v2_struct_0(X3) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ? [X3] :
                    ( r2_hidden(X2,k10_yellow_6(X0,X3))
                    & r1_waybel_0(X0,X3,X1)
                    & l1_waybel_0(X3,X0)
                    & v3_yellow_6(X3,X0)
                    & v7_waybel_0(X3)
                    & v4_orders_2(X3)
                    & ~ v2_struct_0(X3) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ? [X3] :
                    ( r2_hidden(X2,k10_yellow_6(X0,X3))
                    & r1_waybel_0(X0,X3,X1)
                    & l1_waybel_0(X3,X0)
                    & v3_yellow_6(X3,X0)
                    & v7_waybel_0(X3)
                    & v4_orders_2(X3)
                    & ~ v2_struct_0(X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_yellow19)).

fof(f131,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f129])).

fof(f505,plain,
    ( ! [X0] :
        ( ~ v3_yellow_6(sK4(sK0,sK1,X0),sK0)
        | ~ l1_waybel_0(sK4(sK0,sK1,X0),sK0)
        | v2_struct_0(sK4(sK0,sK1,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,k2_pre_topc(sK0,sK1)) )
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_14
    | spl6_15 ),
    inference(subsumption_resolution,[],[f504,f224])).

fof(f224,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k2_pre_topc(sK0,sK1))
        | v7_waybel_0(sK4(sK0,sK1,X2))
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_14
    | spl6_15 ),
    inference(subsumption_resolution,[],[f223,f146])).

fof(f223,plain,
    ( ! [X2] :
        ( v7_waybel_0(sK4(sK0,sK1,X2))
        | ~ r2_hidden(X2,k2_pre_topc(sK0,sK1))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f222,f141])).

fof(f222,plain,
    ( ! [X2] :
        ( v7_waybel_0(sK4(sK0,sK1,X2))
        | ~ r2_hidden(X2,k2_pre_topc(sK0,sK1))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_12
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f187,f136])).

fof(f187,plain,
    ( ! [X2] :
        ( v7_waybel_0(sK4(sK0,sK1,X2))
        | ~ r2_hidden(X2,k2_pre_topc(sK0,sK1))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_12 ),
    inference(resolution,[],[f131,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v7_waybel_0(sK4(X0,X1,X2))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f504,plain,
    ( ! [X0] :
        ( ~ v7_waybel_0(sK4(sK0,sK1,X0))
        | ~ v3_yellow_6(sK4(sK0,sK1,X0),sK0)
        | ~ l1_waybel_0(sK4(sK0,sK1,X0),sK0)
        | v2_struct_0(sK4(sK0,sK1,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,k2_pre_topc(sK0,sK1)) )
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_14
    | spl6_15 ),
    inference(subsumption_resolution,[],[f503,f221])).

fof(f221,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k2_pre_topc(sK0,sK1))
        | v4_orders_2(sK4(sK0,sK1,X1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_14
    | spl6_15 ),
    inference(subsumption_resolution,[],[f220,f146])).

fof(f220,plain,
    ( ! [X1] :
        ( v4_orders_2(sK4(sK0,sK1,X1))
        | ~ r2_hidden(X1,k2_pre_topc(sK0,sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f219,f141])).

% (9122)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
fof(f219,plain,
    ( ! [X1] :
        ( v4_orders_2(sK4(sK0,sK1,X1))
        | ~ r2_hidden(X1,k2_pre_topc(sK0,sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_12
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f186,f136])).

fof(f186,plain,
    ( ! [X1] :
        ( v4_orders_2(sK4(sK0,sK1,X1))
        | ~ r2_hidden(X1,k2_pre_topc(sK0,sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_12 ),
    inference(resolution,[],[f131,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v4_orders_2(sK4(X0,X1,X2))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f503,plain,
    ( ! [X0] :
        ( ~ v4_orders_2(sK4(sK0,sK1,X0))
        | ~ v7_waybel_0(sK4(sK0,sK1,X0))
        | ~ v3_yellow_6(sK4(sK0,sK1,X0),sK0)
        | ~ l1_waybel_0(sK4(sK0,sK1,X0),sK0)
        | v2_struct_0(sK4(sK0,sK1,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,k2_pre_topc(sK0,sK1)) )
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_14
    | spl6_15 ),
    inference(subsumption_resolution,[],[f502,f146])).

fof(f502,plain,
    ( ! [X0] :
        ( ~ v4_orders_2(sK4(sK0,sK1,X0))
        | ~ v7_waybel_0(sK4(sK0,sK1,X0))
        | ~ v3_yellow_6(sK4(sK0,sK1,X0),sK0)
        | ~ l1_waybel_0(sK4(sK0,sK1,X0),sK0)
        | v2_struct_0(sK4(sK0,sK1,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,k2_pre_topc(sK0,sK1))
        | v2_struct_0(sK0) )
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_14
    | spl6_15 ),
    inference(subsumption_resolution,[],[f501,f141])).

fof(f501,plain,
    ( ! [X0] :
        ( ~ v4_orders_2(sK4(sK0,sK1,X0))
        | ~ v7_waybel_0(sK4(sK0,sK1,X0))
        | ~ v3_yellow_6(sK4(sK0,sK1,X0),sK0)
        | ~ l1_waybel_0(sK4(sK0,sK1,X0),sK0)
        | v2_struct_0(sK4(sK0,sK1,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,k2_pre_topc(sK0,sK1))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_14
    | spl6_15 ),
    inference(subsumption_resolution,[],[f500,f136])).

fof(f500,plain,
    ( ! [X0] :
        ( ~ v4_orders_2(sK4(sK0,sK1,X0))
        | ~ v7_waybel_0(sK4(sK0,sK1,X0))
        | ~ v3_yellow_6(sK4(sK0,sK1,X0),sK0)
        | ~ l1_waybel_0(sK4(sK0,sK1,X0),sK0)
        | v2_struct_0(sK4(sK0,sK1,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,k2_pre_topc(sK0,sK1))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_14
    | spl6_15 ),
    inference(subsumption_resolution,[],[f499,f131])).

fof(f499,plain,
    ( ! [X0] :
        ( ~ v4_orders_2(sK4(sK0,sK1,X0))
        | ~ v7_waybel_0(sK4(sK0,sK1,X0))
        | ~ v3_yellow_6(sK4(sK0,sK1,X0),sK0)
        | ~ l1_waybel_0(sK4(sK0,sK1,X0),sK0)
        | v2_struct_0(sK4(sK0,sK1,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,k2_pre_topc(sK0,sK1))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_14
    | spl6_15 ),
    inference(duplicate_literal_removal,[],[f498])).

fof(f498,plain,
    ( ! [X0] :
        ( ~ v4_orders_2(sK4(sK0,sK1,X0))
        | ~ v7_waybel_0(sK4(sK0,sK1,X0))
        | ~ v3_yellow_6(sK4(sK0,sK1,X0),sK0)
        | ~ l1_waybel_0(sK4(sK0,sK1,X0),sK0)
        | v2_struct_0(sK4(sK0,sK1,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,k2_pre_topc(sK0,sK1))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,k2_pre_topc(sK0,sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_14
    | spl6_15 ),
    inference(resolution,[],[f234,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r1_waybel_0(X0,sK4(X0,X1,X2),X1)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f234,plain,
    ( ! [X0,X1] :
        ( ~ r1_waybel_0(sK0,sK4(sK0,X0,X1),sK1)
        | ~ v4_orders_2(sK4(sK0,X0,X1))
        | ~ v7_waybel_0(sK4(sK0,X0,X1))
        | ~ v3_yellow_6(sK4(sK0,X0,X1),sK0)
        | ~ l1_waybel_0(sK4(sK0,X0,X1),sK0)
        | v2_struct_0(sK4(sK0,X0,X1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_hidden(X1,sK1)
        | ~ r2_hidden(X1,k2_pre_topc(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_14
    | spl6_15 ),
    inference(subsumption_resolution,[],[f233,f146])).

fof(f233,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK4(sK0,X0,X1))
        | ~ v4_orders_2(sK4(sK0,X0,X1))
        | ~ v7_waybel_0(sK4(sK0,X0,X1))
        | ~ v3_yellow_6(sK4(sK0,X0,X1),sK0)
        | ~ l1_waybel_0(sK4(sK0,X0,X1),sK0)
        | ~ r1_waybel_0(sK0,sK4(sK0,X0,X1),sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_hidden(X1,sK1)
        | ~ r2_hidden(X1,k2_pre_topc(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_struct_0(sK0) )
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f232,f141])).

fof(f232,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK4(sK0,X0,X1))
        | ~ v4_orders_2(sK4(sK0,X0,X1))
        | ~ v7_waybel_0(sK4(sK0,X0,X1))
        | ~ v3_yellow_6(sK4(sK0,X0,X1),sK0)
        | ~ l1_waybel_0(sK4(sK0,X0,X1),sK0)
        | ~ r1_waybel_0(sK0,sK4(sK0,X0,X1),sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_hidden(X1,sK1)
        | ~ r2_hidden(X1,k2_pre_topc(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_11
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f231,f136])).

fof(f231,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK4(sK0,X0,X1))
        | ~ v4_orders_2(sK4(sK0,X0,X1))
        | ~ v7_waybel_0(sK4(sK0,X0,X1))
        | ~ v3_yellow_6(sK4(sK0,X0,X1),sK0)
        | ~ l1_waybel_0(sK4(sK0,X0,X1),sK0)
        | ~ r1_waybel_0(sK0,sK4(sK0,X0,X1),sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_hidden(X1,sK1)
        | ~ r2_hidden(X1,k2_pre_topc(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_11 ),
    inference(duplicate_literal_removal,[],[f228])).

fof(f228,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK4(sK0,X0,X1))
        | ~ v4_orders_2(sK4(sK0,X0,X1))
        | ~ v7_waybel_0(sK4(sK0,X0,X1))
        | ~ v3_yellow_6(sK4(sK0,X0,X1),sK0)
        | ~ l1_waybel_0(sK4(sK0,X0,X1),sK0)
        | ~ r1_waybel_0(sK0,sK4(sK0,X0,X1),sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_hidden(X1,sK1)
        | ~ r2_hidden(X1,k2_pre_topc(sK0,X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_11 ),
    inference(resolution,[],[f126,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k10_yellow_6(X0,sK4(X0,X1,X2)))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f126,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X5,k10_yellow_6(sK0,X4))
        | v2_struct_0(X4)
        | ~ v4_orders_2(X4)
        | ~ v7_waybel_0(X4)
        | ~ v3_yellow_6(X4,sK0)
        | ~ l1_waybel_0(X4,sK0)
        | ~ r1_waybel_0(sK0,X4,sK1)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | r2_hidden(X5,sK1) )
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f125])).

fof(f720,plain,
    ( l1_waybel_0(sK4(sK0,sK1,sK5(k2_pre_topc(sK0,sK1),sK1)),sK0)
    | ~ spl6_46 ),
    inference(avatar_component_clause,[],[f718])).

fof(f978,plain,
    ( ~ spl6_58
    | spl6_59
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | spl6_10
    | ~ spl6_13
    | ~ spl6_14
    | spl6_15
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f969,f196,f144,f139,f134,f120,f115,f110,f105,f100,f90,f85,f975,f971])).

fof(f971,plain,
    ( spl6_58
  <=> r1_waybel_0(sK0,sK2,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_58])])).

fof(f975,plain,
    ( spl6_59
  <=> r2_hidden(sK3,k2_pre_topc(sK0,k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_59])])).

fof(f85,plain,
    ( spl6_3
  <=> r2_hidden(sK3,k10_yellow_6(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f90,plain,
    ( spl6_4
  <=> m1_subset_1(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f100,plain,
    ( spl6_6
  <=> l1_waybel_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f105,plain,
    ( spl6_7
  <=> v3_yellow_6(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f110,plain,
    ( spl6_8
  <=> v7_waybel_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f115,plain,
    ( spl6_9
  <=> v4_orders_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f120,plain,
    ( spl6_10
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f969,plain,
    ( r2_hidden(sK3,k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)))
    | ~ r1_waybel_0(sK0,sK2,k2_pre_topc(sK0,sK1))
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | spl6_10
    | ~ spl6_13
    | ~ spl6_14
    | spl6_15
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f968,f92])).

fof(f92,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f90])).

fof(f968,plain,
    ( r2_hidden(sK3,k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)))
    | ~ r1_waybel_0(sK0,sK2,k2_pre_topc(sK0,sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | spl6_10
    | ~ spl6_13
    | ~ spl6_14
    | spl6_15
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f967,f122])).

fof(f122,plain,
    ( ~ v2_struct_0(sK2)
    | spl6_10 ),
    inference(avatar_component_clause,[],[f120])).

fof(f967,plain,
    ( r2_hidden(sK3,k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)))
    | ~ r1_waybel_0(sK0,sK2,k2_pre_topc(sK0,sK1))
    | v2_struct_0(sK2)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_13
    | ~ spl6_14
    | spl6_15
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f966,f117])).

fof(f117,plain,
    ( v4_orders_2(sK2)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f115])).

fof(f966,plain,
    ( r2_hidden(sK3,k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)))
    | ~ r1_waybel_0(sK0,sK2,k2_pre_topc(sK0,sK1))
    | ~ v4_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_13
    | ~ spl6_14
    | spl6_15
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f965,f112])).

fof(f112,plain,
    ( v7_waybel_0(sK2)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f110])).

fof(f965,plain,
    ( r2_hidden(sK3,k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)))
    | ~ r1_waybel_0(sK0,sK2,k2_pre_topc(sK0,sK1))
    | ~ v7_waybel_0(sK2)
    | ~ v4_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_13
    | ~ spl6_14
    | spl6_15
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f964,f107])).

fof(f107,plain,
    ( v3_yellow_6(sK2,sK0)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f105])).

fof(f964,plain,
    ( r2_hidden(sK3,k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)))
    | ~ r1_waybel_0(sK0,sK2,k2_pre_topc(sK0,sK1))
    | ~ v3_yellow_6(sK2,sK0)
    | ~ v7_waybel_0(sK2)
    | ~ v4_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_13
    | ~ spl6_14
    | spl6_15
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f959,f102])).

fof(f102,plain,
    ( l1_waybel_0(sK2,sK0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f100])).

fof(f959,plain,
    ( r2_hidden(sK3,k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)))
    | ~ r1_waybel_0(sK0,sK2,k2_pre_topc(sK0,sK1))
    | ~ l1_waybel_0(sK2,sK0)
    | ~ v3_yellow_6(sK2,sK0)
    | ~ v7_waybel_0(sK2)
    | ~ v4_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl6_3
    | ~ spl6_13
    | ~ spl6_14
    | spl6_15
    | ~ spl6_16 ),
    inference(resolution,[],[f413,f87])).

fof(f87,plain,
    ( r2_hidden(sK3,k10_yellow_6(sK0,sK2))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f85])).

fof(f413,plain,
    ( ! [X8,X7] :
        ( ~ r2_hidden(X7,k10_yellow_6(sK0,X8))
        | r2_hidden(X7,k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)))
        | ~ r1_waybel_0(sK0,X8,k2_pre_topc(sK0,sK1))
        | ~ l1_waybel_0(X8,sK0)
        | ~ v3_yellow_6(X8,sK0)
        | ~ v7_waybel_0(X8)
        | ~ v4_orders_2(X8)
        | v2_struct_0(X8)
        | ~ m1_subset_1(X7,u1_struct_0(sK0)) )
    | ~ spl6_13
    | ~ spl6_14
    | spl6_15
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f412,f146])).

fof(f412,plain,
    ( ! [X8,X7] :
        ( r2_hidden(X7,k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)))
        | ~ r2_hidden(X7,k10_yellow_6(sK0,X8))
        | ~ r1_waybel_0(sK0,X8,k2_pre_topc(sK0,sK1))
        | ~ l1_waybel_0(X8,sK0)
        | ~ v3_yellow_6(X8,sK0)
        | ~ v7_waybel_0(X8)
        | ~ v4_orders_2(X8)
        | v2_struct_0(X8)
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f411,f141])).

fof(f411,plain,
    ( ! [X8,X7] :
        ( r2_hidden(X7,k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)))
        | ~ r2_hidden(X7,k10_yellow_6(sK0,X8))
        | ~ r1_waybel_0(sK0,X8,k2_pre_topc(sK0,sK1))
        | ~ l1_waybel_0(X8,sK0)
        | ~ v3_yellow_6(X8,sK0)
        | ~ v7_waybel_0(X8)
        | ~ v4_orders_2(X8)
        | v2_struct_0(X8)
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_13
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f375,f136])).

fof(f375,plain,
    ( ! [X8,X7] :
        ( r2_hidden(X7,k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)))
        | ~ r2_hidden(X7,k10_yellow_6(sK0,X8))
        | ~ r1_waybel_0(sK0,X8,k2_pre_topc(sK0,sK1))
        | ~ l1_waybel_0(X8,sK0)
        | ~ v3_yellow_6(X8,sK0)
        | ~ v7_waybel_0(X8)
        | ~ v4_orders_2(X8)
        | v2_struct_0(X8)
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_16 ),
    inference(resolution,[],[f198,f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ r2_hidden(X2,k10_yellow_6(X0,X3))
      | ~ r1_waybel_0(X0,X3,X1)
      | ~ l1_waybel_0(X3,X0)
      | ~ v3_yellow_6(X3,X0)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f726,plain,
    ( spl6_47
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_14
    | spl6_15
    | ~ spl6_21
    | ~ spl6_40 ),
    inference(avatar_split_clause,[],[f693,f640,f260,f144,f139,f134,f129,f723])).

fof(f640,plain,
    ( spl6_40
  <=> m1_subset_1(sK5(k2_pre_topc(sK0,sK1),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f693,plain,
    ( v3_yellow_6(sK4(sK0,sK1,sK5(k2_pre_topc(sK0,sK1),sK1)),sK0)
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_14
    | spl6_15
    | ~ spl6_21
    | ~ spl6_40 ),
    inference(unit_resulting_resolution,[],[f146,f141,f136,f131,f262,f642,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v3_yellow_6(sK4(X0,X1,X2),X0)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f642,plain,
    ( m1_subset_1(sK5(k2_pre_topc(sK0,sK1),sK1),u1_struct_0(sK0))
    | ~ spl6_40 ),
    inference(avatar_component_clause,[],[f640])).

fof(f721,plain,
    ( spl6_46
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_14
    | spl6_15
    | ~ spl6_21
    | ~ spl6_40 ),
    inference(avatar_split_clause,[],[f694,f640,f260,f144,f139,f134,f129,f718])).

fof(f694,plain,
    ( l1_waybel_0(sK4(sK0,sK1,sK5(k2_pre_topc(sK0,sK1),sK1)),sK0)
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_14
    | spl6_15
    | ~ spl6_21
    | ~ spl6_40 ),
    inference(unit_resulting_resolution,[],[f146,f141,f136,f131,f262,f642,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(sK4(X0,X1,X2),X0)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f645,plain,
    ( spl6_40
    | ~ spl6_16
    | ~ spl6_21 ),
    inference(avatar_split_clause,[],[f620,f260,f196,f640])).

fof(f620,plain,
    ( m1_subset_1(sK5(k2_pre_topc(sK0,sK1),sK1),u1_struct_0(sK0))
    | ~ spl6_16
    | ~ spl6_21 ),
    inference(resolution,[],[f262,f377])).

fof(f353,plain,
    ( spl6_21
    | spl6_19 ),
    inference(avatar_split_clause,[],[f347,f244,f260])).

fof(f244,plain,
    ( spl6_19
  <=> r1_tarski(k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f347,plain,
    ( r2_hidden(sK5(k2_pre_topc(sK0,sK1),sK1),k2_pre_topc(sK0,sK1))
    | spl6_19 ),
    inference(unit_resulting_resolution,[],[f246,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f37,f38])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f246,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,sK1),sK1)
    | spl6_19 ),
    inference(avatar_component_clause,[],[f244])).

fof(f352,plain,
    ( ~ spl6_20
    | spl6_19 ),
    inference(avatar_split_clause,[],[f348,f244,f255])).

fof(f348,plain,
    ( ~ r2_hidden(sK5(k2_pre_topc(sK0,sK1),sK1),sK1)
    | spl6_19 ),
    inference(unit_resulting_resolution,[],[f246,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f332,plain,
    ( ~ spl6_19
    | spl6_17
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f327,f206,f201,f244])).

fof(f201,plain,
    ( spl6_17
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f206,plain,
    ( spl6_18
  <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f327,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,sK1),sK1)
    | spl6_17
    | ~ spl6_18 ),
    inference(unit_resulting_resolution,[],[f208,f203,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f203,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | spl6_17 ),
    inference(avatar_component_clause,[],[f201])).

fof(f208,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f206])).

fof(f313,plain,
    ( ~ spl6_17
    | spl6_1
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f311,f139,f134,f129,f76,f201])).

fof(f76,plain,
    ( spl6_1
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f311,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | spl6_1
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_14 ),
    inference(unit_resulting_resolution,[],[f136,f141,f131,f78,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f78,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f76])).

fof(f303,plain,
    ( ~ spl6_1
    | ~ spl6_12
    | ~ spl6_13
    | spl6_17 ),
    inference(avatar_split_clause,[],[f235,f201,f134,f129,f76])).

fof(f235,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | ~ spl6_12
    | ~ spl6_13
    | spl6_17 ),
    inference(unit_resulting_resolution,[],[f136,f131,f203,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f211,plain,
    ( spl6_18
    | ~ spl6_12
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f210,f134,f129,f206])).

fof(f210,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl6_12
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f182,f136])).

fof(f182,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl6_12 ),
    inference(resolution,[],[f131,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

fof(f199,plain,
    ( spl6_16
    | ~ spl6_12
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f181,f134,f129,f196])).

fof(f181,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_12
    | ~ spl6_13 ),
    inference(unit_resulting_resolution,[],[f136,f131,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f147,plain,(
    ~ spl6_15 ),
    inference(avatar_split_clause,[],[f40,f144])).

fof(f40,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ( ( ~ r2_hidden(sK3,sK1)
        & r2_hidden(sK3,k10_yellow_6(sK0,sK2))
        & m1_subset_1(sK3,u1_struct_0(sK0))
        & r1_waybel_0(sK0,sK2,sK1)
        & l1_waybel_0(sK2,sK0)
        & v3_yellow_6(sK2,sK0)
        & v7_waybel_0(sK2)
        & v4_orders_2(sK2)
        & ~ v2_struct_0(sK2) )
      | ~ v4_pre_topc(sK1,sK0) )
    & ( ! [X4] :
          ( ! [X5] :
              ( r2_hidden(X5,sK1)
              | ~ r2_hidden(X5,k10_yellow_6(sK0,X4))
              | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
          | ~ r1_waybel_0(sK0,X4,sK1)
          | ~ l1_waybel_0(X4,sK0)
          | ~ v3_yellow_6(X4,sK0)
          | ~ v7_waybel_0(X4)
          | ~ v4_orders_2(X4)
          | v2_struct_0(X4) )
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f28,f27,f26,f25])).

fof(f25,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & r2_hidden(X3,k10_yellow_6(X0,X2))
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & r1_waybel_0(X0,X2,X1)
                  & l1_waybel_0(X2,X0)
                  & v3_yellow_6(X2,X0)
                  & v7_waybel_0(X2)
                  & v4_orders_2(X2)
                  & ~ v2_struct_0(X2) )
              | ~ v4_pre_topc(X1,X0) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | ~ r2_hidden(X5,k10_yellow_6(X0,X4))
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ r1_waybel_0(X0,X4,X1)
                  | ~ l1_waybel_0(X4,X0)
                  | ~ v3_yellow_6(X4,X0)
                  | ~ v7_waybel_0(X4)
                  | ~ v4_orders_2(X4)
                  | v2_struct_0(X4) )
              | v4_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(X3,X1)
                    & r2_hidden(X3,k10_yellow_6(sK0,X2))
                    & m1_subset_1(X3,u1_struct_0(sK0)) )
                & r1_waybel_0(sK0,X2,X1)
                & l1_waybel_0(X2,sK0)
                & v3_yellow_6(X2,sK0)
                & v7_waybel_0(X2)
                & v4_orders_2(X2)
                & ~ v2_struct_0(X2) )
            | ~ v4_pre_topc(X1,sK0) )
          & ( ! [X4] :
                ( ! [X5] :
                    ( r2_hidden(X5,X1)
                    | ~ r2_hidden(X5,k10_yellow_6(sK0,X4))
                    | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
                | ~ r1_waybel_0(sK0,X4,X1)
                | ~ l1_waybel_0(X4,sK0)
                | ~ v3_yellow_6(X4,sK0)
                | ~ v7_waybel_0(X4)
                | ~ v4_orders_2(X4)
                | v2_struct_0(X4) )
            | v4_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X1] :
        ( ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(X3,X1)
                  & r2_hidden(X3,k10_yellow_6(sK0,X2))
                  & m1_subset_1(X3,u1_struct_0(sK0)) )
              & r1_waybel_0(sK0,X2,X1)
              & l1_waybel_0(X2,sK0)
              & v3_yellow_6(X2,sK0)
              & v7_waybel_0(X2)
              & v4_orders_2(X2)
              & ~ v2_struct_0(X2) )
          | ~ v4_pre_topc(X1,sK0) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( r2_hidden(X5,X1)
                  | ~ r2_hidden(X5,k10_yellow_6(sK0,X4))
                  | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
              | ~ r1_waybel_0(sK0,X4,X1)
              | ~ l1_waybel_0(X4,sK0)
              | ~ v3_yellow_6(X4,sK0)
              | ~ v7_waybel_0(X4)
              | ~ v4_orders_2(X4)
              | v2_struct_0(X4) )
          | v4_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ? [X2] :
            ( ? [X3] :
                ( ~ r2_hidden(X3,sK1)
                & r2_hidden(X3,k10_yellow_6(sK0,X2))
                & m1_subset_1(X3,u1_struct_0(sK0)) )
            & r1_waybel_0(sK0,X2,sK1)
            & l1_waybel_0(X2,sK0)
            & v3_yellow_6(X2,sK0)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) )
        | ~ v4_pre_topc(sK1,sK0) )
      & ( ! [X4] :
            ( ! [X5] :
                ( r2_hidden(X5,sK1)
                | ~ r2_hidden(X5,k10_yellow_6(sK0,X4))
                | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
            | ~ r1_waybel_0(sK0,X4,sK1)
            | ~ l1_waybel_0(X4,sK0)
            | ~ v3_yellow_6(X4,sK0)
            | ~ v7_waybel_0(X4)
            | ~ v4_orders_2(X4)
            | v2_struct_0(X4) )
        | v4_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ r2_hidden(X3,sK1)
            & r2_hidden(X3,k10_yellow_6(sK0,X2))
            & m1_subset_1(X3,u1_struct_0(sK0)) )
        & r1_waybel_0(sK0,X2,sK1)
        & l1_waybel_0(X2,sK0)
        & v3_yellow_6(X2,sK0)
        & v7_waybel_0(X2)
        & v4_orders_2(X2)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ~ r2_hidden(X3,sK1)
          & r2_hidden(X3,k10_yellow_6(sK0,sK2))
          & m1_subset_1(X3,u1_struct_0(sK0)) )
      & r1_waybel_0(sK0,sK2,sK1)
      & l1_waybel_0(sK2,sK0)
      & v3_yellow_6(sK2,sK0)
      & v7_waybel_0(sK2)
      & v4_orders_2(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X3] :
        ( ~ r2_hidden(X3,sK1)
        & r2_hidden(X3,k10_yellow_6(sK0,sK2))
        & m1_subset_1(X3,u1_struct_0(sK0)) )
   => ( ~ r2_hidden(sK3,sK1)
      & r2_hidden(sK3,k10_yellow_6(sK0,sK2))
      & m1_subset_1(sK3,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(X3,X1)
                    & r2_hidden(X3,k10_yellow_6(X0,X2))
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & r1_waybel_0(X0,X2,X1)
                & l1_waybel_0(X2,X0)
                & v3_yellow_6(X2,X0)
                & v7_waybel_0(X2)
                & v4_orders_2(X2)
                & ~ v2_struct_0(X2) )
            | ~ v4_pre_topc(X1,X0) )
          & ( ! [X4] :
                ( ! [X5] :
                    ( r2_hidden(X5,X1)
                    | ~ r2_hidden(X5,k10_yellow_6(X0,X4))
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                | ~ r1_waybel_0(X0,X4,X1)
                | ~ l1_waybel_0(X4,X0)
                | ~ v3_yellow_6(X4,X0)
                | ~ v7_waybel_0(X4)
                | ~ v4_orders_2(X4)
                | v2_struct_0(X4) )
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(X3,X1)
                    & r2_hidden(X3,k10_yellow_6(X0,X2))
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & r1_waybel_0(X0,X2,X1)
                & l1_waybel_0(X2,X0)
                & v3_yellow_6(X2,X0)
                & v7_waybel_0(X2)
                & v4_orders_2(X2)
                & ~ v2_struct_0(X2) )
            | ~ v4_pre_topc(X1,X0) )
          & ( ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r2_hidden(X3,k10_yellow_6(X0,X2))
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_waybel_0(X0,X2,X1)
                | ~ l1_waybel_0(X2,X0)
                | ~ v3_yellow_6(X2,X0)
                | ~ v7_waybel_0(X2)
                | ~ v4_orders_2(X2)
                | v2_struct_0(X2) )
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(X3,X1)
                    & r2_hidden(X3,k10_yellow_6(X0,X2))
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & r1_waybel_0(X0,X2,X1)
                & l1_waybel_0(X2,X0)
                & v3_yellow_6(X2,X0)
                & v7_waybel_0(X2)
                & v4_orders_2(X2)
                & ~ v2_struct_0(X2) )
            | ~ v4_pre_topc(X1,X0) )
          & ( ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r2_hidden(X3,k10_yellow_6(X0,X2))
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_waybel_0(X0,X2,X1)
                | ~ l1_waybel_0(X2,X0)
                | ~ v3_yellow_6(X2,X0)
                | ~ v7_waybel_0(X2)
                | ~ v4_orders_2(X2)
                | v2_struct_0(X2) )
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r2_hidden(X3,k10_yellow_6(X0,X2))
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_waybel_0(X0,X2,X1)
                | ~ l1_waybel_0(X2,X0)
                | ~ v3_yellow_6(X2,X0)
                | ~ v7_waybel_0(X2)
                | ~ v4_orders_2(X2)
                | v2_struct_0(X2) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r2_hidden(X3,k10_yellow_6(X0,X2))
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_waybel_0(X0,X2,X1)
                | ~ l1_waybel_0(X2,X0)
                | ~ v3_yellow_6(X2,X0)
                | ~ v7_waybel_0(X2)
                | ~ v4_orders_2(X2)
                | v2_struct_0(X2) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> ! [X2] :
                  ( ( l1_waybel_0(X2,X0)
                    & v3_yellow_6(X2,X0)
                    & v7_waybel_0(X2)
                    & v4_orders_2(X2)
                    & ~ v2_struct_0(X2) )
                 => ( r1_waybel_0(X0,X2,X1)
                   => ! [X3] :
                        ( m1_subset_1(X3,u1_struct_0(X0))
                       => ( r2_hidden(X3,k10_yellow_6(X0,X2))
                         => r2_hidden(X3,X1) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> ! [X2] :
                ( ( l1_waybel_0(X2,X0)
                  & v3_yellow_6(X2,X0)
                  & v7_waybel_0(X2)
                  & v4_orders_2(X2)
                  & ~ v2_struct_0(X2) )
               => ( r1_waybel_0(X0,X2,X1)
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_hidden(X3,k10_yellow_6(X0,X2))
                       => r2_hidden(X3,X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_yellow19)).

fof(f142,plain,(
    spl6_14 ),
    inference(avatar_split_clause,[],[f41,f139])).

fof(f41,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f137,plain,(
    spl6_13 ),
    inference(avatar_split_clause,[],[f42,f134])).

fof(f42,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f132,plain,(
    spl6_12 ),
    inference(avatar_split_clause,[],[f43,f129])).

fof(f43,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f127,plain,
    ( spl6_1
    | spl6_11 ),
    inference(avatar_split_clause,[],[f44,f125,f76])).

fof(f44,plain,(
    ! [X4,X5] :
      ( r2_hidden(X5,sK1)
      | ~ r2_hidden(X5,k10_yellow_6(sK0,X4))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ r1_waybel_0(sK0,X4,sK1)
      | ~ l1_waybel_0(X4,sK0)
      | ~ v3_yellow_6(X4,sK0)
      | ~ v7_waybel_0(X4)
      | ~ v4_orders_2(X4)
      | v2_struct_0(X4)
      | v4_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f123,plain,
    ( ~ spl6_1
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f45,f120,f76])).

fof(f45,plain,
    ( ~ v2_struct_0(sK2)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f118,plain,
    ( ~ spl6_1
    | spl6_9 ),
    inference(avatar_split_clause,[],[f46,f115,f76])).

fof(f46,plain,
    ( v4_orders_2(sK2)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f113,plain,
    ( ~ spl6_1
    | spl6_8 ),
    inference(avatar_split_clause,[],[f47,f110,f76])).

fof(f47,plain,
    ( v7_waybel_0(sK2)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f108,plain,
    ( ~ spl6_1
    | spl6_7 ),
    inference(avatar_split_clause,[],[f48,f105,f76])).

fof(f48,plain,
    ( v3_yellow_6(sK2,sK0)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f103,plain,
    ( ~ spl6_1
    | spl6_6 ),
    inference(avatar_split_clause,[],[f49,f100,f76])).

fof(f49,plain,
    ( l1_waybel_0(sK2,sK0)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f98,plain,
    ( ~ spl6_1
    | spl6_5 ),
    inference(avatar_split_clause,[],[f50,f95,f76])).

fof(f95,plain,
    ( spl6_5
  <=> r1_waybel_0(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f50,plain,
    ( r1_waybel_0(sK0,sK2,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f93,plain,
    ( ~ spl6_1
    | spl6_4 ),
    inference(avatar_split_clause,[],[f51,f90,f76])).

fof(f51,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f88,plain,
    ( ~ spl6_1
    | spl6_3 ),
    inference(avatar_split_clause,[],[f52,f85,f76])).

fof(f52,plain,
    ( r2_hidden(sK3,k10_yellow_6(sK0,sK2))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f83,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f53,f80,f76])).

fof(f80,plain,
    ( spl6_2
  <=> r2_hidden(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f53,plain,
    ( ~ r2_hidden(sK3,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f29])).

%------------------------------------------------------------------------------
