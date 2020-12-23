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
% DateTime   : Thu Dec  3 13:23:36 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  298 (2879 expanded)
%              Number of leaves         :   30 (1008 expanded)
%              Depth                    :   32
%              Number of atoms          : 1995 (49554 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f384,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f81,f112,f119,f126,f133,f224,f232,f240,f248,f256,f268,f283,f290,f340,f348,f356,f364,f375,f383])).

fof(f383,plain,
    ( ~ spl8_12
    | ~ spl8_13
    | ~ spl8_14 ),
    inference(avatar_contradiction_clause,[],[f382])).

fof(f382,plain,
    ( $false
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f381,f35])).

fof(f35,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f20,f19,f18,f17])).

fof(f17,plain,
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

fof(f18,plain,
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

fof(f19,plain,
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

fof(f20,plain,
    ( ? [X3] :
        ( ~ r2_hidden(X3,sK1)
        & r2_hidden(X3,k10_yellow_6(sK0,sK2))
        & m1_subset_1(X3,u1_struct_0(sK0)) )
   => ( ~ r2_hidden(sK3,sK1)
      & r2_hidden(sK3,k10_yellow_6(sK0,sK2))
      & m1_subset_1(sK3,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
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
    inference(rectify,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
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
    inference(flattening,[],[f6])).

fof(f6,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
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
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
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

fof(f381,plain,
    ( v2_struct_0(sK0)
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f380,f36])).

fof(f36,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f380,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f379,f37])).

fof(f37,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f379,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f378,f38])).

fof(f38,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f378,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f377,f277])).

fof(f277,plain,
    ( m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f276])).

fof(f276,plain,
    ( spl8_12
  <=> m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f377,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_13
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f376,f282])).

fof(f282,plain,
    ( r2_hidden(sK5(sK0,sK1),k2_pre_topc(sK0,sK1))
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f280])).

fof(f280,plain,
    ( spl8_13
  <=> r2_hidden(sK5(sK0,sK1),k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f376,plain,
    ( ~ r2_hidden(sK5(sK0,sK1),k2_pre_topc(sK0,sK1))
    | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_14 ),
    inference(resolution,[],[f324,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(sK6(X0,X1,X2))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

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
                & ( ( r2_hidden(X2,k10_yellow_6(X0,sK6(X0,X1,X2)))
                    & r1_waybel_0(X0,sK6(X0,X1,X2),X1)
                    & l1_waybel_0(sK6(X0,X1,X2),X0)
                    & v3_yellow_6(sK6(X0,X1,X2),X0)
                    & v7_waybel_0(sK6(X0,X1,X2))
                    & v4_orders_2(sK6(X0,X1,X2))
                    & ~ v2_struct_0(sK6(X0,X1,X2)) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f28,f29])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X2,k10_yellow_6(X0,X4))
          & r1_waybel_0(X0,X4,X1)
          & l1_waybel_0(X4,X0)
          & v3_yellow_6(X4,X0)
          & v7_waybel_0(X4)
          & v4_orders_2(X4)
          & ~ v2_struct_0(X4) )
     => ( r2_hidden(X2,k10_yellow_6(X0,sK6(X0,X1,X2)))
        & r1_waybel_0(X0,sK6(X0,X1,X2),X1)
        & l1_waybel_0(sK6(X0,X1,X2),X0)
        & v3_yellow_6(sK6(X0,X1,X2),X0)
        & v7_waybel_0(sK6(X0,X1,X2))
        & v4_orders_2(sK6(X0,X1,X2))
        & ~ v2_struct_0(sK6(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f324,plain,
    ( v2_struct_0(sK6(sK0,sK1,sK5(sK0,sK1)))
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f322])).

fof(f322,plain,
    ( spl8_14
  <=> v2_struct_0(sK6(sK0,sK1,sK5(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f375,plain,
    ( spl8_1
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_18 ),
    inference(avatar_contradiction_clause,[],[f374])).

fof(f374,plain,
    ( $false
    | spl8_1
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f373,f282])).

fof(f373,plain,
    ( ~ r2_hidden(sK5(sK0,sK1),k2_pre_topc(sK0,sK1))
    | spl8_1
    | ~ spl8_12
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f372,f35])).

fof(f372,plain,
    ( v2_struct_0(sK0)
    | ~ r2_hidden(sK5(sK0,sK1),k2_pre_topc(sK0,sK1))
    | spl8_1
    | ~ spl8_12
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f371,f36])).

fof(f371,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ r2_hidden(sK5(sK0,sK1),k2_pre_topc(sK0,sK1))
    | spl8_1
    | ~ spl8_12
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f370,f37])).

fof(f370,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ r2_hidden(sK5(sK0,sK1),k2_pre_topc(sK0,sK1))
    | spl8_1
    | ~ spl8_12
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f369,f38])).

fof(f369,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ r2_hidden(sK5(sK0,sK1),k2_pre_topc(sK0,sK1))
    | spl8_1
    | ~ spl8_12
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f368,f76])).

fof(f76,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl8_1
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f368,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ r2_hidden(sK5(sK0,sK1),k2_pre_topc(sK0,sK1))
    | ~ spl8_12
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f367,f277])).

fof(f367,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ r2_hidden(sK5(sK0,sK1),k2_pre_topc(sK0,sK1))
    | ~ spl8_18 ),
    inference(duplicate_literal_removal,[],[f366])).

fof(f366,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ r2_hidden(sK5(sK0,sK1),k2_pre_topc(sK0,sK1))
    | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_18 ),
    inference(resolution,[],[f365,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k10_yellow_6(X0,sK6(X0,X1,X2)))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f365,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5(X0,sK1),k10_yellow_6(sK0,sK6(sK0,sK1,sK5(sK0,sK1))))
        | ~ m1_subset_1(sK5(X0,sK1),u1_struct_0(sK0))
        | v4_pre_topc(sK1,X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl8_18 ),
    inference(resolution,[],[f339,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

% (22712)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ( ~ r2_hidden(sK5(X0,X1),X1)
                & r3_waybel_9(X0,sK4(X0,X1),sK5(X0,X1))
                & m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
                & r1_waybel_0(X0,sK4(X0,X1),X1)
                & l1_waybel_0(sK4(X0,X1),X0)
                & v7_waybel_0(sK4(X0,X1))
                & v4_orders_2(sK4(X0,X1))
                & ~ v2_struct_0(sK4(X0,X1)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | ~ r3_waybel_9(X0,X4,X5)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ r1_waybel_0(X0,X4,X1)
                  | ~ l1_waybel_0(X4,X0)
                  | ~ v7_waybel_0(X4)
                  | ~ v4_orders_2(X4)
                  | v2_struct_0(X4) )
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f23,f25,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(X3,X1)
              & r3_waybel_9(X0,X2,X3)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & r1_waybel_0(X0,X2,X1)
          & l1_waybel_0(X2,X0)
          & v7_waybel_0(X2)
          & v4_orders_2(X2)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ~ r2_hidden(X3,X1)
            & r3_waybel_9(X0,sK4(X0,X1),X3)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & r1_waybel_0(X0,sK4(X0,X1),X1)
        & l1_waybel_0(sK4(X0,X1),X0)
        & v7_waybel_0(sK4(X0,X1))
        & v4_orders_2(sK4(X0,X1))
        & ~ v2_struct_0(sK4(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & r3_waybel_9(X0,sK4(X0,X1),X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r3_waybel_9(X0,sK4(X0,X1),sK5(X0,X1))
        & m1_subset_1(sK5(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & r3_waybel_9(X0,X2,X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & r1_waybel_0(X0,X2,X1)
                  & l1_waybel_0(X2,X0)
                  & v7_waybel_0(X2)
                  & v4_orders_2(X2)
                  & ~ v2_struct_0(X2) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | ~ r3_waybel_9(X0,X4,X5)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ r1_waybel_0(X0,X4,X1)
                  | ~ l1_waybel_0(X4,X0)
                  | ~ v7_waybel_0(X4)
                  | ~ v4_orders_2(X4)
                  | v2_struct_0(X4) )
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & r3_waybel_9(X0,X2,X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & r1_waybel_0(X0,X2,X1)
                  & l1_waybel_0(X2,X0)
                  & v7_waybel_0(X2)
                  & v4_orders_2(X2)
                  & ~ v2_struct_0(X2) ) )
            & ( ! [X2] :
                  ( ! [X3] :
                      ( r2_hidden(X3,X1)
                      | ~ r3_waybel_9(X0,X2,X3)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ r1_waybel_0(X0,X2,X1)
                  | ~ l1_waybel_0(X2,X0)
                  | ~ v7_waybel_0(X2)
                  | ~ v4_orders_2(X2)
                  | v2_struct_0(X2) )
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r3_waybel_9(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_waybel_0(X0,X2,X1)
                | ~ l1_waybel_0(X2,X0)
                | ~ v7_waybel_0(X2)
                | ~ v4_orders_2(X2)
                | v2_struct_0(X2) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r3_waybel_9(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_waybel_0(X0,X2,X1)
                | ~ l1_waybel_0(X2,X0)
                | ~ v7_waybel_0(X2)
                | ~ v4_orders_2(X2)
                | v2_struct_0(X2) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> ! [X2] :
                ( ( l1_waybel_0(X2,X0)
                  & v7_waybel_0(X2)
                  & v4_orders_2(X2)
                  & ~ v2_struct_0(X2) )
               => ( r1_waybel_0(X0,X2,X1)
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r3_waybel_9(X0,X2,X3)
                       => r2_hidden(X3,X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_yellow19)).

fof(f339,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,k10_yellow_6(sK0,sK6(sK0,sK1,sK5(sK0,sK1))))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f338])).

fof(f338,plain,
    ( spl8_18
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k10_yellow_6(sK0,sK6(sK0,sK1,sK5(sK0,sK1))))
        | r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f364,plain,
    ( ~ spl8_12
    | ~ spl8_13
    | spl8_17 ),
    inference(avatar_contradiction_clause,[],[f363])).

fof(f363,plain,
    ( $false
    | ~ spl8_12
    | ~ spl8_13
    | spl8_17 ),
    inference(subsumption_resolution,[],[f362,f35])).

fof(f362,plain,
    ( v2_struct_0(sK0)
    | ~ spl8_12
    | ~ spl8_13
    | spl8_17 ),
    inference(subsumption_resolution,[],[f361,f36])).

fof(f361,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_12
    | ~ spl8_13
    | spl8_17 ),
    inference(subsumption_resolution,[],[f360,f37])).

fof(f360,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_12
    | ~ spl8_13
    | spl8_17 ),
    inference(subsumption_resolution,[],[f359,f38])).

fof(f359,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_12
    | ~ spl8_13
    | spl8_17 ),
    inference(subsumption_resolution,[],[f358,f277])).

fof(f358,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_13
    | spl8_17 ),
    inference(subsumption_resolution,[],[f357,f282])).

fof(f357,plain,
    ( ~ r2_hidden(sK5(sK0,sK1),k2_pre_topc(sK0,sK1))
    | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_17 ),
    inference(resolution,[],[f336,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(sK6(X0,X1,X2),X0)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f336,plain,
    ( ~ l1_waybel_0(sK6(sK0,sK1,sK5(sK0,sK1)),sK0)
    | spl8_17 ),
    inference(avatar_component_clause,[],[f334])).

fof(f334,plain,
    ( spl8_17
  <=> l1_waybel_0(sK6(sK0,sK1,sK5(sK0,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f356,plain,
    ( ~ spl8_12
    | ~ spl8_13
    | spl8_16 ),
    inference(avatar_contradiction_clause,[],[f355])).

fof(f355,plain,
    ( $false
    | ~ spl8_12
    | ~ spl8_13
    | spl8_16 ),
    inference(subsumption_resolution,[],[f354,f35])).

fof(f354,plain,
    ( v2_struct_0(sK0)
    | ~ spl8_12
    | ~ spl8_13
    | spl8_16 ),
    inference(subsumption_resolution,[],[f353,f36])).

fof(f353,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_12
    | ~ spl8_13
    | spl8_16 ),
    inference(subsumption_resolution,[],[f352,f37])).

fof(f352,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_12
    | ~ spl8_13
    | spl8_16 ),
    inference(subsumption_resolution,[],[f351,f38])).

fof(f351,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_12
    | ~ spl8_13
    | spl8_16 ),
    inference(subsumption_resolution,[],[f350,f277])).

fof(f350,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_13
    | spl8_16 ),
    inference(subsumption_resolution,[],[f349,f282])).

fof(f349,plain,
    ( ~ r2_hidden(sK5(sK0,sK1),k2_pre_topc(sK0,sK1))
    | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_16 ),
    inference(resolution,[],[f332,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v7_waybel_0(sK6(X0,X1,X2))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f332,plain,
    ( ~ v7_waybel_0(sK6(sK0,sK1,sK5(sK0,sK1)))
    | spl8_16 ),
    inference(avatar_component_clause,[],[f330])).

fof(f330,plain,
    ( spl8_16
  <=> v7_waybel_0(sK6(sK0,sK1,sK5(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f348,plain,
    ( ~ spl8_12
    | ~ spl8_13
    | spl8_15 ),
    inference(avatar_contradiction_clause,[],[f347])).

fof(f347,plain,
    ( $false
    | ~ spl8_12
    | ~ spl8_13
    | spl8_15 ),
    inference(subsumption_resolution,[],[f346,f35])).

fof(f346,plain,
    ( v2_struct_0(sK0)
    | ~ spl8_12
    | ~ spl8_13
    | spl8_15 ),
    inference(subsumption_resolution,[],[f345,f36])).

fof(f345,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_12
    | ~ spl8_13
    | spl8_15 ),
    inference(subsumption_resolution,[],[f344,f37])).

fof(f344,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_12
    | ~ spl8_13
    | spl8_15 ),
    inference(subsumption_resolution,[],[f343,f38])).

fof(f343,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_12
    | ~ spl8_13
    | spl8_15 ),
    inference(subsumption_resolution,[],[f342,f277])).

fof(f342,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_13
    | spl8_15 ),
    inference(subsumption_resolution,[],[f341,f282])).

fof(f341,plain,
    ( ~ r2_hidden(sK5(sK0,sK1),k2_pre_topc(sK0,sK1))
    | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_15 ),
    inference(resolution,[],[f328,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v4_orders_2(sK6(X0,X1,X2))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f328,plain,
    ( ~ v4_orders_2(sK6(sK0,sK1,sK5(sK0,sK1)))
    | spl8_15 ),
    inference(avatar_component_clause,[],[f326])).

fof(f326,plain,
    ( spl8_15
  <=> v4_orders_2(sK6(sK0,sK1,sK5(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f340,plain,
    ( spl8_14
    | ~ spl8_15
    | ~ spl8_16
    | ~ spl8_17
    | spl8_18
    | spl8_1
    | ~ spl8_12
    | ~ spl8_13 ),
    inference(avatar_split_clause,[],[f320,f280,f276,f74,f338,f334,f330,f326,f322])).

fof(f320,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k10_yellow_6(sK0,sK6(sK0,sK1,sK5(sK0,sK1))))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_waybel_0(sK6(sK0,sK1,sK5(sK0,sK1)),sK0)
        | r2_hidden(X0,sK1)
        | ~ v7_waybel_0(sK6(sK0,sK1,sK5(sK0,sK1)))
        | ~ v4_orders_2(sK6(sK0,sK1,sK5(sK0,sK1)))
        | v2_struct_0(sK6(sK0,sK1,sK5(sK0,sK1))) )
    | spl8_1
    | ~ spl8_12
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f319,f309])).

fof(f309,plain,
    ( r1_waybel_0(sK0,sK6(sK0,sK1,sK5(sK0,sK1)),sK1)
    | ~ spl8_12
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f308,f35])).

fof(f308,plain,
    ( r1_waybel_0(sK0,sK6(sK0,sK1,sK5(sK0,sK1)),sK1)
    | v2_struct_0(sK0)
    | ~ spl8_12
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f307,f36])).

fof(f307,plain,
    ( r1_waybel_0(sK0,sK6(sK0,sK1,sK5(sK0,sK1)),sK1)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_12
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f306,f37])).

fof(f306,plain,
    ( r1_waybel_0(sK0,sK6(sK0,sK1,sK5(sK0,sK1)),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_12
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f305,f38])).

fof(f305,plain,
    ( r1_waybel_0(sK0,sK6(sK0,sK1,sK5(sK0,sK1)),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_12
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f293,f277])).

fof(f293,plain,
    ( r1_waybel_0(sK0,sK6(sK0,sK1,sK5(sK0,sK1)),sK1)
    | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_13 ),
    inference(resolution,[],[f282,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | r1_waybel_0(X0,sK6(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f319,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k10_yellow_6(sK0,sK6(sK0,sK1,sK5(sK0,sK1))))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_waybel_0(sK0,sK6(sK0,sK1,sK5(sK0,sK1)),sK1)
        | ~ l1_waybel_0(sK6(sK0,sK1,sK5(sK0,sK1)),sK0)
        | r2_hidden(X0,sK1)
        | ~ v7_waybel_0(sK6(sK0,sK1,sK5(sK0,sK1)))
        | ~ v4_orders_2(sK6(sK0,sK1,sK5(sK0,sK1)))
        | v2_struct_0(sK6(sK0,sK1,sK5(sK0,sK1))) )
    | spl8_1
    | ~ spl8_12
    | ~ spl8_13 ),
    inference(resolution,[],[f318,f314])).

fof(f314,plain,
    ( v3_yellow_6(sK6(sK0,sK1,sK5(sK0,sK1)),sK0)
    | ~ spl8_12
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f313,f35])).

fof(f313,plain,
    ( v3_yellow_6(sK6(sK0,sK1,sK5(sK0,sK1)),sK0)
    | v2_struct_0(sK0)
    | ~ spl8_12
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f312,f36])).

fof(f312,plain,
    ( v3_yellow_6(sK6(sK0,sK1,sK5(sK0,sK1)),sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_12
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f311,f37])).

fof(f311,plain,
    ( v3_yellow_6(sK6(sK0,sK1,sK5(sK0,sK1)),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_12
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f310,f38])).

fof(f310,plain,
    ( v3_yellow_6(sK6(sK0,sK1,sK5(sK0,sK1)),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_12
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f294,f277])).

fof(f294,plain,
    ( v3_yellow_6(sK6(sK0,sK1,sK5(sK0,sK1)),sK0)
    | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_13 ),
    inference(resolution,[],[f282,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | v3_yellow_6(sK6(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f318,plain,
    ( ! [X4,X5] :
        ( ~ v3_yellow_6(X4,sK0)
        | ~ r2_hidden(X5,k10_yellow_6(sK0,X4))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ r1_waybel_0(sK0,X4,sK1)
        | ~ l1_waybel_0(X4,sK0)
        | r2_hidden(X5,sK1)
        | ~ v7_waybel_0(X4)
        | ~ v4_orders_2(X4)
        | v2_struct_0(X4) )
    | spl8_1 ),
    inference(subsumption_resolution,[],[f39,f76])).

fof(f39,plain,(
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
    inference(cnf_transformation,[],[f21])).

fof(f290,plain,
    ( spl8_1
    | spl8_12 ),
    inference(avatar_contradiction_clause,[],[f289])).

fof(f289,plain,
    ( $false
    | spl8_1
    | spl8_12 ),
    inference(subsumption_resolution,[],[f288,f35])).

fof(f288,plain,
    ( v2_struct_0(sK0)
    | spl8_1
    | spl8_12 ),
    inference(subsumption_resolution,[],[f287,f36])).

fof(f287,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | spl8_12 ),
    inference(subsumption_resolution,[],[f286,f37])).

fof(f286,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | spl8_12 ),
    inference(subsumption_resolution,[],[f285,f38])).

fof(f285,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | spl8_12 ),
    inference(subsumption_resolution,[],[f284,f76])).

fof(f284,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_12 ),
    inference(resolution,[],[f278,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
      | v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f278,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | spl8_12 ),
    inference(avatar_component_clause,[],[f276])).

fof(f283,plain,
    ( ~ spl8_12
    | spl8_13
    | spl8_1
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f274,f94,f74,f280,f276])).

fof(f94,plain,
    ( spl8_3
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,k2_pre_topc(sK0,sK1))
        | ~ r3_waybel_9(sK0,sK4(sK0,sK1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f274,plain,
    ( r2_hidden(sK5(sK0,sK1),k2_pre_topc(sK0,sK1))
    | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | spl8_1
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f273,f35])).

fof(f273,plain,
    ( r2_hidden(sK5(sK0,sK1),k2_pre_topc(sK0,sK1))
    | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f272,f36])).

fof(f272,plain,
    ( r2_hidden(sK5(sK0,sK1),k2_pre_topc(sK0,sK1))
    | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f271,f37])).

fof(f271,plain,
    ( r2_hidden(sK5(sK0,sK1),k2_pre_topc(sK0,sK1))
    | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f270,f38])).

fof(f270,plain,
    ( r2_hidden(sK5(sK0,sK1),k2_pre_topc(sK0,sK1))
    | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f269,f76])).

fof(f269,plain,
    ( r2_hidden(sK5(sK0,sK1),k2_pre_topc(sK0,sK1))
    | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_3 ),
    inference(resolution,[],[f95,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r3_waybel_9(X0,sK4(X0,X1),sK5(X0,X1))
      | v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f95,plain,
    ( ! [X0] :
        ( ~ r3_waybel_9(sK0,sK4(sK0,sK1),X0)
        | r2_hidden(X0,k2_pre_topc(sK0,sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f94])).

fof(f268,plain,
    ( spl8_1
    | ~ spl8_4 ),
    inference(avatar_contradiction_clause,[],[f267])).

fof(f267,plain,
    ( $false
    | spl8_1
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f266,f35])).

fof(f266,plain,
    ( v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f265,f36])).

fof(f265,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f264,f37])).

fof(f264,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f263,f38])).

fof(f263,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f262,f76])).

fof(f262,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_4 ),
    inference(resolution,[],[f99,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK4(X0,X1))
      | v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f99,plain,
    ( v2_struct_0(sK4(sK0,sK1))
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl8_4
  <=> v2_struct_0(sK4(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f256,plain,
    ( ~ spl8_1
    | spl8_2
    | ~ spl8_8 ),
    inference(avatar_contradiction_clause,[],[f255])).

fof(f255,plain,
    ( $false
    | ~ spl8_1
    | spl8_2
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f254,f35])).

fof(f254,plain,
    ( v2_struct_0(sK0)
    | ~ spl8_1
    | spl8_2
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f253,f36])).

fof(f253,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_1
    | spl8_2
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f252,f37])).

fof(f252,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_1
    | spl8_2
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f251,f38])).

fof(f251,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_1
    | spl8_2
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f250,f157])).

fof(f157,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f46,f75])).

fof(f75,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f74])).

fof(f46,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f250,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_1
    | spl8_2
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f249,f176])).

fof(f176,plain,
    ( r2_hidden(sK3,k2_pre_topc(sK0,sK1))
    | ~ spl8_1
    | spl8_2 ),
    inference(subsumption_resolution,[],[f175,f157])).

fof(f175,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | r2_hidden(sK3,k2_pre_topc(sK0,sK1))
    | ~ spl8_1
    | spl8_2 ),
    inference(resolution,[],[f174,f158])).

fof(f158,plain,
    ( r2_hidden(sK3,k10_yellow_6(sK0,sK2))
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f47,f75])).

fof(f47,plain,
    ( r2_hidden(sK3,k10_yellow_6(sK0,sK2))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f174,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k10_yellow_6(sK0,sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,k2_pre_topc(sK0,sK1)) )
    | ~ spl8_1
    | spl8_2 ),
    inference(subsumption_resolution,[],[f173,f38])).

fof(f173,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k10_yellow_6(sK0,sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X0,k2_pre_topc(sK0,sK1)) )
    | ~ spl8_1
    | spl8_2 ),
    inference(resolution,[],[f172,f151])).

fof(f151,plain,
    ( r1_waybel_0(sK0,sK2,sK1)
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f45,f75])).

fof(f45,plain,
    ( r1_waybel_0(sK0,sK2,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f172,plain,
    ( ! [X0,X1] :
        ( ~ r1_waybel_0(sK0,sK2,X0)
        | ~ r2_hidden(X1,k10_yellow_6(sK0,sK2))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X1,k2_pre_topc(sK0,X0)) )
    | ~ spl8_1
    | spl8_2 ),
    inference(subsumption_resolution,[],[f171,f80])).

fof(f80,plain,
    ( ~ v2_struct_0(sK2)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl8_2
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f171,plain,
    ( ! [X0,X1] :
        ( ~ r1_waybel_0(sK0,sK2,X0)
        | ~ r2_hidden(X1,k10_yellow_6(sK0,sK2))
        | v2_struct_0(sK2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X1,k2_pre_topc(sK0,X0)) )
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f170,f146])).

fof(f146,plain,
    ( v4_orders_2(sK2)
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f41,f75])).

fof(f41,plain,
    ( v4_orders_2(sK2)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f170,plain,
    ( ! [X0,X1] :
        ( ~ r1_waybel_0(sK0,sK2,X0)
        | ~ r2_hidden(X1,k10_yellow_6(sK0,sK2))
        | ~ v4_orders_2(sK2)
        | v2_struct_0(sK2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X1,k2_pre_topc(sK0,X0)) )
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f169,f147])).

fof(f147,plain,
    ( v7_waybel_0(sK2)
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f42,f75])).

fof(f42,plain,
    ( v7_waybel_0(sK2)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f169,plain,
    ( ! [X0,X1] :
        ( ~ r1_waybel_0(sK0,sK2,X0)
        | ~ r2_hidden(X1,k10_yellow_6(sK0,sK2))
        | ~ v7_waybel_0(sK2)
        | ~ v4_orders_2(sK2)
        | v2_struct_0(sK2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X1,k2_pre_topc(sK0,X0)) )
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f168,f149])).

fof(f149,plain,
    ( l1_waybel_0(sK2,sK0)
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f44,f75])).

fof(f44,plain,
    ( l1_waybel_0(sK2,sK0)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f168,plain,
    ( ! [X0,X1] :
        ( ~ r1_waybel_0(sK0,sK2,X0)
        | ~ l1_waybel_0(sK2,sK0)
        | ~ r2_hidden(X1,k10_yellow_6(sK0,sK2))
        | ~ v7_waybel_0(sK2)
        | ~ v4_orders_2(sK2)
        | v2_struct_0(sK2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X1,k2_pre_topc(sK0,X0)) )
    | ~ spl8_1 ),
    inference(resolution,[],[f167,f148])).

fof(f148,plain,
    ( v3_yellow_6(sK2,sK0)
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f43,f75])).

fof(f43,plain,
    ( v3_yellow_6(sK2,sK0)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f167,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_yellow_6(X1,sK0)
      | ~ r1_waybel_0(sK0,X1,X2)
      | ~ l1_waybel_0(X1,sK0)
      | ~ r2_hidden(X0,k10_yellow_6(sK0,X1))
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X0,k2_pre_topc(sK0,X2)) ) ),
    inference(subsumption_resolution,[],[f166,f35])).

fof(f166,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k10_yellow_6(sK0,X1))
      | ~ r1_waybel_0(sK0,X1,X2)
      | ~ l1_waybel_0(X1,sK0)
      | ~ v3_yellow_6(X1,sK0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X0,k2_pre_topc(sK0,X2))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f165,f36])).

fof(f165,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k10_yellow_6(sK0,X1))
      | ~ r1_waybel_0(sK0,X1,X2)
      | ~ l1_waybel_0(X1,sK0)
      | ~ v3_yellow_6(X1,sK0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X0,k2_pre_topc(sK0,X2))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f65,f37])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r2_hidden(X2,k10_yellow_6(X0,X3))
      | ~ r1_waybel_0(X0,X3,X1)
      | ~ l1_waybel_0(X3,X0)
      | ~ v3_yellow_6(X3,X0)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f249,plain,
    ( ~ r2_hidden(sK3,k2_pre_topc(sK0,sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_8 ),
    inference(resolution,[],[f211,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(sK7(X0,X1,X2))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

% (22714)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ! [X3] :
                      ( ~ r3_waybel_9(X0,X3,X2)
                      | ~ r1_waybel_0(X0,X3,X1)
                      | ~ l1_waybel_0(X3,X0)
                      | ~ v7_waybel_0(X3)
                      | ~ v4_orders_2(X3)
                      | v2_struct_0(X3) ) )
                & ( ( r3_waybel_9(X0,sK7(X0,X1,X2),X2)
                    & r1_waybel_0(X0,sK7(X0,X1,X2),X1)
                    & l1_waybel_0(sK7(X0,X1,X2),X0)
                    & v7_waybel_0(sK7(X0,X1,X2))
                    & v4_orders_2(sK7(X0,X1,X2))
                    & ~ v2_struct_0(sK7(X0,X1,X2)) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f32,f33])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r3_waybel_9(X0,X4,X2)
          & r1_waybel_0(X0,X4,X1)
          & l1_waybel_0(X4,X0)
          & v7_waybel_0(X4)
          & v4_orders_2(X4)
          & ~ v2_struct_0(X4) )
     => ( r3_waybel_9(X0,sK7(X0,X1,X2),X2)
        & r1_waybel_0(X0,sK7(X0,X1,X2),X1)
        & l1_waybel_0(sK7(X0,X1,X2),X0)
        & v7_waybel_0(sK7(X0,X1,X2))
        & v4_orders_2(sK7(X0,X1,X2))
        & ~ v2_struct_0(sK7(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ! [X3] :
                      ( ~ r3_waybel_9(X0,X3,X2)
                      | ~ r1_waybel_0(X0,X3,X1)
                      | ~ l1_waybel_0(X3,X0)
                      | ~ v7_waybel_0(X3)
                      | ~ v4_orders_2(X3)
                      | v2_struct_0(X3) ) )
                & ( ? [X4] :
                      ( r3_waybel_9(X0,X4,X2)
                      & r1_waybel_0(X0,X4,X1)
                      & l1_waybel_0(X4,X0)
                      & v7_waybel_0(X4)
                      & v4_orders_2(X4)
                      & ~ v2_struct_0(X4) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ! [X3] :
                      ( ~ r3_waybel_9(X0,X3,X2)
                      | ~ r1_waybel_0(X0,X3,X1)
                      | ~ l1_waybel_0(X3,X0)
                      | ~ v7_waybel_0(X3)
                      | ~ v4_orders_2(X3)
                      | v2_struct_0(X3) ) )
                & ( ? [X3] :
                      ( r3_waybel_9(X0,X3,X2)
                      & r1_waybel_0(X0,X3,X1)
                      & l1_waybel_0(X3,X0)
                      & v7_waybel_0(X3)
                      & v4_orders_2(X3)
                      & ~ v2_struct_0(X3) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ? [X3] :
                    ( r3_waybel_9(X0,X3,X2)
                    & r1_waybel_0(X0,X3,X1)
                    & l1_waybel_0(X3,X0)
                    & v7_waybel_0(X3)
                    & v4_orders_2(X3)
                    & ~ v2_struct_0(X3) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ? [X3] :
                    ( r3_waybel_9(X0,X3,X2)
                    & r1_waybel_0(X0,X3,X1)
                    & l1_waybel_0(X3,X0)
                    & v7_waybel_0(X3)
                    & v4_orders_2(X3)
                    & ~ v2_struct_0(X3) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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
                    ( r3_waybel_9(X0,X3,X2)
                    & r1_waybel_0(X0,X3,X1)
                    & l1_waybel_0(X3,X0)
                    & v7_waybel_0(X3)
                    & v4_orders_2(X3)
                    & ~ v2_struct_0(X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_yellow19)).

fof(f211,plain,
    ( v2_struct_0(sK7(sK0,sK1,sK3))
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f209])).

fof(f209,plain,
    ( spl8_8
  <=> v2_struct_0(sK7(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f248,plain,
    ( ~ spl8_1
    | spl8_2
    | spl8_11 ),
    inference(avatar_contradiction_clause,[],[f247])).

fof(f247,plain,
    ( $false
    | ~ spl8_1
    | spl8_2
    | spl8_11 ),
    inference(subsumption_resolution,[],[f246,f35])).

fof(f246,plain,
    ( v2_struct_0(sK0)
    | ~ spl8_1
    | spl8_2
    | spl8_11 ),
    inference(subsumption_resolution,[],[f245,f36])).

fof(f245,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_1
    | spl8_2
    | spl8_11 ),
    inference(subsumption_resolution,[],[f244,f37])).

fof(f244,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_1
    | spl8_2
    | spl8_11 ),
    inference(subsumption_resolution,[],[f243,f38])).

fof(f243,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_1
    | spl8_2
    | spl8_11 ),
    inference(subsumption_resolution,[],[f242,f157])).

fof(f242,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_1
    | spl8_2
    | spl8_11 ),
    inference(subsumption_resolution,[],[f241,f176])).

fof(f241,plain,
    ( ~ r2_hidden(sK3,k2_pre_topc(sK0,sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_11 ),
    inference(resolution,[],[f223,f69])).

% (22703)lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3 on theBenchmark
fof(f69,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(sK7(X0,X1,X2),X0)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f223,plain,
    ( ~ l1_waybel_0(sK7(sK0,sK1,sK3),sK0)
    | spl8_11 ),
    inference(avatar_component_clause,[],[f221])).

fof(f221,plain,
    ( spl8_11
  <=> l1_waybel_0(sK7(sK0,sK1,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f240,plain,
    ( ~ spl8_1
    | spl8_2
    | spl8_10 ),
    inference(avatar_contradiction_clause,[],[f239])).

fof(f239,plain,
    ( $false
    | ~ spl8_1
    | spl8_2
    | spl8_10 ),
    inference(subsumption_resolution,[],[f238,f35])).

fof(f238,plain,
    ( v2_struct_0(sK0)
    | ~ spl8_1
    | spl8_2
    | spl8_10 ),
    inference(subsumption_resolution,[],[f237,f36])).

fof(f237,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_1
    | spl8_2
    | spl8_10 ),
    inference(subsumption_resolution,[],[f236,f37])).

fof(f236,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_1
    | spl8_2
    | spl8_10 ),
    inference(subsumption_resolution,[],[f235,f38])).

fof(f235,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_1
    | spl8_2
    | spl8_10 ),
    inference(subsumption_resolution,[],[f234,f157])).

fof(f234,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_1
    | spl8_2
    | spl8_10 ),
    inference(subsumption_resolution,[],[f233,f176])).

fof(f233,plain,
    ( ~ r2_hidden(sK3,k2_pre_topc(sK0,sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_10 ),
    inference(resolution,[],[f219,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v7_waybel_0(sK7(X0,X1,X2))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f219,plain,
    ( ~ v7_waybel_0(sK7(sK0,sK1,sK3))
    | spl8_10 ),
    inference(avatar_component_clause,[],[f217])).

fof(f217,plain,
    ( spl8_10
  <=> v7_waybel_0(sK7(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f232,plain,
    ( ~ spl8_1
    | spl8_2
    | spl8_9 ),
    inference(avatar_contradiction_clause,[],[f231])).

fof(f231,plain,
    ( $false
    | ~ spl8_1
    | spl8_2
    | spl8_9 ),
    inference(subsumption_resolution,[],[f230,f35])).

fof(f230,plain,
    ( v2_struct_0(sK0)
    | ~ spl8_1
    | spl8_2
    | spl8_9 ),
    inference(subsumption_resolution,[],[f229,f36])).

fof(f229,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_1
    | spl8_2
    | spl8_9 ),
    inference(subsumption_resolution,[],[f228,f37])).

fof(f228,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_1
    | spl8_2
    | spl8_9 ),
    inference(subsumption_resolution,[],[f227,f38])).

fof(f227,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_1
    | spl8_2
    | spl8_9 ),
    inference(subsumption_resolution,[],[f226,f157])).

fof(f226,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_1
    | spl8_2
    | spl8_9 ),
    inference(subsumption_resolution,[],[f225,f176])).

fof(f225,plain,
    ( ~ r2_hidden(sK3,k2_pre_topc(sK0,sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_9 ),
    inference(resolution,[],[f215,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v4_orders_2(sK7(X0,X1,X2))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f215,plain,
    ( ~ v4_orders_2(sK7(sK0,sK1,sK3))
    | spl8_9 ),
    inference(avatar_component_clause,[],[f213])).

fof(f213,plain,
    ( spl8_9
  <=> v4_orders_2(sK7(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f224,plain,
    ( spl8_8
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f207,f78,f74,f221,f217,f213,f209])).

fof(f207,plain,
    ( ~ l1_waybel_0(sK7(sK0,sK1,sK3),sK0)
    | ~ v7_waybel_0(sK7(sK0,sK1,sK3))
    | ~ v4_orders_2(sK7(sK0,sK1,sK3))
    | v2_struct_0(sK7(sK0,sK1,sK3))
    | ~ spl8_1
    | spl8_2 ),
    inference(subsumption_resolution,[],[f204,f190])).

fof(f190,plain,
    ( r1_waybel_0(sK0,sK7(sK0,sK1,sK3),sK1)
    | ~ spl8_1
    | spl8_2 ),
    inference(subsumption_resolution,[],[f189,f35])).

fof(f189,plain,
    ( r1_waybel_0(sK0,sK7(sK0,sK1,sK3),sK1)
    | v2_struct_0(sK0)
    | ~ spl8_1
    | spl8_2 ),
    inference(subsumption_resolution,[],[f188,f36])).

fof(f188,plain,
    ( r1_waybel_0(sK0,sK7(sK0,sK1,sK3),sK1)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_1
    | spl8_2 ),
    inference(subsumption_resolution,[],[f187,f37])).

fof(f187,plain,
    ( r1_waybel_0(sK0,sK7(sK0,sK1,sK3),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_1
    | spl8_2 ),
    inference(subsumption_resolution,[],[f186,f38])).

fof(f186,plain,
    ( r1_waybel_0(sK0,sK7(sK0,sK1,sK3),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_1
    | spl8_2 ),
    inference(subsumption_resolution,[],[f178,f157])).

fof(f178,plain,
    ( r1_waybel_0(sK0,sK7(sK0,sK1,sK3),sK1)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_1
    | spl8_2 ),
    inference(resolution,[],[f176,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | r1_waybel_0(X0,sK7(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f204,plain,
    ( ~ r1_waybel_0(sK0,sK7(sK0,sK1,sK3),sK1)
    | ~ l1_waybel_0(sK7(sK0,sK1,sK3),sK0)
    | ~ v7_waybel_0(sK7(sK0,sK1,sK3))
    | ~ v4_orders_2(sK7(sK0,sK1,sK3))
    | v2_struct_0(sK7(sK0,sK1,sK3))
    | ~ spl8_1
    | spl8_2 ),
    inference(subsumption_resolution,[],[f203,f150])).

fof(f150,plain,
    ( ~ r2_hidden(sK3,sK1)
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f48,f75])).

fof(f48,plain,
    ( ~ r2_hidden(sK3,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f203,plain,
    ( ~ r1_waybel_0(sK0,sK7(sK0,sK1,sK3),sK1)
    | ~ l1_waybel_0(sK7(sK0,sK1,sK3),sK0)
    | ~ v7_waybel_0(sK7(sK0,sK1,sK3))
    | ~ v4_orders_2(sK7(sK0,sK1,sK3))
    | v2_struct_0(sK7(sK0,sK1,sK3))
    | r2_hidden(sK3,sK1)
    | ~ spl8_1
    | spl8_2 ),
    inference(subsumption_resolution,[],[f202,f157])).

fof(f202,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r1_waybel_0(sK0,sK7(sK0,sK1,sK3),sK1)
    | ~ l1_waybel_0(sK7(sK0,sK1,sK3),sK0)
    | ~ v7_waybel_0(sK7(sK0,sK1,sK3))
    | ~ v4_orders_2(sK7(sK0,sK1,sK3))
    | v2_struct_0(sK7(sK0,sK1,sK3))
    | r2_hidden(sK3,sK1)
    | ~ spl8_1
    | spl8_2 ),
    inference(resolution,[],[f185,f145])).

fof(f145,plain,
    ( ! [X0,X1] :
        ( ~ r3_waybel_9(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_waybel_0(sK0,X0,sK1)
        | ~ l1_waybel_0(X0,sK0)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | r2_hidden(X1,sK1) )
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f144,f35])).

fof(f144,plain,
    ( ! [X0,X1] :
        ( ~ r3_waybel_9(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_waybel_0(sK0,X0,sK1)
        | ~ l1_waybel_0(X0,sK0)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | r2_hidden(X1,sK1)
        | v2_struct_0(sK0) )
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f143,f36])).

fof(f143,plain,
    ( ! [X0,X1] :
        ( ~ r3_waybel_9(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_waybel_0(sK0,X0,sK1)
        | ~ l1_waybel_0(X0,sK0)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | r2_hidden(X1,sK1)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f142,f37])).

fof(f142,plain,
    ( ! [X0,X1] :
        ( ~ r3_waybel_9(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_waybel_0(sK0,X0,sK1)
        | ~ l1_waybel_0(X0,sK0)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | r2_hidden(X1,sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f141,f38])).

fof(f141,plain,
    ( ! [X0,X1] :
        ( ~ r3_waybel_9(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_waybel_0(sK0,X0,sK1)
        | ~ l1_waybel_0(X0,sK0)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | r2_hidden(X1,sK1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_1 ),
    inference(resolution,[],[f75,f49])).

fof(f49,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ v4_pre_topc(X1,X0)
      | ~ r3_waybel_9(X0,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ r1_waybel_0(X0,X4,X1)
      | ~ l1_waybel_0(X4,X0)
      | ~ v7_waybel_0(X4)
      | ~ v4_orders_2(X4)
      | v2_struct_0(X4)
      | r2_hidden(X5,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f185,plain,
    ( r3_waybel_9(sK0,sK7(sK0,sK1,sK3),sK3)
    | ~ spl8_1
    | spl8_2 ),
    inference(subsumption_resolution,[],[f184,f35])).

fof(f184,plain,
    ( r3_waybel_9(sK0,sK7(sK0,sK1,sK3),sK3)
    | v2_struct_0(sK0)
    | ~ spl8_1
    | spl8_2 ),
    inference(subsumption_resolution,[],[f183,f36])).

fof(f183,plain,
    ( r3_waybel_9(sK0,sK7(sK0,sK1,sK3),sK3)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_1
    | spl8_2 ),
    inference(subsumption_resolution,[],[f182,f37])).

fof(f182,plain,
    ( r3_waybel_9(sK0,sK7(sK0,sK1,sK3),sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_1
    | spl8_2 ),
    inference(subsumption_resolution,[],[f181,f38])).

fof(f181,plain,
    ( r3_waybel_9(sK0,sK7(sK0,sK1,sK3),sK3)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_1
    | spl8_2 ),
    inference(subsumption_resolution,[],[f177,f157])).

fof(f177,plain,
    ( r3_waybel_9(sK0,sK7(sK0,sK1,sK3),sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_1
    | spl8_2 ),
    inference(resolution,[],[f176,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | r3_waybel_9(X0,sK7(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f133,plain,
    ( spl8_1
    | spl8_7 ),
    inference(avatar_contradiction_clause,[],[f132])).

fof(f132,plain,
    ( $false
    | spl8_1
    | spl8_7 ),
    inference(subsumption_resolution,[],[f131,f35])).

fof(f131,plain,
    ( v2_struct_0(sK0)
    | spl8_1
    | spl8_7 ),
    inference(subsumption_resolution,[],[f130,f36])).

fof(f130,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | spl8_7 ),
    inference(subsumption_resolution,[],[f129,f37])).

fof(f129,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | spl8_7 ),
    inference(subsumption_resolution,[],[f128,f38])).

fof(f128,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | spl8_7 ),
    inference(subsumption_resolution,[],[f127,f76])).

fof(f127,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_7 ),
    inference(resolution,[],[f111,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( l1_waybel_0(sK4(X0,X1),X0)
      | v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f111,plain,
    ( ~ l1_waybel_0(sK4(sK0,sK1),sK0)
    | spl8_7 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl8_7
  <=> l1_waybel_0(sK4(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f126,plain,
    ( spl8_1
    | spl8_6 ),
    inference(avatar_contradiction_clause,[],[f125])).

fof(f125,plain,
    ( $false
    | spl8_1
    | spl8_6 ),
    inference(subsumption_resolution,[],[f124,f35])).

fof(f124,plain,
    ( v2_struct_0(sK0)
    | spl8_1
    | spl8_6 ),
    inference(subsumption_resolution,[],[f123,f36])).

fof(f123,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | spl8_6 ),
    inference(subsumption_resolution,[],[f122,f37])).

fof(f122,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | spl8_6 ),
    inference(subsumption_resolution,[],[f121,f38])).

fof(f121,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | spl8_6 ),
    inference(subsumption_resolution,[],[f120,f76])).

fof(f120,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_6 ),
    inference(resolution,[],[f107,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v7_waybel_0(sK4(X0,X1))
      | v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f107,plain,
    ( ~ v7_waybel_0(sK4(sK0,sK1))
    | spl8_6 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl8_6
  <=> v7_waybel_0(sK4(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f119,plain,
    ( spl8_1
    | spl8_5 ),
    inference(avatar_contradiction_clause,[],[f118])).

fof(f118,plain,
    ( $false
    | spl8_1
    | spl8_5 ),
    inference(subsumption_resolution,[],[f117,f35])).

fof(f117,plain,
    ( v2_struct_0(sK0)
    | spl8_1
    | spl8_5 ),
    inference(subsumption_resolution,[],[f116,f36])).

fof(f116,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | spl8_5 ),
    inference(subsumption_resolution,[],[f115,f37])).

fof(f115,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | spl8_5 ),
    inference(subsumption_resolution,[],[f114,f38])).

fof(f114,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | spl8_5 ),
    inference(subsumption_resolution,[],[f113,f76])).

fof(f113,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_5 ),
    inference(resolution,[],[f103,f51])).

% (22714)Refutation not found, incomplete strategy% (22714)------------------------------
% (22714)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (22714)Termination reason: Refutation not found, incomplete strategy

% (22714)Memory used [KB]: 5373
% (22714)Time elapsed: 0.083 s
% (22714)------------------------------
% (22714)------------------------------
fof(f51,plain,(
    ! [X0,X1] :
      ( v4_orders_2(sK4(X0,X1))
      | v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f103,plain,
    ( ~ v4_orders_2(sK4(sK0,sK1))
    | spl8_5 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl8_5
  <=> v4_orders_2(sK4(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f112,plain,
    ( spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | spl8_1 ),
    inference(avatar_split_clause,[],[f92,f74,f109,f105,f101,f97,f94])).

fof(f92,plain,
    ( ! [X0] :
        ( ~ l1_waybel_0(sK4(sK0,sK1),sK0)
        | ~ v7_waybel_0(sK4(sK0,sK1))
        | ~ v4_orders_2(sK4(sK0,sK1))
        | v2_struct_0(sK4(sK0,sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,sK4(sK0,sK1),X0)
        | r2_hidden(X0,k2_pre_topc(sK0,sK1)) )
    | spl8_1 ),
    inference(subsumption_resolution,[],[f91,f35])).

% (22709)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
fof(f91,plain,
    ( ! [X0] :
        ( ~ l1_waybel_0(sK4(sK0,sK1),sK0)
        | ~ v7_waybel_0(sK4(sK0,sK1))
        | ~ v4_orders_2(sK4(sK0,sK1))
        | v2_struct_0(sK4(sK0,sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,sK4(sK0,sK1),X0)
        | r2_hidden(X0,k2_pre_topc(sK0,sK1))
        | v2_struct_0(sK0) )
    | spl8_1 ),
    inference(subsumption_resolution,[],[f90,f36])).

fof(f90,plain,
    ( ! [X0] :
        ( ~ l1_waybel_0(sK4(sK0,sK1),sK0)
        | ~ v7_waybel_0(sK4(sK0,sK1))
        | ~ v4_orders_2(sK4(sK0,sK1))
        | v2_struct_0(sK4(sK0,sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,sK4(sK0,sK1),X0)
        | r2_hidden(X0,k2_pre_topc(sK0,sK1))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl8_1 ),
    inference(subsumption_resolution,[],[f89,f37])).

fof(f89,plain,
    ( ! [X0] :
        ( ~ l1_waybel_0(sK4(sK0,sK1),sK0)
        | ~ v7_waybel_0(sK4(sK0,sK1))
        | ~ v4_orders_2(sK4(sK0,sK1))
        | v2_struct_0(sK4(sK0,sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,sK4(sK0,sK1),X0)
        | r2_hidden(X0,k2_pre_topc(sK0,sK1))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl8_1 ),
    inference(subsumption_resolution,[],[f88,f38])).

fof(f88,plain,
    ( ! [X0] :
        ( ~ l1_waybel_0(sK4(sK0,sK1),sK0)
        | ~ v7_waybel_0(sK4(sK0,sK1))
        | ~ v4_orders_2(sK4(sK0,sK1))
        | v2_struct_0(sK4(sK0,sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,sK4(sK0,sK1),X0)
        | r2_hidden(X0,k2_pre_topc(sK0,sK1))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl8_1 ),
    inference(subsumption_resolution,[],[f87,f76])).

fof(f87,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(sK4(sK0,sK1),sK0)
      | ~ v7_waybel_0(sK4(sK0,sK1))
      | ~ v4_orders_2(sK4(sK0,sK1))
      | v2_struct_0(sK4(sK0,sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK4(sK0,sK1),X0)
      | r2_hidden(X0,k2_pre_topc(sK0,sK1))
      | v4_pre_topc(sK1,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f86,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_waybel_0(X0,sK4(X0,X1),X1)
      | v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ r1_waybel_0(sK0,X0,sK1)
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X0,X1)
      | r2_hidden(X1,k2_pre_topc(sK0,sK1)) ) ),
    inference(resolution,[],[f85,f38])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_waybel_0(sK0,X0,X2)
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X0,X1)
      | r2_hidden(X1,k2_pre_topc(sK0,X2)) ) ),
    inference(subsumption_resolution,[],[f84,f35])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_waybel_9(sK0,X0,X1)
      | ~ r1_waybel_0(sK0,X0,X2)
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X1,k2_pre_topc(sK0,X2))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f83,f36])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_waybel_9(sK0,X0,X1)
      | ~ r1_waybel_0(sK0,X0,X2)
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X1,k2_pre_topc(sK0,X2))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f72,f37])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r3_waybel_9(X0,X3,X2)
      | ~ r1_waybel_0(X0,X3,X1)
      | ~ l1_waybel_0(X3,X0)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f81,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f40,f78,f74])).

fof(f40,plain,
    ( ~ v2_struct_0(sK2)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:48:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (22708)lrs+1003_2:3_afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=on:fde=unused:gs=on:inw=on:nm=0:newcnf=on:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:tha=off:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.47  % (22704)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12 on theBenchmark
% 0.21/0.47  % (22705)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.21/0.47  % (22700)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.21/0.47  % (22715)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.21/0.48  % (22710)WARNING: option uwaf not known.
% 0.21/0.48  % (22717)ott+11_5:1_afp=100000:afq=1.1:br=off:gs=on:nm=64:nwc=1:sos=all:urr=on:updr=off_287 on theBenchmark
% 0.21/0.48  % (22715)Refutation not found, incomplete strategy% (22715)------------------------------
% 0.21/0.48  % (22715)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (22715)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (22715)Memory used [KB]: 895
% 0.21/0.48  % (22715)Time elapsed: 0.030 s
% 0.21/0.48  % (22715)------------------------------
% 0.21/0.48  % (22715)------------------------------
% 0.21/0.48  % (22710)lrs+10_4:1_av=off:bd=off:bsr=on:cond=on:fde=unused:inw=on:lcm=reverse:lma=on:lwlo=on:nm=64:nwc=5:stl=90:sp=reverse_arity:thi=strong:uwa=ground:updr=off:uwaf=on_73 on theBenchmark
% 0.21/0.48  % (22700)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f384,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f81,f112,f119,f126,f133,f224,f232,f240,f248,f256,f268,f283,f290,f340,f348,f356,f364,f375,f383])).
% 0.21/0.48  fof(f383,plain,(
% 0.21/0.48    ~spl8_12 | ~spl8_13 | ~spl8_14),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f382])).
% 0.21/0.48  fof(f382,plain,(
% 0.21/0.48    $false | (~spl8_12 | ~spl8_13 | ~spl8_14)),
% 0.21/0.48    inference(subsumption_resolution,[],[f381,f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ~v2_struct_0(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ((((~r2_hidden(sK3,sK1) & r2_hidden(sK3,k10_yellow_6(sK0,sK2)) & m1_subset_1(sK3,u1_struct_0(sK0))) & r1_waybel_0(sK0,sK2,sK1) & l1_waybel_0(sK2,sK0) & v3_yellow_6(sK2,sK0) & v7_waybel_0(sK2) & v4_orders_2(sK2) & ~v2_struct_0(sK2)) | ~v4_pre_topc(sK1,sK0)) & (! [X4] : (! [X5] : (r2_hidden(X5,sK1) | ~r2_hidden(X5,k10_yellow_6(sK0,X4)) | ~m1_subset_1(X5,u1_struct_0(sK0))) | ~r1_waybel_0(sK0,X4,sK1) | ~l1_waybel_0(X4,sK0) | ~v3_yellow_6(X4,sK0) | ~v7_waybel_0(X4) | ~v4_orders_2(X4) | v2_struct_0(X4)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f20,f19,f18,f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : ((? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r2_hidden(X3,k10_yellow_6(X0,X2)) & m1_subset_1(X3,u1_struct_0(X0))) & r1_waybel_0(X0,X2,X1) & l1_waybel_0(X2,X0) & v3_yellow_6(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~v4_pre_topc(X1,X0)) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r2_hidden(X5,k10_yellow_6(X0,X4)) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~r1_waybel_0(X0,X4,X1) | ~l1_waybel_0(X4,X0) | ~v3_yellow_6(X4,X0) | ~v7_waybel_0(X4) | ~v4_orders_2(X4) | v2_struct_0(X4)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r2_hidden(X3,k10_yellow_6(sK0,X2)) & m1_subset_1(X3,u1_struct_0(sK0))) & r1_waybel_0(sK0,X2,X1) & l1_waybel_0(X2,sK0) & v3_yellow_6(X2,sK0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~v4_pre_topc(X1,sK0)) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r2_hidden(X5,k10_yellow_6(sK0,X4)) | ~m1_subset_1(X5,u1_struct_0(sK0))) | ~r1_waybel_0(sK0,X4,X1) | ~l1_waybel_0(X4,sK0) | ~v3_yellow_6(X4,sK0) | ~v7_waybel_0(X4) | ~v4_orders_2(X4) | v2_struct_0(X4)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ? [X1] : ((? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r2_hidden(X3,k10_yellow_6(sK0,X2)) & m1_subset_1(X3,u1_struct_0(sK0))) & r1_waybel_0(sK0,X2,X1) & l1_waybel_0(X2,sK0) & v3_yellow_6(X2,sK0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~v4_pre_topc(X1,sK0)) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r2_hidden(X5,k10_yellow_6(sK0,X4)) | ~m1_subset_1(X5,u1_struct_0(sK0))) | ~r1_waybel_0(sK0,X4,X1) | ~l1_waybel_0(X4,sK0) | ~v3_yellow_6(X4,sK0) | ~v7_waybel_0(X4) | ~v4_orders_2(X4) | v2_struct_0(X4)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((? [X2] : (? [X3] : (~r2_hidden(X3,sK1) & r2_hidden(X3,k10_yellow_6(sK0,X2)) & m1_subset_1(X3,u1_struct_0(sK0))) & r1_waybel_0(sK0,X2,sK1) & l1_waybel_0(X2,sK0) & v3_yellow_6(X2,sK0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~v4_pre_topc(sK1,sK0)) & (! [X4] : (! [X5] : (r2_hidden(X5,sK1) | ~r2_hidden(X5,k10_yellow_6(sK0,X4)) | ~m1_subset_1(X5,u1_struct_0(sK0))) | ~r1_waybel_0(sK0,X4,sK1) | ~l1_waybel_0(X4,sK0) | ~v3_yellow_6(X4,sK0) | ~v7_waybel_0(X4) | ~v4_orders_2(X4) | v2_struct_0(X4)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ? [X2] : (? [X3] : (~r2_hidden(X3,sK1) & r2_hidden(X3,k10_yellow_6(sK0,X2)) & m1_subset_1(X3,u1_struct_0(sK0))) & r1_waybel_0(sK0,X2,sK1) & l1_waybel_0(X2,sK0) & v3_yellow_6(X2,sK0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => (? [X3] : (~r2_hidden(X3,sK1) & r2_hidden(X3,k10_yellow_6(sK0,sK2)) & m1_subset_1(X3,u1_struct_0(sK0))) & r1_waybel_0(sK0,sK2,sK1) & l1_waybel_0(sK2,sK0) & v3_yellow_6(sK2,sK0) & v7_waybel_0(sK2) & v4_orders_2(sK2) & ~v2_struct_0(sK2))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ? [X3] : (~r2_hidden(X3,sK1) & r2_hidden(X3,k10_yellow_6(sK0,sK2)) & m1_subset_1(X3,u1_struct_0(sK0))) => (~r2_hidden(sK3,sK1) & r2_hidden(sK3,k10_yellow_6(sK0,sK2)) & m1_subset_1(sK3,u1_struct_0(sK0)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : ((? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r2_hidden(X3,k10_yellow_6(X0,X2)) & m1_subset_1(X3,u1_struct_0(X0))) & r1_waybel_0(X0,X2,X1) & l1_waybel_0(X2,X0) & v3_yellow_6(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~v4_pre_topc(X1,X0)) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r2_hidden(X5,k10_yellow_6(X0,X4)) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~r1_waybel_0(X0,X4,X1) | ~l1_waybel_0(X4,X0) | ~v3_yellow_6(X4,X0) | ~v7_waybel_0(X4) | ~v4_orders_2(X4) | v2_struct_0(X4)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(rectify,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : ((? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r2_hidden(X3,k10_yellow_6(X0,X2)) & m1_subset_1(X3,u1_struct_0(X0))) & r1_waybel_0(X0,X2,X1) & l1_waybel_0(X2,X0) & v3_yellow_6(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~v4_pre_topc(X1,X0)) & (! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,k10_yellow_6(X0,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_waybel_0(X0,X2,X1) | ~l1_waybel_0(X2,X0) | ~v3_yellow_6(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (((? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r2_hidden(X3,k10_yellow_6(X0,X2)) & m1_subset_1(X3,u1_struct_0(X0))) & r1_waybel_0(X0,X2,X1) & l1_waybel_0(X2,X0) & v3_yellow_6(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~v4_pre_topc(X1,X0)) & (! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,k10_yellow_6(X0,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_waybel_0(X0,X2,X1) | ~l1_waybel_0(X2,X0) | ~v3_yellow_6(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,k10_yellow_6(X0,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_waybel_0(X0,X2,X1) | ~l1_waybel_0(X2,X0) | ~v3_yellow_6(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f6])).
% 0.21/0.48  fof(f6,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> ! [X2] : ((! [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,k10_yellow_6(X0,X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_waybel_0(X0,X2,X1)) | (~l1_waybel_0(X2,X0) | ~v3_yellow_6(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,negated_conjecture,(
% 0.21/0.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> ! [X2] : ((l1_waybel_0(X2,X0) & v3_yellow_6(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => (r1_waybel_0(X0,X2,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,k10_yellow_6(X0,X2)) => r2_hidden(X3,X1))))))))),
% 0.21/0.48    inference(negated_conjecture,[],[f4])).
% 0.21/0.48  fof(f4,conjecture,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> ! [X2] : ((l1_waybel_0(X2,X0) & v3_yellow_6(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => (r1_waybel_0(X0,X2,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,k10_yellow_6(X0,X2)) => r2_hidden(X3,X1))))))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_yellow19)).
% 0.21/0.48  fof(f381,plain,(
% 0.21/0.48    v2_struct_0(sK0) | (~spl8_12 | ~spl8_13 | ~spl8_14)),
% 0.21/0.48    inference(subsumption_resolution,[],[f380,f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    v2_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f380,plain,(
% 0.21/0.48    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_12 | ~spl8_13 | ~spl8_14)),
% 0.21/0.48    inference(subsumption_resolution,[],[f379,f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    l1_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f379,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_12 | ~spl8_13 | ~spl8_14)),
% 0.21/0.48    inference(subsumption_resolution,[],[f378,f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f378,plain,(
% 0.21/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_12 | ~spl8_13 | ~spl8_14)),
% 0.21/0.48    inference(subsumption_resolution,[],[f377,f277])).
% 0.21/0.48  fof(f277,plain,(
% 0.21/0.48    m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0)) | ~spl8_12),
% 0.21/0.48    inference(avatar_component_clause,[],[f276])).
% 0.21/0.48  fof(f276,plain,(
% 0.21/0.48    spl8_12 <=> m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 0.21/0.48  fof(f377,plain,(
% 0.21/0.48    ~m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_13 | ~spl8_14)),
% 0.21/0.48    inference(subsumption_resolution,[],[f376,f282])).
% 0.21/0.48  fof(f282,plain,(
% 0.21/0.48    r2_hidden(sK5(sK0,sK1),k2_pre_topc(sK0,sK1)) | ~spl8_13),
% 0.21/0.48    inference(avatar_component_clause,[],[f280])).
% 0.21/0.48  fof(f280,plain,(
% 0.21/0.48    spl8_13 <=> r2_hidden(sK5(sK0,sK1),k2_pre_topc(sK0,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 0.21/0.48  fof(f376,plain,(
% 0.21/0.48    ~r2_hidden(sK5(sK0,sK1),k2_pre_topc(sK0,sK1)) | ~m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl8_14),
% 0.21/0.48    inference(resolution,[],[f324,f58])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v2_struct_0(sK6(X0,X1,X2)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ! [X3] : (~r2_hidden(X2,k10_yellow_6(X0,X3)) | ~r1_waybel_0(X0,X3,X1) | ~l1_waybel_0(X3,X0) | ~v3_yellow_6(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3))) & ((r2_hidden(X2,k10_yellow_6(X0,sK6(X0,X1,X2))) & r1_waybel_0(X0,sK6(X0,X1,X2),X1) & l1_waybel_0(sK6(X0,X1,X2),X0) & v3_yellow_6(sK6(X0,X1,X2),X0) & v7_waybel_0(sK6(X0,X1,X2)) & v4_orders_2(sK6(X0,X1,X2)) & ~v2_struct_0(sK6(X0,X1,X2))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f28,f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X2,k10_yellow_6(X0,X4)) & r1_waybel_0(X0,X4,X1) & l1_waybel_0(X4,X0) & v3_yellow_6(X4,X0) & v7_waybel_0(X4) & v4_orders_2(X4) & ~v2_struct_0(X4)) => (r2_hidden(X2,k10_yellow_6(X0,sK6(X0,X1,X2))) & r1_waybel_0(X0,sK6(X0,X1,X2),X1) & l1_waybel_0(sK6(X0,X1,X2),X0) & v3_yellow_6(sK6(X0,X1,X2),X0) & v7_waybel_0(sK6(X0,X1,X2)) & v4_orders_2(sK6(X0,X1,X2)) & ~v2_struct_0(sK6(X0,X1,X2))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ! [X3] : (~r2_hidden(X2,k10_yellow_6(X0,X3)) | ~r1_waybel_0(X0,X3,X1) | ~l1_waybel_0(X3,X0) | ~v3_yellow_6(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3))) & (? [X4] : (r2_hidden(X2,k10_yellow_6(X0,X4)) & r1_waybel_0(X0,X4,X1) & l1_waybel_0(X4,X0) & v3_yellow_6(X4,X0) & v7_waybel_0(X4) & v4_orders_2(X4) & ~v2_struct_0(X4)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(rectify,[],[f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ! [X3] : (~r2_hidden(X2,k10_yellow_6(X0,X3)) | ~r1_waybel_0(X0,X3,X1) | ~l1_waybel_0(X3,X0) | ~v3_yellow_6(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3))) & (? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & r1_waybel_0(X0,X3,X1) & l1_waybel_0(X3,X0) & v3_yellow_6(X3,X0) & v7_waybel_0(X3) & v4_orders_2(X3) & ~v2_struct_0(X3)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & r1_waybel_0(X0,X3,X1) & l1_waybel_0(X3,X0) & v3_yellow_6(X3,X0) & v7_waybel_0(X3) & v4_orders_2(X3) & ~v2_struct_0(X3))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & r1_waybel_0(X0,X3,X1) & l1_waybel_0(X3,X0) & v3_yellow_6(X3,X0) & v7_waybel_0(X3) & v4_orders_2(X3) & ~v2_struct_0(X3))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & r1_waybel_0(X0,X3,X1) & l1_waybel_0(X3,X0) & v3_yellow_6(X3,X0) & v7_waybel_0(X3) & v4_orders_2(X3) & ~v2_struct_0(X3))))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_yellow19)).
% 0.21/0.48  fof(f324,plain,(
% 0.21/0.48    v2_struct_0(sK6(sK0,sK1,sK5(sK0,sK1))) | ~spl8_14),
% 0.21/0.48    inference(avatar_component_clause,[],[f322])).
% 0.21/0.48  fof(f322,plain,(
% 0.21/0.48    spl8_14 <=> v2_struct_0(sK6(sK0,sK1,sK5(sK0,sK1)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 0.21/0.48  fof(f375,plain,(
% 0.21/0.48    spl8_1 | ~spl8_12 | ~spl8_13 | ~spl8_18),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f374])).
% 0.21/0.48  fof(f374,plain,(
% 0.21/0.48    $false | (spl8_1 | ~spl8_12 | ~spl8_13 | ~spl8_18)),
% 0.21/0.48    inference(subsumption_resolution,[],[f373,f282])).
% 0.21/0.48  fof(f373,plain,(
% 0.21/0.48    ~r2_hidden(sK5(sK0,sK1),k2_pre_topc(sK0,sK1)) | (spl8_1 | ~spl8_12 | ~spl8_18)),
% 0.21/0.48    inference(subsumption_resolution,[],[f372,f35])).
% 0.21/0.48  fof(f372,plain,(
% 0.21/0.48    v2_struct_0(sK0) | ~r2_hidden(sK5(sK0,sK1),k2_pre_topc(sK0,sK1)) | (spl8_1 | ~spl8_12 | ~spl8_18)),
% 0.21/0.48    inference(subsumption_resolution,[],[f371,f36])).
% 0.21/0.48  fof(f371,plain,(
% 0.21/0.48    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~r2_hidden(sK5(sK0,sK1),k2_pre_topc(sK0,sK1)) | (spl8_1 | ~spl8_12 | ~spl8_18)),
% 0.21/0.48    inference(subsumption_resolution,[],[f370,f37])).
% 0.21/0.48  fof(f370,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~r2_hidden(sK5(sK0,sK1),k2_pre_topc(sK0,sK1)) | (spl8_1 | ~spl8_12 | ~spl8_18)),
% 0.21/0.48    inference(subsumption_resolution,[],[f369,f38])).
% 0.21/0.48  fof(f369,plain,(
% 0.21/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~r2_hidden(sK5(sK0,sK1),k2_pre_topc(sK0,sK1)) | (spl8_1 | ~spl8_12 | ~spl8_18)),
% 0.21/0.48    inference(subsumption_resolution,[],[f368,f76])).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    ~v4_pre_topc(sK1,sK0) | spl8_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f74])).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    spl8_1 <=> v4_pre_topc(sK1,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.48  fof(f368,plain,(
% 0.21/0.48    v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~r2_hidden(sK5(sK0,sK1),k2_pre_topc(sK0,sK1)) | (~spl8_12 | ~spl8_18)),
% 0.21/0.48    inference(subsumption_resolution,[],[f367,f277])).
% 0.21/0.48  fof(f367,plain,(
% 0.21/0.48    ~m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0)) | v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~r2_hidden(sK5(sK0,sK1),k2_pre_topc(sK0,sK1)) | ~spl8_18),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f366])).
% 0.21/0.48  fof(f366,plain,(
% 0.21/0.48    ~m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0)) | v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~r2_hidden(sK5(sK0,sK1),k2_pre_topc(sK0,sK1)) | ~m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl8_18),
% 0.21/0.48    inference(resolution,[],[f365,f64])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r2_hidden(X2,k10_yellow_6(X0,sK6(X0,X1,X2))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f30])).
% 0.21/0.48  fof(f365,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(sK5(X0,sK1),k10_yellow_6(sK0,sK6(sK0,sK1,sK5(sK0,sK1)))) | ~m1_subset_1(sK5(X0,sK1),u1_struct_0(sK0)) | v4_pre_topc(sK1,X0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | ~spl8_18),
% 0.21/0.48    inference(resolution,[],[f339,f57])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f26])).
% 0.21/0.48  % (22712)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ((~r2_hidden(sK5(X0,X1),X1) & r3_waybel_9(X0,sK4(X0,X1),sK5(X0,X1)) & m1_subset_1(sK5(X0,X1),u1_struct_0(X0))) & r1_waybel_0(X0,sK4(X0,X1),X1) & l1_waybel_0(sK4(X0,X1),X0) & v7_waybel_0(sK4(X0,X1)) & v4_orders_2(sK4(X0,X1)) & ~v2_struct_0(sK4(X0,X1)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r3_waybel_9(X0,X4,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~r1_waybel_0(X0,X4,X1) | ~l1_waybel_0(X4,X0) | ~v7_waybel_0(X4) | ~v4_orders_2(X4) | v2_struct_0(X4)) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f23,f25,f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X1,X0] : (? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r3_waybel_9(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) & r1_waybel_0(X0,X2,X1) & l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => (? [X3] : (~r2_hidden(X3,X1) & r3_waybel_9(X0,sK4(X0,X1),X3) & m1_subset_1(X3,u1_struct_0(X0))) & r1_waybel_0(X0,sK4(X0,X1),X1) & l1_waybel_0(sK4(X0,X1),X0) & v7_waybel_0(sK4(X0,X1)) & v4_orders_2(sK4(X0,X1)) & ~v2_struct_0(sK4(X0,X1))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X1,X0] : (? [X3] : (~r2_hidden(X3,X1) & r3_waybel_9(X0,sK4(X0,X1),X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r2_hidden(sK5(X0,X1),X1) & r3_waybel_9(X0,sK4(X0,X1),sK5(X0,X1)) & m1_subset_1(sK5(X0,X1),u1_struct_0(X0))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r3_waybel_9(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) & r1_waybel_0(X0,X2,X1) & l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r3_waybel_9(X0,X4,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~r1_waybel_0(X0,X4,X1) | ~l1_waybel_0(X4,X0) | ~v7_waybel_0(X4) | ~v4_orders_2(X4) | v2_struct_0(X4)) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(rectify,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r3_waybel_9(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) & r1_waybel_0(X0,X2,X1) & l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2))) & (! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r3_waybel_9(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_waybel_0(X0,X2,X1) | ~l1_waybel_0(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2)) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r3_waybel_9(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_waybel_0(X0,X2,X1) | ~l1_waybel_0(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f8])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> ! [X2] : ((! [X3] : ((r2_hidden(X3,X1) | ~r3_waybel_9(X0,X2,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_waybel_0(X0,X2,X1)) | (~l1_waybel_0(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> ! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => (r1_waybel_0(X0,X2,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_waybel_9(X0,X2,X3) => r2_hidden(X3,X1))))))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_yellow19)).
% 0.21/0.48  fof(f339,plain,(
% 0.21/0.48    ( ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,k10_yellow_6(sK0,sK6(sK0,sK1,sK5(sK0,sK1)))) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl8_18),
% 0.21/0.48    inference(avatar_component_clause,[],[f338])).
% 0.21/0.48  fof(f338,plain,(
% 0.21/0.48    spl8_18 <=> ! [X0] : (~r2_hidden(X0,k10_yellow_6(sK0,sK6(sK0,sK1,sK5(sK0,sK1)))) | r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 0.21/0.48  fof(f364,plain,(
% 0.21/0.48    ~spl8_12 | ~spl8_13 | spl8_17),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f363])).
% 0.21/0.48  fof(f363,plain,(
% 0.21/0.48    $false | (~spl8_12 | ~spl8_13 | spl8_17)),
% 0.21/0.48    inference(subsumption_resolution,[],[f362,f35])).
% 0.21/0.48  fof(f362,plain,(
% 0.21/0.48    v2_struct_0(sK0) | (~spl8_12 | ~spl8_13 | spl8_17)),
% 0.21/0.48    inference(subsumption_resolution,[],[f361,f36])).
% 0.21/0.48  fof(f361,plain,(
% 0.21/0.48    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_12 | ~spl8_13 | spl8_17)),
% 0.21/0.48    inference(subsumption_resolution,[],[f360,f37])).
% 0.21/0.48  fof(f360,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_12 | ~spl8_13 | spl8_17)),
% 0.21/0.48    inference(subsumption_resolution,[],[f359,f38])).
% 0.21/0.48  fof(f359,plain,(
% 0.21/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_12 | ~spl8_13 | spl8_17)),
% 0.21/0.48    inference(subsumption_resolution,[],[f358,f277])).
% 0.21/0.48  fof(f358,plain,(
% 0.21/0.48    ~m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_13 | spl8_17)),
% 0.21/0.48    inference(subsumption_resolution,[],[f357,f282])).
% 0.21/0.48  fof(f357,plain,(
% 0.21/0.48    ~r2_hidden(sK5(sK0,sK1),k2_pre_topc(sK0,sK1)) | ~m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl8_17),
% 0.21/0.48    inference(resolution,[],[f336,f62])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (l1_waybel_0(sK6(X0,X1,X2),X0) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f30])).
% 0.21/0.48  fof(f336,plain,(
% 0.21/0.48    ~l1_waybel_0(sK6(sK0,sK1,sK5(sK0,sK1)),sK0) | spl8_17),
% 0.21/0.48    inference(avatar_component_clause,[],[f334])).
% 0.21/0.48  fof(f334,plain,(
% 0.21/0.48    spl8_17 <=> l1_waybel_0(sK6(sK0,sK1,sK5(sK0,sK1)),sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 0.21/0.48  fof(f356,plain,(
% 0.21/0.48    ~spl8_12 | ~spl8_13 | spl8_16),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f355])).
% 0.21/0.48  fof(f355,plain,(
% 0.21/0.48    $false | (~spl8_12 | ~spl8_13 | spl8_16)),
% 0.21/0.48    inference(subsumption_resolution,[],[f354,f35])).
% 0.21/0.48  fof(f354,plain,(
% 0.21/0.48    v2_struct_0(sK0) | (~spl8_12 | ~spl8_13 | spl8_16)),
% 0.21/0.48    inference(subsumption_resolution,[],[f353,f36])).
% 0.21/0.48  fof(f353,plain,(
% 0.21/0.48    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_12 | ~spl8_13 | spl8_16)),
% 0.21/0.48    inference(subsumption_resolution,[],[f352,f37])).
% 0.21/0.48  fof(f352,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_12 | ~spl8_13 | spl8_16)),
% 0.21/0.48    inference(subsumption_resolution,[],[f351,f38])).
% 0.21/0.48  fof(f351,plain,(
% 0.21/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_12 | ~spl8_13 | spl8_16)),
% 0.21/0.48    inference(subsumption_resolution,[],[f350,f277])).
% 0.21/0.48  fof(f350,plain,(
% 0.21/0.48    ~m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_13 | spl8_16)),
% 0.21/0.48    inference(subsumption_resolution,[],[f349,f282])).
% 0.21/0.48  fof(f349,plain,(
% 0.21/0.48    ~r2_hidden(sK5(sK0,sK1),k2_pre_topc(sK0,sK1)) | ~m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl8_16),
% 0.21/0.48    inference(resolution,[],[f332,f60])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (v7_waybel_0(sK6(X0,X1,X2)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f30])).
% 0.21/0.48  fof(f332,plain,(
% 0.21/0.48    ~v7_waybel_0(sK6(sK0,sK1,sK5(sK0,sK1))) | spl8_16),
% 0.21/0.48    inference(avatar_component_clause,[],[f330])).
% 0.21/0.48  fof(f330,plain,(
% 0.21/0.48    spl8_16 <=> v7_waybel_0(sK6(sK0,sK1,sK5(sK0,sK1)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 0.21/0.48  fof(f348,plain,(
% 0.21/0.48    ~spl8_12 | ~spl8_13 | spl8_15),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f347])).
% 0.21/0.48  fof(f347,plain,(
% 0.21/0.48    $false | (~spl8_12 | ~spl8_13 | spl8_15)),
% 0.21/0.48    inference(subsumption_resolution,[],[f346,f35])).
% 0.21/0.48  fof(f346,plain,(
% 0.21/0.48    v2_struct_0(sK0) | (~spl8_12 | ~spl8_13 | spl8_15)),
% 0.21/0.48    inference(subsumption_resolution,[],[f345,f36])).
% 0.21/0.48  fof(f345,plain,(
% 0.21/0.48    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_12 | ~spl8_13 | spl8_15)),
% 0.21/0.48    inference(subsumption_resolution,[],[f344,f37])).
% 0.21/0.48  fof(f344,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_12 | ~spl8_13 | spl8_15)),
% 0.21/0.48    inference(subsumption_resolution,[],[f343,f38])).
% 0.21/0.48  fof(f343,plain,(
% 0.21/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_12 | ~spl8_13 | spl8_15)),
% 0.21/0.48    inference(subsumption_resolution,[],[f342,f277])).
% 0.21/0.48  fof(f342,plain,(
% 0.21/0.48    ~m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_13 | spl8_15)),
% 0.21/0.48    inference(subsumption_resolution,[],[f341,f282])).
% 0.21/0.48  fof(f341,plain,(
% 0.21/0.48    ~r2_hidden(sK5(sK0,sK1),k2_pre_topc(sK0,sK1)) | ~m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl8_15),
% 0.21/0.48    inference(resolution,[],[f328,f59])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (v4_orders_2(sK6(X0,X1,X2)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f30])).
% 0.21/0.48  fof(f328,plain,(
% 0.21/0.48    ~v4_orders_2(sK6(sK0,sK1,sK5(sK0,sK1))) | spl8_15),
% 0.21/0.48    inference(avatar_component_clause,[],[f326])).
% 0.21/0.48  fof(f326,plain,(
% 0.21/0.48    spl8_15 <=> v4_orders_2(sK6(sK0,sK1,sK5(sK0,sK1)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 0.21/0.48  fof(f340,plain,(
% 0.21/0.48    spl8_14 | ~spl8_15 | ~spl8_16 | ~spl8_17 | spl8_18 | spl8_1 | ~spl8_12 | ~spl8_13),
% 0.21/0.48    inference(avatar_split_clause,[],[f320,f280,f276,f74,f338,f334,f330,f326,f322])).
% 0.21/0.48  fof(f320,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(X0,k10_yellow_6(sK0,sK6(sK0,sK1,sK5(sK0,sK1)))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_waybel_0(sK6(sK0,sK1,sK5(sK0,sK1)),sK0) | r2_hidden(X0,sK1) | ~v7_waybel_0(sK6(sK0,sK1,sK5(sK0,sK1))) | ~v4_orders_2(sK6(sK0,sK1,sK5(sK0,sK1))) | v2_struct_0(sK6(sK0,sK1,sK5(sK0,sK1)))) ) | (spl8_1 | ~spl8_12 | ~spl8_13)),
% 0.21/0.48    inference(subsumption_resolution,[],[f319,f309])).
% 0.21/0.48  fof(f309,plain,(
% 0.21/0.48    r1_waybel_0(sK0,sK6(sK0,sK1,sK5(sK0,sK1)),sK1) | (~spl8_12 | ~spl8_13)),
% 0.21/0.48    inference(subsumption_resolution,[],[f308,f35])).
% 0.21/0.48  fof(f308,plain,(
% 0.21/0.48    r1_waybel_0(sK0,sK6(sK0,sK1,sK5(sK0,sK1)),sK1) | v2_struct_0(sK0) | (~spl8_12 | ~spl8_13)),
% 0.21/0.48    inference(subsumption_resolution,[],[f307,f36])).
% 0.21/0.48  fof(f307,plain,(
% 0.21/0.48    r1_waybel_0(sK0,sK6(sK0,sK1,sK5(sK0,sK1)),sK1) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_12 | ~spl8_13)),
% 0.21/0.48    inference(subsumption_resolution,[],[f306,f37])).
% 0.21/0.48  fof(f306,plain,(
% 0.21/0.48    r1_waybel_0(sK0,sK6(sK0,sK1,sK5(sK0,sK1)),sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_12 | ~spl8_13)),
% 0.21/0.48    inference(subsumption_resolution,[],[f305,f38])).
% 0.21/0.48  fof(f305,plain,(
% 0.21/0.48    r1_waybel_0(sK0,sK6(sK0,sK1,sK5(sK0,sK1)),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_12 | ~spl8_13)),
% 0.21/0.48    inference(subsumption_resolution,[],[f293,f277])).
% 0.21/0.48  fof(f293,plain,(
% 0.21/0.48    r1_waybel_0(sK0,sK6(sK0,sK1,sK5(sK0,sK1)),sK1) | ~m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl8_13),
% 0.21/0.48    inference(resolution,[],[f282,f63])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X2,k2_pre_topc(X0,X1)) | r1_waybel_0(X0,sK6(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f30])).
% 0.21/0.48  fof(f319,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(X0,k10_yellow_6(sK0,sK6(sK0,sK1,sK5(sK0,sK1)))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_waybel_0(sK0,sK6(sK0,sK1,sK5(sK0,sK1)),sK1) | ~l1_waybel_0(sK6(sK0,sK1,sK5(sK0,sK1)),sK0) | r2_hidden(X0,sK1) | ~v7_waybel_0(sK6(sK0,sK1,sK5(sK0,sK1))) | ~v4_orders_2(sK6(sK0,sK1,sK5(sK0,sK1))) | v2_struct_0(sK6(sK0,sK1,sK5(sK0,sK1)))) ) | (spl8_1 | ~spl8_12 | ~spl8_13)),
% 0.21/0.48    inference(resolution,[],[f318,f314])).
% 0.21/0.48  fof(f314,plain,(
% 0.21/0.48    v3_yellow_6(sK6(sK0,sK1,sK5(sK0,sK1)),sK0) | (~spl8_12 | ~spl8_13)),
% 0.21/0.48    inference(subsumption_resolution,[],[f313,f35])).
% 0.21/0.48  fof(f313,plain,(
% 0.21/0.48    v3_yellow_6(sK6(sK0,sK1,sK5(sK0,sK1)),sK0) | v2_struct_0(sK0) | (~spl8_12 | ~spl8_13)),
% 0.21/0.48    inference(subsumption_resolution,[],[f312,f36])).
% 0.21/0.48  fof(f312,plain,(
% 0.21/0.48    v3_yellow_6(sK6(sK0,sK1,sK5(sK0,sK1)),sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_12 | ~spl8_13)),
% 0.21/0.48    inference(subsumption_resolution,[],[f311,f37])).
% 0.21/0.48  fof(f311,plain,(
% 0.21/0.48    v3_yellow_6(sK6(sK0,sK1,sK5(sK0,sK1)),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_12 | ~spl8_13)),
% 0.21/0.48    inference(subsumption_resolution,[],[f310,f38])).
% 0.21/0.48  fof(f310,plain,(
% 0.21/0.48    v3_yellow_6(sK6(sK0,sK1,sK5(sK0,sK1)),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_12 | ~spl8_13)),
% 0.21/0.48    inference(subsumption_resolution,[],[f294,f277])).
% 0.21/0.48  fof(f294,plain,(
% 0.21/0.48    v3_yellow_6(sK6(sK0,sK1,sK5(sK0,sK1)),sK0) | ~m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl8_13),
% 0.21/0.48    inference(resolution,[],[f282,f61])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X2,k2_pre_topc(X0,X1)) | v3_yellow_6(sK6(X0,X1,X2),X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f30])).
% 0.21/0.48  fof(f318,plain,(
% 0.21/0.48    ( ! [X4,X5] : (~v3_yellow_6(X4,sK0) | ~r2_hidden(X5,k10_yellow_6(sK0,X4)) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~r1_waybel_0(sK0,X4,sK1) | ~l1_waybel_0(X4,sK0) | r2_hidden(X5,sK1) | ~v7_waybel_0(X4) | ~v4_orders_2(X4) | v2_struct_0(X4)) ) | spl8_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f39,f76])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ( ! [X4,X5] : (r2_hidden(X5,sK1) | ~r2_hidden(X5,k10_yellow_6(sK0,X4)) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~r1_waybel_0(sK0,X4,sK1) | ~l1_waybel_0(X4,sK0) | ~v3_yellow_6(X4,sK0) | ~v7_waybel_0(X4) | ~v4_orders_2(X4) | v2_struct_0(X4) | v4_pre_topc(sK1,sK0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f290,plain,(
% 0.21/0.48    spl8_1 | spl8_12),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f289])).
% 0.21/0.48  fof(f289,plain,(
% 0.21/0.48    $false | (spl8_1 | spl8_12)),
% 0.21/0.48    inference(subsumption_resolution,[],[f288,f35])).
% 0.21/0.48  fof(f288,plain,(
% 0.21/0.48    v2_struct_0(sK0) | (spl8_1 | spl8_12)),
% 0.21/0.48    inference(subsumption_resolution,[],[f287,f36])).
% 0.21/0.48  fof(f287,plain,(
% 0.21/0.48    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl8_1 | spl8_12)),
% 0.21/0.48    inference(subsumption_resolution,[],[f286,f37])).
% 0.21/0.48  fof(f286,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl8_1 | spl8_12)),
% 0.21/0.48    inference(subsumption_resolution,[],[f285,f38])).
% 0.21/0.48  fof(f285,plain,(
% 0.21/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl8_1 | spl8_12)),
% 0.21/0.48    inference(subsumption_resolution,[],[f284,f76])).
% 0.21/0.48  fof(f284,plain,(
% 0.21/0.48    v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl8_12),
% 0.21/0.48    inference(resolution,[],[f278,f55])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    ( ! [X0,X1] : (m1_subset_1(sK5(X0,X1),u1_struct_0(X0)) | v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f26])).
% 0.21/0.48  fof(f278,plain,(
% 0.21/0.48    ~m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0)) | spl8_12),
% 0.21/0.48    inference(avatar_component_clause,[],[f276])).
% 0.21/0.48  fof(f283,plain,(
% 0.21/0.48    ~spl8_12 | spl8_13 | spl8_1 | ~spl8_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f274,f94,f74,f280,f276])).
% 0.21/0.48  fof(f94,plain,(
% 0.21/0.48    spl8_3 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,k2_pre_topc(sK0,sK1)) | ~r3_waybel_9(sK0,sK4(sK0,sK1),X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.21/0.48  fof(f274,plain,(
% 0.21/0.48    r2_hidden(sK5(sK0,sK1),k2_pre_topc(sK0,sK1)) | ~m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0)) | (spl8_1 | ~spl8_3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f273,f35])).
% 0.21/0.48  fof(f273,plain,(
% 0.21/0.48    r2_hidden(sK5(sK0,sK1),k2_pre_topc(sK0,sK1)) | ~m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0)) | v2_struct_0(sK0) | (spl8_1 | ~spl8_3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f272,f36])).
% 0.21/0.48  fof(f272,plain,(
% 0.21/0.48    r2_hidden(sK5(sK0,sK1),k2_pre_topc(sK0,sK1)) | ~m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl8_1 | ~spl8_3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f271,f37])).
% 0.21/0.48  fof(f271,plain,(
% 0.21/0.48    r2_hidden(sK5(sK0,sK1),k2_pre_topc(sK0,sK1)) | ~m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl8_1 | ~spl8_3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f270,f38])).
% 0.21/0.48  fof(f270,plain,(
% 0.21/0.48    r2_hidden(sK5(sK0,sK1),k2_pre_topc(sK0,sK1)) | ~m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl8_1 | ~spl8_3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f269,f76])).
% 0.21/0.48  fof(f269,plain,(
% 0.21/0.48    r2_hidden(sK5(sK0,sK1),k2_pre_topc(sK0,sK1)) | ~m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0)) | v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl8_3),
% 0.21/0.48    inference(resolution,[],[f95,f56])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r3_waybel_9(X0,sK4(X0,X1),sK5(X0,X1)) | v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f26])).
% 0.21/0.48  fof(f95,plain,(
% 0.21/0.48    ( ! [X0] : (~r3_waybel_9(sK0,sK4(sK0,sK1),X0) | r2_hidden(X0,k2_pre_topc(sK0,sK1)) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl8_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f94])).
% 0.21/0.48  fof(f268,plain,(
% 0.21/0.48    spl8_1 | ~spl8_4),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f267])).
% 0.21/0.48  fof(f267,plain,(
% 0.21/0.48    $false | (spl8_1 | ~spl8_4)),
% 0.21/0.48    inference(subsumption_resolution,[],[f266,f35])).
% 0.21/0.48  fof(f266,plain,(
% 0.21/0.48    v2_struct_0(sK0) | (spl8_1 | ~spl8_4)),
% 0.21/0.48    inference(subsumption_resolution,[],[f265,f36])).
% 0.21/0.48  fof(f265,plain,(
% 0.21/0.48    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl8_1 | ~spl8_4)),
% 0.21/0.48    inference(subsumption_resolution,[],[f264,f37])).
% 0.21/0.48  fof(f264,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl8_1 | ~spl8_4)),
% 0.21/0.48    inference(subsumption_resolution,[],[f263,f38])).
% 0.21/0.48  fof(f263,plain,(
% 0.21/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl8_1 | ~spl8_4)),
% 0.21/0.48    inference(subsumption_resolution,[],[f262,f76])).
% 0.21/0.48  fof(f262,plain,(
% 0.21/0.48    v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl8_4),
% 0.21/0.48    inference(resolution,[],[f99,f50])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v2_struct_0(sK4(X0,X1)) | v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f26])).
% 0.21/0.48  fof(f99,plain,(
% 0.21/0.48    v2_struct_0(sK4(sK0,sK1)) | ~spl8_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f97])).
% 0.21/0.48  fof(f97,plain,(
% 0.21/0.48    spl8_4 <=> v2_struct_0(sK4(sK0,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.21/0.48  fof(f256,plain,(
% 0.21/0.48    ~spl8_1 | spl8_2 | ~spl8_8),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f255])).
% 0.21/0.48  fof(f255,plain,(
% 0.21/0.48    $false | (~spl8_1 | spl8_2 | ~spl8_8)),
% 0.21/0.48    inference(subsumption_resolution,[],[f254,f35])).
% 0.21/0.48  fof(f254,plain,(
% 0.21/0.48    v2_struct_0(sK0) | (~spl8_1 | spl8_2 | ~spl8_8)),
% 0.21/0.48    inference(subsumption_resolution,[],[f253,f36])).
% 0.21/0.48  fof(f253,plain,(
% 0.21/0.48    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_1 | spl8_2 | ~spl8_8)),
% 0.21/0.48    inference(subsumption_resolution,[],[f252,f37])).
% 0.21/0.48  fof(f252,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_1 | spl8_2 | ~spl8_8)),
% 0.21/0.48    inference(subsumption_resolution,[],[f251,f38])).
% 0.21/0.48  fof(f251,plain,(
% 0.21/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_1 | spl8_2 | ~spl8_8)),
% 0.21/0.48    inference(subsumption_resolution,[],[f250,f157])).
% 0.21/0.48  fof(f157,plain,(
% 0.21/0.48    m1_subset_1(sK3,u1_struct_0(sK0)) | ~spl8_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f46,f75])).
% 0.21/0.48  fof(f75,plain,(
% 0.21/0.48    v4_pre_topc(sK1,sK0) | ~spl8_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f74])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    m1_subset_1(sK3,u1_struct_0(sK0)) | ~v4_pre_topc(sK1,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f250,plain,(
% 0.21/0.48    ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_1 | spl8_2 | ~spl8_8)),
% 0.21/0.48    inference(subsumption_resolution,[],[f249,f176])).
% 0.21/0.48  fof(f176,plain,(
% 0.21/0.48    r2_hidden(sK3,k2_pre_topc(sK0,sK1)) | (~spl8_1 | spl8_2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f175,f157])).
% 0.21/0.48  fof(f175,plain,(
% 0.21/0.48    ~m1_subset_1(sK3,u1_struct_0(sK0)) | r2_hidden(sK3,k2_pre_topc(sK0,sK1)) | (~spl8_1 | spl8_2)),
% 0.21/0.48    inference(resolution,[],[f174,f158])).
% 0.21/0.48  fof(f158,plain,(
% 0.21/0.48    r2_hidden(sK3,k10_yellow_6(sK0,sK2)) | ~spl8_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f47,f75])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    r2_hidden(sK3,k10_yellow_6(sK0,sK2)) | ~v4_pre_topc(sK1,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f174,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(X0,k10_yellow_6(sK0,sK2)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,k2_pre_topc(sK0,sK1))) ) | (~spl8_1 | spl8_2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f173,f38])).
% 0.21/0.48  fof(f173,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(X0,k10_yellow_6(sK0,sK2)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X0,k2_pre_topc(sK0,sK1))) ) | (~spl8_1 | spl8_2)),
% 0.21/0.48    inference(resolution,[],[f172,f151])).
% 0.21/0.48  fof(f151,plain,(
% 0.21/0.48    r1_waybel_0(sK0,sK2,sK1) | ~spl8_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f45,f75])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    r1_waybel_0(sK0,sK2,sK1) | ~v4_pre_topc(sK1,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f172,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_waybel_0(sK0,sK2,X0) | ~r2_hidden(X1,k10_yellow_6(sK0,sK2)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X1,k2_pre_topc(sK0,X0))) ) | (~spl8_1 | spl8_2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f171,f80])).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    ~v2_struct_0(sK2) | spl8_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f78])).
% 0.21/0.48  fof(f78,plain,(
% 0.21/0.48    spl8_2 <=> v2_struct_0(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.48  fof(f171,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_waybel_0(sK0,sK2,X0) | ~r2_hidden(X1,k10_yellow_6(sK0,sK2)) | v2_struct_0(sK2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X1,k2_pre_topc(sK0,X0))) ) | ~spl8_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f170,f146])).
% 0.21/0.48  fof(f146,plain,(
% 0.21/0.48    v4_orders_2(sK2) | ~spl8_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f41,f75])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    v4_orders_2(sK2) | ~v4_pre_topc(sK1,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f170,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_waybel_0(sK0,sK2,X0) | ~r2_hidden(X1,k10_yellow_6(sK0,sK2)) | ~v4_orders_2(sK2) | v2_struct_0(sK2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X1,k2_pre_topc(sK0,X0))) ) | ~spl8_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f169,f147])).
% 0.21/0.48  fof(f147,plain,(
% 0.21/0.48    v7_waybel_0(sK2) | ~spl8_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f42,f75])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    v7_waybel_0(sK2) | ~v4_pre_topc(sK1,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f169,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_waybel_0(sK0,sK2,X0) | ~r2_hidden(X1,k10_yellow_6(sK0,sK2)) | ~v7_waybel_0(sK2) | ~v4_orders_2(sK2) | v2_struct_0(sK2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X1,k2_pre_topc(sK0,X0))) ) | ~spl8_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f168,f149])).
% 0.21/0.48  fof(f149,plain,(
% 0.21/0.48    l1_waybel_0(sK2,sK0) | ~spl8_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f44,f75])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    l1_waybel_0(sK2,sK0) | ~v4_pre_topc(sK1,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f168,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_waybel_0(sK0,sK2,X0) | ~l1_waybel_0(sK2,sK0) | ~r2_hidden(X1,k10_yellow_6(sK0,sK2)) | ~v7_waybel_0(sK2) | ~v4_orders_2(sK2) | v2_struct_0(sK2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X1,k2_pre_topc(sK0,X0))) ) | ~spl8_1),
% 0.21/0.48    inference(resolution,[],[f167,f148])).
% 0.21/0.48  fof(f148,plain,(
% 0.21/0.48    v3_yellow_6(sK2,sK0) | ~spl8_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f43,f75])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    v3_yellow_6(sK2,sK0) | ~v4_pre_topc(sK1,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f167,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v3_yellow_6(X1,sK0) | ~r1_waybel_0(sK0,X1,X2) | ~l1_waybel_0(X1,sK0) | ~r2_hidden(X0,k10_yellow_6(sK0,X1)) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X0,k2_pre_topc(sK0,X2))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f166,f35])).
% 0.21/0.48  fof(f166,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X0,k10_yellow_6(sK0,X1)) | ~r1_waybel_0(sK0,X1,X2) | ~l1_waybel_0(X1,sK0) | ~v3_yellow_6(X1,sK0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X0,k2_pre_topc(sK0,X2)) | v2_struct_0(sK0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f165,f36])).
% 0.21/0.48  fof(f165,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X0,k10_yellow_6(sK0,X1)) | ~r1_waybel_0(sK0,X1,X2) | ~l1_waybel_0(X1,sK0) | ~v3_yellow_6(X1,sK0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X0,k2_pre_topc(sK0,X2)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.48    inference(resolution,[],[f65,f37])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X0) | ~r2_hidden(X2,k10_yellow_6(X0,X3)) | ~r1_waybel_0(X0,X3,X1) | ~l1_waybel_0(X3,X0) | ~v3_yellow_6(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(X2,k2_pre_topc(X0,X1)) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f30])).
% 0.21/0.48  fof(f249,plain,(
% 0.21/0.48    ~r2_hidden(sK3,k2_pre_topc(sK0,sK1)) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl8_8),
% 0.21/0.48    inference(resolution,[],[f211,f66])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v2_struct_0(sK7(X0,X1,X2)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f34])).
% 0.21/0.48  % (22714)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ! [X3] : (~r3_waybel_9(X0,X3,X2) | ~r1_waybel_0(X0,X3,X1) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3))) & ((r3_waybel_9(X0,sK7(X0,X1,X2),X2) & r1_waybel_0(X0,sK7(X0,X1,X2),X1) & l1_waybel_0(sK7(X0,X1,X2),X0) & v7_waybel_0(sK7(X0,X1,X2)) & v4_orders_2(sK7(X0,X1,X2)) & ~v2_struct_0(sK7(X0,X1,X2))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f32,f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ! [X2,X1,X0] : (? [X4] : (r3_waybel_9(X0,X4,X2) & r1_waybel_0(X0,X4,X1) & l1_waybel_0(X4,X0) & v7_waybel_0(X4) & v4_orders_2(X4) & ~v2_struct_0(X4)) => (r3_waybel_9(X0,sK7(X0,X1,X2),X2) & r1_waybel_0(X0,sK7(X0,X1,X2),X1) & l1_waybel_0(sK7(X0,X1,X2),X0) & v7_waybel_0(sK7(X0,X1,X2)) & v4_orders_2(sK7(X0,X1,X2)) & ~v2_struct_0(sK7(X0,X1,X2))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ! [X3] : (~r3_waybel_9(X0,X3,X2) | ~r1_waybel_0(X0,X3,X1) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3))) & (? [X4] : (r3_waybel_9(X0,X4,X2) & r1_waybel_0(X0,X4,X1) & l1_waybel_0(X4,X0) & v7_waybel_0(X4) & v4_orders_2(X4) & ~v2_struct_0(X4)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(rectify,[],[f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ! [X3] : (~r3_waybel_9(X0,X3,X2) | ~r1_waybel_0(X0,X3,X1) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3))) & (? [X3] : (r3_waybel_9(X0,X3,X2) & r1_waybel_0(X0,X3,X1) & l1_waybel_0(X3,X0) & v7_waybel_0(X3) & v4_orders_2(X3) & ~v2_struct_0(X3)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ? [X3] : (r3_waybel_9(X0,X3,X2) & r1_waybel_0(X0,X3,X1) & l1_waybel_0(X3,X0) & v7_waybel_0(X3) & v4_orders_2(X3) & ~v2_struct_0(X3))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ? [X3] : (r3_waybel_9(X0,X3,X2) & r1_waybel_0(X0,X3,X1) & l1_waybel_0(X3,X0) & v7_waybel_0(X3) & v4_orders_2(X3) & ~v2_struct_0(X3))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ? [X3] : (r3_waybel_9(X0,X3,X2) & r1_waybel_0(X0,X3,X1) & l1_waybel_0(X3,X0) & v7_waybel_0(X3) & v4_orders_2(X3) & ~v2_struct_0(X3))))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_yellow19)).
% 0.21/0.48  fof(f211,plain,(
% 0.21/0.48    v2_struct_0(sK7(sK0,sK1,sK3)) | ~spl8_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f209])).
% 0.21/0.48  fof(f209,plain,(
% 0.21/0.48    spl8_8 <=> v2_struct_0(sK7(sK0,sK1,sK3))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.21/0.48  fof(f248,plain,(
% 0.21/0.48    ~spl8_1 | spl8_2 | spl8_11),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f247])).
% 0.21/0.48  fof(f247,plain,(
% 0.21/0.48    $false | (~spl8_1 | spl8_2 | spl8_11)),
% 0.21/0.48    inference(subsumption_resolution,[],[f246,f35])).
% 0.21/0.48  fof(f246,plain,(
% 0.21/0.48    v2_struct_0(sK0) | (~spl8_1 | spl8_2 | spl8_11)),
% 0.21/0.48    inference(subsumption_resolution,[],[f245,f36])).
% 0.21/0.48  fof(f245,plain,(
% 0.21/0.48    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_1 | spl8_2 | spl8_11)),
% 0.21/0.48    inference(subsumption_resolution,[],[f244,f37])).
% 0.21/0.48  fof(f244,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_1 | spl8_2 | spl8_11)),
% 0.21/0.48    inference(subsumption_resolution,[],[f243,f38])).
% 0.21/0.48  fof(f243,plain,(
% 0.21/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_1 | spl8_2 | spl8_11)),
% 0.21/0.48    inference(subsumption_resolution,[],[f242,f157])).
% 0.21/0.48  fof(f242,plain,(
% 0.21/0.48    ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_1 | spl8_2 | spl8_11)),
% 0.21/0.48    inference(subsumption_resolution,[],[f241,f176])).
% 0.21/0.48  fof(f241,plain,(
% 0.21/0.48    ~r2_hidden(sK3,k2_pre_topc(sK0,sK1)) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl8_11),
% 0.21/0.48    inference(resolution,[],[f223,f69])).
% 0.21/0.48  % (22703)lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3 on theBenchmark
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (l1_waybel_0(sK7(X0,X1,X2),X0) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f34])).
% 0.21/0.48  fof(f223,plain,(
% 0.21/0.48    ~l1_waybel_0(sK7(sK0,sK1,sK3),sK0) | spl8_11),
% 0.21/0.48    inference(avatar_component_clause,[],[f221])).
% 0.21/0.48  fof(f221,plain,(
% 0.21/0.48    spl8_11 <=> l1_waybel_0(sK7(sK0,sK1,sK3),sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 0.21/0.48  fof(f240,plain,(
% 0.21/0.48    ~spl8_1 | spl8_2 | spl8_10),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f239])).
% 0.21/0.48  fof(f239,plain,(
% 0.21/0.48    $false | (~spl8_1 | spl8_2 | spl8_10)),
% 0.21/0.48    inference(subsumption_resolution,[],[f238,f35])).
% 0.21/0.48  fof(f238,plain,(
% 0.21/0.48    v2_struct_0(sK0) | (~spl8_1 | spl8_2 | spl8_10)),
% 0.21/0.48    inference(subsumption_resolution,[],[f237,f36])).
% 0.21/0.48  fof(f237,plain,(
% 0.21/0.48    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_1 | spl8_2 | spl8_10)),
% 0.21/0.48    inference(subsumption_resolution,[],[f236,f37])).
% 0.21/0.48  fof(f236,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_1 | spl8_2 | spl8_10)),
% 0.21/0.48    inference(subsumption_resolution,[],[f235,f38])).
% 0.21/0.48  fof(f235,plain,(
% 0.21/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_1 | spl8_2 | spl8_10)),
% 0.21/0.48    inference(subsumption_resolution,[],[f234,f157])).
% 0.21/0.48  fof(f234,plain,(
% 0.21/0.48    ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_1 | spl8_2 | spl8_10)),
% 0.21/0.48    inference(subsumption_resolution,[],[f233,f176])).
% 0.21/0.48  fof(f233,plain,(
% 0.21/0.48    ~r2_hidden(sK3,k2_pre_topc(sK0,sK1)) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl8_10),
% 0.21/0.48    inference(resolution,[],[f219,f68])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (v7_waybel_0(sK7(X0,X1,X2)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f34])).
% 0.21/0.48  fof(f219,plain,(
% 0.21/0.48    ~v7_waybel_0(sK7(sK0,sK1,sK3)) | spl8_10),
% 0.21/0.48    inference(avatar_component_clause,[],[f217])).
% 0.21/0.48  fof(f217,plain,(
% 0.21/0.48    spl8_10 <=> v7_waybel_0(sK7(sK0,sK1,sK3))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.21/0.48  fof(f232,plain,(
% 0.21/0.48    ~spl8_1 | spl8_2 | spl8_9),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f231])).
% 0.21/0.48  fof(f231,plain,(
% 0.21/0.48    $false | (~spl8_1 | spl8_2 | spl8_9)),
% 0.21/0.48    inference(subsumption_resolution,[],[f230,f35])).
% 0.21/0.48  fof(f230,plain,(
% 0.21/0.48    v2_struct_0(sK0) | (~spl8_1 | spl8_2 | spl8_9)),
% 0.21/0.48    inference(subsumption_resolution,[],[f229,f36])).
% 0.21/0.48  fof(f229,plain,(
% 0.21/0.48    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_1 | spl8_2 | spl8_9)),
% 0.21/0.48    inference(subsumption_resolution,[],[f228,f37])).
% 0.21/0.48  fof(f228,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_1 | spl8_2 | spl8_9)),
% 0.21/0.48    inference(subsumption_resolution,[],[f227,f38])).
% 0.21/0.48  fof(f227,plain,(
% 0.21/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_1 | spl8_2 | spl8_9)),
% 0.21/0.48    inference(subsumption_resolution,[],[f226,f157])).
% 0.21/0.48  fof(f226,plain,(
% 0.21/0.48    ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_1 | spl8_2 | spl8_9)),
% 0.21/0.48    inference(subsumption_resolution,[],[f225,f176])).
% 0.21/0.48  fof(f225,plain,(
% 0.21/0.48    ~r2_hidden(sK3,k2_pre_topc(sK0,sK1)) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl8_9),
% 0.21/0.48    inference(resolution,[],[f215,f67])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (v4_orders_2(sK7(X0,X1,X2)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f34])).
% 0.21/0.48  fof(f215,plain,(
% 0.21/0.48    ~v4_orders_2(sK7(sK0,sK1,sK3)) | spl8_9),
% 0.21/0.48    inference(avatar_component_clause,[],[f213])).
% 0.21/0.48  fof(f213,plain,(
% 0.21/0.48    spl8_9 <=> v4_orders_2(sK7(sK0,sK1,sK3))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.21/0.48  fof(f224,plain,(
% 0.21/0.48    spl8_8 | ~spl8_9 | ~spl8_10 | ~spl8_11 | ~spl8_1 | spl8_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f207,f78,f74,f221,f217,f213,f209])).
% 0.21/0.48  fof(f207,plain,(
% 0.21/0.48    ~l1_waybel_0(sK7(sK0,sK1,sK3),sK0) | ~v7_waybel_0(sK7(sK0,sK1,sK3)) | ~v4_orders_2(sK7(sK0,sK1,sK3)) | v2_struct_0(sK7(sK0,sK1,sK3)) | (~spl8_1 | spl8_2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f204,f190])).
% 0.21/0.48  fof(f190,plain,(
% 0.21/0.48    r1_waybel_0(sK0,sK7(sK0,sK1,sK3),sK1) | (~spl8_1 | spl8_2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f189,f35])).
% 0.21/0.48  fof(f189,plain,(
% 0.21/0.48    r1_waybel_0(sK0,sK7(sK0,sK1,sK3),sK1) | v2_struct_0(sK0) | (~spl8_1 | spl8_2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f188,f36])).
% 0.21/0.48  fof(f188,plain,(
% 0.21/0.48    r1_waybel_0(sK0,sK7(sK0,sK1,sK3),sK1) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_1 | spl8_2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f187,f37])).
% 0.21/0.48  fof(f187,plain,(
% 0.21/0.48    r1_waybel_0(sK0,sK7(sK0,sK1,sK3),sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_1 | spl8_2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f186,f38])).
% 0.21/0.48  fof(f186,plain,(
% 0.21/0.48    r1_waybel_0(sK0,sK7(sK0,sK1,sK3),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_1 | spl8_2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f178,f157])).
% 0.21/0.48  fof(f178,plain,(
% 0.21/0.48    r1_waybel_0(sK0,sK7(sK0,sK1,sK3),sK1) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_1 | spl8_2)),
% 0.21/0.48    inference(resolution,[],[f176,f70])).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X2,k2_pre_topc(X0,X1)) | r1_waybel_0(X0,sK7(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f34])).
% 0.21/0.48  fof(f204,plain,(
% 0.21/0.48    ~r1_waybel_0(sK0,sK7(sK0,sK1,sK3),sK1) | ~l1_waybel_0(sK7(sK0,sK1,sK3),sK0) | ~v7_waybel_0(sK7(sK0,sK1,sK3)) | ~v4_orders_2(sK7(sK0,sK1,sK3)) | v2_struct_0(sK7(sK0,sK1,sK3)) | (~spl8_1 | spl8_2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f203,f150])).
% 0.21/0.48  fof(f150,plain,(
% 0.21/0.48    ~r2_hidden(sK3,sK1) | ~spl8_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f48,f75])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    ~r2_hidden(sK3,sK1) | ~v4_pre_topc(sK1,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f203,plain,(
% 0.21/0.48    ~r1_waybel_0(sK0,sK7(sK0,sK1,sK3),sK1) | ~l1_waybel_0(sK7(sK0,sK1,sK3),sK0) | ~v7_waybel_0(sK7(sK0,sK1,sK3)) | ~v4_orders_2(sK7(sK0,sK1,sK3)) | v2_struct_0(sK7(sK0,sK1,sK3)) | r2_hidden(sK3,sK1) | (~spl8_1 | spl8_2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f202,f157])).
% 0.21/0.48  fof(f202,plain,(
% 0.21/0.48    ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~r1_waybel_0(sK0,sK7(sK0,sK1,sK3),sK1) | ~l1_waybel_0(sK7(sK0,sK1,sK3),sK0) | ~v7_waybel_0(sK7(sK0,sK1,sK3)) | ~v4_orders_2(sK7(sK0,sK1,sK3)) | v2_struct_0(sK7(sK0,sK1,sK3)) | r2_hidden(sK3,sK1) | (~spl8_1 | spl8_2)),
% 0.21/0.48    inference(resolution,[],[f185,f145])).
% 0.21/0.48  fof(f145,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r3_waybel_9(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_waybel_0(sK0,X0,sK1) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | r2_hidden(X1,sK1)) ) | ~spl8_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f144,f35])).
% 0.21/0.48  fof(f144,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r3_waybel_9(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_waybel_0(sK0,X0,sK1) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | r2_hidden(X1,sK1) | v2_struct_0(sK0)) ) | ~spl8_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f143,f36])).
% 0.21/0.48  fof(f143,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r3_waybel_9(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_waybel_0(sK0,X0,sK1) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | r2_hidden(X1,sK1) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl8_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f142,f37])).
% 0.21/0.48  fof(f142,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r3_waybel_9(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_waybel_0(sK0,X0,sK1) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | r2_hidden(X1,sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl8_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f141,f38])).
% 0.21/0.48  fof(f141,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r3_waybel_9(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_waybel_0(sK0,X0,sK1) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | r2_hidden(X1,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl8_1),
% 0.21/0.48    inference(resolution,[],[f75,f49])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ( ! [X4,X0,X5,X1] : (~v4_pre_topc(X1,X0) | ~r3_waybel_9(X0,X4,X5) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~r1_waybel_0(X0,X4,X1) | ~l1_waybel_0(X4,X0) | ~v7_waybel_0(X4) | ~v4_orders_2(X4) | v2_struct_0(X4) | r2_hidden(X5,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f26])).
% 0.21/0.48  fof(f185,plain,(
% 0.21/0.48    r3_waybel_9(sK0,sK7(sK0,sK1,sK3),sK3) | (~spl8_1 | spl8_2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f184,f35])).
% 0.21/0.48  fof(f184,plain,(
% 0.21/0.48    r3_waybel_9(sK0,sK7(sK0,sK1,sK3),sK3) | v2_struct_0(sK0) | (~spl8_1 | spl8_2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f183,f36])).
% 0.21/0.48  fof(f183,plain,(
% 0.21/0.48    r3_waybel_9(sK0,sK7(sK0,sK1,sK3),sK3) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_1 | spl8_2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f182,f37])).
% 0.21/0.48  fof(f182,plain,(
% 0.21/0.48    r3_waybel_9(sK0,sK7(sK0,sK1,sK3),sK3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_1 | spl8_2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f181,f38])).
% 0.21/0.48  fof(f181,plain,(
% 0.21/0.48    r3_waybel_9(sK0,sK7(sK0,sK1,sK3),sK3) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_1 | spl8_2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f177,f157])).
% 0.21/0.48  fof(f177,plain,(
% 0.21/0.48    r3_waybel_9(sK0,sK7(sK0,sK1,sK3),sK3) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_1 | spl8_2)),
% 0.21/0.48    inference(resolution,[],[f176,f71])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X2,k2_pre_topc(X0,X1)) | r3_waybel_9(X0,sK7(X0,X1,X2),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f34])).
% 0.21/0.48  fof(f133,plain,(
% 0.21/0.48    spl8_1 | spl8_7),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f132])).
% 0.21/0.48  fof(f132,plain,(
% 0.21/0.48    $false | (spl8_1 | spl8_7)),
% 0.21/0.48    inference(subsumption_resolution,[],[f131,f35])).
% 0.21/0.48  fof(f131,plain,(
% 0.21/0.48    v2_struct_0(sK0) | (spl8_1 | spl8_7)),
% 0.21/0.48    inference(subsumption_resolution,[],[f130,f36])).
% 0.21/0.48  fof(f130,plain,(
% 0.21/0.48    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl8_1 | spl8_7)),
% 0.21/0.48    inference(subsumption_resolution,[],[f129,f37])).
% 0.21/0.48  fof(f129,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl8_1 | spl8_7)),
% 0.21/0.48    inference(subsumption_resolution,[],[f128,f38])).
% 0.21/0.48  fof(f128,plain,(
% 0.21/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl8_1 | spl8_7)),
% 0.21/0.48    inference(subsumption_resolution,[],[f127,f76])).
% 0.21/0.48  fof(f127,plain,(
% 0.21/0.48    v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl8_7),
% 0.21/0.48    inference(resolution,[],[f111,f53])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    ( ! [X0,X1] : (l1_waybel_0(sK4(X0,X1),X0) | v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f26])).
% 0.21/0.48  fof(f111,plain,(
% 0.21/0.48    ~l1_waybel_0(sK4(sK0,sK1),sK0) | spl8_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f109])).
% 0.21/0.48  fof(f109,plain,(
% 0.21/0.48    spl8_7 <=> l1_waybel_0(sK4(sK0,sK1),sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.21/0.48  fof(f126,plain,(
% 0.21/0.48    spl8_1 | spl8_6),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f125])).
% 0.21/0.48  fof(f125,plain,(
% 0.21/0.48    $false | (spl8_1 | spl8_6)),
% 0.21/0.48    inference(subsumption_resolution,[],[f124,f35])).
% 0.21/0.48  fof(f124,plain,(
% 0.21/0.48    v2_struct_0(sK0) | (spl8_1 | spl8_6)),
% 0.21/0.48    inference(subsumption_resolution,[],[f123,f36])).
% 0.21/0.48  fof(f123,plain,(
% 0.21/0.48    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl8_1 | spl8_6)),
% 0.21/0.48    inference(subsumption_resolution,[],[f122,f37])).
% 0.21/0.48  fof(f122,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl8_1 | spl8_6)),
% 0.21/0.48    inference(subsumption_resolution,[],[f121,f38])).
% 0.21/0.48  fof(f121,plain,(
% 0.21/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl8_1 | spl8_6)),
% 0.21/0.48    inference(subsumption_resolution,[],[f120,f76])).
% 0.21/0.48  fof(f120,plain,(
% 0.21/0.48    v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl8_6),
% 0.21/0.48    inference(resolution,[],[f107,f52])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v7_waybel_0(sK4(X0,X1)) | v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f26])).
% 0.21/0.48  fof(f107,plain,(
% 0.21/0.48    ~v7_waybel_0(sK4(sK0,sK1)) | spl8_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f105])).
% 0.21/0.48  fof(f105,plain,(
% 0.21/0.48    spl8_6 <=> v7_waybel_0(sK4(sK0,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.21/0.48  fof(f119,plain,(
% 0.21/0.48    spl8_1 | spl8_5),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f118])).
% 0.21/0.48  fof(f118,plain,(
% 0.21/0.48    $false | (spl8_1 | spl8_5)),
% 0.21/0.48    inference(subsumption_resolution,[],[f117,f35])).
% 0.21/0.48  fof(f117,plain,(
% 0.21/0.48    v2_struct_0(sK0) | (spl8_1 | spl8_5)),
% 0.21/0.48    inference(subsumption_resolution,[],[f116,f36])).
% 0.21/0.48  fof(f116,plain,(
% 0.21/0.48    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl8_1 | spl8_5)),
% 0.21/0.48    inference(subsumption_resolution,[],[f115,f37])).
% 0.21/0.48  fof(f115,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl8_1 | spl8_5)),
% 0.21/0.48    inference(subsumption_resolution,[],[f114,f38])).
% 0.21/0.48  fof(f114,plain,(
% 0.21/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl8_1 | spl8_5)),
% 0.21/0.48    inference(subsumption_resolution,[],[f113,f76])).
% 0.21/0.48  fof(f113,plain,(
% 0.21/0.48    v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl8_5),
% 0.21/0.48    inference(resolution,[],[f103,f51])).
% 0.21/0.48  % (22714)Refutation not found, incomplete strategy% (22714)------------------------------
% 0.21/0.48  % (22714)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (22714)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (22714)Memory used [KB]: 5373
% 0.21/0.48  % (22714)Time elapsed: 0.083 s
% 0.21/0.48  % (22714)------------------------------
% 0.21/0.48  % (22714)------------------------------
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v4_orders_2(sK4(X0,X1)) | v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f26])).
% 0.21/0.48  fof(f103,plain,(
% 0.21/0.48    ~v4_orders_2(sK4(sK0,sK1)) | spl8_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f101])).
% 0.21/0.48  fof(f101,plain,(
% 0.21/0.48    spl8_5 <=> v4_orders_2(sK4(sK0,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.21/0.48  fof(f112,plain,(
% 0.21/0.48    spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_7 | spl8_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f92,f74,f109,f105,f101,f97,f94])).
% 0.21/0.48  fof(f92,plain,(
% 0.21/0.48    ( ! [X0] : (~l1_waybel_0(sK4(sK0,sK1),sK0) | ~v7_waybel_0(sK4(sK0,sK1)) | ~v4_orders_2(sK4(sK0,sK1)) | v2_struct_0(sK4(sK0,sK1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK4(sK0,sK1),X0) | r2_hidden(X0,k2_pre_topc(sK0,sK1))) ) | spl8_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f91,f35])).
% 0.21/0.48  % (22709)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
% 0.21/0.48  fof(f91,plain,(
% 0.21/0.48    ( ! [X0] : (~l1_waybel_0(sK4(sK0,sK1),sK0) | ~v7_waybel_0(sK4(sK0,sK1)) | ~v4_orders_2(sK4(sK0,sK1)) | v2_struct_0(sK4(sK0,sK1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK4(sK0,sK1),X0) | r2_hidden(X0,k2_pre_topc(sK0,sK1)) | v2_struct_0(sK0)) ) | spl8_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f90,f36])).
% 0.21/0.48  fof(f90,plain,(
% 0.21/0.48    ( ! [X0] : (~l1_waybel_0(sK4(sK0,sK1),sK0) | ~v7_waybel_0(sK4(sK0,sK1)) | ~v4_orders_2(sK4(sK0,sK1)) | v2_struct_0(sK4(sK0,sK1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK4(sK0,sK1),X0) | r2_hidden(X0,k2_pre_topc(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | spl8_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f89,f37])).
% 0.21/0.48  fof(f89,plain,(
% 0.21/0.48    ( ! [X0] : (~l1_waybel_0(sK4(sK0,sK1),sK0) | ~v7_waybel_0(sK4(sK0,sK1)) | ~v4_orders_2(sK4(sK0,sK1)) | v2_struct_0(sK4(sK0,sK1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK4(sK0,sK1),X0) | r2_hidden(X0,k2_pre_topc(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | spl8_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f88,f38])).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    ( ! [X0] : (~l1_waybel_0(sK4(sK0,sK1),sK0) | ~v7_waybel_0(sK4(sK0,sK1)) | ~v4_orders_2(sK4(sK0,sK1)) | v2_struct_0(sK4(sK0,sK1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK4(sK0,sK1),X0) | r2_hidden(X0,k2_pre_topc(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | spl8_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f87,f76])).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    ( ! [X0] : (~l1_waybel_0(sK4(sK0,sK1),sK0) | ~v7_waybel_0(sK4(sK0,sK1)) | ~v4_orders_2(sK4(sK0,sK1)) | v2_struct_0(sK4(sK0,sK1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK4(sK0,sK1),X0) | r2_hidden(X0,k2_pre_topc(sK0,sK1)) | v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.48    inference(resolution,[],[f86,f54])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_waybel_0(X0,sK4(X0,X1),X1) | v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f26])).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_waybel_0(sK0,X0,sK1) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X0,X1) | r2_hidden(X1,k2_pre_topc(sK0,sK1))) )),
% 0.21/0.48    inference(resolution,[],[f85,f38])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_waybel_0(sK0,X0,X2) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X0,X1) | r2_hidden(X1,k2_pre_topc(sK0,X2))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f84,f35])).
% 0.21/0.48  fof(f84,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r3_waybel_9(sK0,X0,X1) | ~r1_waybel_0(sK0,X0,X2) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X1,k2_pre_topc(sK0,X2)) | v2_struct_0(sK0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f83,f36])).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r3_waybel_9(sK0,X0,X1) | ~r1_waybel_0(sK0,X0,X2) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X1,k2_pre_topc(sK0,X2)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.48    inference(resolution,[],[f72,f37])).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X0) | ~r3_waybel_9(X0,X3,X2) | ~r1_waybel_0(X0,X3,X1) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(X2,k2_pre_topc(X0,X1)) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f34])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    ~spl8_1 | ~spl8_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f40,f78,f74])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ~v2_struct_0(sK2) | ~v4_pre_topc(sK1,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (22700)------------------------------
% 0.21/0.48  % (22700)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (22700)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (22700)Memory used [KB]: 5500
% 0.21/0.48  % (22700)Time elapsed: 0.071 s
% 0.21/0.48  % (22700)------------------------------
% 0.21/0.48  % (22700)------------------------------
% 0.21/0.48  % (22699)Success in time 0.13 s
%------------------------------------------------------------------------------
