%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:38 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :  158 (16414 expanded)
%              Number of leaves         :   29 (5451 expanded)
%              Depth                    :   23
%              Number of atoms          : 1009 (195778 expanded)
%              Number of equality atoms :   14 (  58 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f320,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f105,f110,f115,f120,f125,f129,f133,f271,f319])).

fof(f319,plain,
    ( ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_6 ),
    inference(avatar_contradiction_clause,[],[f318])).

fof(f318,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_6 ),
    inference(subsumption_resolution,[],[f312,f68])).

fof(f68,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f312,plain,
    ( ~ r1_tarski(k1_xboole_0,sK4(sK0,sK1))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_6 ),
    inference(unit_resulting_resolution,[],[f310,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f310,plain,
    ( r2_hidden(sK4(sK0,sK1),k1_xboole_0)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_6 ),
    inference(subsumption_resolution,[],[f309,f58])).

fof(f58,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,
    ( ( ( ! [X2] :
            ( ~ v3_yellow_6(X2,sK0)
            | ~ m2_yellow_6(X2,sK0,sK1) )
        & l1_waybel_0(sK1,sK0)
        & v7_waybel_0(sK1)
        & v4_orders_2(sK1)
        & ~ v2_struct_0(sK1) )
      | ~ v1_compts_1(sK0) )
    & ( ! [X3] :
          ( ( v3_yellow_6(sK2(X3),sK0)
            & m2_yellow_6(sK2(X3),sK0,X3) )
          | ~ l1_waybel_0(X3,sK0)
          | ~ v7_waybel_0(X3)
          | ~ v4_orders_2(X3)
          | v2_struct_0(X3) )
      | v1_compts_1(sK0) )
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f39,f42,f41,f40])).

fof(f40,plain,
    ( ? [X0] :
        ( ( ? [X1] :
              ( ! [X2] :
                  ( ~ v3_yellow_6(X2,X0)
                  | ~ m2_yellow_6(X2,X0,X1) )
              & l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
          | ~ v1_compts_1(X0) )
        & ( ! [X3] :
              ( ? [X4] :
                  ( v3_yellow_6(X4,X0)
                  & m2_yellow_6(X4,X0,X3) )
              | ~ l1_waybel_0(X3,X0)
              | ~ v7_waybel_0(X3)
              | ~ v4_orders_2(X3)
              | v2_struct_0(X3) )
          | v1_compts_1(X0) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ( ? [X1] :
            ( ! [X2] :
                ( ~ v3_yellow_6(X2,sK0)
                | ~ m2_yellow_6(X2,sK0,X1) )
            & l1_waybel_0(X1,sK0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        | ~ v1_compts_1(sK0) )
      & ( ! [X3] :
            ( ? [X4] :
                ( v3_yellow_6(X4,sK0)
                & m2_yellow_6(X4,sK0,X3) )
            | ~ l1_waybel_0(X3,sK0)
            | ~ v7_waybel_0(X3)
            | ~ v4_orders_2(X3)
            | v2_struct_0(X3) )
        | v1_compts_1(sK0) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X1] :
        ( ! [X2] :
            ( ~ v3_yellow_6(X2,sK0)
            | ~ m2_yellow_6(X2,sK0,X1) )
        & l1_waybel_0(X1,sK0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1) )
   => ( ! [X2] :
          ( ~ v3_yellow_6(X2,sK0)
          | ~ m2_yellow_6(X2,sK0,sK1) )
      & l1_waybel_0(sK1,sK0)
      & v7_waybel_0(sK1)
      & v4_orders_2(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

% (31901)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
fof(f42,plain,(
    ! [X3] :
      ( ? [X4] :
          ( v3_yellow_6(X4,sK0)
          & m2_yellow_6(X4,sK0,X3) )
     => ( v3_yellow_6(sK2(X3),sK0)
        & m2_yellow_6(sK2(X3),sK0,X3) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ! [X2] :
                ( ~ v3_yellow_6(X2,X0)
                | ~ m2_yellow_6(X2,X0,X1) )
            & l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        | ~ v1_compts_1(X0) )
      & ( ! [X3] :
            ( ? [X4] :
                ( v3_yellow_6(X4,X0)
                & m2_yellow_6(X4,X0,X3) )
            | ~ l1_waybel_0(X3,X0)
            | ~ v7_waybel_0(X3)
            | ~ v4_orders_2(X3)
            | v2_struct_0(X3) )
        | v1_compts_1(X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ! [X2] :
                ( ~ v3_yellow_6(X2,X0)
                | ~ m2_yellow_6(X2,X0,X1) )
            & l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        | ~ v1_compts_1(X0) )
      & ( ! [X1] :
            ( ? [X2] :
                ( v3_yellow_6(X2,X0)
                & m2_yellow_6(X2,X0,X1) )
            | ~ l1_waybel_0(X1,X0)
            | ~ v7_waybel_0(X1)
            | ~ v4_orders_2(X1)
            | v2_struct_0(X1) )
        | v1_compts_1(X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ! [X2] :
                ( ~ v3_yellow_6(X2,X0)
                | ~ m2_yellow_6(X2,X0,X1) )
            & l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        | ~ v1_compts_1(X0) )
      & ( ! [X1] :
            ( ? [X2] :
                ( v3_yellow_6(X2,X0)
                & m2_yellow_6(X2,X0,X1) )
            | ~ l1_waybel_0(X1,X0)
            | ~ v7_waybel_0(X1)
            | ~ v4_orders_2(X1)
            | v2_struct_0(X1) )
        | v1_compts_1(X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ( v1_compts_1(X0)
      <~> ! [X1] :
            ( ? [X2] :
                ( v3_yellow_6(X2,X0)
                & m2_yellow_6(X2,X0,X1) )
            | ~ l1_waybel_0(X1,X0)
            | ~ v7_waybel_0(X1)
            | ~ v4_orders_2(X1)
            | v2_struct_0(X1) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ( v1_compts_1(X0)
      <~> ! [X1] :
            ( ? [X2] :
                ( v3_yellow_6(X2,X0)
                & m2_yellow_6(X2,X0,X1) )
            | ~ l1_waybel_0(X1,X0)
            | ~ v7_waybel_0(X1)
            | ~ v4_orders_2(X1)
            | v2_struct_0(X1) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ( v1_compts_1(X0)
        <=> ! [X1] :
              ( ( l1_waybel_0(X1,X0)
                & v7_waybel_0(X1)
                & v4_orders_2(X1)
                & ~ v2_struct_0(X1) )
             => ? [X2] :
                  ( v3_yellow_6(X2,X0)
                  & m2_yellow_6(X2,X0,X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_compts_1(X0)
      <=> ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ? [X2] :
                ( v3_yellow_6(X2,X0)
                & m2_yellow_6(X2,X0,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_yellow19)).

fof(f309,plain,
    ( r2_hidden(sK4(sK0,sK1),k1_xboole_0)
    | v2_struct_0(sK0)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_6 ),
    inference(subsumption_resolution,[],[f308,f59])).

fof(f59,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f308,plain,
    ( r2_hidden(sK4(sK0,sK1),k1_xboole_0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_6 ),
    inference(subsumption_resolution,[],[f307,f60])).

fof(f60,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f307,plain,
    ( r2_hidden(sK4(sK0,sK1),k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_6 ),
    inference(subsumption_resolution,[],[f306,f295])).

fof(f295,plain,
    ( ~ v2_struct_0(sK5(sK0,sK1,sK4(sK0,sK1)))
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_6 ),
    inference(unit_resulting_resolution,[],[f58,f134,f124,f119,f114,f109,f285,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(X2)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( l1_waybel_0(X2,X0)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) )
          | ~ m2_yellow_6(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( l1_waybel_0(X2,X0)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) )
          | ~ m2_yellow_6(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m2_yellow_6(X2,X0,X1)
         => ( l1_waybel_0(X2,X0)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_yellow_6)).

fof(f285,plain,
    ( m2_yellow_6(sK5(sK0,sK1,sK4(sK0,sK1)),sK0,sK1)
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_6 ),
    inference(unit_resulting_resolution,[],[f58,f59,f60,f124,f119,f114,f109,f274,f275,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( m2_yellow_6(sK5(X0,X1,X2),X0,X1)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k10_yellow_6(X0,sK5(X0,X1,X2)))
                & m2_yellow_6(sK5(X0,X1,X2),X0,X1) )
              | ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f26,f50])).

fof(f50,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X2,k10_yellow_6(X0,X3))
          & m2_yellow_6(X3,X0,X1) )
     => ( r2_hidden(X2,k10_yellow_6(X0,sK5(X0,X1,X2)))
        & m2_yellow_6(sK5(X0,X1,X2),X0,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r2_hidden(X2,k10_yellow_6(X0,X3))
                  & m2_yellow_6(X3,X0,X1) )
              | ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r2_hidden(X2,k10_yellow_6(X0,X3))
                  & m2_yellow_6(X3,X0,X1) )
              | ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
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
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ~ ( ! [X3] :
                      ( m2_yellow_6(X3,X0,X1)
                     => ~ r2_hidden(X2,k10_yellow_6(X0,X3)) )
                  & r3_waybel_9(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_waybel_9)).

fof(f275,plain,
    ( r3_waybel_9(sK0,sK1,sK4(sK0,sK1))
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_6 ),
    inference(unit_resulting_resolution,[],[f58,f59,f60,f100,f124,f119,f114,f109,f71])).

fof(f71,plain,(
    ! [X0,X3] :
      ( r3_waybel_9(X0,X3,sK4(X0,X3))
      | ~ l1_waybel_0(X3,X0)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ( ( v1_compts_1(X0)
          | ( ! [X2] :
                ( ~ r3_waybel_9(X0,sK3(X0),X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & l1_waybel_0(sK3(X0),X0)
            & v7_waybel_0(sK3(X0))
            & v4_orders_2(sK3(X0))
            & ~ v2_struct_0(sK3(X0)) ) )
        & ( ! [X3] :
              ( ( r3_waybel_9(X0,X3,sK4(X0,X3))
                & m1_subset_1(sK4(X0,X3),u1_struct_0(X0)) )
              | ~ l1_waybel_0(X3,X0)
              | ~ v7_waybel_0(X3)
              | ~ v4_orders_2(X3)
              | v2_struct_0(X3) )
          | ~ v1_compts_1(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f45,f47,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
     => ( ! [X2] :
            ( ~ r3_waybel_9(X0,sK3(X0),X2)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        & l1_waybel_0(sK3(X0),X0)
        & v7_waybel_0(sK3(X0))
        & v4_orders_2(sK3(X0))
        & ~ v2_struct_0(sK3(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X3,X0] :
      ( ? [X4] :
          ( r3_waybel_9(X0,X3,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( r3_waybel_9(X0,X3,sK4(X0,X3))
        & m1_subset_1(sK4(X0,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ( ( v1_compts_1(X0)
          | ? [X1] :
              ( ! [X2] :
                  ( ~ r3_waybel_9(X0,X1,X2)
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              & l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) ) )
        & ( ! [X3] :
              ( ? [X4] :
                  ( r3_waybel_9(X0,X3,X4)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ l1_waybel_0(X3,X0)
              | ~ v7_waybel_0(X3)
              | ~ v4_orders_2(X3)
              | v2_struct_0(X3) )
          | ~ v1_compts_1(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ( ( v1_compts_1(X0)
          | ? [X1] :
              ( ! [X2] :
                  ( ~ r3_waybel_9(X0,X1,X2)
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              & l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) ) )
        & ( ! [X1] :
              ( ? [X2] :
                  ( r3_waybel_9(X0,X1,X2)
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ l1_waybel_0(X1,X0)
              | ~ v7_waybel_0(X1)
              | ~ v4_orders_2(X1)
              | v2_struct_0(X1) )
          | ~ v1_compts_1(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_compts_1(X0)
      <=> ! [X1] :
            ( ? [X2] :
                ( r3_waybel_9(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ l1_waybel_0(X1,X0)
            | ~ v7_waybel_0(X1)
            | ~ v4_orders_2(X1)
            | v2_struct_0(X1) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v1_compts_1(X0)
      <=> ! [X1] :
            ( ? [X2] :
                ( r3_waybel_9(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ l1_waybel_0(X1,X0)
            | ~ v7_waybel_0(X1)
            | ~ v4_orders_2(X1)
            | v2_struct_0(X1) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_compts_1(X0)
      <=> ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ? [X2] :
                ( r3_waybel_9(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_yellow19)).

fof(f100,plain,
    ( v1_compts_1(sK0)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl7_1
  <=> v1_compts_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f274,plain,
    ( m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_6 ),
    inference(unit_resulting_resolution,[],[f58,f59,f60,f100,f124,f119,f114,f109,f70])).

fof(f70,plain,(
    ! [X0,X3] :
      ( m1_subset_1(sK4(X0,X3),u1_struct_0(X0))
      | ~ l1_waybel_0(X3,X0)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f109,plain,
    ( l1_waybel_0(sK1,sK0)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl7_3
  <=> l1_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f114,plain,
    ( v7_waybel_0(sK1)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl7_4
  <=> v7_waybel_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f119,plain,
    ( v4_orders_2(sK1)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl7_5
  <=> v4_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f124,plain,
    ( ~ v2_struct_0(sK1)
    | spl7_6 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl7_6
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f134,plain,(
    l1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f60,f69])).

fof(f69,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f306,plain,
    ( r2_hidden(sK4(sK0,sK1),k1_xboole_0)
    | v2_struct_0(sK5(sK0,sK1,sK4(sK0,sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_6 ),
    inference(subsumption_resolution,[],[f305,f296])).

fof(f296,plain,
    ( v4_orders_2(sK5(sK0,sK1,sK4(sK0,sK1)))
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_6 ),
    inference(unit_resulting_resolution,[],[f58,f134,f124,f119,f114,f109,f285,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( v4_orders_2(X2)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f305,plain,
    ( r2_hidden(sK4(sK0,sK1),k1_xboole_0)
    | ~ v4_orders_2(sK5(sK0,sK1,sK4(sK0,sK1)))
    | v2_struct_0(sK5(sK0,sK1,sK4(sK0,sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_6 ),
    inference(subsumption_resolution,[],[f304,f297])).

fof(f297,plain,
    ( v7_waybel_0(sK5(sK0,sK1,sK4(sK0,sK1)))
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_6 ),
    inference(unit_resulting_resolution,[],[f58,f134,f124,f119,f114,f109,f285,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( v7_waybel_0(X2)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f304,plain,
    ( r2_hidden(sK4(sK0,sK1),k1_xboole_0)
    | ~ v7_waybel_0(sK5(sK0,sK1,sK4(sK0,sK1)))
    | ~ v4_orders_2(sK5(sK0,sK1,sK4(sK0,sK1)))
    | v2_struct_0(sK5(sK0,sK1,sK4(sK0,sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_6 ),
    inference(subsumption_resolution,[],[f303,f298])).

fof(f298,plain,
    ( l1_waybel_0(sK5(sK0,sK1,sK4(sK0,sK1)),sK0)
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_6 ),
    inference(unit_resulting_resolution,[],[f58,f134,f124,f119,f114,f109,f285,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(X2,X0)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f303,plain,
    ( r2_hidden(sK4(sK0,sK1),k1_xboole_0)
    | ~ l1_waybel_0(sK5(sK0,sK1,sK4(sK0,sK1)),sK0)
    | ~ v7_waybel_0(sK5(sK0,sK1,sK4(sK0,sK1)))
    | ~ v4_orders_2(sK5(sK0,sK1,sK4(sK0,sK1)))
    | v2_struct_0(sK5(sK0,sK1,sK4(sK0,sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_6 ),
    inference(subsumption_resolution,[],[f302,f294])).

fof(f294,plain,
    ( ~ v3_yellow_6(sK5(sK0,sK1,sK4(sK0,sK1)),sK0)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_6 ),
    inference(unit_resulting_resolution,[],[f285,f104])).

fof(f104,plain,
    ( ! [X2] :
        ( ~ v3_yellow_6(X2,sK0)
        | ~ m2_yellow_6(X2,sK0,sK1) )
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl7_2
  <=> ! [X2] :
        ( ~ v3_yellow_6(X2,sK0)
        | ~ m2_yellow_6(X2,sK0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f302,plain,
    ( r2_hidden(sK4(sK0,sK1),k1_xboole_0)
    | v3_yellow_6(sK5(sK0,sK1,sK4(sK0,sK1)),sK0)
    | ~ l1_waybel_0(sK5(sK0,sK1,sK4(sK0,sK1)),sK0)
    | ~ v7_waybel_0(sK5(sK0,sK1,sK4(sK0,sK1)))
    | ~ v4_orders_2(sK5(sK0,sK1,sK4(sK0,sK1)))
    | v2_struct_0(sK5(sK0,sK1,sK4(sK0,sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_6 ),
    inference(superposition,[],[f286,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( v3_yellow_6(X1,X0)
      | k1_xboole_0 = k10_yellow_6(X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_yellow_6(X1,X0)
              | k1_xboole_0 = k10_yellow_6(X0,X1) )
            & ( k1_xboole_0 != k10_yellow_6(X0,X1)
              | ~ v3_yellow_6(X1,X0) ) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_yellow_6(X1,X0)
          <=> k1_xboole_0 != k10_yellow_6(X0,X1) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_yellow_6(X1,X0)
          <=> k1_xboole_0 != k10_yellow_6(X0,X1) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ( v3_yellow_6(X1,X0)
          <=> k1_xboole_0 != k10_yellow_6(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_yellow_6)).

fof(f286,plain,
    ( r2_hidden(sK4(sK0,sK1),k10_yellow_6(sK0,sK5(sK0,sK1,sK4(sK0,sK1))))
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_6 ),
    inference(unit_resulting_resolution,[],[f58,f59,f60,f124,f119,f114,f109,f274,f275,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k10_yellow_6(X0,sK5(X0,X1,X2)))
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f271,plain,
    ( spl7_1
    | ~ spl7_7
    | ~ spl7_8 ),
    inference(avatar_contradiction_clause,[],[f270])).

fof(f270,plain,
    ( $false
    | spl7_1
    | ~ spl7_7
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f266,f249])).

fof(f249,plain,
    ( r3_waybel_9(sK0,sK2(sK3(sK0)),sK6(k10_yellow_6(sK0,sK2(sK3(sK0))),k1_xboole_0))
    | spl7_1
    | ~ spl7_7
    | ~ spl7_8 ),
    inference(unit_resulting_resolution,[],[f58,f59,f60,f142,f143,f144,f145,f190,f217,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( r3_waybel_9(X0,X1,X2)
      | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_waybel_9(X0,X1,X2)
              | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_waybel_9(X0,X1,X2)
              | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k10_yellow_6(X0,X1))
               => r3_waybel_9(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_waybel_9)).

fof(f217,plain,
    ( m1_subset_1(sK6(k10_yellow_6(sK0,sK2(sK3(sK0))),k1_xboole_0),u1_struct_0(sK0))
    | spl7_1
    | ~ spl7_7
    | ~ spl7_8 ),
    inference(unit_resulting_resolution,[],[f167,f190,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f167,plain,
    ( m1_subset_1(k10_yellow_6(sK0,sK2(sK3(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl7_1
    | ~ spl7_8 ),
    inference(unit_resulting_resolution,[],[f58,f59,f60,f142,f143,f144,f145,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_yellow_6)).

fof(f190,plain,
    ( r2_hidden(sK6(k10_yellow_6(sK0,sK2(sK3(sK0))),k1_xboole_0),k10_yellow_6(sK0,sK2(sK3(sK0))))
    | spl7_1
    | ~ spl7_7
    | ~ spl7_8 ),
    inference(unit_resulting_resolution,[],[f175,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK6(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f55,f56])).

fof(f56,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f175,plain,
    ( ~ r1_tarski(k10_yellow_6(sK0,sK2(sK3(sK0))),k1_xboole_0)
    | spl7_1
    | ~ spl7_7
    | ~ spl7_8 ),
    inference(unit_resulting_resolution,[],[f68,f166,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f166,plain,
    ( k1_xboole_0 != k10_yellow_6(sK0,sK2(sK3(sK0)))
    | spl7_1
    | ~ spl7_7
    | ~ spl7_8 ),
    inference(unit_resulting_resolution,[],[f58,f59,f60,f142,f143,f144,f140,f145,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_yellow_6(X0,X1)
      | ~ v3_yellow_6(X1,X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f140,plain,
    ( v3_yellow_6(sK2(sK3(sK0)),sK0)
    | spl7_1
    | ~ spl7_7 ),
    inference(unit_resulting_resolution,[],[f137,f135,f136,f138,f128])).

fof(f128,plain,
    ( ! [X3] :
        ( ~ v7_waybel_0(X3)
        | v2_struct_0(X3)
        | ~ v4_orders_2(X3)
        | v3_yellow_6(sK2(X3),sK0)
        | ~ l1_waybel_0(X3,sK0) )
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl7_7
  <=> ! [X3] :
        ( v3_yellow_6(sK2(X3),sK0)
        | v2_struct_0(X3)
        | ~ v4_orders_2(X3)
        | ~ v7_waybel_0(X3)
        | ~ l1_waybel_0(X3,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f138,plain,
    ( l1_waybel_0(sK3(sK0),sK0)
    | spl7_1 ),
    inference(unit_resulting_resolution,[],[f58,f59,f60,f101,f75])).

fof(f75,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | l1_waybel_0(sK3(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f101,plain,
    ( ~ v1_compts_1(sK0)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f99])).

fof(f136,plain,
    ( v4_orders_2(sK3(sK0))
    | spl7_1 ),
    inference(unit_resulting_resolution,[],[f58,f59,f60,f101,f73])).

fof(f73,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | v4_orders_2(sK3(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f135,plain,
    ( ~ v2_struct_0(sK3(sK0))
    | spl7_1 ),
    inference(unit_resulting_resolution,[],[f58,f59,f60,f101,f72])).

fof(f72,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | ~ v2_struct_0(sK3(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f137,plain,
    ( v7_waybel_0(sK3(sK0))
    | spl7_1 ),
    inference(unit_resulting_resolution,[],[f58,f59,f60,f101,f74])).

fof(f74,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | v7_waybel_0(sK3(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f145,plain,
    ( l1_waybel_0(sK2(sK3(sK0)),sK0)
    | spl7_1
    | ~ spl7_8 ),
    inference(unit_resulting_resolution,[],[f58,f134,f135,f136,f137,f138,f139,f86])).

fof(f139,plain,
    ( m2_yellow_6(sK2(sK3(sK0)),sK0,sK3(sK0))
    | spl7_1
    | ~ spl7_8 ),
    inference(unit_resulting_resolution,[],[f137,f135,f136,f138,f132])).

fof(f132,plain,
    ( ! [X3] :
        ( ~ v7_waybel_0(X3)
        | v2_struct_0(X3)
        | ~ v4_orders_2(X3)
        | m2_yellow_6(sK2(X3),sK0,X3)
        | ~ l1_waybel_0(X3,sK0) )
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl7_8
  <=> ! [X3] :
        ( m2_yellow_6(sK2(X3),sK0,X3)
        | v2_struct_0(X3)
        | ~ v4_orders_2(X3)
        | ~ v7_waybel_0(X3)
        | ~ l1_waybel_0(X3,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f144,plain,
    ( v7_waybel_0(sK2(sK3(sK0)))
    | spl7_1
    | ~ spl7_8 ),
    inference(unit_resulting_resolution,[],[f58,f134,f135,f136,f137,f138,f139,f85])).

fof(f143,plain,
    ( v4_orders_2(sK2(sK3(sK0)))
    | spl7_1
    | ~ spl7_8 ),
    inference(unit_resulting_resolution,[],[f58,f134,f135,f136,f137,f138,f139,f84])).

fof(f142,plain,
    ( ~ v2_struct_0(sK2(sK3(sK0)))
    | spl7_1
    | ~ spl7_8 ),
    inference(unit_resulting_resolution,[],[f58,f134,f135,f136,f137,f138,f139,f83])).

fof(f266,plain,
    ( ~ r3_waybel_9(sK0,sK2(sK3(sK0)),sK6(k10_yellow_6(sK0,sK2(sK3(sK0))),k1_xboole_0))
    | spl7_1
    | ~ spl7_7
    | ~ spl7_8 ),
    inference(unit_resulting_resolution,[],[f58,f59,f60,f135,f136,f137,f138,f139,f217,f250,f82])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( r3_waybel_9(X0,X1,X3)
      | ~ r3_waybel_9(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r3_waybel_9(X0,X1,X3)
                  | ~ r3_waybel_9(X0,X2,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m2_yellow_6(X2,X0,X1) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r3_waybel_9(X0,X1,X3)
                  | ~ r3_waybel_9(X0,X2,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m2_yellow_6(X2,X0,X1) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
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
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m2_yellow_6(X2,X0,X1)
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r3_waybel_9(X0,X2,X3)
                   => r3_waybel_9(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_waybel_9)).

fof(f250,plain,
    ( ~ r3_waybel_9(sK0,sK3(sK0),sK6(k10_yellow_6(sK0,sK2(sK3(sK0))),k1_xboole_0))
    | spl7_1
    | ~ spl7_7
    | ~ spl7_8 ),
    inference(unit_resulting_resolution,[],[f58,f59,f60,f101,f217,f76])).

fof(f76,plain,(
    ! [X2,X0] :
      ( v1_compts_1(X0)
      | ~ r3_waybel_9(X0,sK3(X0),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f133,plain,
    ( spl7_1
    | spl7_8 ),
    inference(avatar_split_clause,[],[f61,f131,f99])).

fof(f61,plain,(
    ! [X3] :
      ( m2_yellow_6(sK2(X3),sK0,X3)
      | ~ l1_waybel_0(X3,sK0)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | v1_compts_1(sK0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f129,plain,
    ( spl7_1
    | spl7_7 ),
    inference(avatar_split_clause,[],[f62,f127,f99])).

fof(f62,plain,(
    ! [X3] :
      ( v3_yellow_6(sK2(X3),sK0)
      | ~ l1_waybel_0(X3,sK0)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | v1_compts_1(sK0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f125,plain,
    ( ~ spl7_1
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f63,f122,f99])).

fof(f63,plain,
    ( ~ v2_struct_0(sK1)
    | ~ v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f120,plain,
    ( ~ spl7_1
    | spl7_5 ),
    inference(avatar_split_clause,[],[f64,f117,f99])).

fof(f64,plain,
    ( v4_orders_2(sK1)
    | ~ v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f115,plain,
    ( ~ spl7_1
    | spl7_4 ),
    inference(avatar_split_clause,[],[f65,f112,f99])).

fof(f65,plain,
    ( v7_waybel_0(sK1)
    | ~ v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f110,plain,
    ( ~ spl7_1
    | spl7_3 ),
    inference(avatar_split_clause,[],[f66,f107,f99])).

fof(f66,plain,
    ( l1_waybel_0(sK1,sK0)
    | ~ v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f105,plain,
    ( ~ spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f67,f103,f99])).

fof(f67,plain,(
    ! [X2] :
      ( ~ v3_yellow_6(X2,sK0)
      | ~ m2_yellow_6(X2,sK0,sK1)
      | ~ v1_compts_1(sK0) ) ),
    inference(cnf_transformation,[],[f43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:39:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (31890)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (31906)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.51  % (31892)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (31884)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (31898)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.52  % (31900)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (31880)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (31878)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (31879)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (31889)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (31882)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (31907)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.53  % (31899)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.53  % (31894)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.53  % (31891)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (31900)Refutation not found, incomplete strategy% (31900)------------------------------
% 0.21/0.53  % (31900)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (31900)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (31900)Memory used [KB]: 10874
% 0.21/0.53  % (31900)Time elapsed: 0.104 s
% 0.21/0.53  % (31900)------------------------------
% 0.21/0.53  % (31900)------------------------------
% 0.21/0.53  % (31904)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.53  % (31893)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (31895)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.53  % (31881)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (31905)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (31897)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  % (31885)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (31896)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (31887)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (31886)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.55  % (31888)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.55  % (31883)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.55  % (31895)Refutation not found, incomplete strategy% (31895)------------------------------
% 0.21/0.55  % (31895)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (31895)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (31895)Memory used [KB]: 10746
% 0.21/0.55  % (31895)Time elapsed: 0.148 s
% 0.21/0.55  % (31895)------------------------------
% 0.21/0.55  % (31895)------------------------------
% 0.21/0.56  % (31902)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.56  % (31903)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.56  % (31904)Refutation found. Thanks to Tanya!
% 0.21/0.56  % SZS status Theorem for theBenchmark
% 0.21/0.56  % SZS output start Proof for theBenchmark
% 0.21/0.56  fof(f320,plain,(
% 0.21/0.56    $false),
% 0.21/0.56    inference(avatar_sat_refutation,[],[f105,f110,f115,f120,f125,f129,f133,f271,f319])).
% 0.21/0.56  fof(f319,plain,(
% 0.21/0.56    ~spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | spl7_6),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f318])).
% 0.21/0.56  fof(f318,plain,(
% 0.21/0.56    $false | (~spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | spl7_6)),
% 0.21/0.56    inference(subsumption_resolution,[],[f312,f68])).
% 0.21/0.56  fof(f68,plain,(
% 0.21/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f3])).
% 0.21/0.56  fof(f3,axiom,(
% 0.21/0.56    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.56  fof(f312,plain,(
% 0.21/0.56    ~r1_tarski(k1_xboole_0,sK4(sK0,sK1)) | (~spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | spl7_6)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f310,f94])).
% 0.21/0.56  fof(f94,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f34])).
% 0.21/0.56  fof(f34,plain,(
% 0.21/0.56    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.56    inference(ennf_transformation,[],[f5])).
% 0.21/0.56  fof(f5,axiom,(
% 0.21/0.56    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.21/0.56  fof(f310,plain,(
% 0.21/0.56    r2_hidden(sK4(sK0,sK1),k1_xboole_0) | (~spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | spl7_6)),
% 0.21/0.56    inference(subsumption_resolution,[],[f309,f58])).
% 0.21/0.56  fof(f58,plain,(
% 0.21/0.56    ~v2_struct_0(sK0)),
% 0.21/0.56    inference(cnf_transformation,[],[f43])).
% 0.21/0.56  fof(f43,plain,(
% 0.21/0.56    ((! [X2] : (~v3_yellow_6(X2,sK0) | ~m2_yellow_6(X2,sK0,sK1)) & l1_waybel_0(sK1,sK0) & v7_waybel_0(sK1) & v4_orders_2(sK1) & ~v2_struct_0(sK1)) | ~v1_compts_1(sK0)) & (! [X3] : ((v3_yellow_6(sK2(X3),sK0) & m2_yellow_6(sK2(X3),sK0,X3)) | ~l1_waybel_0(X3,sK0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(sK0)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f39,f42,f41,f40])).
% 0.21/0.56  fof(f40,plain,(
% 0.21/0.56    ? [X0] : ((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X3] : (? [X4] : (v3_yellow_6(X4,X0) & m2_yellow_6(X4,X0,X3)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ((? [X1] : (! [X2] : (~v3_yellow_6(X2,sK0) | ~m2_yellow_6(X2,sK0,X1)) & l1_waybel_0(X1,sK0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(sK0)) & (! [X3] : (? [X4] : (v3_yellow_6(X4,sK0) & m2_yellow_6(X4,sK0,X3)) | ~l1_waybel_0(X3,sK0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(sK0)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f41,plain,(
% 0.21/0.56    ? [X1] : (! [X2] : (~v3_yellow_6(X2,sK0) | ~m2_yellow_6(X2,sK0,X1)) & l1_waybel_0(X1,sK0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (! [X2] : (~v3_yellow_6(X2,sK0) | ~m2_yellow_6(X2,sK0,sK1)) & l1_waybel_0(sK1,sK0) & v7_waybel_0(sK1) & v4_orders_2(sK1) & ~v2_struct_0(sK1))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  % (31901)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.58  fof(f42,plain,(
% 0.21/0.58    ! [X3] : (? [X4] : (v3_yellow_6(X4,sK0) & m2_yellow_6(X4,sK0,X3)) => (v3_yellow_6(sK2(X3),sK0) & m2_yellow_6(sK2(X3),sK0,X3)))),
% 0.21/0.58    introduced(choice_axiom,[])).
% 0.21/0.58  fof(f39,plain,(
% 0.21/0.58    ? [X0] : ((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X3] : (? [X4] : (v3_yellow_6(X4,X0) & m2_yellow_6(X4,X0,X3)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.58    inference(rectify,[],[f38])).
% 0.21/0.58  fof(f38,plain,(
% 0.21/0.58    ? [X0] : ((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | v1_compts_1(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.58    inference(flattening,[],[f37])).
% 0.21/0.58  fof(f37,plain,(
% 0.21/0.58    ? [X0] : (((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | v1_compts_1(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.58    inference(nnf_transformation,[],[f17])).
% 0.21/0.58  fof(f17,plain,(
% 0.21/0.58    ? [X0] : ((v1_compts_1(X0) <~> ! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.58    inference(flattening,[],[f16])).
% 0.21/0.58  fof(f16,plain,(
% 0.21/0.58    ? [X0] : ((v1_compts_1(X0) <~> ! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f15])).
% 0.21/0.58  fof(f15,negated_conjecture,(
% 0.21/0.58    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)))))),
% 0.21/0.58    inference(negated_conjecture,[],[f14])).
% 1.79/0.59  fof(f14,conjecture,(
% 1.79/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)))))),
% 1.79/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_yellow19)).
% 1.79/0.59  fof(f309,plain,(
% 1.79/0.59    r2_hidden(sK4(sK0,sK1),k1_xboole_0) | v2_struct_0(sK0) | (~spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | spl7_6)),
% 1.79/0.59    inference(subsumption_resolution,[],[f308,f59])).
% 1.79/0.59  fof(f59,plain,(
% 1.79/0.59    v2_pre_topc(sK0)),
% 1.79/0.59    inference(cnf_transformation,[],[f43])).
% 1.79/0.59  fof(f308,plain,(
% 1.79/0.59    r2_hidden(sK4(sK0,sK1),k1_xboole_0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | spl7_6)),
% 1.79/0.59    inference(subsumption_resolution,[],[f307,f60])).
% 1.79/0.59  fof(f60,plain,(
% 1.79/0.59    l1_pre_topc(sK0)),
% 1.79/0.59    inference(cnf_transformation,[],[f43])).
% 1.79/0.59  fof(f307,plain,(
% 1.79/0.59    r2_hidden(sK4(sK0,sK1),k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | spl7_6)),
% 1.79/0.59    inference(subsumption_resolution,[],[f306,f295])).
% 1.79/0.59  fof(f295,plain,(
% 1.79/0.59    ~v2_struct_0(sK5(sK0,sK1,sK4(sK0,sK1))) | (~spl7_1 | ~spl7_3 | ~spl7_4 | ~spl7_5 | spl7_6)),
% 1.79/0.59    inference(unit_resulting_resolution,[],[f58,f134,f124,f119,f114,f109,f285,f83])).
% 1.79/0.59  fof(f83,plain,(
% 1.79/0.59    ( ! [X2,X0,X1] : (~v2_struct_0(X2) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.79/0.59    inference(cnf_transformation,[],[f30])).
% 1.79/0.59  fof(f30,plain,(
% 1.79/0.59    ! [X0,X1] : (! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.79/0.59    inference(flattening,[],[f29])).
% 1.79/0.59  fof(f29,plain,(
% 1.79/0.59    ! [X0,X1] : (! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.79/0.59    inference(ennf_transformation,[],[f8])).
% 1.79/0.59  fof(f8,axiom,(
% 1.79/0.59    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_yellow_6(X2,X0,X1) => (l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2))))),
% 1.79/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_yellow_6)).
% 1.79/0.59  fof(f285,plain,(
% 1.79/0.59    m2_yellow_6(sK5(sK0,sK1,sK4(sK0,sK1)),sK0,sK1) | (~spl7_1 | ~spl7_3 | ~spl7_4 | ~spl7_5 | spl7_6)),
% 1.79/0.59    inference(unit_resulting_resolution,[],[f58,f59,f60,f124,f119,f114,f109,f274,f275,f80])).
% 1.79/0.59  fof(f80,plain,(
% 1.79/0.59    ( ! [X2,X0,X1] : (m2_yellow_6(sK5(X0,X1,X2),X0,X1) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.79/0.59    inference(cnf_transformation,[],[f51])).
% 1.79/0.59  fof(f51,plain,(
% 1.79/0.59    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k10_yellow_6(X0,sK5(X0,X1,X2))) & m2_yellow_6(sK5(X0,X1,X2),X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.79/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f26,f50])).
% 1.79/0.59  fof(f50,plain,(
% 1.79/0.59    ! [X2,X1,X0] : (? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) => (r2_hidden(X2,k10_yellow_6(X0,sK5(X0,X1,X2))) & m2_yellow_6(sK5(X0,X1,X2),X0,X1)))),
% 1.79/0.59    introduced(choice_axiom,[])).
% 1.79/0.59  fof(f26,plain,(
% 1.79/0.59    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.79/0.59    inference(flattening,[],[f25])).
% 1.79/0.59  fof(f25,plain,(
% 1.79/0.59    ! [X0] : (! [X1] : (! [X2] : ((? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) | ~r3_waybel_9(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.79/0.59    inference(ennf_transformation,[],[f12])).
% 1.79/0.59  fof(f12,axiom,(
% 1.79/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m2_yellow_6(X3,X0,X1) => ~r2_hidden(X2,k10_yellow_6(X0,X3))) & r3_waybel_9(X0,X1,X2)))))),
% 1.79/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_waybel_9)).
% 1.79/0.59  fof(f275,plain,(
% 1.79/0.59    r3_waybel_9(sK0,sK1,sK4(sK0,sK1)) | (~spl7_1 | ~spl7_3 | ~spl7_4 | ~spl7_5 | spl7_6)),
% 1.79/0.59    inference(unit_resulting_resolution,[],[f58,f59,f60,f100,f124,f119,f114,f109,f71])).
% 1.79/0.59  fof(f71,plain,(
% 1.79/0.59    ( ! [X0,X3] : (r3_waybel_9(X0,X3,sK4(X0,X3)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | ~v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.79/0.59    inference(cnf_transformation,[],[f48])).
% 1.79/0.59  fof(f48,plain,(
% 1.79/0.59    ! [X0] : (((v1_compts_1(X0) | (! [X2] : (~r3_waybel_9(X0,sK3(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(sK3(X0),X0) & v7_waybel_0(sK3(X0)) & v4_orders_2(sK3(X0)) & ~v2_struct_0(sK3(X0)))) & (! [X3] : ((r3_waybel_9(X0,X3,sK4(X0,X3)) & m1_subset_1(sK4(X0,X3),u1_struct_0(X0))) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.79/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f45,f47,f46])).
% 1.79/0.59  fof(f46,plain,(
% 1.79/0.59    ! [X0] : (? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (! [X2] : (~r3_waybel_9(X0,sK3(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(sK3(X0),X0) & v7_waybel_0(sK3(X0)) & v4_orders_2(sK3(X0)) & ~v2_struct_0(sK3(X0))))),
% 1.79/0.59    introduced(choice_axiom,[])).
% 1.79/0.59  fof(f47,plain,(
% 1.79/0.59    ! [X3,X0] : (? [X4] : (r3_waybel_9(X0,X3,X4) & m1_subset_1(X4,u1_struct_0(X0))) => (r3_waybel_9(X0,X3,sK4(X0,X3)) & m1_subset_1(sK4(X0,X3),u1_struct_0(X0))))),
% 1.79/0.59    introduced(choice_axiom,[])).
% 1.79/0.59  fof(f45,plain,(
% 1.79/0.59    ! [X0] : (((v1_compts_1(X0) | ? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (! [X3] : (? [X4] : (r3_waybel_9(X0,X3,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.79/0.59    inference(rectify,[],[f44])).
% 1.79/0.59  fof(f44,plain,(
% 1.79/0.59    ! [X0] : (((v1_compts_1(X0) | ? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.79/0.59    inference(nnf_transformation,[],[f20])).
% 1.79/0.59  fof(f20,plain,(
% 1.79/0.59    ! [X0] : ((v1_compts_1(X0) <=> ! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.79/0.59    inference(flattening,[],[f19])).
% 1.79/0.59  fof(f19,plain,(
% 1.79/0.59    ! [X0] : ((v1_compts_1(X0) <=> ! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.79/0.59    inference(ennf_transformation,[],[f13])).
% 1.79/0.59  fof(f13,axiom,(
% 1.79/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))))))),
% 1.79/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_yellow19)).
% 1.79/0.59  fof(f100,plain,(
% 1.79/0.59    v1_compts_1(sK0) | ~spl7_1),
% 1.79/0.59    inference(avatar_component_clause,[],[f99])).
% 1.79/0.59  fof(f99,plain,(
% 1.79/0.59    spl7_1 <=> v1_compts_1(sK0)),
% 1.79/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.79/0.59  fof(f274,plain,(
% 1.79/0.59    m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0)) | (~spl7_1 | ~spl7_3 | ~spl7_4 | ~spl7_5 | spl7_6)),
% 1.79/0.59    inference(unit_resulting_resolution,[],[f58,f59,f60,f100,f124,f119,f114,f109,f70])).
% 1.79/0.59  fof(f70,plain,(
% 1.79/0.59    ( ! [X0,X3] : (m1_subset_1(sK4(X0,X3),u1_struct_0(X0)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | ~v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.79/0.59    inference(cnf_transformation,[],[f48])).
% 1.79/0.59  fof(f109,plain,(
% 1.79/0.59    l1_waybel_0(sK1,sK0) | ~spl7_3),
% 1.79/0.59    inference(avatar_component_clause,[],[f107])).
% 1.79/0.59  fof(f107,plain,(
% 1.79/0.59    spl7_3 <=> l1_waybel_0(sK1,sK0)),
% 1.79/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.79/0.59  fof(f114,plain,(
% 1.79/0.59    v7_waybel_0(sK1) | ~spl7_4),
% 1.79/0.59    inference(avatar_component_clause,[],[f112])).
% 1.79/0.59  fof(f112,plain,(
% 1.79/0.59    spl7_4 <=> v7_waybel_0(sK1)),
% 1.79/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 1.79/0.59  fof(f119,plain,(
% 1.79/0.59    v4_orders_2(sK1) | ~spl7_5),
% 1.79/0.59    inference(avatar_component_clause,[],[f117])).
% 1.79/0.59  fof(f117,plain,(
% 1.79/0.59    spl7_5 <=> v4_orders_2(sK1)),
% 1.79/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 1.79/0.59  fof(f124,plain,(
% 1.79/0.59    ~v2_struct_0(sK1) | spl7_6),
% 1.79/0.59    inference(avatar_component_clause,[],[f122])).
% 1.79/0.59  fof(f122,plain,(
% 1.79/0.59    spl7_6 <=> v2_struct_0(sK1)),
% 1.79/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 1.79/0.59  fof(f134,plain,(
% 1.79/0.59    l1_struct_0(sK0)),
% 1.79/0.59    inference(unit_resulting_resolution,[],[f60,f69])).
% 1.79/0.59  fof(f69,plain,(
% 1.79/0.59    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.79/0.59    inference(cnf_transformation,[],[f18])).
% 1.79/0.59  fof(f18,plain,(
% 1.79/0.59    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.79/0.59    inference(ennf_transformation,[],[f6])).
% 1.79/0.59  fof(f6,axiom,(
% 1.79/0.59    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.79/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.79/0.59  fof(f306,plain,(
% 1.79/0.59    r2_hidden(sK4(sK0,sK1),k1_xboole_0) | v2_struct_0(sK5(sK0,sK1,sK4(sK0,sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | spl7_6)),
% 1.79/0.59    inference(subsumption_resolution,[],[f305,f296])).
% 1.79/0.59  fof(f296,plain,(
% 1.79/0.59    v4_orders_2(sK5(sK0,sK1,sK4(sK0,sK1))) | (~spl7_1 | ~spl7_3 | ~spl7_4 | ~spl7_5 | spl7_6)),
% 1.79/0.59    inference(unit_resulting_resolution,[],[f58,f134,f124,f119,f114,f109,f285,f84])).
% 1.79/0.59  fof(f84,plain,(
% 1.79/0.59    ( ! [X2,X0,X1] : (v4_orders_2(X2) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.79/0.59    inference(cnf_transformation,[],[f30])).
% 1.79/0.59  fof(f305,plain,(
% 1.79/0.59    r2_hidden(sK4(sK0,sK1),k1_xboole_0) | ~v4_orders_2(sK5(sK0,sK1,sK4(sK0,sK1))) | v2_struct_0(sK5(sK0,sK1,sK4(sK0,sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | spl7_6)),
% 1.79/0.59    inference(subsumption_resolution,[],[f304,f297])).
% 1.79/0.59  fof(f297,plain,(
% 1.79/0.59    v7_waybel_0(sK5(sK0,sK1,sK4(sK0,sK1))) | (~spl7_1 | ~spl7_3 | ~spl7_4 | ~spl7_5 | spl7_6)),
% 1.79/0.59    inference(unit_resulting_resolution,[],[f58,f134,f124,f119,f114,f109,f285,f85])).
% 1.79/0.59  fof(f85,plain,(
% 1.79/0.59    ( ! [X2,X0,X1] : (v7_waybel_0(X2) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.79/0.59    inference(cnf_transformation,[],[f30])).
% 1.79/0.59  fof(f304,plain,(
% 1.79/0.59    r2_hidden(sK4(sK0,sK1),k1_xboole_0) | ~v7_waybel_0(sK5(sK0,sK1,sK4(sK0,sK1))) | ~v4_orders_2(sK5(sK0,sK1,sK4(sK0,sK1))) | v2_struct_0(sK5(sK0,sK1,sK4(sK0,sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | spl7_6)),
% 1.79/0.59    inference(subsumption_resolution,[],[f303,f298])).
% 1.79/0.59  fof(f298,plain,(
% 1.79/0.59    l1_waybel_0(sK5(sK0,sK1,sK4(sK0,sK1)),sK0) | (~spl7_1 | ~spl7_3 | ~spl7_4 | ~spl7_5 | spl7_6)),
% 1.79/0.59    inference(unit_resulting_resolution,[],[f58,f134,f124,f119,f114,f109,f285,f86])).
% 1.79/0.59  fof(f86,plain,(
% 1.79/0.59    ( ! [X2,X0,X1] : (l1_waybel_0(X2,X0) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.79/0.59    inference(cnf_transformation,[],[f30])).
% 1.79/0.59  fof(f303,plain,(
% 1.79/0.59    r2_hidden(sK4(sK0,sK1),k1_xboole_0) | ~l1_waybel_0(sK5(sK0,sK1,sK4(sK0,sK1)),sK0) | ~v7_waybel_0(sK5(sK0,sK1,sK4(sK0,sK1))) | ~v4_orders_2(sK5(sK0,sK1,sK4(sK0,sK1))) | v2_struct_0(sK5(sK0,sK1,sK4(sK0,sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | spl7_6)),
% 1.79/0.59    inference(subsumption_resolution,[],[f302,f294])).
% 1.79/0.59  fof(f294,plain,(
% 1.79/0.59    ~v3_yellow_6(sK5(sK0,sK1,sK4(sK0,sK1)),sK0) | (~spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | spl7_6)),
% 1.79/0.59    inference(unit_resulting_resolution,[],[f285,f104])).
% 1.79/0.59  fof(f104,plain,(
% 1.79/0.59    ( ! [X2] : (~v3_yellow_6(X2,sK0) | ~m2_yellow_6(X2,sK0,sK1)) ) | ~spl7_2),
% 1.79/0.59    inference(avatar_component_clause,[],[f103])).
% 1.79/0.59  fof(f103,plain,(
% 1.79/0.59    spl7_2 <=> ! [X2] : (~v3_yellow_6(X2,sK0) | ~m2_yellow_6(X2,sK0,sK1))),
% 1.79/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.79/0.59  fof(f302,plain,(
% 1.79/0.59    r2_hidden(sK4(sK0,sK1),k1_xboole_0) | v3_yellow_6(sK5(sK0,sK1,sK4(sK0,sK1)),sK0) | ~l1_waybel_0(sK5(sK0,sK1,sK4(sK0,sK1)),sK0) | ~v7_waybel_0(sK5(sK0,sK1,sK4(sK0,sK1))) | ~v4_orders_2(sK5(sK0,sK1,sK4(sK0,sK1))) | v2_struct_0(sK5(sK0,sK1,sK4(sK0,sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl7_1 | ~spl7_3 | ~spl7_4 | ~spl7_5 | spl7_6)),
% 1.79/0.59    inference(superposition,[],[f286,f78])).
% 1.79/0.59  fof(f78,plain,(
% 1.79/0.59    ( ! [X0,X1] : (v3_yellow_6(X1,X0) | k1_xboole_0 = k10_yellow_6(X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.79/0.59    inference(cnf_transformation,[],[f49])).
% 1.79/0.59  fof(f49,plain,(
% 1.79/0.59    ! [X0] : (! [X1] : (((v3_yellow_6(X1,X0) | k1_xboole_0 = k10_yellow_6(X0,X1)) & (k1_xboole_0 != k10_yellow_6(X0,X1) | ~v3_yellow_6(X1,X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.79/0.59    inference(nnf_transformation,[],[f22])).
% 1.79/0.59  fof(f22,plain,(
% 1.79/0.59    ! [X0] : (! [X1] : ((v3_yellow_6(X1,X0) <=> k1_xboole_0 != k10_yellow_6(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.79/0.59    inference(flattening,[],[f21])).
% 1.79/0.59  fof(f21,plain,(
% 1.79/0.59    ! [X0] : (! [X1] : ((v3_yellow_6(X1,X0) <=> k1_xboole_0 != k10_yellow_6(X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.79/0.59    inference(ennf_transformation,[],[f9])).
% 1.79/0.59  fof(f9,axiom,(
% 1.79/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (v3_yellow_6(X1,X0) <=> k1_xboole_0 != k10_yellow_6(X0,X1))))),
% 1.79/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_yellow_6)).
% 1.79/0.59  fof(f286,plain,(
% 1.79/0.59    r2_hidden(sK4(sK0,sK1),k10_yellow_6(sK0,sK5(sK0,sK1,sK4(sK0,sK1)))) | (~spl7_1 | ~spl7_3 | ~spl7_4 | ~spl7_5 | spl7_6)),
% 1.79/0.59    inference(unit_resulting_resolution,[],[f58,f59,f60,f124,f119,f114,f109,f274,f275,f81])).
% 1.79/0.59  fof(f81,plain,(
% 1.79/0.59    ( ! [X2,X0,X1] : (r2_hidden(X2,k10_yellow_6(X0,sK5(X0,X1,X2))) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.79/0.59    inference(cnf_transformation,[],[f51])).
% 1.79/0.59  fof(f271,plain,(
% 1.79/0.59    spl7_1 | ~spl7_7 | ~spl7_8),
% 1.79/0.59    inference(avatar_contradiction_clause,[],[f270])).
% 1.79/0.59  fof(f270,plain,(
% 1.79/0.59    $false | (spl7_1 | ~spl7_7 | ~spl7_8)),
% 1.79/0.59    inference(subsumption_resolution,[],[f266,f249])).
% 1.79/0.59  fof(f249,plain,(
% 1.79/0.59    r3_waybel_9(sK0,sK2(sK3(sK0)),sK6(k10_yellow_6(sK0,sK2(sK3(sK0))),k1_xboole_0)) | (spl7_1 | ~spl7_7 | ~spl7_8)),
% 1.79/0.59    inference(unit_resulting_resolution,[],[f58,f59,f60,f142,f143,f144,f145,f190,f217,f79])).
% 1.79/0.59  fof(f79,plain,(
% 1.79/0.59    ( ! [X2,X0,X1] : (r3_waybel_9(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.79/0.59    inference(cnf_transformation,[],[f24])).
% 1.79/0.59  fof(f24,plain,(
% 1.79/0.59    ! [X0] : (! [X1] : (! [X2] : (r3_waybel_9(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.79/0.59    inference(flattening,[],[f23])).
% 1.79/0.59  fof(f23,plain,(
% 1.79/0.59    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.79/0.59    inference(ennf_transformation,[],[f10])).
% 1.79/0.59  fof(f10,axiom,(
% 1.79/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k10_yellow_6(X0,X1)) => r3_waybel_9(X0,X1,X2)))))),
% 1.79/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_waybel_9)).
% 1.79/0.59  fof(f217,plain,(
% 1.79/0.59    m1_subset_1(sK6(k10_yellow_6(sK0,sK2(sK3(sK0))),k1_xboole_0),u1_struct_0(sK0)) | (spl7_1 | ~spl7_7 | ~spl7_8)),
% 1.79/0.59    inference(unit_resulting_resolution,[],[f167,f190,f95])).
% 1.79/0.59  fof(f95,plain,(
% 1.79/0.59    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.79/0.59    inference(cnf_transformation,[],[f36])).
% 1.79/0.59  fof(f36,plain,(
% 1.79/0.59    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.79/0.59    inference(flattening,[],[f35])).
% 1.79/0.59  fof(f35,plain,(
% 1.79/0.59    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.79/0.59    inference(ennf_transformation,[],[f4])).
% 1.79/0.59  fof(f4,axiom,(
% 1.79/0.59    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.79/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 1.79/0.59  fof(f167,plain,(
% 1.79/0.59    m1_subset_1(k10_yellow_6(sK0,sK2(sK3(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) | (spl7_1 | ~spl7_8)),
% 1.79/0.59    inference(unit_resulting_resolution,[],[f58,f59,f60,f142,f143,f144,f145,f87])).
% 1.79/0.59  fof(f87,plain,(
% 1.79/0.59    ( ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.79/0.59    inference(cnf_transformation,[],[f32])).
% 1.79/0.59  fof(f32,plain,(
% 1.79/0.59    ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.79/0.59    inference(flattening,[],[f31])).
% 1.79/0.59  fof(f31,plain,(
% 1.79/0.59    ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.79/0.59    inference(ennf_transformation,[],[f7])).
% 1.79/0.59  fof(f7,axiom,(
% 1.79/0.59    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.79/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_yellow_6)).
% 1.79/0.59  fof(f190,plain,(
% 1.79/0.59    r2_hidden(sK6(k10_yellow_6(sK0,sK2(sK3(sK0))),k1_xboole_0),k10_yellow_6(sK0,sK2(sK3(sK0)))) | (spl7_1 | ~spl7_7 | ~spl7_8)),
% 1.79/0.59    inference(unit_resulting_resolution,[],[f175,f92])).
% 1.79/0.59  fof(f92,plain,(
% 1.79/0.59    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK6(X0,X1),X0)) )),
% 1.79/0.59    inference(cnf_transformation,[],[f57])).
% 1.79/0.59  fof(f57,plain,(
% 1.79/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.79/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f55,f56])).
% 1.79/0.59  fof(f56,plain,(
% 1.79/0.59    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)))),
% 1.79/0.59    introduced(choice_axiom,[])).
% 1.79/0.59  fof(f55,plain,(
% 1.79/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.79/0.59    inference(rectify,[],[f54])).
% 1.79/0.59  fof(f54,plain,(
% 1.79/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.79/0.59    inference(nnf_transformation,[],[f33])).
% 1.79/0.59  fof(f33,plain,(
% 1.79/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.79/0.59    inference(ennf_transformation,[],[f1])).
% 1.79/0.59  fof(f1,axiom,(
% 1.79/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.79/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.79/0.59  fof(f175,plain,(
% 1.79/0.59    ~r1_tarski(k10_yellow_6(sK0,sK2(sK3(sK0))),k1_xboole_0) | (spl7_1 | ~spl7_7 | ~spl7_8)),
% 1.79/0.59    inference(unit_resulting_resolution,[],[f68,f166,f90])).
% 1.79/0.59  fof(f90,plain,(
% 1.79/0.59    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 1.79/0.59    inference(cnf_transformation,[],[f53])).
% 1.79/0.59  fof(f53,plain,(
% 1.79/0.59    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.79/0.59    inference(flattening,[],[f52])).
% 1.79/0.59  fof(f52,plain,(
% 1.79/0.59    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.79/0.59    inference(nnf_transformation,[],[f2])).
% 1.79/0.59  fof(f2,axiom,(
% 1.79/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.79/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.79/0.59  fof(f166,plain,(
% 1.79/0.59    k1_xboole_0 != k10_yellow_6(sK0,sK2(sK3(sK0))) | (spl7_1 | ~spl7_7 | ~spl7_8)),
% 1.79/0.59    inference(unit_resulting_resolution,[],[f58,f59,f60,f142,f143,f144,f140,f145,f77])).
% 1.79/0.59  fof(f77,plain,(
% 1.79/0.59    ( ! [X0,X1] : (k1_xboole_0 != k10_yellow_6(X0,X1) | ~v3_yellow_6(X1,X0) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.79/0.59    inference(cnf_transformation,[],[f49])).
% 1.79/0.59  fof(f140,plain,(
% 1.79/0.59    v3_yellow_6(sK2(sK3(sK0)),sK0) | (spl7_1 | ~spl7_7)),
% 1.79/0.59    inference(unit_resulting_resolution,[],[f137,f135,f136,f138,f128])).
% 1.79/0.59  fof(f128,plain,(
% 1.79/0.59    ( ! [X3] : (~v7_waybel_0(X3) | v2_struct_0(X3) | ~v4_orders_2(X3) | v3_yellow_6(sK2(X3),sK0) | ~l1_waybel_0(X3,sK0)) ) | ~spl7_7),
% 1.79/0.59    inference(avatar_component_clause,[],[f127])).
% 1.79/0.59  fof(f127,plain,(
% 1.79/0.59    spl7_7 <=> ! [X3] : (v3_yellow_6(sK2(X3),sK0) | v2_struct_0(X3) | ~v4_orders_2(X3) | ~v7_waybel_0(X3) | ~l1_waybel_0(X3,sK0))),
% 1.79/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 1.79/0.59  fof(f138,plain,(
% 1.79/0.59    l1_waybel_0(sK3(sK0),sK0) | spl7_1),
% 1.79/0.59    inference(unit_resulting_resolution,[],[f58,f59,f60,f101,f75])).
% 1.79/0.59  fof(f75,plain,(
% 1.79/0.59    ( ! [X0] : (v1_compts_1(X0) | l1_waybel_0(sK3(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.79/0.59    inference(cnf_transformation,[],[f48])).
% 1.79/0.59  fof(f101,plain,(
% 1.79/0.59    ~v1_compts_1(sK0) | spl7_1),
% 1.79/0.59    inference(avatar_component_clause,[],[f99])).
% 1.79/0.59  fof(f136,plain,(
% 1.79/0.59    v4_orders_2(sK3(sK0)) | spl7_1),
% 1.79/0.59    inference(unit_resulting_resolution,[],[f58,f59,f60,f101,f73])).
% 1.79/0.59  fof(f73,plain,(
% 1.79/0.59    ( ! [X0] : (v1_compts_1(X0) | v4_orders_2(sK3(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.79/0.59    inference(cnf_transformation,[],[f48])).
% 1.79/0.59  fof(f135,plain,(
% 1.79/0.59    ~v2_struct_0(sK3(sK0)) | spl7_1),
% 1.79/0.59    inference(unit_resulting_resolution,[],[f58,f59,f60,f101,f72])).
% 1.79/0.59  fof(f72,plain,(
% 1.79/0.59    ( ! [X0] : (v1_compts_1(X0) | ~v2_struct_0(sK3(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.79/0.59    inference(cnf_transformation,[],[f48])).
% 1.79/0.59  fof(f137,plain,(
% 1.79/0.59    v7_waybel_0(sK3(sK0)) | spl7_1),
% 1.79/0.59    inference(unit_resulting_resolution,[],[f58,f59,f60,f101,f74])).
% 1.79/0.59  fof(f74,plain,(
% 1.79/0.59    ( ! [X0] : (v1_compts_1(X0) | v7_waybel_0(sK3(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.79/0.59    inference(cnf_transformation,[],[f48])).
% 1.79/0.59  fof(f145,plain,(
% 1.79/0.59    l1_waybel_0(sK2(sK3(sK0)),sK0) | (spl7_1 | ~spl7_8)),
% 1.79/0.59    inference(unit_resulting_resolution,[],[f58,f134,f135,f136,f137,f138,f139,f86])).
% 1.79/0.59  fof(f139,plain,(
% 1.79/0.59    m2_yellow_6(sK2(sK3(sK0)),sK0,sK3(sK0)) | (spl7_1 | ~spl7_8)),
% 1.79/0.59    inference(unit_resulting_resolution,[],[f137,f135,f136,f138,f132])).
% 1.79/0.59  fof(f132,plain,(
% 1.79/0.59    ( ! [X3] : (~v7_waybel_0(X3) | v2_struct_0(X3) | ~v4_orders_2(X3) | m2_yellow_6(sK2(X3),sK0,X3) | ~l1_waybel_0(X3,sK0)) ) | ~spl7_8),
% 1.79/0.59    inference(avatar_component_clause,[],[f131])).
% 1.79/0.59  fof(f131,plain,(
% 1.79/0.59    spl7_8 <=> ! [X3] : (m2_yellow_6(sK2(X3),sK0,X3) | v2_struct_0(X3) | ~v4_orders_2(X3) | ~v7_waybel_0(X3) | ~l1_waybel_0(X3,sK0))),
% 1.79/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 1.79/0.59  fof(f144,plain,(
% 1.79/0.59    v7_waybel_0(sK2(sK3(sK0))) | (spl7_1 | ~spl7_8)),
% 1.79/0.59    inference(unit_resulting_resolution,[],[f58,f134,f135,f136,f137,f138,f139,f85])).
% 1.79/0.59  fof(f143,plain,(
% 1.79/0.59    v4_orders_2(sK2(sK3(sK0))) | (spl7_1 | ~spl7_8)),
% 1.79/0.59    inference(unit_resulting_resolution,[],[f58,f134,f135,f136,f137,f138,f139,f84])).
% 1.79/0.59  fof(f142,plain,(
% 1.79/0.59    ~v2_struct_0(sK2(sK3(sK0))) | (spl7_1 | ~spl7_8)),
% 1.79/0.59    inference(unit_resulting_resolution,[],[f58,f134,f135,f136,f137,f138,f139,f83])).
% 1.79/0.59  fof(f266,plain,(
% 1.79/0.59    ~r3_waybel_9(sK0,sK2(sK3(sK0)),sK6(k10_yellow_6(sK0,sK2(sK3(sK0))),k1_xboole_0)) | (spl7_1 | ~spl7_7 | ~spl7_8)),
% 1.79/0.59    inference(unit_resulting_resolution,[],[f58,f59,f60,f135,f136,f137,f138,f139,f217,f250,f82])).
% 1.79/0.59  fof(f82,plain,(
% 1.79/0.59    ( ! [X2,X0,X3,X1] : (r3_waybel_9(X0,X1,X3) | ~r3_waybel_9(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.79/0.59    inference(cnf_transformation,[],[f28])).
% 1.79/0.59  fof(f28,plain,(
% 1.79/0.59    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r3_waybel_9(X0,X1,X3) | ~r3_waybel_9(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.79/0.59    inference(flattening,[],[f27])).
% 1.79/0.59  fof(f27,plain,(
% 1.79/0.59    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r3_waybel_9(X0,X1,X3) | ~r3_waybel_9(X0,X2,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.79/0.59    inference(ennf_transformation,[],[f11])).
% 1.79/0.59  fof(f11,axiom,(
% 1.79/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m2_yellow_6(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_waybel_9(X0,X2,X3) => r3_waybel_9(X0,X1,X3))))))),
% 1.79/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_waybel_9)).
% 1.79/0.59  fof(f250,plain,(
% 1.79/0.59    ~r3_waybel_9(sK0,sK3(sK0),sK6(k10_yellow_6(sK0,sK2(sK3(sK0))),k1_xboole_0)) | (spl7_1 | ~spl7_7 | ~spl7_8)),
% 1.79/0.59    inference(unit_resulting_resolution,[],[f58,f59,f60,f101,f217,f76])).
% 1.79/0.59  fof(f76,plain,(
% 1.79/0.59    ( ! [X2,X0] : (v1_compts_1(X0) | ~r3_waybel_9(X0,sK3(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.79/0.59    inference(cnf_transformation,[],[f48])).
% 1.79/0.59  fof(f133,plain,(
% 1.79/0.59    spl7_1 | spl7_8),
% 1.79/0.59    inference(avatar_split_clause,[],[f61,f131,f99])).
% 1.79/0.59  fof(f61,plain,(
% 1.79/0.59    ( ! [X3] : (m2_yellow_6(sK2(X3),sK0,X3) | ~l1_waybel_0(X3,sK0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | v1_compts_1(sK0)) )),
% 1.79/0.59    inference(cnf_transformation,[],[f43])).
% 1.79/0.59  fof(f129,plain,(
% 1.79/0.59    spl7_1 | spl7_7),
% 1.79/0.59    inference(avatar_split_clause,[],[f62,f127,f99])).
% 1.79/0.59  fof(f62,plain,(
% 1.79/0.59    ( ! [X3] : (v3_yellow_6(sK2(X3),sK0) | ~l1_waybel_0(X3,sK0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | v1_compts_1(sK0)) )),
% 1.79/0.59    inference(cnf_transformation,[],[f43])).
% 1.79/0.59  fof(f125,plain,(
% 1.79/0.59    ~spl7_1 | ~spl7_6),
% 1.79/0.59    inference(avatar_split_clause,[],[f63,f122,f99])).
% 1.79/0.59  fof(f63,plain,(
% 1.79/0.59    ~v2_struct_0(sK1) | ~v1_compts_1(sK0)),
% 1.79/0.59    inference(cnf_transformation,[],[f43])).
% 1.79/0.59  fof(f120,plain,(
% 1.79/0.59    ~spl7_1 | spl7_5),
% 1.79/0.59    inference(avatar_split_clause,[],[f64,f117,f99])).
% 1.79/0.59  fof(f64,plain,(
% 1.79/0.59    v4_orders_2(sK1) | ~v1_compts_1(sK0)),
% 1.79/0.59    inference(cnf_transformation,[],[f43])).
% 1.79/0.59  fof(f115,plain,(
% 1.79/0.59    ~spl7_1 | spl7_4),
% 1.79/0.59    inference(avatar_split_clause,[],[f65,f112,f99])).
% 1.79/0.59  fof(f65,plain,(
% 1.79/0.59    v7_waybel_0(sK1) | ~v1_compts_1(sK0)),
% 1.79/0.59    inference(cnf_transformation,[],[f43])).
% 1.79/0.59  fof(f110,plain,(
% 1.79/0.59    ~spl7_1 | spl7_3),
% 1.79/0.59    inference(avatar_split_clause,[],[f66,f107,f99])).
% 1.79/0.59  fof(f66,plain,(
% 1.79/0.59    l1_waybel_0(sK1,sK0) | ~v1_compts_1(sK0)),
% 1.79/0.59    inference(cnf_transformation,[],[f43])).
% 1.79/0.59  fof(f105,plain,(
% 1.79/0.59    ~spl7_1 | spl7_2),
% 1.79/0.59    inference(avatar_split_clause,[],[f67,f103,f99])).
% 1.79/0.59  fof(f67,plain,(
% 1.79/0.59    ( ! [X2] : (~v3_yellow_6(X2,sK0) | ~m2_yellow_6(X2,sK0,sK1) | ~v1_compts_1(sK0)) )),
% 1.79/0.59    inference(cnf_transformation,[],[f43])).
% 1.79/0.59  % SZS output end Proof for theBenchmark
% 1.79/0.59  % (31904)------------------------------
% 1.79/0.59  % (31904)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.79/0.59  % (31904)Termination reason: Refutation
% 1.79/0.59  
% 1.79/0.59  % (31904)Memory used [KB]: 11001
% 1.79/0.59  % (31904)Time elapsed: 0.159 s
% 1.79/0.59  % (31904)------------------------------
% 1.79/0.59  % (31904)------------------------------
% 1.79/0.59  % (31877)Success in time 0.229 s
%------------------------------------------------------------------------------
