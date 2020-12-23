%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:39 EST 2020

% Result     : Theorem 1.53s
% Output     : Refutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :  198 (77327 expanded)
%              Number of leaves         :   35 (25612 expanded)
%              Depth                    :   27
%              Number of atoms          : 1438 (932115 expanded)
%              Number of equality atoms :   31 ( 361 expanded)
%              Maximal formula depth    :   17 (   8 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f770,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f129,f134,f139,f144,f149,f153,f157,f663,f678,f769])).

fof(f769,plain,
    ( ~ spl11_1
    | ~ spl11_2
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_5
    | spl11_6 ),
    inference(avatar_contradiction_clause,[],[f768])).

fof(f768,plain,
    ( $false
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_5
    | spl11_6 ),
    inference(subsumption_resolution,[],[f764,f83])).

fof(f83,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f764,plain,
    ( ~ r1_tarski(k1_xboole_0,sK4(sK0,sK1))
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_5
    | spl11_6 ),
    inference(unit_resulting_resolution,[],[f762,f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f762,plain,
    ( r2_hidden(sK4(sK0,sK1),k1_xboole_0)
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_5
    | spl11_6 ),
    inference(subsumption_resolution,[],[f761,f73])).

fof(f73,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f45,f48,f47,f46])).

fof(f46,plain,
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

fof(f47,plain,
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

fof(f48,plain,(
    ! [X3] :
      ( ? [X4] :
          ( v3_yellow_6(X4,sK0)
          & m2_yellow_6(X4,sK0,X3) )
     => ( v3_yellow_6(sK2(X3),sK0)
        & m2_yellow_6(sK2(X3),sK0,X3) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
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
    inference(rectify,[],[f44])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
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

fof(f761,plain,
    ( r2_hidden(sK4(sK0,sK1),k1_xboole_0)
    | v2_struct_0(sK0)
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_5
    | spl11_6 ),
    inference(subsumption_resolution,[],[f760,f74])).

fof(f74,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f760,plain,
    ( r2_hidden(sK4(sK0,sK1),k1_xboole_0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_5
    | spl11_6 ),
    inference(subsumption_resolution,[],[f759,f75])).

fof(f75,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f759,plain,
    ( r2_hidden(sK4(sK0,sK1),k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_5
    | spl11_6 ),
    inference(subsumption_resolution,[],[f758,f717])).

fof(f717,plain,
    ( ~ v2_struct_0(sK5(sK0,sK1,sK4(sK0,sK1)))
    | ~ spl11_1
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_5
    | spl11_6 ),
    inference(unit_resulting_resolution,[],[f73,f158,f148,f143,f138,f133,f703,f109])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(X2)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f703,plain,
    ( m2_yellow_6(sK5(sK0,sK1,sK4(sK0,sK1)),sK0,sK1)
    | ~ spl11_1
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_5
    | spl11_6 ),
    inference(unit_resulting_resolution,[],[f73,f74,f75,f148,f143,f138,f133,f692,f693,f97])).

fof(f97,plain,(
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
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f30,f56])).

fof(f56,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X2,k10_yellow_6(X0,X3))
          & m2_yellow_6(X3,X0,X1) )
     => ( r2_hidden(X2,k10_yellow_6(X0,sK5(X0,X1,X2)))
        & m2_yellow_6(sK5(X0,X1,X2),X0,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f693,plain,
    ( r3_waybel_9(sK0,sK1,sK4(sK0,sK1))
    | ~ spl11_1
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_5
    | spl11_6 ),
    inference(unit_resulting_resolution,[],[f73,f74,f75,f124,f148,f143,f138,f133,f88])).

fof(f88,plain,(
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
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f51,f53,f52])).

fof(f52,plain,(
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

fof(f53,plain,(
    ! [X3,X0] :
      ( ? [X4] :
          ( r3_waybel_9(X0,X3,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( r3_waybel_9(X0,X3,sK4(X0,X3))
        & m1_subset_1(sK4(X0,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
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
    inference(rectify,[],[f50])).

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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

fof(f124,plain,
    ( v1_compts_1(sK0)
    | ~ spl11_1 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl11_1
  <=> v1_compts_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f692,plain,
    ( m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | ~ spl11_1
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_5
    | spl11_6 ),
    inference(unit_resulting_resolution,[],[f73,f74,f75,f124,f148,f143,f138,f133,f87])).

fof(f87,plain,(
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
    inference(cnf_transformation,[],[f54])).

fof(f133,plain,
    ( l1_waybel_0(sK1,sK0)
    | ~ spl11_3 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl11_3
  <=> l1_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f138,plain,
    ( v7_waybel_0(sK1)
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl11_4
  <=> v7_waybel_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f143,plain,
    ( v4_orders_2(sK1)
    | ~ spl11_5 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl11_5
  <=> v4_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f148,plain,
    ( ~ v2_struct_0(sK1)
    | spl11_6 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl11_6
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f158,plain,(
    l1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f75,f85])).

fof(f85,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f758,plain,
    ( r2_hidden(sK4(sK0,sK1),k1_xboole_0)
    | v2_struct_0(sK5(sK0,sK1,sK4(sK0,sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_5
    | spl11_6 ),
    inference(subsumption_resolution,[],[f757,f718])).

fof(f718,plain,
    ( v4_orders_2(sK5(sK0,sK1,sK4(sK0,sK1)))
    | ~ spl11_1
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_5
    | spl11_6 ),
    inference(unit_resulting_resolution,[],[f73,f158,f148,f143,f138,f133,f703,f110])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( v4_orders_2(X2)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f757,plain,
    ( r2_hidden(sK4(sK0,sK1),k1_xboole_0)
    | ~ v4_orders_2(sK5(sK0,sK1,sK4(sK0,sK1)))
    | v2_struct_0(sK5(sK0,sK1,sK4(sK0,sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_5
    | spl11_6 ),
    inference(subsumption_resolution,[],[f756,f719])).

fof(f719,plain,
    ( v7_waybel_0(sK5(sK0,sK1,sK4(sK0,sK1)))
    | ~ spl11_1
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_5
    | spl11_6 ),
    inference(unit_resulting_resolution,[],[f73,f158,f148,f143,f138,f133,f703,f111])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( v7_waybel_0(X2)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f756,plain,
    ( r2_hidden(sK4(sK0,sK1),k1_xboole_0)
    | ~ v7_waybel_0(sK5(sK0,sK1,sK4(sK0,sK1)))
    | ~ v4_orders_2(sK5(sK0,sK1,sK4(sK0,sK1)))
    | v2_struct_0(sK5(sK0,sK1,sK4(sK0,sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_5
    | spl11_6 ),
    inference(subsumption_resolution,[],[f755,f720])).

fof(f720,plain,
    ( l1_waybel_0(sK5(sK0,sK1,sK4(sK0,sK1)),sK0)
    | ~ spl11_1
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_5
    | spl11_6 ),
    inference(unit_resulting_resolution,[],[f73,f158,f148,f143,f138,f133,f703,f112])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(X2,X0)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f755,plain,
    ( r2_hidden(sK4(sK0,sK1),k1_xboole_0)
    | ~ l1_waybel_0(sK5(sK0,sK1,sK4(sK0,sK1)),sK0)
    | ~ v7_waybel_0(sK5(sK0,sK1,sK4(sK0,sK1)))
    | ~ v4_orders_2(sK5(sK0,sK1,sK4(sK0,sK1)))
    | v2_struct_0(sK5(sK0,sK1,sK4(sK0,sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_5
    | spl11_6 ),
    inference(subsumption_resolution,[],[f726,f716])).

fof(f716,plain,
    ( ~ v3_yellow_6(sK5(sK0,sK1,sK4(sK0,sK1)),sK0)
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_5
    | spl11_6 ),
    inference(unit_resulting_resolution,[],[f703,f128])).

fof(f128,plain,
    ( ! [X2] :
        ( ~ v3_yellow_6(X2,sK0)
        | ~ m2_yellow_6(X2,sK0,sK1) )
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl11_2
  <=> ! [X2] :
        ( ~ v3_yellow_6(X2,sK0)
        | ~ m2_yellow_6(X2,sK0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f726,plain,
    ( r2_hidden(sK4(sK0,sK1),k1_xboole_0)
    | v3_yellow_6(sK5(sK0,sK1,sK4(sK0,sK1)),sK0)
    | ~ l1_waybel_0(sK5(sK0,sK1,sK4(sK0,sK1)),sK0)
    | ~ v7_waybel_0(sK5(sK0,sK1,sK4(sK0,sK1)))
    | ~ v4_orders_2(sK5(sK0,sK1,sK4(sK0,sK1)))
    | v2_struct_0(sK5(sK0,sK1,sK4(sK0,sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_1
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_5
    | spl11_6 ),
    inference(superposition,[],[f704,f95])).

fof(f95,plain,(
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
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
         => ( v3_yellow_6(X1,X0)
          <=> k1_xboole_0 != k10_yellow_6(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_yellow_6)).

fof(f704,plain,
    ( r2_hidden(sK4(sK0,sK1),k10_yellow_6(sK0,sK5(sK0,sK1,sK4(sK0,sK1))))
    | ~ spl11_1
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_5
    | spl11_6 ),
    inference(unit_resulting_resolution,[],[f73,f74,f75,f148,f143,f138,f133,f692,f693,f98])).

fof(f98,plain,(
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
    inference(cnf_transformation,[],[f57])).

fof(f678,plain,
    ( ~ spl11_9
    | spl11_1
    | ~ spl11_7
    | ~ spl11_8 ),
    inference(avatar_split_clause,[],[f301,f155,f151,f123,f233])).

fof(f233,plain,
    ( spl11_9
  <=> r2_hidden(sK6(sK0,sK2(sK3(sK0)),k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).

fof(f151,plain,
    ( spl11_7
  <=> ! [X3] :
        ( v3_yellow_6(sK2(X3),sK0)
        | v2_struct_0(X3)
        | ~ v4_orders_2(X3)
        | ~ v7_waybel_0(X3)
        | ~ l1_waybel_0(X3,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f155,plain,
    ( spl11_8
  <=> ! [X3] :
        ( m2_yellow_6(sK2(X3),sK0,X3)
        | v2_struct_0(X3)
        | ~ v4_orders_2(X3)
        | ~ v7_waybel_0(X3)
        | ~ l1_waybel_0(X3,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f301,plain,
    ( ~ r2_hidden(sK6(sK0,sK2(sK3(sK0)),k1_xboole_0),k1_xboole_0)
    | spl11_1
    | ~ spl11_7
    | ~ spl11_8 ),
    inference(unit_resulting_resolution,[],[f83,f289,f114])).

fof(f114,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK10(X0,X1),X1)
          & r2_hidden(sK10(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f70,f71])).

fof(f71,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK10(X0,X1),X1)
        & r2_hidden(sK10(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
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

fof(f289,plain,
    ( ~ r2_hidden(sK6(sK0,sK2(sK3(sK0)),k1_xboole_0),k10_yellow_6(sK0,sK3(sK0)))
    | spl11_1
    | ~ spl11_7
    | ~ spl11_8 ),
    inference(unit_resulting_resolution,[],[f73,f74,f75,f159,f160,f161,f162,f180,f228,f96])).

fof(f96,plain,(
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
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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

fof(f228,plain,
    ( ~ r3_waybel_9(sK0,sK3(sK0),sK6(sK0,sK2(sK3(sK0)),k1_xboole_0))
    | spl11_1
    | ~ spl11_7
    | ~ spl11_8 ),
    inference(unit_resulting_resolution,[],[f73,f74,f75,f125,f180,f93])).

fof(f93,plain,(
    ! [X2,X0] :
      ( v1_compts_1(X0)
      | ~ r3_waybel_9(X0,sK3(X0),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f125,plain,
    ( ~ v1_compts_1(sK0)
    | spl11_1 ),
    inference(avatar_component_clause,[],[f123])).

fof(f180,plain,
    ( m1_subset_1(sK6(sK0,sK2(sK3(sK0)),k1_xboole_0),u1_struct_0(sK0))
    | spl11_1
    | ~ spl11_7
    | ~ spl11_8 ),
    inference(unit_resulting_resolution,[],[f73,f74,f75,f166,f167,f168,f169,f84,f177,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( k10_yellow_6(X0,X1) = X2
      | m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k10_yellow_6(X0,X1) = X2
                  | ( ( ( ~ r1_waybel_0(X0,X1,sK7(X0,X1,X2))
                        & m1_connsp_2(sK7(X0,X1,X2),X0,sK6(X0,X1,X2)) )
                      | ~ r2_hidden(sK6(X0,X1,X2),X2) )
                    & ( ! [X5] :
                          ( r1_waybel_0(X0,X1,X5)
                          | ~ m1_connsp_2(X5,X0,sK6(X0,X1,X2)) )
                      | r2_hidden(sK6(X0,X1,X2),X2) )
                    & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) ) )
                & ( ! [X6] :
                      ( ( ( r2_hidden(X6,X2)
                          | ( ~ r1_waybel_0(X0,X1,sK8(X0,X1,X6))
                            & m1_connsp_2(sK8(X0,X1,X6),X0,X6) ) )
                        & ( ! [X8] :
                              ( r1_waybel_0(X0,X1,X8)
                              | ~ m1_connsp_2(X8,X0,X6) )
                          | ~ r2_hidden(X6,X2) ) )
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | k10_yellow_6(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f60,f63,f62,f61])).

fof(f61,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ? [X4] :
                ( ~ r1_waybel_0(X0,X1,X4)
                & m1_connsp_2(X4,X0,X3) )
            | ~ r2_hidden(X3,X2) )
          & ( ! [X5] :
                ( r1_waybel_0(X0,X1,X5)
                | ~ m1_connsp_2(X5,X0,X3) )
            | r2_hidden(X3,X2) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ( ? [X4] :
              ( ~ r1_waybel_0(X0,X1,X4)
              & m1_connsp_2(X4,X0,sK6(X0,X1,X2)) )
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( ! [X5] :
              ( r1_waybel_0(X0,X1,X5)
              | ~ m1_connsp_2(X5,X0,sK6(X0,X1,X2)) )
          | r2_hidden(sK6(X0,X1,X2),X2) )
        & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_waybel_0(X0,X1,X4)
          & m1_connsp_2(X4,X0,sK6(X0,X1,X2)) )
     => ( ~ r1_waybel_0(X0,X1,sK7(X0,X1,X2))
        & m1_connsp_2(sK7(X0,X1,X2),X0,sK6(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X6,X1,X0] :
      ( ? [X7] :
          ( ~ r1_waybel_0(X0,X1,X7)
          & m1_connsp_2(X7,X0,X6) )
     => ( ~ r1_waybel_0(X0,X1,sK8(X0,X1,X6))
        & m1_connsp_2(sK8(X0,X1,X6),X0,X6) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k10_yellow_6(X0,X1) = X2
                  | ? [X3] :
                      ( ( ? [X4] :
                            ( ~ r1_waybel_0(X0,X1,X4)
                            & m1_connsp_2(X4,X0,X3) )
                        | ~ r2_hidden(X3,X2) )
                      & ( ! [X5] :
                            ( r1_waybel_0(X0,X1,X5)
                            | ~ m1_connsp_2(X5,X0,X3) )
                        | r2_hidden(X3,X2) )
                      & m1_subset_1(X3,u1_struct_0(X0)) ) )
                & ( ! [X6] :
                      ( ( ( r2_hidden(X6,X2)
                          | ? [X7] :
                              ( ~ r1_waybel_0(X0,X1,X7)
                              & m1_connsp_2(X7,X0,X6) ) )
                        & ( ! [X8] :
                              ( r1_waybel_0(X0,X1,X8)
                              | ~ m1_connsp_2(X8,X0,X6) )
                          | ~ r2_hidden(X6,X2) ) )
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | k10_yellow_6(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k10_yellow_6(X0,X1) = X2
                  | ? [X3] :
                      ( ( ? [X4] :
                            ( ~ r1_waybel_0(X0,X1,X4)
                            & m1_connsp_2(X4,X0,X3) )
                        | ~ r2_hidden(X3,X2) )
                      & ( ! [X4] :
                            ( r1_waybel_0(X0,X1,X4)
                            | ~ m1_connsp_2(X4,X0,X3) )
                        | r2_hidden(X3,X2) )
                      & m1_subset_1(X3,u1_struct_0(X0)) ) )
                & ( ! [X3] :
                      ( ( ( r2_hidden(X3,X2)
                          | ? [X4] :
                              ( ~ r1_waybel_0(X0,X1,X4)
                              & m1_connsp_2(X4,X0,X3) ) )
                        & ( ! [X4] :
                              ( r1_waybel_0(X0,X1,X4)
                              | ~ m1_connsp_2(X4,X0,X3) )
                          | ~ r2_hidden(X3,X2) ) )
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | k10_yellow_6(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k10_yellow_6(X0,X1) = X2
                  | ? [X3] :
                      ( ( ? [X4] :
                            ( ~ r1_waybel_0(X0,X1,X4)
                            & m1_connsp_2(X4,X0,X3) )
                        | ~ r2_hidden(X3,X2) )
                      & ( ! [X4] :
                            ( r1_waybel_0(X0,X1,X4)
                            | ~ m1_connsp_2(X4,X0,X3) )
                        | r2_hidden(X3,X2) )
                      & m1_subset_1(X3,u1_struct_0(X0)) ) )
                & ( ! [X3] :
                      ( ( ( r2_hidden(X3,X2)
                          | ? [X4] :
                              ( ~ r1_waybel_0(X0,X1,X4)
                              & m1_connsp_2(X4,X0,X3) ) )
                        & ( ! [X4] :
                              ( r1_waybel_0(X0,X1,X4)
                              | ~ m1_connsp_2(X4,X0,X3) )
                          | ~ r2_hidden(X3,X2) ) )
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | k10_yellow_6(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k10_yellow_6(X0,X1) = X2
              <=> ! [X3] :
                    ( ( r2_hidden(X3,X2)
                    <=> ! [X4] :
                          ( r1_waybel_0(X0,X1,X4)
                          | ~ m1_connsp_2(X4,X0,X3) ) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k10_yellow_6(X0,X1) = X2
              <=> ! [X3] :
                    ( ( r2_hidden(X3,X2)
                    <=> ! [X4] :
                          ( r1_waybel_0(X0,X1,X4)
                          | ~ m1_connsp_2(X4,X0,X3) ) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( k10_yellow_6(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_hidden(X3,X2)
                    <=> ! [X4] :
                          ( m1_connsp_2(X4,X0,X3)
                         => r1_waybel_0(X0,X1,X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_yellow_6)).

fof(f177,plain,
    ( k1_xboole_0 != k10_yellow_6(sK0,sK2(sK3(sK0)))
    | spl11_1
    | ~ spl11_7
    | ~ spl11_8 ),
    inference(unit_resulting_resolution,[],[f73,f74,f75,f166,f167,f168,f164,f169,f94])).

fof(f94,plain,(
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
    inference(cnf_transformation,[],[f55])).

fof(f164,plain,
    ( v3_yellow_6(sK2(sK3(sK0)),sK0)
    | spl11_1
    | ~ spl11_7 ),
    inference(unit_resulting_resolution,[],[f161,f159,f160,f162,f152])).

fof(f152,plain,
    ( ! [X3] :
        ( ~ v7_waybel_0(X3)
        | v2_struct_0(X3)
        | ~ v4_orders_2(X3)
        | v3_yellow_6(sK2(X3),sK0)
        | ~ l1_waybel_0(X3,sK0) )
    | ~ spl11_7 ),
    inference(avatar_component_clause,[],[f151])).

fof(f84,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f169,plain,
    ( l1_waybel_0(sK2(sK3(sK0)),sK0)
    | spl11_1
    | ~ spl11_8 ),
    inference(unit_resulting_resolution,[],[f73,f158,f159,f160,f161,f162,f163,f112])).

fof(f163,plain,
    ( m2_yellow_6(sK2(sK3(sK0)),sK0,sK3(sK0))
    | spl11_1
    | ~ spl11_8 ),
    inference(unit_resulting_resolution,[],[f161,f159,f160,f162,f156])).

fof(f156,plain,
    ( ! [X3] :
        ( ~ v7_waybel_0(X3)
        | v2_struct_0(X3)
        | ~ v4_orders_2(X3)
        | m2_yellow_6(sK2(X3),sK0,X3)
        | ~ l1_waybel_0(X3,sK0) )
    | ~ spl11_8 ),
    inference(avatar_component_clause,[],[f155])).

fof(f168,plain,
    ( v7_waybel_0(sK2(sK3(sK0)))
    | spl11_1
    | ~ spl11_8 ),
    inference(unit_resulting_resolution,[],[f73,f158,f159,f160,f161,f162,f163,f111])).

fof(f167,plain,
    ( v4_orders_2(sK2(sK3(sK0)))
    | spl11_1
    | ~ spl11_8 ),
    inference(unit_resulting_resolution,[],[f73,f158,f159,f160,f161,f162,f163,f110])).

fof(f166,plain,
    ( ~ v2_struct_0(sK2(sK3(sK0)))
    | spl11_1
    | ~ spl11_8 ),
    inference(unit_resulting_resolution,[],[f73,f158,f159,f160,f161,f162,f163,f109])).

fof(f162,plain,
    ( l1_waybel_0(sK3(sK0),sK0)
    | spl11_1 ),
    inference(unit_resulting_resolution,[],[f73,f74,f75,f125,f92])).

fof(f92,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | l1_waybel_0(sK3(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f161,plain,
    ( v7_waybel_0(sK3(sK0))
    | spl11_1 ),
    inference(unit_resulting_resolution,[],[f73,f74,f75,f125,f91])).

fof(f91,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | v7_waybel_0(sK3(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f160,plain,
    ( v4_orders_2(sK3(sK0))
    | spl11_1 ),
    inference(unit_resulting_resolution,[],[f73,f74,f75,f125,f90])).

fof(f90,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | v4_orders_2(sK3(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f159,plain,
    ( ~ v2_struct_0(sK3(sK0))
    | spl11_1 ),
    inference(unit_resulting_resolution,[],[f73,f74,f75,f125,f89])).

fof(f89,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | ~ v2_struct_0(sK3(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f663,plain,
    ( spl11_1
    | ~ spl11_7
    | ~ spl11_8
    | spl11_9 ),
    inference(avatar_contradiction_clause,[],[f662])).

fof(f662,plain,
    ( $false
    | spl11_1
    | ~ spl11_7
    | ~ spl11_8
    | spl11_9 ),
    inference(subsumption_resolution,[],[f658,f520])).

fof(f520,plain,
    ( m1_connsp_2(sK8(sK0,sK2(sK3(sK0)),sK6(sK0,sK2(sK3(sK0)),k1_xboole_0)),sK0,sK6(sK0,sK2(sK3(sK0)),k1_xboole_0))
    | spl11_1
    | ~ spl11_7
    | ~ spl11_8 ),
    inference(unit_resulting_resolution,[],[f73,f74,f75,f166,f167,f168,f169,f178,f180,f416,f120])).

fof(f120,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(X6,k10_yellow_6(X0,X1))
      | m1_connsp_2(sK8(X0,X1,X6),X0,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f100])).

fof(f100,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,X2)
      | m1_connsp_2(sK8(X0,X1,X6),X0,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | k10_yellow_6(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f416,plain,
    ( ~ r2_hidden(sK6(sK0,sK2(sK3(sK0)),k1_xboole_0),k10_yellow_6(sK0,sK2(sK3(sK0))))
    | spl11_1
    | ~ spl11_7
    | ~ spl11_8 ),
    inference(unit_resulting_resolution,[],[f73,f74,f75,f166,f167,f168,f169,f180,f405,f96])).

fof(f405,plain,
    ( ~ r3_waybel_9(sK0,sK2(sK3(sK0)),sK6(sK0,sK2(sK3(sK0)),k1_xboole_0))
    | spl11_1
    | ~ spl11_7
    | ~ spl11_8 ),
    inference(unit_resulting_resolution,[],[f73,f74,f75,f166,f169,f180,f287,f335,f106])).

fof(f106,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_waybel_0(X0,X1,X4)
      | ~ m1_connsp_2(X4,X0,X2)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_waybel_9(X0,X1,X2)
                  | ( ~ r2_waybel_0(X0,X1,sK9(X0,X1,X2))
                    & m1_connsp_2(sK9(X0,X1,X2),X0,X2) ) )
                & ( ! [X4] :
                      ( r2_waybel_0(X0,X1,X4)
                      | ~ m1_connsp_2(X4,X0,X2) )
                  | ~ r3_waybel_9(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f66,f67])).

fof(f67,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_waybel_0(X0,X1,X3)
          & m1_connsp_2(X3,X0,X2) )
     => ( ~ r2_waybel_0(X0,X1,sK9(X0,X1,X2))
        & m1_connsp_2(sK9(X0,X1,X2),X0,X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_waybel_9(X0,X1,X2)
                  | ? [X3] :
                      ( ~ r2_waybel_0(X0,X1,X3)
                      & m1_connsp_2(X3,X0,X2) ) )
                & ( ! [X4] :
                      ( r2_waybel_0(X0,X1,X4)
                      | ~ m1_connsp_2(X4,X0,X2) )
                  | ~ r3_waybel_9(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_waybel_9(X0,X1,X2)
                  | ? [X3] :
                      ( ~ r2_waybel_0(X0,X1,X3)
                      & m1_connsp_2(X3,X0,X2) ) )
                & ( ! [X3] :
                      ( r2_waybel_0(X0,X1,X3)
                      | ~ m1_connsp_2(X3,X0,X2) )
                  | ~ r3_waybel_9(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_waybel_9(X0,X1,X2)
              <=> ! [X3] :
                    ( r2_waybel_0(X0,X1,X3)
                    | ~ m1_connsp_2(X3,X0,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_waybel_9(X0,X1,X2)
              <=> ! [X3] :
                    ( r2_waybel_0(X0,X1,X3)
                    | ~ m1_connsp_2(X3,X0,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
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
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r3_waybel_9(X0,X1,X2)
              <=> ! [X3] :
                    ( m1_connsp_2(X3,X0,X2)
                   => r2_waybel_0(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_waybel_9)).

fof(f335,plain,
    ( ~ r2_waybel_0(sK0,sK2(sK3(sK0)),sK9(sK0,sK3(sK0),sK6(sK0,sK2(sK3(sK0)),k1_xboole_0)))
    | spl11_1
    | ~ spl11_7
    | ~ spl11_8 ),
    inference(unit_resulting_resolution,[],[f73,f158,f159,f160,f161,f162,f163,f288,f86])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_waybel_0(X0,X1,X3)
      | ~ r2_waybel_0(X0,X2,X3)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_waybel_0(X0,X1,X3)
                  | ~ r2_waybel_0(X0,X2,X3) )
              | ~ m2_yellow_6(X2,X0,X1) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_waybel_0(X0,X1,X3)
                  | ~ r2_waybel_0(X0,X2,X3) )
              | ~ m2_yellow_6(X2,X0,X1) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m2_yellow_6(X2,X0,X1)
             => ! [X3] :
                  ( r2_waybel_0(X0,X2,X3)
                 => r2_waybel_0(X0,X1,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_yellow_6)).

fof(f288,plain,
    ( ~ r2_waybel_0(sK0,sK3(sK0),sK9(sK0,sK3(sK0),sK6(sK0,sK2(sK3(sK0)),k1_xboole_0)))
    | spl11_1
    | ~ spl11_7
    | ~ spl11_8 ),
    inference(unit_resulting_resolution,[],[f73,f74,f75,f159,f162,f180,f228,f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( r3_waybel_9(X0,X1,X2)
      | ~ r2_waybel_0(X0,X1,sK9(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f287,plain,
    ( m1_connsp_2(sK9(sK0,sK3(sK0),sK6(sK0,sK2(sK3(sK0)),k1_xboole_0)),sK0,sK6(sK0,sK2(sK3(sK0)),k1_xboole_0))
    | spl11_1
    | ~ spl11_7
    | ~ spl11_8 ),
    inference(unit_resulting_resolution,[],[f73,f74,f75,f159,f162,f180,f228,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( r3_waybel_9(X0,X1,X2)
      | m1_connsp_2(sK9(X0,X1,X2),X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f178,plain,
    ( m1_subset_1(k10_yellow_6(sK0,sK2(sK3(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl11_1
    | ~ spl11_8 ),
    inference(unit_resulting_resolution,[],[f73,f74,f75,f166,f167,f168,f169,f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f658,plain,
    ( ~ m1_connsp_2(sK8(sK0,sK2(sK3(sK0)),sK6(sK0,sK2(sK3(sK0)),k1_xboole_0)),sK0,sK6(sK0,sK2(sK3(sK0)),k1_xboole_0))
    | spl11_1
    | ~ spl11_7
    | ~ spl11_8
    | spl11_9 ),
    inference(unit_resulting_resolution,[],[f521,f244])).

fof(f244,plain,
    ( ! [X0] :
        ( r1_waybel_0(sK0,sK2(sK3(sK0)),X0)
        | ~ m1_connsp_2(X0,sK0,sK6(sK0,sK2(sK3(sK0)),k1_xboole_0)) )
    | spl11_1
    | ~ spl11_7
    | ~ spl11_8
    | spl11_9 ),
    inference(subsumption_resolution,[],[f243,f84])).

fof(f243,plain,
    ( ! [X0] :
        ( r1_waybel_0(sK0,sK2(sK3(sK0)),X0)
        | ~ m1_connsp_2(X0,sK0,sK6(sK0,sK2(sK3(sK0)),k1_xboole_0))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl11_1
    | ~ spl11_7
    | ~ spl11_8
    | spl11_9 ),
    inference(subsumption_resolution,[],[f242,f235])).

fof(f235,plain,
    ( ~ r2_hidden(sK6(sK0,sK2(sK3(sK0)),k1_xboole_0),k1_xboole_0)
    | spl11_9 ),
    inference(avatar_component_clause,[],[f233])).

fof(f242,plain,
    ( ! [X0] :
        ( r1_waybel_0(sK0,sK2(sK3(sK0)),X0)
        | ~ m1_connsp_2(X0,sK0,sK6(sK0,sK2(sK3(sK0)),k1_xboole_0))
        | r2_hidden(sK6(sK0,sK2(sK3(sK0)),k1_xboole_0),k1_xboole_0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl11_1
    | ~ spl11_7
    | ~ spl11_8 ),
    inference(equality_resolution,[],[f200])).

fof(f200,plain,
    ( ! [X2,X1] :
        ( k1_xboole_0 != X1
        | r1_waybel_0(sK0,sK2(sK3(sK0)),X2)
        | ~ m1_connsp_2(X2,sK0,sK6(sK0,sK2(sK3(sK0)),X1))
        | r2_hidden(sK6(sK0,sK2(sK3(sK0)),X1),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl11_1
    | ~ spl11_7
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f199,f73])).

fof(f199,plain,
    ( ! [X2,X1] :
        ( k1_xboole_0 != X1
        | r1_waybel_0(sK0,sK2(sK3(sK0)),X2)
        | ~ m1_connsp_2(X2,sK0,sK6(sK0,sK2(sK3(sK0)),X1))
        | r2_hidden(sK6(sK0,sK2(sK3(sK0)),X1),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_struct_0(sK0) )
    | spl11_1
    | ~ spl11_7
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f198,f74])).

fof(f198,plain,
    ( ! [X2,X1] :
        ( k1_xboole_0 != X1
        | r1_waybel_0(sK0,sK2(sK3(sK0)),X2)
        | ~ m1_connsp_2(X2,sK0,sK6(sK0,sK2(sK3(sK0)),X1))
        | r2_hidden(sK6(sK0,sK2(sK3(sK0)),X1),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl11_1
    | ~ spl11_7
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f197,f75])).

fof(f197,plain,
    ( ! [X2,X1] :
        ( k1_xboole_0 != X1
        | r1_waybel_0(sK0,sK2(sK3(sK0)),X2)
        | ~ m1_connsp_2(X2,sK0,sK6(sK0,sK2(sK3(sK0)),X1))
        | r2_hidden(sK6(sK0,sK2(sK3(sK0)),X1),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl11_1
    | ~ spl11_7
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f196,f166])).

fof(f196,plain,
    ( ! [X2,X1] :
        ( k1_xboole_0 != X1
        | r1_waybel_0(sK0,sK2(sK3(sK0)),X2)
        | ~ m1_connsp_2(X2,sK0,sK6(sK0,sK2(sK3(sK0)),X1))
        | r2_hidden(sK6(sK0,sK2(sK3(sK0)),X1),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_struct_0(sK2(sK3(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl11_1
    | ~ spl11_7
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f195,f167])).

fof(f195,plain,
    ( ! [X2,X1] :
        ( k1_xboole_0 != X1
        | r1_waybel_0(sK0,sK2(sK3(sK0)),X2)
        | ~ m1_connsp_2(X2,sK0,sK6(sK0,sK2(sK3(sK0)),X1))
        | r2_hidden(sK6(sK0,sK2(sK3(sK0)),X1),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_orders_2(sK2(sK3(sK0)))
        | v2_struct_0(sK2(sK3(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl11_1
    | ~ spl11_7
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f194,f168])).

fof(f194,plain,
    ( ! [X2,X1] :
        ( k1_xboole_0 != X1
        | r1_waybel_0(sK0,sK2(sK3(sK0)),X2)
        | ~ m1_connsp_2(X2,sK0,sK6(sK0,sK2(sK3(sK0)),X1))
        | r2_hidden(sK6(sK0,sK2(sK3(sK0)),X1),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v7_waybel_0(sK2(sK3(sK0)))
        | ~ v4_orders_2(sK2(sK3(sK0)))
        | v2_struct_0(sK2(sK3(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl11_1
    | ~ spl11_7
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f182,f169])).

fof(f182,plain,
    ( ! [X2,X1] :
        ( k1_xboole_0 != X1
        | r1_waybel_0(sK0,sK2(sK3(sK0)),X2)
        | ~ m1_connsp_2(X2,sK0,sK6(sK0,sK2(sK3(sK0)),X1))
        | r2_hidden(sK6(sK0,sK2(sK3(sK0)),X1),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_waybel_0(sK2(sK3(sK0)),sK0)
        | ~ v7_waybel_0(sK2(sK3(sK0)))
        | ~ v4_orders_2(sK2(sK3(sK0)))
        | v2_struct_0(sK2(sK3(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl11_1
    | ~ spl11_7
    | ~ spl11_8 ),
    inference(superposition,[],[f177,f103])).

fof(f103,plain,(
    ! [X2,X0,X5,X1] :
      ( k10_yellow_6(X0,X1) = X2
      | r1_waybel_0(X0,X1,X5)
      | ~ m1_connsp_2(X5,X0,sK6(X0,X1,X2))
      | r2_hidden(sK6(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f521,plain,
    ( ~ r1_waybel_0(sK0,sK2(sK3(sK0)),sK8(sK0,sK2(sK3(sK0)),sK6(sK0,sK2(sK3(sK0)),k1_xboole_0)))
    | spl11_1
    | ~ spl11_7
    | ~ spl11_8 ),
    inference(unit_resulting_resolution,[],[f73,f74,f75,f166,f167,f168,f169,f178,f180,f416,f119])).

fof(f119,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(X6,k10_yellow_6(X0,X1))
      | ~ r1_waybel_0(X0,X1,sK8(X0,X1,X6))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f101])).

fof(f101,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,X2)
      | ~ r1_waybel_0(X0,X1,sK8(X0,X1,X6))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | k10_yellow_6(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f157,plain,
    ( spl11_1
    | spl11_8 ),
    inference(avatar_split_clause,[],[f76,f155,f123])).

fof(f76,plain,(
    ! [X3] :
      ( m2_yellow_6(sK2(X3),sK0,X3)
      | ~ l1_waybel_0(X3,sK0)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | v1_compts_1(sK0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f153,plain,
    ( spl11_1
    | spl11_7 ),
    inference(avatar_split_clause,[],[f77,f151,f123])).

fof(f77,plain,(
    ! [X3] :
      ( v3_yellow_6(sK2(X3),sK0)
      | ~ l1_waybel_0(X3,sK0)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | v1_compts_1(sK0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f149,plain,
    ( ~ spl11_1
    | ~ spl11_6 ),
    inference(avatar_split_clause,[],[f78,f146,f123])).

fof(f78,plain,
    ( ~ v2_struct_0(sK1)
    | ~ v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f144,plain,
    ( ~ spl11_1
    | spl11_5 ),
    inference(avatar_split_clause,[],[f79,f141,f123])).

fof(f79,plain,
    ( v4_orders_2(sK1)
    | ~ v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f139,plain,
    ( ~ spl11_1
    | spl11_4 ),
    inference(avatar_split_clause,[],[f80,f136,f123])).

fof(f80,plain,
    ( v7_waybel_0(sK1)
    | ~ v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f134,plain,
    ( ~ spl11_1
    | spl11_3 ),
    inference(avatar_split_clause,[],[f81,f131,f123])).

fof(f81,plain,
    ( l1_waybel_0(sK1,sK0)
    | ~ v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f129,plain,
    ( ~ spl11_1
    | spl11_2 ),
    inference(avatar_split_clause,[],[f82,f127,f123])).

fof(f82,plain,(
    ! [X2] :
      ( ~ v3_yellow_6(X2,sK0)
      | ~ m2_yellow_6(X2,sK0,sK1)
      | ~ v1_compts_1(sK0) ) ),
    inference(cnf_transformation,[],[f49])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:08:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.53  % (19415)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.39/0.53  % (19417)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.39/0.53  % (19431)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.39/0.54  % (19414)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.39/0.54  % (19416)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.39/0.54  % (19419)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.39/0.54  % (19412)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.39/0.54  % (19429)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.39/0.54  % (19413)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.39/0.54  % (19423)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.39/0.55  % (19425)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.39/0.55  % (19430)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.39/0.55  % (19434)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.39/0.55  % (19424)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.39/0.55  % (19439)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.39/0.55  % (19422)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.39/0.55  % (19426)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.39/0.55  % (19432)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.39/0.56  % (19433)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.39/0.56  % (19421)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.53/0.56  % (19437)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.53/0.56  % (19418)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.53/0.56  % (19438)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.53/0.56  % (19441)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.53/0.57  % (19440)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.53/0.57  % (19429)Refutation not found, incomplete strategy% (19429)------------------------------
% 1.53/0.57  % (19429)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.57  % (19429)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.57  
% 1.53/0.57  % (19429)Memory used [KB]: 10746
% 1.53/0.57  % (19429)Time elapsed: 0.156 s
% 1.53/0.57  % (19429)------------------------------
% 1.53/0.57  % (19429)------------------------------
% 1.53/0.57  % (19434)Refutation not found, incomplete strategy% (19434)------------------------------
% 1.53/0.57  % (19434)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.57  % (19434)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.57  
% 1.53/0.57  % (19434)Memory used [KB]: 11001
% 1.53/0.57  % (19434)Time elapsed: 0.115 s
% 1.53/0.57  % (19434)------------------------------
% 1.53/0.57  % (19434)------------------------------
% 1.53/0.57  % (19428)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.53/0.58  % (19422)Refutation not found, incomplete strategy% (19422)------------------------------
% 1.53/0.58  % (19422)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.58  % (19436)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.53/0.58  % (19422)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.58  
% 1.53/0.58  % (19422)Memory used [KB]: 10746
% 1.53/0.58  % (19422)Time elapsed: 0.167 s
% 1.53/0.58  % (19422)------------------------------
% 1.53/0.58  % (19422)------------------------------
% 1.53/0.59  % (19435)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.53/0.59  % (19427)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.53/0.59  % (19420)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.53/0.64  % (19438)Refutation found. Thanks to Tanya!
% 1.53/0.64  % SZS status Theorem for theBenchmark
% 2.22/0.65  % SZS output start Proof for theBenchmark
% 2.22/0.65  fof(f770,plain,(
% 2.22/0.65    $false),
% 2.22/0.65    inference(avatar_sat_refutation,[],[f129,f134,f139,f144,f149,f153,f157,f663,f678,f769])).
% 2.22/0.65  fof(f769,plain,(
% 2.22/0.65    ~spl11_1 | ~spl11_2 | ~spl11_3 | ~spl11_4 | ~spl11_5 | spl11_6),
% 2.22/0.65    inference(avatar_contradiction_clause,[],[f768])).
% 2.22/0.65  fof(f768,plain,(
% 2.22/0.65    $false | (~spl11_1 | ~spl11_2 | ~spl11_3 | ~spl11_4 | ~spl11_5 | spl11_6)),
% 2.22/0.65    inference(subsumption_resolution,[],[f764,f83])).
% 2.22/0.65  fof(f83,plain,(
% 2.22/0.65    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.22/0.65    inference(cnf_transformation,[],[f2])).
% 2.22/0.65  fof(f2,axiom,(
% 2.22/0.65    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.22/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 2.22/0.65  fof(f764,plain,(
% 2.22/0.65    ~r1_tarski(k1_xboole_0,sK4(sK0,sK1)) | (~spl11_1 | ~spl11_2 | ~spl11_3 | ~spl11_4 | ~spl11_5 | spl11_6)),
% 2.22/0.65    inference(unit_resulting_resolution,[],[f762,f117])).
% 2.22/0.65  fof(f117,plain,(
% 2.22/0.65    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.22/0.65    inference(cnf_transformation,[],[f40])).
% 2.22/0.65  fof(f40,plain,(
% 2.22/0.65    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.22/0.65    inference(ennf_transformation,[],[f5])).
% 2.22/0.65  fof(f5,axiom,(
% 2.22/0.65    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.22/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 2.22/0.65  fof(f762,plain,(
% 2.22/0.65    r2_hidden(sK4(sK0,sK1),k1_xboole_0) | (~spl11_1 | ~spl11_2 | ~spl11_3 | ~spl11_4 | ~spl11_5 | spl11_6)),
% 2.22/0.65    inference(subsumption_resolution,[],[f761,f73])).
% 2.22/0.65  fof(f73,plain,(
% 2.22/0.65    ~v2_struct_0(sK0)),
% 2.22/0.65    inference(cnf_transformation,[],[f49])).
% 2.22/0.65  fof(f49,plain,(
% 2.22/0.65    ((! [X2] : (~v3_yellow_6(X2,sK0) | ~m2_yellow_6(X2,sK0,sK1)) & l1_waybel_0(sK1,sK0) & v7_waybel_0(sK1) & v4_orders_2(sK1) & ~v2_struct_0(sK1)) | ~v1_compts_1(sK0)) & (! [X3] : ((v3_yellow_6(sK2(X3),sK0) & m2_yellow_6(sK2(X3),sK0,X3)) | ~l1_waybel_0(X3,sK0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(sK0)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 2.22/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f45,f48,f47,f46])).
% 2.22/0.65  fof(f46,plain,(
% 2.22/0.65    ? [X0] : ((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X3] : (? [X4] : (v3_yellow_6(X4,X0) & m2_yellow_6(X4,X0,X3)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ((? [X1] : (! [X2] : (~v3_yellow_6(X2,sK0) | ~m2_yellow_6(X2,sK0,X1)) & l1_waybel_0(X1,sK0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(sK0)) & (! [X3] : (? [X4] : (v3_yellow_6(X4,sK0) & m2_yellow_6(X4,sK0,X3)) | ~l1_waybel_0(X3,sK0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(sK0)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 2.22/0.65    introduced(choice_axiom,[])).
% 2.22/0.65  fof(f47,plain,(
% 2.22/0.65    ? [X1] : (! [X2] : (~v3_yellow_6(X2,sK0) | ~m2_yellow_6(X2,sK0,X1)) & l1_waybel_0(X1,sK0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (! [X2] : (~v3_yellow_6(X2,sK0) | ~m2_yellow_6(X2,sK0,sK1)) & l1_waybel_0(sK1,sK0) & v7_waybel_0(sK1) & v4_orders_2(sK1) & ~v2_struct_0(sK1))),
% 2.22/0.65    introduced(choice_axiom,[])).
% 2.22/0.65  fof(f48,plain,(
% 2.22/0.65    ! [X3] : (? [X4] : (v3_yellow_6(X4,sK0) & m2_yellow_6(X4,sK0,X3)) => (v3_yellow_6(sK2(X3),sK0) & m2_yellow_6(sK2(X3),sK0,X3)))),
% 2.22/0.65    introduced(choice_axiom,[])).
% 2.22/0.65  fof(f45,plain,(
% 2.22/0.65    ? [X0] : ((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X3] : (? [X4] : (v3_yellow_6(X4,X0) & m2_yellow_6(X4,X0,X3)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.22/0.65    inference(rectify,[],[f44])).
% 2.22/0.65  fof(f44,plain,(
% 2.22/0.65    ? [X0] : ((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | v1_compts_1(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.22/0.65    inference(flattening,[],[f43])).
% 2.22/0.65  fof(f43,plain,(
% 2.22/0.65    ? [X0] : (((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | v1_compts_1(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.22/0.65    inference(nnf_transformation,[],[f19])).
% 2.22/0.65  fof(f19,plain,(
% 2.22/0.65    ? [X0] : ((v1_compts_1(X0) <~> ! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.22/0.65    inference(flattening,[],[f18])).
% 2.22/0.65  fof(f18,plain,(
% 2.22/0.65    ? [X0] : ((v1_compts_1(X0) <~> ! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.22/0.65    inference(ennf_transformation,[],[f17])).
% 2.22/0.65  fof(f17,negated_conjecture,(
% 2.22/0.65    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)))))),
% 2.22/0.65    inference(negated_conjecture,[],[f16])).
% 2.22/0.65  fof(f16,conjecture,(
% 2.22/0.65    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)))))),
% 2.22/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_yellow19)).
% 2.22/0.65  fof(f761,plain,(
% 2.22/0.65    r2_hidden(sK4(sK0,sK1),k1_xboole_0) | v2_struct_0(sK0) | (~spl11_1 | ~spl11_2 | ~spl11_3 | ~spl11_4 | ~spl11_5 | spl11_6)),
% 2.22/0.65    inference(subsumption_resolution,[],[f760,f74])).
% 2.22/0.65  fof(f74,plain,(
% 2.22/0.65    v2_pre_topc(sK0)),
% 2.22/0.65    inference(cnf_transformation,[],[f49])).
% 2.22/0.65  fof(f760,plain,(
% 2.22/0.65    r2_hidden(sK4(sK0,sK1),k1_xboole_0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl11_1 | ~spl11_2 | ~spl11_3 | ~spl11_4 | ~spl11_5 | spl11_6)),
% 2.22/0.65    inference(subsumption_resolution,[],[f759,f75])).
% 2.22/0.65  fof(f75,plain,(
% 2.22/0.65    l1_pre_topc(sK0)),
% 2.22/0.65    inference(cnf_transformation,[],[f49])).
% 2.22/0.65  fof(f759,plain,(
% 2.22/0.65    r2_hidden(sK4(sK0,sK1),k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl11_1 | ~spl11_2 | ~spl11_3 | ~spl11_4 | ~spl11_5 | spl11_6)),
% 2.22/0.65    inference(subsumption_resolution,[],[f758,f717])).
% 2.22/0.65  fof(f717,plain,(
% 2.22/0.65    ~v2_struct_0(sK5(sK0,sK1,sK4(sK0,sK1))) | (~spl11_1 | ~spl11_3 | ~spl11_4 | ~spl11_5 | spl11_6)),
% 2.22/0.65    inference(unit_resulting_resolution,[],[f73,f158,f148,f143,f138,f133,f703,f109])).
% 2.22/0.65  fof(f109,plain,(
% 2.22/0.65    ( ! [X2,X0,X1] : (~v2_struct_0(X2) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.22/0.65    inference(cnf_transformation,[],[f36])).
% 2.22/0.65  fof(f36,plain,(
% 2.22/0.65    ! [X0,X1] : (! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.22/0.65    inference(flattening,[],[f35])).
% 2.22/0.65  fof(f35,plain,(
% 2.22/0.65    ! [X0,X1] : (! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.22/0.65    inference(ennf_transformation,[],[f9])).
% 2.22/0.65  fof(f9,axiom,(
% 2.22/0.65    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_yellow_6(X2,X0,X1) => (l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2))))),
% 2.22/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_yellow_6)).
% 2.22/0.65  fof(f703,plain,(
% 2.22/0.65    m2_yellow_6(sK5(sK0,sK1,sK4(sK0,sK1)),sK0,sK1) | (~spl11_1 | ~spl11_3 | ~spl11_4 | ~spl11_5 | spl11_6)),
% 2.22/0.65    inference(unit_resulting_resolution,[],[f73,f74,f75,f148,f143,f138,f133,f692,f693,f97])).
% 2.22/0.65  fof(f97,plain,(
% 2.22/0.65    ( ! [X2,X0,X1] : (m2_yellow_6(sK5(X0,X1,X2),X0,X1) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.22/0.65    inference(cnf_transformation,[],[f57])).
% 2.22/0.65  fof(f57,plain,(
% 2.22/0.65    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k10_yellow_6(X0,sK5(X0,X1,X2))) & m2_yellow_6(sK5(X0,X1,X2),X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.22/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f30,f56])).
% 2.22/0.65  fof(f56,plain,(
% 2.22/0.65    ! [X2,X1,X0] : (? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) => (r2_hidden(X2,k10_yellow_6(X0,sK5(X0,X1,X2))) & m2_yellow_6(sK5(X0,X1,X2),X0,X1)))),
% 2.22/0.65    introduced(choice_axiom,[])).
% 2.22/0.65  fof(f30,plain,(
% 2.22/0.65    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.22/0.65    inference(flattening,[],[f29])).
% 2.22/0.65  fof(f29,plain,(
% 2.22/0.65    ! [X0] : (! [X1] : (! [X2] : ((? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) | ~r3_waybel_9(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.22/0.65    inference(ennf_transformation,[],[f14])).
% 2.22/0.65  fof(f14,axiom,(
% 2.22/0.65    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m2_yellow_6(X3,X0,X1) => ~r2_hidden(X2,k10_yellow_6(X0,X3))) & r3_waybel_9(X0,X1,X2)))))),
% 2.22/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_waybel_9)).
% 2.22/0.65  fof(f693,plain,(
% 2.22/0.65    r3_waybel_9(sK0,sK1,sK4(sK0,sK1)) | (~spl11_1 | ~spl11_3 | ~spl11_4 | ~spl11_5 | spl11_6)),
% 2.22/0.65    inference(unit_resulting_resolution,[],[f73,f74,f75,f124,f148,f143,f138,f133,f88])).
% 2.22/0.65  fof(f88,plain,(
% 2.22/0.65    ( ! [X0,X3] : (r3_waybel_9(X0,X3,sK4(X0,X3)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | ~v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.22/0.65    inference(cnf_transformation,[],[f54])).
% 2.22/0.65  fof(f54,plain,(
% 2.22/0.65    ! [X0] : (((v1_compts_1(X0) | (! [X2] : (~r3_waybel_9(X0,sK3(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(sK3(X0),X0) & v7_waybel_0(sK3(X0)) & v4_orders_2(sK3(X0)) & ~v2_struct_0(sK3(X0)))) & (! [X3] : ((r3_waybel_9(X0,X3,sK4(X0,X3)) & m1_subset_1(sK4(X0,X3),u1_struct_0(X0))) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.22/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f51,f53,f52])).
% 2.22/0.65  fof(f52,plain,(
% 2.22/0.65    ! [X0] : (? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (! [X2] : (~r3_waybel_9(X0,sK3(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(sK3(X0),X0) & v7_waybel_0(sK3(X0)) & v4_orders_2(sK3(X0)) & ~v2_struct_0(sK3(X0))))),
% 2.22/0.65    introduced(choice_axiom,[])).
% 2.22/0.65  fof(f53,plain,(
% 2.22/0.65    ! [X3,X0] : (? [X4] : (r3_waybel_9(X0,X3,X4) & m1_subset_1(X4,u1_struct_0(X0))) => (r3_waybel_9(X0,X3,sK4(X0,X3)) & m1_subset_1(sK4(X0,X3),u1_struct_0(X0))))),
% 2.22/0.65    introduced(choice_axiom,[])).
% 2.22/0.65  fof(f51,plain,(
% 2.22/0.65    ! [X0] : (((v1_compts_1(X0) | ? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (! [X3] : (? [X4] : (r3_waybel_9(X0,X3,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.22/0.65    inference(rectify,[],[f50])).
% 2.22/0.65  fof(f50,plain,(
% 2.22/0.65    ! [X0] : (((v1_compts_1(X0) | ? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.22/0.65    inference(nnf_transformation,[],[f24])).
% 2.22/0.65  fof(f24,plain,(
% 2.22/0.65    ! [X0] : ((v1_compts_1(X0) <=> ! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.22/0.65    inference(flattening,[],[f23])).
% 2.22/0.65  fof(f23,plain,(
% 2.22/0.65    ! [X0] : ((v1_compts_1(X0) <=> ! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.22/0.65    inference(ennf_transformation,[],[f15])).
% 2.22/0.65  fof(f15,axiom,(
% 2.22/0.65    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))))))),
% 2.22/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_yellow19)).
% 2.22/0.65  fof(f124,plain,(
% 2.22/0.65    v1_compts_1(sK0) | ~spl11_1),
% 2.22/0.65    inference(avatar_component_clause,[],[f123])).
% 2.22/0.65  fof(f123,plain,(
% 2.22/0.65    spl11_1 <=> v1_compts_1(sK0)),
% 2.22/0.65    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 2.22/0.65  fof(f692,plain,(
% 2.22/0.65    m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0)) | (~spl11_1 | ~spl11_3 | ~spl11_4 | ~spl11_5 | spl11_6)),
% 2.22/0.65    inference(unit_resulting_resolution,[],[f73,f74,f75,f124,f148,f143,f138,f133,f87])).
% 2.22/0.65  fof(f87,plain,(
% 2.22/0.65    ( ! [X0,X3] : (m1_subset_1(sK4(X0,X3),u1_struct_0(X0)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | ~v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.22/0.65    inference(cnf_transformation,[],[f54])).
% 2.22/0.65  fof(f133,plain,(
% 2.22/0.65    l1_waybel_0(sK1,sK0) | ~spl11_3),
% 2.22/0.65    inference(avatar_component_clause,[],[f131])).
% 2.22/0.65  fof(f131,plain,(
% 2.22/0.65    spl11_3 <=> l1_waybel_0(sK1,sK0)),
% 2.22/0.65    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).
% 2.22/0.65  fof(f138,plain,(
% 2.22/0.65    v7_waybel_0(sK1) | ~spl11_4),
% 2.22/0.65    inference(avatar_component_clause,[],[f136])).
% 2.22/0.65  fof(f136,plain,(
% 2.22/0.65    spl11_4 <=> v7_waybel_0(sK1)),
% 2.22/0.65    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).
% 2.22/0.65  fof(f143,plain,(
% 2.22/0.65    v4_orders_2(sK1) | ~spl11_5),
% 2.22/0.65    inference(avatar_component_clause,[],[f141])).
% 2.22/0.65  fof(f141,plain,(
% 2.22/0.65    spl11_5 <=> v4_orders_2(sK1)),
% 2.22/0.65    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).
% 2.22/0.65  fof(f148,plain,(
% 2.22/0.65    ~v2_struct_0(sK1) | spl11_6),
% 2.22/0.65    inference(avatar_component_clause,[],[f146])).
% 2.22/0.65  fof(f146,plain,(
% 2.22/0.65    spl11_6 <=> v2_struct_0(sK1)),
% 2.22/0.65    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).
% 2.22/0.65  fof(f158,plain,(
% 2.22/0.65    l1_struct_0(sK0)),
% 2.22/0.65    inference(unit_resulting_resolution,[],[f75,f85])).
% 2.22/0.65  fof(f85,plain,(
% 2.22/0.65    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.22/0.65    inference(cnf_transformation,[],[f20])).
% 2.22/0.65  fof(f20,plain,(
% 2.22/0.65    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.22/0.65    inference(ennf_transformation,[],[f6])).
% 2.22/0.65  fof(f6,axiom,(
% 2.22/0.65    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.22/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 2.22/0.65  fof(f758,plain,(
% 2.22/0.65    r2_hidden(sK4(sK0,sK1),k1_xboole_0) | v2_struct_0(sK5(sK0,sK1,sK4(sK0,sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl11_1 | ~spl11_2 | ~spl11_3 | ~spl11_4 | ~spl11_5 | spl11_6)),
% 2.22/0.65    inference(subsumption_resolution,[],[f757,f718])).
% 2.22/0.65  fof(f718,plain,(
% 2.22/0.65    v4_orders_2(sK5(sK0,sK1,sK4(sK0,sK1))) | (~spl11_1 | ~spl11_3 | ~spl11_4 | ~spl11_5 | spl11_6)),
% 2.22/0.65    inference(unit_resulting_resolution,[],[f73,f158,f148,f143,f138,f133,f703,f110])).
% 2.22/0.65  fof(f110,plain,(
% 2.22/0.65    ( ! [X2,X0,X1] : (v4_orders_2(X2) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.22/0.65    inference(cnf_transformation,[],[f36])).
% 2.22/0.65  fof(f757,plain,(
% 2.22/0.65    r2_hidden(sK4(sK0,sK1),k1_xboole_0) | ~v4_orders_2(sK5(sK0,sK1,sK4(sK0,sK1))) | v2_struct_0(sK5(sK0,sK1,sK4(sK0,sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl11_1 | ~spl11_2 | ~spl11_3 | ~spl11_4 | ~spl11_5 | spl11_6)),
% 2.22/0.65    inference(subsumption_resolution,[],[f756,f719])).
% 2.22/0.65  fof(f719,plain,(
% 2.22/0.65    v7_waybel_0(sK5(sK0,sK1,sK4(sK0,sK1))) | (~spl11_1 | ~spl11_3 | ~spl11_4 | ~spl11_5 | spl11_6)),
% 2.22/0.65    inference(unit_resulting_resolution,[],[f73,f158,f148,f143,f138,f133,f703,f111])).
% 2.22/0.65  fof(f111,plain,(
% 2.22/0.65    ( ! [X2,X0,X1] : (v7_waybel_0(X2) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.22/0.65    inference(cnf_transformation,[],[f36])).
% 2.22/0.65  fof(f756,plain,(
% 2.22/0.65    r2_hidden(sK4(sK0,sK1),k1_xboole_0) | ~v7_waybel_0(sK5(sK0,sK1,sK4(sK0,sK1))) | ~v4_orders_2(sK5(sK0,sK1,sK4(sK0,sK1))) | v2_struct_0(sK5(sK0,sK1,sK4(sK0,sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl11_1 | ~spl11_2 | ~spl11_3 | ~spl11_4 | ~spl11_5 | spl11_6)),
% 2.22/0.65    inference(subsumption_resolution,[],[f755,f720])).
% 2.22/0.65  fof(f720,plain,(
% 2.22/0.65    l1_waybel_0(sK5(sK0,sK1,sK4(sK0,sK1)),sK0) | (~spl11_1 | ~spl11_3 | ~spl11_4 | ~spl11_5 | spl11_6)),
% 2.22/0.65    inference(unit_resulting_resolution,[],[f73,f158,f148,f143,f138,f133,f703,f112])).
% 2.22/0.65  fof(f112,plain,(
% 2.22/0.65    ( ! [X2,X0,X1] : (l1_waybel_0(X2,X0) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.22/0.65    inference(cnf_transformation,[],[f36])).
% 2.22/0.65  fof(f755,plain,(
% 2.22/0.65    r2_hidden(sK4(sK0,sK1),k1_xboole_0) | ~l1_waybel_0(sK5(sK0,sK1,sK4(sK0,sK1)),sK0) | ~v7_waybel_0(sK5(sK0,sK1,sK4(sK0,sK1))) | ~v4_orders_2(sK5(sK0,sK1,sK4(sK0,sK1))) | v2_struct_0(sK5(sK0,sK1,sK4(sK0,sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl11_1 | ~spl11_2 | ~spl11_3 | ~spl11_4 | ~spl11_5 | spl11_6)),
% 2.22/0.65    inference(subsumption_resolution,[],[f726,f716])).
% 2.22/0.65  fof(f716,plain,(
% 2.22/0.65    ~v3_yellow_6(sK5(sK0,sK1,sK4(sK0,sK1)),sK0) | (~spl11_1 | ~spl11_2 | ~spl11_3 | ~spl11_4 | ~spl11_5 | spl11_6)),
% 2.22/0.65    inference(unit_resulting_resolution,[],[f703,f128])).
% 2.22/0.65  fof(f128,plain,(
% 2.22/0.65    ( ! [X2] : (~v3_yellow_6(X2,sK0) | ~m2_yellow_6(X2,sK0,sK1)) ) | ~spl11_2),
% 2.22/0.65    inference(avatar_component_clause,[],[f127])).
% 2.22/0.65  fof(f127,plain,(
% 2.22/0.65    spl11_2 <=> ! [X2] : (~v3_yellow_6(X2,sK0) | ~m2_yellow_6(X2,sK0,sK1))),
% 2.22/0.65    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 2.22/0.65  fof(f726,plain,(
% 2.22/0.65    r2_hidden(sK4(sK0,sK1),k1_xboole_0) | v3_yellow_6(sK5(sK0,sK1,sK4(sK0,sK1)),sK0) | ~l1_waybel_0(sK5(sK0,sK1,sK4(sK0,sK1)),sK0) | ~v7_waybel_0(sK5(sK0,sK1,sK4(sK0,sK1))) | ~v4_orders_2(sK5(sK0,sK1,sK4(sK0,sK1))) | v2_struct_0(sK5(sK0,sK1,sK4(sK0,sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl11_1 | ~spl11_3 | ~spl11_4 | ~spl11_5 | spl11_6)),
% 2.22/0.65    inference(superposition,[],[f704,f95])).
% 2.22/0.65  fof(f95,plain,(
% 2.22/0.65    ( ! [X0,X1] : (v3_yellow_6(X1,X0) | k1_xboole_0 = k10_yellow_6(X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.22/0.65    inference(cnf_transformation,[],[f55])).
% 2.22/0.65  fof(f55,plain,(
% 2.22/0.65    ! [X0] : (! [X1] : (((v3_yellow_6(X1,X0) | k1_xboole_0 = k10_yellow_6(X0,X1)) & (k1_xboole_0 != k10_yellow_6(X0,X1) | ~v3_yellow_6(X1,X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.22/0.65    inference(nnf_transformation,[],[f26])).
% 2.22/0.65  fof(f26,plain,(
% 2.22/0.65    ! [X0] : (! [X1] : ((v3_yellow_6(X1,X0) <=> k1_xboole_0 != k10_yellow_6(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.22/0.65    inference(flattening,[],[f25])).
% 2.22/0.65  fof(f25,plain,(
% 2.22/0.65    ! [X0] : (! [X1] : ((v3_yellow_6(X1,X0) <=> k1_xboole_0 != k10_yellow_6(X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.22/0.65    inference(ennf_transformation,[],[f11])).
% 2.22/0.65  fof(f11,axiom,(
% 2.22/0.65    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (v3_yellow_6(X1,X0) <=> k1_xboole_0 != k10_yellow_6(X0,X1))))),
% 2.22/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_yellow_6)).
% 2.22/0.65  fof(f704,plain,(
% 2.22/0.65    r2_hidden(sK4(sK0,sK1),k10_yellow_6(sK0,sK5(sK0,sK1,sK4(sK0,sK1)))) | (~spl11_1 | ~spl11_3 | ~spl11_4 | ~spl11_5 | spl11_6)),
% 2.22/0.65    inference(unit_resulting_resolution,[],[f73,f74,f75,f148,f143,f138,f133,f692,f693,f98])).
% 2.22/0.65  fof(f98,plain,(
% 2.22/0.65    ( ! [X2,X0,X1] : (r2_hidden(X2,k10_yellow_6(X0,sK5(X0,X1,X2))) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.22/0.65    inference(cnf_transformation,[],[f57])).
% 2.22/0.65  fof(f678,plain,(
% 2.22/0.65    ~spl11_9 | spl11_1 | ~spl11_7 | ~spl11_8),
% 2.22/0.65    inference(avatar_split_clause,[],[f301,f155,f151,f123,f233])).
% 2.22/0.65  fof(f233,plain,(
% 2.22/0.65    spl11_9 <=> r2_hidden(sK6(sK0,sK2(sK3(sK0)),k1_xboole_0),k1_xboole_0)),
% 2.22/0.65    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).
% 2.22/0.65  fof(f151,plain,(
% 2.22/0.65    spl11_7 <=> ! [X3] : (v3_yellow_6(sK2(X3),sK0) | v2_struct_0(X3) | ~v4_orders_2(X3) | ~v7_waybel_0(X3) | ~l1_waybel_0(X3,sK0))),
% 2.22/0.65    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).
% 2.22/0.65  fof(f155,plain,(
% 2.22/0.65    spl11_8 <=> ! [X3] : (m2_yellow_6(sK2(X3),sK0,X3) | v2_struct_0(X3) | ~v4_orders_2(X3) | ~v7_waybel_0(X3) | ~l1_waybel_0(X3,sK0))),
% 2.22/0.65    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).
% 2.22/0.65  fof(f301,plain,(
% 2.22/0.65    ~r2_hidden(sK6(sK0,sK2(sK3(sK0)),k1_xboole_0),k1_xboole_0) | (spl11_1 | ~spl11_7 | ~spl11_8)),
% 2.22/0.65    inference(unit_resulting_resolution,[],[f83,f289,f114])).
% 2.22/0.65  fof(f114,plain,(
% 2.22/0.65    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.22/0.65    inference(cnf_transformation,[],[f72])).
% 2.22/0.65  fof(f72,plain,(
% 2.22/0.65    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK10(X0,X1),X1) & r2_hidden(sK10(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.22/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f70,f71])).
% 2.22/0.65  fof(f71,plain,(
% 2.22/0.65    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK10(X0,X1),X1) & r2_hidden(sK10(X0,X1),X0)))),
% 2.22/0.65    introduced(choice_axiom,[])).
% 2.22/0.65  fof(f70,plain,(
% 2.22/0.65    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.22/0.65    inference(rectify,[],[f69])).
% 2.22/0.65  fof(f69,plain,(
% 2.22/0.65    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.22/0.65    inference(nnf_transformation,[],[f39])).
% 2.22/0.65  fof(f39,plain,(
% 2.22/0.65    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.22/0.65    inference(ennf_transformation,[],[f1])).
% 2.22/0.65  fof(f1,axiom,(
% 2.22/0.65    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.22/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 2.22/0.65  fof(f289,plain,(
% 2.22/0.65    ~r2_hidden(sK6(sK0,sK2(sK3(sK0)),k1_xboole_0),k10_yellow_6(sK0,sK3(sK0))) | (spl11_1 | ~spl11_7 | ~spl11_8)),
% 2.22/0.65    inference(unit_resulting_resolution,[],[f73,f74,f75,f159,f160,f161,f162,f180,f228,f96])).
% 2.22/0.65  fof(f96,plain,(
% 2.22/0.65    ( ! [X2,X0,X1] : (r3_waybel_9(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.22/0.65    inference(cnf_transformation,[],[f28])).
% 2.22/0.65  fof(f28,plain,(
% 2.22/0.65    ! [X0] : (! [X1] : (! [X2] : (r3_waybel_9(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.22/0.65    inference(flattening,[],[f27])).
% 2.22/0.65  fof(f27,plain,(
% 2.22/0.65    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.22/0.65    inference(ennf_transformation,[],[f13])).
% 2.22/0.65  fof(f13,axiom,(
% 2.22/0.65    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k10_yellow_6(X0,X1)) => r3_waybel_9(X0,X1,X2)))))),
% 2.22/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_waybel_9)).
% 2.22/0.65  fof(f228,plain,(
% 2.22/0.65    ~r3_waybel_9(sK0,sK3(sK0),sK6(sK0,sK2(sK3(sK0)),k1_xboole_0)) | (spl11_1 | ~spl11_7 | ~spl11_8)),
% 2.22/0.65    inference(unit_resulting_resolution,[],[f73,f74,f75,f125,f180,f93])).
% 2.22/0.65  fof(f93,plain,(
% 2.22/0.65    ( ! [X2,X0] : (v1_compts_1(X0) | ~r3_waybel_9(X0,sK3(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.22/0.65    inference(cnf_transformation,[],[f54])).
% 2.22/0.65  fof(f125,plain,(
% 2.22/0.65    ~v1_compts_1(sK0) | spl11_1),
% 2.22/0.65    inference(avatar_component_clause,[],[f123])).
% 2.22/0.65  fof(f180,plain,(
% 2.22/0.65    m1_subset_1(sK6(sK0,sK2(sK3(sK0)),k1_xboole_0),u1_struct_0(sK0)) | (spl11_1 | ~spl11_7 | ~spl11_8)),
% 2.22/0.65    inference(unit_resulting_resolution,[],[f73,f74,f75,f166,f167,f168,f169,f84,f177,f102])).
% 2.22/0.65  fof(f102,plain,(
% 2.22/0.65    ( ! [X2,X0,X1] : (k10_yellow_6(X0,X1) = X2 | m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.22/0.65    inference(cnf_transformation,[],[f64])).
% 2.22/0.65  fof(f64,plain,(
% 2.22/0.65    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | (((~r1_waybel_0(X0,X1,sK7(X0,X1,X2)) & m1_connsp_2(sK7(X0,X1,X2),X0,sK6(X0,X1,X2))) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,sK6(X0,X1,X2))) | r2_hidden(sK6(X0,X1,X2),X2)) & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)))) & (! [X6] : (((r2_hidden(X6,X2) | (~r1_waybel_0(X0,X1,sK8(X0,X1,X6)) & m1_connsp_2(sK8(X0,X1,X6),X0,X6))) & (! [X8] : (r1_waybel_0(X0,X1,X8) | ~m1_connsp_2(X8,X0,X6)) | ~r2_hidden(X6,X2))) | ~m1_subset_1(X6,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.22/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f60,f63,f62,f61])).
% 2.22/0.65  fof(f61,plain,(
% 2.22/0.65    ! [X2,X1,X0] : (? [X3] : ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,X3)) | r2_hidden(X3,X2)) & m1_subset_1(X3,u1_struct_0(X0))) => ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,sK6(X0,X1,X2))) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,sK6(X0,X1,X2))) | r2_hidden(sK6(X0,X1,X2),X2)) & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))))),
% 2.22/0.65    introduced(choice_axiom,[])).
% 2.22/0.65  fof(f62,plain,(
% 2.22/0.65    ! [X2,X1,X0] : (? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,sK6(X0,X1,X2))) => (~r1_waybel_0(X0,X1,sK7(X0,X1,X2)) & m1_connsp_2(sK7(X0,X1,X2),X0,sK6(X0,X1,X2))))),
% 2.22/0.65    introduced(choice_axiom,[])).
% 2.22/0.65  fof(f63,plain,(
% 2.22/0.65    ! [X6,X1,X0] : (? [X7] : (~r1_waybel_0(X0,X1,X7) & m1_connsp_2(X7,X0,X6)) => (~r1_waybel_0(X0,X1,sK8(X0,X1,X6)) & m1_connsp_2(sK8(X0,X1,X6),X0,X6)))),
% 2.22/0.65    introduced(choice_axiom,[])).
% 2.22/0.65  fof(f60,plain,(
% 2.22/0.65    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | ? [X3] : ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,X3)) | r2_hidden(X3,X2)) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X6] : (((r2_hidden(X6,X2) | ? [X7] : (~r1_waybel_0(X0,X1,X7) & m1_connsp_2(X7,X0,X6))) & (! [X8] : (r1_waybel_0(X0,X1,X8) | ~m1_connsp_2(X8,X0,X6)) | ~r2_hidden(X6,X2))) | ~m1_subset_1(X6,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.22/0.65    inference(rectify,[],[f59])).
% 2.22/0.65  fof(f59,plain,(
% 2.22/0.65    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | ? [X3] : ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | r2_hidden(X3,X2)) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3))) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.22/0.65    inference(flattening,[],[f58])).
% 2.22/0.65  fof(f58,plain,(
% 2.22/0.65    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | ? [X3] : (((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | r2_hidden(X3,X2))) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3))) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.22/0.65    inference(nnf_transformation,[],[f32])).
% 2.22/0.65  fof(f32,plain,(
% 2.22/0.65    ! [X0] : (! [X1] : (! [X2] : ((k10_yellow_6(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3))) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.22/0.65    inference(flattening,[],[f31])).
% 2.22/0.65  fof(f31,plain,(
% 2.22/0.65    ! [X0] : (! [X1] : (! [X2] : ((k10_yellow_6(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3))) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.22/0.65    inference(ennf_transformation,[],[f7])).
% 2.22/0.65  fof(f7,axiom,(
% 2.22/0.65    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (k10_yellow_6(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) <=> ! [X4] : (m1_connsp_2(X4,X0,X3) => r1_waybel_0(X0,X1,X4))))))))),
% 2.22/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_yellow_6)).
% 2.22/0.65  fof(f177,plain,(
% 2.22/0.65    k1_xboole_0 != k10_yellow_6(sK0,sK2(sK3(sK0))) | (spl11_1 | ~spl11_7 | ~spl11_8)),
% 2.22/0.65    inference(unit_resulting_resolution,[],[f73,f74,f75,f166,f167,f168,f164,f169,f94])).
% 2.22/0.65  fof(f94,plain,(
% 2.22/0.65    ( ! [X0,X1] : (k1_xboole_0 != k10_yellow_6(X0,X1) | ~v3_yellow_6(X1,X0) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.22/0.65    inference(cnf_transformation,[],[f55])).
% 2.22/0.65  fof(f164,plain,(
% 2.22/0.65    v3_yellow_6(sK2(sK3(sK0)),sK0) | (spl11_1 | ~spl11_7)),
% 2.22/0.65    inference(unit_resulting_resolution,[],[f161,f159,f160,f162,f152])).
% 2.22/0.65  fof(f152,plain,(
% 2.22/0.65    ( ! [X3] : (~v7_waybel_0(X3) | v2_struct_0(X3) | ~v4_orders_2(X3) | v3_yellow_6(sK2(X3),sK0) | ~l1_waybel_0(X3,sK0)) ) | ~spl11_7),
% 2.22/0.65    inference(avatar_component_clause,[],[f151])).
% 2.22/0.65  fof(f84,plain,(
% 2.22/0.65    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.22/0.65    inference(cnf_transformation,[],[f3])).
% 2.22/0.65  fof(f3,axiom,(
% 2.22/0.65    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.22/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 2.22/0.65  fof(f169,plain,(
% 2.22/0.65    l1_waybel_0(sK2(sK3(sK0)),sK0) | (spl11_1 | ~spl11_8)),
% 2.22/0.65    inference(unit_resulting_resolution,[],[f73,f158,f159,f160,f161,f162,f163,f112])).
% 2.22/0.65  fof(f163,plain,(
% 2.22/0.65    m2_yellow_6(sK2(sK3(sK0)),sK0,sK3(sK0)) | (spl11_1 | ~spl11_8)),
% 2.22/0.65    inference(unit_resulting_resolution,[],[f161,f159,f160,f162,f156])).
% 2.22/0.65  fof(f156,plain,(
% 2.22/0.65    ( ! [X3] : (~v7_waybel_0(X3) | v2_struct_0(X3) | ~v4_orders_2(X3) | m2_yellow_6(sK2(X3),sK0,X3) | ~l1_waybel_0(X3,sK0)) ) | ~spl11_8),
% 2.22/0.65    inference(avatar_component_clause,[],[f155])).
% 2.22/0.65  fof(f168,plain,(
% 2.22/0.65    v7_waybel_0(sK2(sK3(sK0))) | (spl11_1 | ~spl11_8)),
% 2.22/0.65    inference(unit_resulting_resolution,[],[f73,f158,f159,f160,f161,f162,f163,f111])).
% 2.22/0.65  fof(f167,plain,(
% 2.22/0.65    v4_orders_2(sK2(sK3(sK0))) | (spl11_1 | ~spl11_8)),
% 2.22/0.65    inference(unit_resulting_resolution,[],[f73,f158,f159,f160,f161,f162,f163,f110])).
% 2.22/0.65  fof(f166,plain,(
% 2.22/0.65    ~v2_struct_0(sK2(sK3(sK0))) | (spl11_1 | ~spl11_8)),
% 2.22/0.65    inference(unit_resulting_resolution,[],[f73,f158,f159,f160,f161,f162,f163,f109])).
% 2.22/0.65  fof(f162,plain,(
% 2.22/0.65    l1_waybel_0(sK3(sK0),sK0) | spl11_1),
% 2.22/0.65    inference(unit_resulting_resolution,[],[f73,f74,f75,f125,f92])).
% 2.22/0.65  fof(f92,plain,(
% 2.22/0.65    ( ! [X0] : (v1_compts_1(X0) | l1_waybel_0(sK3(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.22/0.65    inference(cnf_transformation,[],[f54])).
% 2.22/0.65  fof(f161,plain,(
% 2.22/0.65    v7_waybel_0(sK3(sK0)) | spl11_1),
% 2.22/0.65    inference(unit_resulting_resolution,[],[f73,f74,f75,f125,f91])).
% 2.22/0.65  fof(f91,plain,(
% 2.22/0.65    ( ! [X0] : (v1_compts_1(X0) | v7_waybel_0(sK3(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.22/0.65    inference(cnf_transformation,[],[f54])).
% 2.22/0.65  fof(f160,plain,(
% 2.22/0.65    v4_orders_2(sK3(sK0)) | spl11_1),
% 2.22/0.65    inference(unit_resulting_resolution,[],[f73,f74,f75,f125,f90])).
% 2.22/0.65  fof(f90,plain,(
% 2.22/0.65    ( ! [X0] : (v1_compts_1(X0) | v4_orders_2(sK3(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.22/0.65    inference(cnf_transformation,[],[f54])).
% 2.22/0.65  fof(f159,plain,(
% 2.22/0.65    ~v2_struct_0(sK3(sK0)) | spl11_1),
% 2.22/0.65    inference(unit_resulting_resolution,[],[f73,f74,f75,f125,f89])).
% 2.22/0.65  fof(f89,plain,(
% 2.22/0.65    ( ! [X0] : (v1_compts_1(X0) | ~v2_struct_0(sK3(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.22/0.65    inference(cnf_transformation,[],[f54])).
% 2.22/0.65  fof(f663,plain,(
% 2.22/0.65    spl11_1 | ~spl11_7 | ~spl11_8 | spl11_9),
% 2.22/0.65    inference(avatar_contradiction_clause,[],[f662])).
% 2.22/0.65  fof(f662,plain,(
% 2.22/0.65    $false | (spl11_1 | ~spl11_7 | ~spl11_8 | spl11_9)),
% 2.22/0.65    inference(subsumption_resolution,[],[f658,f520])).
% 2.22/0.65  fof(f520,plain,(
% 2.22/0.65    m1_connsp_2(sK8(sK0,sK2(sK3(sK0)),sK6(sK0,sK2(sK3(sK0)),k1_xboole_0)),sK0,sK6(sK0,sK2(sK3(sK0)),k1_xboole_0)) | (spl11_1 | ~spl11_7 | ~spl11_8)),
% 2.22/0.65    inference(unit_resulting_resolution,[],[f73,f74,f75,f166,f167,f168,f169,f178,f180,f416,f120])).
% 2.22/0.65  fof(f120,plain,(
% 2.22/0.65    ( ! [X6,X0,X1] : (r2_hidden(X6,k10_yellow_6(X0,X1)) | m1_connsp_2(sK8(X0,X1,X6),X0,X6) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.22/0.65    inference(equality_resolution,[],[f100])).
% 2.22/0.65  fof(f100,plain,(
% 2.22/0.65    ( ! [X6,X2,X0,X1] : (r2_hidden(X6,X2) | m1_connsp_2(sK8(X0,X1,X6),X0,X6) | ~m1_subset_1(X6,u1_struct_0(X0)) | k10_yellow_6(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.22/0.65    inference(cnf_transformation,[],[f64])).
% 2.22/0.65  fof(f416,plain,(
% 2.22/0.65    ~r2_hidden(sK6(sK0,sK2(sK3(sK0)),k1_xboole_0),k10_yellow_6(sK0,sK2(sK3(sK0)))) | (spl11_1 | ~spl11_7 | ~spl11_8)),
% 2.22/0.65    inference(unit_resulting_resolution,[],[f73,f74,f75,f166,f167,f168,f169,f180,f405,f96])).
% 2.22/0.65  fof(f405,plain,(
% 2.22/0.65    ~r3_waybel_9(sK0,sK2(sK3(sK0)),sK6(sK0,sK2(sK3(sK0)),k1_xboole_0)) | (spl11_1 | ~spl11_7 | ~spl11_8)),
% 2.22/0.65    inference(unit_resulting_resolution,[],[f73,f74,f75,f166,f169,f180,f287,f335,f106])).
% 2.22/0.65  fof(f106,plain,(
% 2.22/0.65    ( ! [X4,X2,X0,X1] : (r2_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X2) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.22/0.65    inference(cnf_transformation,[],[f68])).
% 2.22/0.65  fof(f68,plain,(
% 2.22/0.65    ! [X0] : (! [X1] : (! [X2] : (((r3_waybel_9(X0,X1,X2) | (~r2_waybel_0(X0,X1,sK9(X0,X1,X2)) & m1_connsp_2(sK9(X0,X1,X2),X0,X2))) & (! [X4] : (r2_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X2)) | ~r3_waybel_9(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.22/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f66,f67])).
% 2.22/0.65  fof(f67,plain,(
% 2.22/0.65    ! [X2,X1,X0] : (? [X3] : (~r2_waybel_0(X0,X1,X3) & m1_connsp_2(X3,X0,X2)) => (~r2_waybel_0(X0,X1,sK9(X0,X1,X2)) & m1_connsp_2(sK9(X0,X1,X2),X0,X2)))),
% 2.22/0.65    introduced(choice_axiom,[])).
% 2.22/0.65  fof(f66,plain,(
% 2.22/0.65    ! [X0] : (! [X1] : (! [X2] : (((r3_waybel_9(X0,X1,X2) | ? [X3] : (~r2_waybel_0(X0,X1,X3) & m1_connsp_2(X3,X0,X2))) & (! [X4] : (r2_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X2)) | ~r3_waybel_9(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.22/0.65    inference(rectify,[],[f65])).
% 2.22/0.65  fof(f65,plain,(
% 2.22/0.65    ! [X0] : (! [X1] : (! [X2] : (((r3_waybel_9(X0,X1,X2) | ? [X3] : (~r2_waybel_0(X0,X1,X3) & m1_connsp_2(X3,X0,X2))) & (! [X3] : (r2_waybel_0(X0,X1,X3) | ~m1_connsp_2(X3,X0,X2)) | ~r3_waybel_9(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.22/0.65    inference(nnf_transformation,[],[f34])).
% 2.22/0.65  fof(f34,plain,(
% 2.22/0.65    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) <=> ! [X3] : (r2_waybel_0(X0,X1,X3) | ~m1_connsp_2(X3,X0,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.22/0.65    inference(flattening,[],[f33])).
% 2.22/0.65  fof(f33,plain,(
% 2.22/0.65    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) <=> ! [X3] : (r2_waybel_0(X0,X1,X3) | ~m1_connsp_2(X3,X0,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.22/0.65    inference(ennf_transformation,[],[f12])).
% 2.22/0.65  fof(f12,axiom,(
% 2.22/0.65    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,X1,X2) <=> ! [X3] : (m1_connsp_2(X3,X0,X2) => r2_waybel_0(X0,X1,X3))))))),
% 2.22/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_waybel_9)).
% 2.22/0.66  fof(f335,plain,(
% 2.22/0.66    ~r2_waybel_0(sK0,sK2(sK3(sK0)),sK9(sK0,sK3(sK0),sK6(sK0,sK2(sK3(sK0)),k1_xboole_0))) | (spl11_1 | ~spl11_7 | ~spl11_8)),
% 2.22/0.66    inference(unit_resulting_resolution,[],[f73,f158,f159,f160,f161,f162,f163,f288,f86])).
% 2.22/0.66  fof(f86,plain,(
% 2.22/0.66    ( ! [X2,X0,X3,X1] : (r2_waybel_0(X0,X1,X3) | ~r2_waybel_0(X0,X2,X3) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.22/0.66    inference(cnf_transformation,[],[f22])).
% 2.22/0.66  fof(f22,plain,(
% 2.22/0.66    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_waybel_0(X0,X1,X3) | ~r2_waybel_0(X0,X2,X3)) | ~m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.22/0.66    inference(flattening,[],[f21])).
% 2.22/0.66  fof(f21,plain,(
% 2.22/0.66    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_waybel_0(X0,X1,X3) | ~r2_waybel_0(X0,X2,X3)) | ~m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.22/0.66    inference(ennf_transformation,[],[f10])).
% 2.22/0.66  fof(f10,axiom,(
% 2.22/0.66    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m2_yellow_6(X2,X0,X1) => ! [X3] : (r2_waybel_0(X0,X2,X3) => r2_waybel_0(X0,X1,X3)))))),
% 2.22/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_yellow_6)).
% 2.22/0.66  fof(f288,plain,(
% 2.22/0.66    ~r2_waybel_0(sK0,sK3(sK0),sK9(sK0,sK3(sK0),sK6(sK0,sK2(sK3(sK0)),k1_xboole_0))) | (spl11_1 | ~spl11_7 | ~spl11_8)),
% 2.22/0.66    inference(unit_resulting_resolution,[],[f73,f74,f75,f159,f162,f180,f228,f108])).
% 2.22/0.66  fof(f108,plain,(
% 2.22/0.66    ( ! [X2,X0,X1] : (r3_waybel_9(X0,X1,X2) | ~r2_waybel_0(X0,X1,sK9(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.22/0.66    inference(cnf_transformation,[],[f68])).
% 2.22/0.66  fof(f287,plain,(
% 2.22/0.66    m1_connsp_2(sK9(sK0,sK3(sK0),sK6(sK0,sK2(sK3(sK0)),k1_xboole_0)),sK0,sK6(sK0,sK2(sK3(sK0)),k1_xboole_0)) | (spl11_1 | ~spl11_7 | ~spl11_8)),
% 2.22/0.66    inference(unit_resulting_resolution,[],[f73,f74,f75,f159,f162,f180,f228,f107])).
% 2.22/0.66  fof(f107,plain,(
% 2.22/0.66    ( ! [X2,X0,X1] : (r3_waybel_9(X0,X1,X2) | m1_connsp_2(sK9(X0,X1,X2),X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.22/0.66    inference(cnf_transformation,[],[f68])).
% 2.22/0.66  fof(f178,plain,(
% 2.22/0.66    m1_subset_1(k10_yellow_6(sK0,sK2(sK3(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) | (spl11_1 | ~spl11_8)),
% 2.22/0.66    inference(unit_resulting_resolution,[],[f73,f74,f75,f166,f167,f168,f169,f113])).
% 2.22/0.66  fof(f113,plain,(
% 2.22/0.66    ( ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.22/0.66    inference(cnf_transformation,[],[f38])).
% 2.22/0.66  fof(f38,plain,(
% 2.22/0.66    ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.22/0.66    inference(flattening,[],[f37])).
% 2.22/0.66  fof(f37,plain,(
% 2.22/0.66    ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.22/0.66    inference(ennf_transformation,[],[f8])).
% 2.22/0.66  fof(f8,axiom,(
% 2.22/0.66    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.22/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_yellow_6)).
% 2.22/0.66  fof(f658,plain,(
% 2.22/0.66    ~m1_connsp_2(sK8(sK0,sK2(sK3(sK0)),sK6(sK0,sK2(sK3(sK0)),k1_xboole_0)),sK0,sK6(sK0,sK2(sK3(sK0)),k1_xboole_0)) | (spl11_1 | ~spl11_7 | ~spl11_8 | spl11_9)),
% 2.22/0.66    inference(unit_resulting_resolution,[],[f521,f244])).
% 2.22/0.66  fof(f244,plain,(
% 2.22/0.66    ( ! [X0] : (r1_waybel_0(sK0,sK2(sK3(sK0)),X0) | ~m1_connsp_2(X0,sK0,sK6(sK0,sK2(sK3(sK0)),k1_xboole_0))) ) | (spl11_1 | ~spl11_7 | ~spl11_8 | spl11_9)),
% 2.22/0.66    inference(subsumption_resolution,[],[f243,f84])).
% 2.22/0.66  fof(f243,plain,(
% 2.22/0.66    ( ! [X0] : (r1_waybel_0(sK0,sK2(sK3(sK0)),X0) | ~m1_connsp_2(X0,sK0,sK6(sK0,sK2(sK3(sK0)),k1_xboole_0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (spl11_1 | ~spl11_7 | ~spl11_8 | spl11_9)),
% 2.22/0.66    inference(subsumption_resolution,[],[f242,f235])).
% 2.22/0.66  fof(f235,plain,(
% 2.22/0.66    ~r2_hidden(sK6(sK0,sK2(sK3(sK0)),k1_xboole_0),k1_xboole_0) | spl11_9),
% 2.22/0.66    inference(avatar_component_clause,[],[f233])).
% 2.22/0.66  fof(f242,plain,(
% 2.22/0.66    ( ! [X0] : (r1_waybel_0(sK0,sK2(sK3(sK0)),X0) | ~m1_connsp_2(X0,sK0,sK6(sK0,sK2(sK3(sK0)),k1_xboole_0)) | r2_hidden(sK6(sK0,sK2(sK3(sK0)),k1_xboole_0),k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (spl11_1 | ~spl11_7 | ~spl11_8)),
% 2.22/0.66    inference(equality_resolution,[],[f200])).
% 2.22/0.66  fof(f200,plain,(
% 2.22/0.66    ( ! [X2,X1] : (k1_xboole_0 != X1 | r1_waybel_0(sK0,sK2(sK3(sK0)),X2) | ~m1_connsp_2(X2,sK0,sK6(sK0,sK2(sK3(sK0)),X1)) | r2_hidden(sK6(sK0,sK2(sK3(sK0)),X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (spl11_1 | ~spl11_7 | ~spl11_8)),
% 2.22/0.66    inference(subsumption_resolution,[],[f199,f73])).
% 2.22/0.66  fof(f199,plain,(
% 2.22/0.66    ( ! [X2,X1] : (k1_xboole_0 != X1 | r1_waybel_0(sK0,sK2(sK3(sK0)),X2) | ~m1_connsp_2(X2,sK0,sK6(sK0,sK2(sK3(sK0)),X1)) | r2_hidden(sK6(sK0,sK2(sK3(sK0)),X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)) ) | (spl11_1 | ~spl11_7 | ~spl11_8)),
% 2.22/0.66    inference(subsumption_resolution,[],[f198,f74])).
% 2.22/0.66  fof(f198,plain,(
% 2.22/0.66    ( ! [X2,X1] : (k1_xboole_0 != X1 | r1_waybel_0(sK0,sK2(sK3(sK0)),X2) | ~m1_connsp_2(X2,sK0,sK6(sK0,sK2(sK3(sK0)),X1)) | r2_hidden(sK6(sK0,sK2(sK3(sK0)),X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (spl11_1 | ~spl11_7 | ~spl11_8)),
% 2.22/0.66    inference(subsumption_resolution,[],[f197,f75])).
% 2.22/0.66  fof(f197,plain,(
% 2.22/0.66    ( ! [X2,X1] : (k1_xboole_0 != X1 | r1_waybel_0(sK0,sK2(sK3(sK0)),X2) | ~m1_connsp_2(X2,sK0,sK6(sK0,sK2(sK3(sK0)),X1)) | r2_hidden(sK6(sK0,sK2(sK3(sK0)),X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (spl11_1 | ~spl11_7 | ~spl11_8)),
% 2.22/0.66    inference(subsumption_resolution,[],[f196,f166])).
% 2.22/0.66  fof(f196,plain,(
% 2.22/0.66    ( ! [X2,X1] : (k1_xboole_0 != X1 | r1_waybel_0(sK0,sK2(sK3(sK0)),X2) | ~m1_connsp_2(X2,sK0,sK6(sK0,sK2(sK3(sK0)),X1)) | r2_hidden(sK6(sK0,sK2(sK3(sK0)),X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK2(sK3(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (spl11_1 | ~spl11_7 | ~spl11_8)),
% 2.22/0.66    inference(subsumption_resolution,[],[f195,f167])).
% 2.22/0.66  fof(f195,plain,(
% 2.22/0.66    ( ! [X2,X1] : (k1_xboole_0 != X1 | r1_waybel_0(sK0,sK2(sK3(sK0)),X2) | ~m1_connsp_2(X2,sK0,sK6(sK0,sK2(sK3(sK0)),X1)) | r2_hidden(sK6(sK0,sK2(sK3(sK0)),X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_orders_2(sK2(sK3(sK0))) | v2_struct_0(sK2(sK3(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (spl11_1 | ~spl11_7 | ~spl11_8)),
% 2.22/0.66    inference(subsumption_resolution,[],[f194,f168])).
% 2.22/0.66  fof(f194,plain,(
% 2.22/0.66    ( ! [X2,X1] : (k1_xboole_0 != X1 | r1_waybel_0(sK0,sK2(sK3(sK0)),X2) | ~m1_connsp_2(X2,sK0,sK6(sK0,sK2(sK3(sK0)),X1)) | r2_hidden(sK6(sK0,sK2(sK3(sK0)),X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v7_waybel_0(sK2(sK3(sK0))) | ~v4_orders_2(sK2(sK3(sK0))) | v2_struct_0(sK2(sK3(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (spl11_1 | ~spl11_7 | ~spl11_8)),
% 2.22/0.66    inference(subsumption_resolution,[],[f182,f169])).
% 2.22/0.66  fof(f182,plain,(
% 2.22/0.66    ( ! [X2,X1] : (k1_xboole_0 != X1 | r1_waybel_0(sK0,sK2(sK3(sK0)),X2) | ~m1_connsp_2(X2,sK0,sK6(sK0,sK2(sK3(sK0)),X1)) | r2_hidden(sK6(sK0,sK2(sK3(sK0)),X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_waybel_0(sK2(sK3(sK0)),sK0) | ~v7_waybel_0(sK2(sK3(sK0))) | ~v4_orders_2(sK2(sK3(sK0))) | v2_struct_0(sK2(sK3(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (spl11_1 | ~spl11_7 | ~spl11_8)),
% 2.22/0.66    inference(superposition,[],[f177,f103])).
% 2.22/0.66  fof(f103,plain,(
% 2.22/0.66    ( ! [X2,X0,X5,X1] : (k10_yellow_6(X0,X1) = X2 | r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,sK6(X0,X1,X2)) | r2_hidden(sK6(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.22/0.66    inference(cnf_transformation,[],[f64])).
% 2.22/0.66  fof(f521,plain,(
% 2.22/0.66    ~r1_waybel_0(sK0,sK2(sK3(sK0)),sK8(sK0,sK2(sK3(sK0)),sK6(sK0,sK2(sK3(sK0)),k1_xboole_0))) | (spl11_1 | ~spl11_7 | ~spl11_8)),
% 2.22/0.66    inference(unit_resulting_resolution,[],[f73,f74,f75,f166,f167,f168,f169,f178,f180,f416,f119])).
% 2.22/0.66  fof(f119,plain,(
% 2.22/0.66    ( ! [X6,X0,X1] : (r2_hidden(X6,k10_yellow_6(X0,X1)) | ~r1_waybel_0(X0,X1,sK8(X0,X1,X6)) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.22/0.66    inference(equality_resolution,[],[f101])).
% 2.22/0.66  fof(f101,plain,(
% 2.22/0.66    ( ! [X6,X2,X0,X1] : (r2_hidden(X6,X2) | ~r1_waybel_0(X0,X1,sK8(X0,X1,X6)) | ~m1_subset_1(X6,u1_struct_0(X0)) | k10_yellow_6(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.22/0.66    inference(cnf_transformation,[],[f64])).
% 2.22/0.66  fof(f157,plain,(
% 2.22/0.66    spl11_1 | spl11_8),
% 2.22/0.66    inference(avatar_split_clause,[],[f76,f155,f123])).
% 2.22/0.66  fof(f76,plain,(
% 2.22/0.66    ( ! [X3] : (m2_yellow_6(sK2(X3),sK0,X3) | ~l1_waybel_0(X3,sK0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | v1_compts_1(sK0)) )),
% 2.22/0.66    inference(cnf_transformation,[],[f49])).
% 2.22/0.66  fof(f153,plain,(
% 2.22/0.66    spl11_1 | spl11_7),
% 2.22/0.66    inference(avatar_split_clause,[],[f77,f151,f123])).
% 2.22/0.66  fof(f77,plain,(
% 2.22/0.66    ( ! [X3] : (v3_yellow_6(sK2(X3),sK0) | ~l1_waybel_0(X3,sK0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | v1_compts_1(sK0)) )),
% 2.22/0.66    inference(cnf_transformation,[],[f49])).
% 2.22/0.66  fof(f149,plain,(
% 2.22/0.66    ~spl11_1 | ~spl11_6),
% 2.22/0.66    inference(avatar_split_clause,[],[f78,f146,f123])).
% 2.22/0.66  fof(f78,plain,(
% 2.22/0.66    ~v2_struct_0(sK1) | ~v1_compts_1(sK0)),
% 2.22/0.66    inference(cnf_transformation,[],[f49])).
% 2.22/0.66  fof(f144,plain,(
% 2.22/0.66    ~spl11_1 | spl11_5),
% 2.22/0.66    inference(avatar_split_clause,[],[f79,f141,f123])).
% 2.22/0.66  fof(f79,plain,(
% 2.22/0.66    v4_orders_2(sK1) | ~v1_compts_1(sK0)),
% 2.22/0.66    inference(cnf_transformation,[],[f49])).
% 2.22/0.66  fof(f139,plain,(
% 2.22/0.66    ~spl11_1 | spl11_4),
% 2.22/0.66    inference(avatar_split_clause,[],[f80,f136,f123])).
% 2.22/0.66  fof(f80,plain,(
% 2.22/0.66    v7_waybel_0(sK1) | ~v1_compts_1(sK0)),
% 2.22/0.66    inference(cnf_transformation,[],[f49])).
% 2.22/0.66  fof(f134,plain,(
% 2.22/0.66    ~spl11_1 | spl11_3),
% 2.22/0.66    inference(avatar_split_clause,[],[f81,f131,f123])).
% 2.22/0.66  fof(f81,plain,(
% 2.22/0.66    l1_waybel_0(sK1,sK0) | ~v1_compts_1(sK0)),
% 2.22/0.66    inference(cnf_transformation,[],[f49])).
% 2.22/0.66  fof(f129,plain,(
% 2.22/0.66    ~spl11_1 | spl11_2),
% 2.22/0.66    inference(avatar_split_clause,[],[f82,f127,f123])).
% 2.22/0.66  fof(f82,plain,(
% 2.22/0.66    ( ! [X2] : (~v3_yellow_6(X2,sK0) | ~m2_yellow_6(X2,sK0,sK1) | ~v1_compts_1(sK0)) )),
% 2.22/0.66    inference(cnf_transformation,[],[f49])).
% 2.22/0.66  % SZS output end Proof for theBenchmark
% 2.22/0.66  % (19438)------------------------------
% 2.22/0.66  % (19438)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.22/0.66  % (19438)Termination reason: Refutation
% 2.22/0.66  
% 2.22/0.66  % (19438)Memory used [KB]: 11641
% 2.22/0.66  % (19438)Time elapsed: 0.235 s
% 2.22/0.66  % (19438)------------------------------
% 2.22/0.66  % (19438)------------------------------
% 2.22/0.66  % (19411)Success in time 0.301 s
%------------------------------------------------------------------------------
