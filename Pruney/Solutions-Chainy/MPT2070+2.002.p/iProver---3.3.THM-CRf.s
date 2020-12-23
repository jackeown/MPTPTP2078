%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:23 EST 2020

% Result     : Theorem 1.48s
% Output     : CNFRefutation 1.48s
% Verified   : 
% Statistics : Number of formulae       :  196 (1249 expanded)
%              Number of clauses        :  115 ( 182 expanded)
%              Number of leaves         :   14 ( 397 expanded)
%              Depth                    :   29
%              Number of atoms          : 1465 (20903 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   18 (   8 average)
%              Maximal clause size      :   48 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ! [X2] :
          ( ! [X3] :
              ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,k10_yellow_6(X0,X2))
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r1_waybel_0(X0,X2,X1)
          | ~ l1_waybel_0(X2,X0)
          | ~ v3_yellow_6(X2,X0)
          | ~ v7_waybel_0(X2)
          | ~ v4_orders_2(X2)
          | v2_struct_0(X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2] :
            ( ? [X3] :
                ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,k10_yellow_6(X0,X2))
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & r1_waybel_0(X0,X2,X1)
            & l1_waybel_0(X2,X0)
            & v3_yellow_6(X2,X0)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) ) )
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
        | ~ sP0(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ? [X3] :
                ( ~ r2_hidden(X3,X0)
                & r2_hidden(X3,k10_yellow_6(X1,X2))
                & m1_subset_1(X3,u1_struct_0(X1)) )
            & r1_waybel_0(X1,X2,X0)
            & l1_waybel_0(X2,X1)
            & v3_yellow_6(X2,X1)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) ) )
      & ( ! [X4] :
            ( ! [X5] :
                ( r2_hidden(X5,X0)
                | ~ r2_hidden(X5,k10_yellow_6(X1,X4))
                | ~ m1_subset_1(X5,u1_struct_0(X1)) )
            | ~ r1_waybel_0(X1,X4,X0)
            | ~ l1_waybel_0(X4,X1)
            | ~ v3_yellow_6(X4,X1)
            | ~ v7_waybel_0(X4)
            | ~ v4_orders_2(X4)
            | v2_struct_0(X4) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f22])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X0)
          & r2_hidden(X3,k10_yellow_6(X1,X2))
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r2_hidden(sK4(X0,X1),X0)
        & r2_hidden(sK4(X0,X1),k10_yellow_6(X1,X2))
        & m1_subset_1(sK4(X0,X1),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(X3,X0)
              & r2_hidden(X3,k10_yellow_6(X1,X2))
              & m1_subset_1(X3,u1_struct_0(X1)) )
          & r1_waybel_0(X1,X2,X0)
          & l1_waybel_0(X2,X1)
          & v3_yellow_6(X2,X1)
          & v7_waybel_0(X2)
          & v4_orders_2(X2)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ~ r2_hidden(X3,X0)
            & r2_hidden(X3,k10_yellow_6(X1,sK3(X0,X1)))
            & m1_subset_1(X3,u1_struct_0(X1)) )
        & r1_waybel_0(X1,sK3(X0,X1),X0)
        & l1_waybel_0(sK3(X0,X1),X1)
        & v3_yellow_6(sK3(X0,X1),X1)
        & v7_waybel_0(sK3(X0,X1))
        & v4_orders_2(sK3(X0,X1))
        & ~ v2_struct_0(sK3(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X0)
          & r2_hidden(sK4(X0,X1),k10_yellow_6(X1,sK3(X0,X1)))
          & m1_subset_1(sK4(X0,X1),u1_struct_0(X1))
          & r1_waybel_0(X1,sK3(X0,X1),X0)
          & l1_waybel_0(sK3(X0,X1),X1)
          & v3_yellow_6(sK3(X0,X1),X1)
          & v7_waybel_0(sK3(X0,X1))
          & v4_orders_2(sK3(X0,X1))
          & ~ v2_struct_0(sK3(X0,X1)) ) )
      & ( ! [X4] :
            ( ! [X5] :
                ( r2_hidden(X5,X0)
                | ~ r2_hidden(X5,k10_yellow_6(X1,X4))
                | ~ m1_subset_1(X5,u1_struct_0(X1)) )
            | ~ r1_waybel_0(X1,X4,X0)
            | ~ l1_waybel_0(X4,X1)
            | ~ v3_yellow_6(X4,X1)
            | ~ v7_waybel_0(X4)
            | ~ v4_orders_2(X4)
            | v2_struct_0(X4) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f23,f25,f24])).

fof(f49,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X0)
      | ~ r2_hidden(X5,k10_yellow_6(X1,X4))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ r1_waybel_0(X1,X4,X0)
      | ~ l1_waybel_0(X4,X1)
      | ~ v3_yellow_6(X4,X1)
      | ~ v7_waybel_0(X4)
      | ~ v4_orders_2(X4)
      | v2_struct_0(X4)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

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
                    ( r2_hidden(X2,k10_yellow_6(X0,X3))
                    & r1_waybel_0(X0,X3,X1)
                    & l1_waybel_0(X3,X0)
                    & v3_yellow_6(X3,X0)
                    & v7_waybel_0(X3)
                    & v4_orders_2(X3)
                    & ~ v2_struct_0(X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f7,plain,(
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
    inference(flattening,[],[f6])).

fof(f17,plain,(
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
    inference(nnf_transformation,[],[f7])).

fof(f18,plain,(
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
    inference(rectify,[],[f17])).

fof(f19,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X2,k10_yellow_6(X0,X4))
          & r1_waybel_0(X0,X4,X1)
          & l1_waybel_0(X4,X0)
          & v3_yellow_6(X4,X0)
          & v7_waybel_0(X4)
          & v4_orders_2(X4)
          & ~ v2_struct_0(X4) )
     => ( r2_hidden(X2,k10_yellow_6(X0,sK2(X0,X1,X2)))
        & r1_waybel_0(X0,sK2(X0,X1,X2),X1)
        & l1_waybel_0(sK2(X0,X1,X2),X0)
        & v3_yellow_6(sK2(X0,X1,X2),X0)
        & v7_waybel_0(sK2(X0,X1,X2))
        & v4_orders_2(sK2(X0,X1,X2))
        & ~ v2_struct_0(sK2(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
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
                & ( ( r2_hidden(X2,k10_yellow_6(X0,sK2(X0,X1,X2)))
                    & r1_waybel_0(X0,sK2(X0,X1,X2),X1)
                    & l1_waybel_0(sK2(X0,X1,X2),X0)
                    & v3_yellow_6(sK2(X0,X1,X2),X0)
                    & v7_waybel_0(sK2(X0,X1,X2))
                    & v4_orders_2(sK2(X0,X1,X2))
                    & ~ v2_struct_0(sK2(X0,X1,X2)) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f19])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_waybel_0(X0,sK2(X0,X1,X2),X1)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( v7_waybel_0(sK2(X0,X1,X2))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( v4_orders_2(sK2(X0,X1,X2))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(sK2(X0,X1,X2))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(sK2(X0,X1,X2),X0)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( v3_yellow_6(sK2(X0,X1,X2),X0)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                  & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0)))
                  & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                  & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                  & ~ v1_xboole_0(X2) )
               => ( r2_hidden(X1,X2)
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_waybel_7(X0,X2,X3)
                       => r2_hidden(X3,X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> ! [X2] :
                  ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0)))
                    & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                    & ~ v1_xboole_0(X2) )
                 => ( r2_hidden(X1,X2)
                   => ! [X3] :
                        ( m1_subset_1(X3,u1_struct_0(X0))
                       => ( r2_waybel_7(X0,X2,X3)
                         => r2_hidden(X3,X1) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r2_waybel_7(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_hidden(X1,X2)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                | ~ v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0)))
                | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                | v1_xboole_0(X2) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r2_waybel_7(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_hidden(X1,X2)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                | ~ v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0)))
                | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                | v1_xboole_0(X2) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(X3,X1)
                    & r2_waybel_7(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_hidden(X1,X2)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0)))
                & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                & ~ v1_xboole_0(X2) )
            | ~ v4_pre_topc(X1,X0) )
          & ( ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r2_waybel_7(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_hidden(X1,X2)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                | ~ v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0)))
                | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                | v1_xboole_0(X2) )
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(X3,X1)
                    & r2_waybel_7(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_hidden(X1,X2)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0)))
                & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                & ~ v1_xboole_0(X2) )
            | ~ v4_pre_topc(X1,X0) )
          & ( ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r2_waybel_7(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_hidden(X1,X2)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                | ~ v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0)))
                | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                | v1_xboole_0(X2) )
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(X3,X1)
                    & r2_waybel_7(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_hidden(X1,X2)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0)))
                & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                & ~ v1_xboole_0(X2) )
            | ~ v4_pre_topc(X1,X0) )
          & ( ! [X4] :
                ( ! [X5] :
                    ( r2_hidden(X5,X1)
                    | ~ r2_waybel_7(X0,X4,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                | ~ r2_hidden(X1,X4)
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                | ~ v3_waybel_7(X4,k3_yellow_1(k2_struct_0(X0)))
                | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                | v1_xboole_0(X4) )
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f32])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & r2_waybel_7(X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(sK9,X1)
        & r2_waybel_7(X0,X2,sK9)
        & m1_subset_1(sK9,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(X3,X1)
              & r2_waybel_7(X0,X2,X3)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & r2_hidden(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0)))
          & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
          & ~ v1_xboole_0(X2) )
     => ( ? [X3] :
            ( ~ r2_hidden(X3,X1)
            & r2_waybel_7(X0,sK8,X3)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & r2_hidden(X1,sK8)
        & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
        & v3_waybel_7(sK8,k3_yellow_1(k2_struct_0(X0)))
        & v13_waybel_0(sK8,k3_yellow_1(k2_struct_0(X0)))
        & v2_waybel_0(sK8,k3_yellow_1(k2_struct_0(X0)))
        & ~ v1_xboole_0(sK8) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(X3,X1)
                    & r2_waybel_7(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_hidden(X1,X2)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0)))
                & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                & ~ v1_xboole_0(X2) )
            | ~ v4_pre_topc(X1,X0) )
          & ( ! [X4] :
                ( ! [X5] :
                    ( r2_hidden(X5,X1)
                    | ~ r2_waybel_7(X0,X4,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                | ~ r2_hidden(X1,X4)
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                | ~ v3_waybel_7(X4,k3_yellow_1(k2_struct_0(X0)))
                | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                | v1_xboole_0(X4) )
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(X3,sK7)
                  & r2_waybel_7(X0,X2,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_hidden(sK7,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0)))
              & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
              & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
              & ~ v1_xboole_0(X2) )
          | ~ v4_pre_topc(sK7,X0) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( r2_hidden(X5,sK7)
                  | ~ r2_waybel_7(X0,X4,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ r2_hidden(sK7,X4)
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              | ~ v3_waybel_7(X4,k3_yellow_1(k2_struct_0(X0)))
              | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
              | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
              | v1_xboole_0(X4) )
          | v4_pre_topc(sK7,X0) )
        & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & r2_waybel_7(X0,X2,X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & r2_hidden(X1,X2)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                  & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0)))
                  & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                  & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                  & ~ v1_xboole_0(X2) )
              | ~ v4_pre_topc(X1,X0) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | ~ r2_waybel_7(X0,X4,X5)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ r2_hidden(X1,X4)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                  | ~ v3_waybel_7(X4,k3_yellow_1(k2_struct_0(X0)))
                  | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                  | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                  | v1_xboole_0(X4) )
              | v4_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(X3,X1)
                    & r2_waybel_7(sK6,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(sK6)) )
                & r2_hidden(X1,X2)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
                & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(sK6)))
                & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK6)))
                & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(sK6)))
                & ~ v1_xboole_0(X2) )
            | ~ v4_pre_topc(X1,sK6) )
          & ( ! [X4] :
                ( ! [X5] :
                    ( r2_hidden(X5,X1)
                    | ~ r2_waybel_7(sK6,X4,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(sK6)) )
                | ~ r2_hidden(X1,X4)
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
                | ~ v3_waybel_7(X4,k3_yellow_1(k2_struct_0(sK6)))
                | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK6)))
                | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK6)))
                | v1_xboole_0(X4) )
            | v4_pre_topc(X1,sK6) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) )
      & l1_pre_topc(sK6)
      & v2_pre_topc(sK6)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ( ( ~ r2_hidden(sK9,sK7)
        & r2_waybel_7(sK6,sK8,sK9)
        & m1_subset_1(sK9,u1_struct_0(sK6))
        & r2_hidden(sK7,sK8)
        & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
        & v3_waybel_7(sK8,k3_yellow_1(k2_struct_0(sK6)))
        & v13_waybel_0(sK8,k3_yellow_1(k2_struct_0(sK6)))
        & v2_waybel_0(sK8,k3_yellow_1(k2_struct_0(sK6)))
        & ~ v1_xboole_0(sK8) )
      | ~ v4_pre_topc(sK7,sK6) )
    & ( ! [X4] :
          ( ! [X5] :
              ( r2_hidden(X5,sK7)
              | ~ r2_waybel_7(sK6,X4,X5)
              | ~ m1_subset_1(X5,u1_struct_0(sK6)) )
          | ~ r2_hidden(sK7,X4)
          | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
          | ~ v3_waybel_7(X4,k3_yellow_1(k2_struct_0(sK6)))
          | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK6)))
          | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK6)))
          | v1_xboole_0(X4) )
      | v4_pre_topc(sK7,sK6) )
    & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    & l1_pre_topc(sK6)
    & v2_pre_topc(sK6)
    & ~ v2_struct_0(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f33,f37,f36,f35,f34])).

fof(f70,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f38])).

fof(f68,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f38])).

fof(f69,plain,(
    v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f38])).

fof(f3,axiom,(
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
                    ( r2_waybel_7(X0,X3,X2)
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & ~ v1_xboole_0(X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ? [X3] :
                    ( r2_waybel_7(X0,X3,X2)
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & ~ v1_xboole_0(X3) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ? [X3] :
                    ( r2_waybel_7(X0,X3,X2)
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & ~ v1_xboole_0(X3) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ! [X3] :
                      ( ~ r2_waybel_7(X0,X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                      | ~ v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0)))
                      | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      | v1_xboole_0(X3) ) )
                & ( ? [X3] :
                      ( r2_waybel_7(X0,X3,X2)
                      & r2_hidden(X1,X3)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                      & v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0)))
                      & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      & ~ v1_xboole_0(X3) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ! [X3] :
                      ( ~ r2_waybel_7(X0,X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                      | ~ v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0)))
                      | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      | v1_xboole_0(X3) ) )
                & ( ? [X4] :
                      ( r2_waybel_7(X0,X4,X2)
                      & r2_hidden(X1,X4)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                      & v3_waybel_7(X4,k3_yellow_1(k2_struct_0(X0)))
                      & v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                      & v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                      & ~ v1_xboole_0(X4) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f27])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_waybel_7(X0,X4,X2)
          & r2_hidden(X1,X4)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v3_waybel_7(X4,k3_yellow_1(k2_struct_0(X0)))
          & v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
          & ~ v1_xboole_0(X4) )
     => ( r2_waybel_7(X0,sK5(X0,X1,X2),X2)
        & r2_hidden(X1,sK5(X0,X1,X2))
        & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
        & v3_waybel_7(sK5(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
        & v13_waybel_0(sK5(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
        & v2_waybel_0(sK5(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
        & ~ v1_xboole_0(sK5(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ! [X3] :
                      ( ~ r2_waybel_7(X0,X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                      | ~ v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0)))
                      | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      | v1_xboole_0(X3) ) )
                & ( ( r2_waybel_7(X0,sK5(X0,X1,X2),X2)
                    & r2_hidden(X1,sK5(X0,X1,X2))
                    & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v3_waybel_7(sK5(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
                    & v13_waybel_0(sK5(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(sK5(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
                    & ~ v1_xboole_0(sK5(X0,X1,X2)) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f28,f29])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(sK5(X0,X1,X2))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v2_waybel_0(sK5(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v13_waybel_0(sK5(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v3_waybel_7(sK5(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_7(X0,sK5(X0,X1,X2),X2)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f72,plain,(
    ! [X4,X5] :
      ( r2_hidden(X5,sK7)
      | ~ r2_waybel_7(sK6,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(sK6))
      | ~ r2_hidden(sK7,X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
      | ~ v3_waybel_7(X4,k3_yellow_1(k2_struct_0(sK6)))
      | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK6)))
      | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK6)))
      | v1_xboole_0(X4)
      | v4_pre_topc(sK7,sK6) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f46,plain,(
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
    inference(cnf_transformation,[],[f20])).

fof(f55,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | r1_waybel_0(X1,sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f50,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | ~ v2_struct_0(sK3(X0,X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f51,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | v4_orders_2(sK3(X0,X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f52,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | v7_waybel_0(sK3(X0,X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f53,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | v3_yellow_6(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f54,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | l1_waybel_0(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,sK5(X0,X1,X2))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k10_yellow_6(X0,sK2(X0,X1,X2)))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( v4_pre_topc(X1,X0)
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ( v4_pre_topc(X1,X0)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ v4_pre_topc(X1,X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ sP0(X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> ! [X2] :
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
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> ! [X2] :
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
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f9,f15,f14])).

fof(f59,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f47,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ r2_waybel_7(X0,X3,X2)
      | ~ r2_hidden(X1,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0)))
      | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f80,plain,
    ( r2_waybel_7(sK6,sK8,sK9)
    | ~ v4_pre_topc(sK7,sK6) ),
    inference(cnf_transformation,[],[f38])).

fof(f73,plain,
    ( ~ v1_xboole_0(sK8)
    | ~ v4_pre_topc(sK7,sK6) ),
    inference(cnf_transformation,[],[f38])).

fof(f74,plain,
    ( v2_waybel_0(sK8,k3_yellow_1(k2_struct_0(sK6)))
    | ~ v4_pre_topc(sK7,sK6) ),
    inference(cnf_transformation,[],[f38])).

fof(f75,plain,
    ( v13_waybel_0(sK8,k3_yellow_1(k2_struct_0(sK6)))
    | ~ v4_pre_topc(sK7,sK6) ),
    inference(cnf_transformation,[],[f38])).

fof(f76,plain,
    ( v3_waybel_7(sK8,k3_yellow_1(k2_struct_0(sK6)))
    | ~ v4_pre_topc(sK7,sK6) ),
    inference(cnf_transformation,[],[f38])).

fof(f77,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
    | ~ v4_pre_topc(sK7,sK6) ),
    inference(cnf_transformation,[],[f38])).

fof(f79,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK6))
    | ~ v4_pre_topc(sK7,sK6) ),
    inference(cnf_transformation,[],[f38])).

fof(f56,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | m1_subset_1(sK4(X0,X1),u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f57,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | r2_hidden(sK4(X0,X1),k10_yellow_6(X1,sK3(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f58,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | ~ r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f81,plain,
    ( ~ r2_hidden(sK9,sK7)
    | ~ v4_pre_topc(sK7,sK6) ),
    inference(cnf_transformation,[],[f38])).

fof(f71,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f38])).

fof(f78,plain,
    ( r2_hidden(sK7,sK8)
    | ~ v4_pre_topc(sK7,sK6) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_19,plain,
    ( ~ r1_waybel_0(X0,X1,X2)
    | ~ sP0(X2,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v3_yellow_6(X1,X0)
    | ~ l1_waybel_0(X1,X0)
    | r2_hidden(X3,X2)
    | ~ r2_hidden(X3,k10_yellow_6(X0,X1))
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2,plain,
    ( r1_waybel_0(X0,sK2(X0,X1,X2),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_523,plain,
    ( ~ sP0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v3_yellow_6(sK2(X1,X0,X3),X1)
    | ~ l1_waybel_0(sK2(X1,X0,X3),X1)
    | r2_hidden(X2,X0)
    | ~ r2_hidden(X2,k10_yellow_6(X1,sK2(X1,X0,X3)))
    | ~ r2_hidden(X3,k2_pre_topc(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(sK2(X1,X0,X3))
    | ~ v4_orders_2(sK2(X1,X0,X3))
    | ~ v7_waybel_0(sK2(X1,X0,X3)) ),
    inference(resolution,[status(thm)],[c_19,c_2])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,k2_pre_topc(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v7_waybel_0(sK2(X1,X0,X2)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,k2_pre_topc(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v4_orders_2(sK2(X1,X0,X2)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,k2_pre_topc(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ v2_struct_0(sK2(X1,X0,X2)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | l1_waybel_0(sK2(X1,X0,X2),X1)
    | ~ r2_hidden(X2,k2_pre_topc(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v3_yellow_6(sK2(X1,X0,X2),X1)
    | ~ r2_hidden(X2,k2_pre_topc(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_557,plain,
    ( ~ sP0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | r2_hidden(X2,X0)
    | ~ r2_hidden(X2,k10_yellow_6(X1,sK2(X1,X0,X3)))
    | ~ r2_hidden(X3,k2_pre_topc(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_523,c_5,c_6,c_7,c_3,c_4])).

cnf(c_40,negated_conjecture,
    ( l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1061,plain,
    ( ~ sP0(X0,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X2,u1_struct_0(sK6))
    | r2_hidden(X1,X0)
    | ~ r2_hidden(X1,k10_yellow_6(sK6,sK2(sK6,X0,X2)))
    | ~ r2_hidden(X2,k2_pre_topc(sK6,X0))
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6) ),
    inference(resolution,[status(thm)],[c_557,c_40])).

cnf(c_42,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_41,negated_conjecture,
    ( v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1065,plain,
    ( ~ sP0(X0,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X2,u1_struct_0(sK6))
    | r2_hidden(X1,X0)
    | ~ r2_hidden(X1,k10_yellow_6(sK6,sK2(sK6,X0,X2)))
    | ~ r2_hidden(X2,k2_pre_topc(sK6,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1061,c_42,c_41])).

cnf(c_2945,plain,
    ( ~ sP0(X0_60,sK6)
    | ~ m1_subset_1(X0_60,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1_60,u1_struct_0(sK6))
    | ~ m1_subset_1(X2_60,u1_struct_0(sK6))
    | r2_hidden(X1_60,X0_60)
    | ~ r2_hidden(X1_60,k10_yellow_6(sK6,sK2(sK6,X0_60,X2_60)))
    | ~ r2_hidden(X2_60,k2_pre_topc(sK6,X0_60)) ),
    inference(subtyping,[status(esa)],[c_1065])).

cnf(c_3104,plain,
    ( ~ sP0(X0_60,sK6)
    | ~ m1_subset_1(X0_60,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1_60,u1_struct_0(sK6))
    | ~ m1_subset_1(sK9,u1_struct_0(sK6))
    | ~ r2_hidden(X1_60,k2_pre_topc(sK6,X0_60))
    | r2_hidden(sK9,X0_60)
    | ~ r2_hidden(sK9,k10_yellow_6(sK6,sK2(sK6,X0_60,X1_60))) ),
    inference(instantiation,[status(thm)],[c_2945])).

cnf(c_3121,plain,
    ( ~ sP0(X0_60,sK6)
    | ~ m1_subset_1(X0_60,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK9,u1_struct_0(sK6))
    | r2_hidden(sK9,X0_60)
    | ~ r2_hidden(sK9,k10_yellow_6(sK6,sK2(sK6,X0_60,sK9)))
    | ~ r2_hidden(sK9,k2_pre_topc(sK6,X0_60)) ),
    inference(instantiation,[status(thm)],[c_3104])).

cnf(c_3123,plain,
    ( ~ sP0(sK7,sK6)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK9,u1_struct_0(sK6))
    | ~ r2_hidden(sK9,k10_yellow_6(sK6,sK2(sK6,sK7,sK9)))
    | ~ r2_hidden(sK9,k2_pre_topc(sK6,sK7))
    | r2_hidden(sK9,sK7) ),
    inference(instantiation,[status(thm)],[c_3121])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(sK5(X1,X0,X2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
    | ~ r2_hidden(X2,k2_pre_topc(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1093,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | m1_subset_1(sK5(sK6,X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
    | ~ r2_hidden(X1,k2_pre_topc(sK6,X0))
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6) ),
    inference(resolution,[status(thm)],[c_24,c_40])).

cnf(c_1097,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | m1_subset_1(sK5(sK6,X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
    | ~ r2_hidden(X1,k2_pre_topc(sK6,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1093,c_42,c_41])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,k2_pre_topc(X1,X0))
    | ~ v1_xboole_0(sK5(X1,X0,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_27,plain,
    ( v2_waybel_0(sK5(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_26,plain,
    ( v13_waybel_0(sK5(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_25,plain,
    ( v3_waybel_7(sK5(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_22,plain,
    ( r2_waybel_7(X0,sK5(X0,X1,X2),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_38,negated_conjecture,
    ( ~ r2_waybel_7(sK6,X0,X1)
    | ~ v2_waybel_0(X0,k3_yellow_1(k2_struct_0(sK6)))
    | ~ v13_waybel_0(X0,k3_yellow_1(k2_struct_0(sK6)))
    | ~ v3_waybel_7(X0,k3_yellow_1(k2_struct_0(sK6)))
    | v4_pre_topc(sK7,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | r2_hidden(X1,sK7)
    | ~ r2_hidden(sK7,X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_740,plain,
    ( ~ v2_waybel_0(sK5(sK6,X0,X1),k3_yellow_1(k2_struct_0(sK6)))
    | ~ v13_waybel_0(sK5(sK6,X0,X1),k3_yellow_1(k2_struct_0(sK6)))
    | ~ v3_waybel_7(sK5(sK6,X0,X1),k3_yellow_1(k2_struct_0(sK6)))
    | v4_pre_topc(sK7,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(sK5(sK6,X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
    | ~ r2_hidden(X1,k2_pre_topc(sK6,X0))
    | r2_hidden(X1,sK7)
    | ~ r2_hidden(sK7,sK5(sK6,X0,X1))
    | v1_xboole_0(sK5(sK6,X0,X1))
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK6)
    | v2_struct_0(sK6) ),
    inference(resolution,[status(thm)],[c_22,c_38])).

cnf(c_744,plain,
    ( v1_xboole_0(sK5(sK6,X0,X1))
    | ~ r2_hidden(sK7,sK5(sK6,X0,X1))
    | r2_hidden(X1,sK7)
    | ~ r2_hidden(X1,k2_pre_topc(sK6,X0))
    | ~ m1_subset_1(sK5(sK6,X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | v4_pre_topc(sK7,sK6)
    | ~ v3_waybel_7(sK5(sK6,X0,X1),k3_yellow_1(k2_struct_0(sK6)))
    | ~ v13_waybel_0(sK5(sK6,X0,X1),k3_yellow_1(k2_struct_0(sK6)))
    | ~ v2_waybel_0(sK5(sK6,X0,X1),k3_yellow_1(k2_struct_0(sK6))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_740,c_42,c_41,c_40])).

cnf(c_745,plain,
    ( ~ v2_waybel_0(sK5(sK6,X0,X1),k3_yellow_1(k2_struct_0(sK6)))
    | ~ v13_waybel_0(sK5(sK6,X0,X1),k3_yellow_1(k2_struct_0(sK6)))
    | ~ v3_waybel_7(sK5(sK6,X0,X1),k3_yellow_1(k2_struct_0(sK6)))
    | v4_pre_topc(sK7,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(sK5(sK6,X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
    | ~ r2_hidden(X1,k2_pre_topc(sK6,X0))
    | r2_hidden(X1,sK7)
    | ~ r2_hidden(sK7,sK5(sK6,X0,X1))
    | v1_xboole_0(sK5(sK6,X0,X1)) ),
    inference(renaming,[status(thm)],[c_744])).

cnf(c_801,plain,
    ( ~ v2_waybel_0(sK5(sK6,X0,X1),k3_yellow_1(k2_struct_0(sK6)))
    | ~ v13_waybel_0(sK5(sK6,X0,X1),k3_yellow_1(k2_struct_0(sK6)))
    | v4_pre_topc(sK7,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(sK5(sK6,X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
    | ~ r2_hidden(X1,k2_pre_topc(sK6,X0))
    | r2_hidden(X1,sK7)
    | ~ r2_hidden(sK7,sK5(sK6,X0,X1))
    | v1_xboole_0(sK5(sK6,X0,X1))
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK6)
    | v2_struct_0(sK6) ),
    inference(resolution,[status(thm)],[c_25,c_745])).

cnf(c_805,plain,
    ( v1_xboole_0(sK5(sK6,X0,X1))
    | ~ r2_hidden(sK7,sK5(sK6,X0,X1))
    | r2_hidden(X1,sK7)
    | ~ r2_hidden(X1,k2_pre_topc(sK6,X0))
    | ~ m1_subset_1(sK5(sK6,X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | v4_pre_topc(sK7,sK6)
    | ~ v13_waybel_0(sK5(sK6,X0,X1),k3_yellow_1(k2_struct_0(sK6)))
    | ~ v2_waybel_0(sK5(sK6,X0,X1),k3_yellow_1(k2_struct_0(sK6))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_801,c_42,c_41,c_40])).

cnf(c_806,plain,
    ( ~ v2_waybel_0(sK5(sK6,X0,X1),k3_yellow_1(k2_struct_0(sK6)))
    | ~ v13_waybel_0(sK5(sK6,X0,X1),k3_yellow_1(k2_struct_0(sK6)))
    | v4_pre_topc(sK7,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(sK5(sK6,X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
    | ~ r2_hidden(X1,k2_pre_topc(sK6,X0))
    | r2_hidden(X1,sK7)
    | ~ r2_hidden(sK7,sK5(sK6,X0,X1))
    | v1_xboole_0(sK5(sK6,X0,X1)) ),
    inference(renaming,[status(thm)],[c_805])).

cnf(c_853,plain,
    ( ~ v2_waybel_0(sK5(sK6,X0,X1),k3_yellow_1(k2_struct_0(sK6)))
    | v4_pre_topc(sK7,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(sK5(sK6,X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
    | ~ r2_hidden(X1,k2_pre_topc(sK6,X0))
    | r2_hidden(X1,sK7)
    | ~ r2_hidden(sK7,sK5(sK6,X0,X1))
    | v1_xboole_0(sK5(sK6,X0,X1))
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK6)
    | v2_struct_0(sK6) ),
    inference(resolution,[status(thm)],[c_26,c_806])).

cnf(c_857,plain,
    ( v1_xboole_0(sK5(sK6,X0,X1))
    | ~ r2_hidden(sK7,sK5(sK6,X0,X1))
    | r2_hidden(X1,sK7)
    | ~ r2_hidden(X1,k2_pre_topc(sK6,X0))
    | ~ m1_subset_1(sK5(sK6,X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | v4_pre_topc(sK7,sK6)
    | ~ v2_waybel_0(sK5(sK6,X0,X1),k3_yellow_1(k2_struct_0(sK6))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_853,c_42,c_41,c_40])).

cnf(c_858,plain,
    ( ~ v2_waybel_0(sK5(sK6,X0,X1),k3_yellow_1(k2_struct_0(sK6)))
    | v4_pre_topc(sK7,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(sK5(sK6,X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
    | ~ r2_hidden(X1,k2_pre_topc(sK6,X0))
    | r2_hidden(X1,sK7)
    | ~ r2_hidden(sK7,sK5(sK6,X0,X1))
    | v1_xboole_0(sK5(sK6,X0,X1)) ),
    inference(renaming,[status(thm)],[c_857])).

cnf(c_901,plain,
    ( v4_pre_topc(sK7,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(sK5(sK6,X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
    | ~ r2_hidden(X1,k2_pre_topc(sK6,X0))
    | r2_hidden(X1,sK7)
    | ~ r2_hidden(sK7,sK5(sK6,X0,X1))
    | v1_xboole_0(sK5(sK6,X0,X1))
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK6)
    | v2_struct_0(sK6) ),
    inference(resolution,[status(thm)],[c_27,c_858])).

cnf(c_905,plain,
    ( v1_xboole_0(sK5(sK6,X0,X1))
    | ~ r2_hidden(sK7,sK5(sK6,X0,X1))
    | r2_hidden(X1,sK7)
    | ~ r2_hidden(X1,k2_pre_topc(sK6,X0))
    | ~ m1_subset_1(sK5(sK6,X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | v4_pre_topc(sK7,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_901,c_42,c_41,c_40])).

cnf(c_906,plain,
    ( v4_pre_topc(sK7,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(sK5(sK6,X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
    | ~ r2_hidden(X1,k2_pre_topc(sK6,X0))
    | r2_hidden(X1,sK7)
    | ~ r2_hidden(sK7,sK5(sK6,X0,X1))
    | v1_xboole_0(sK5(sK6,X0,X1)) ),
    inference(renaming,[status(thm)],[c_905])).

cnf(c_945,plain,
    ( v4_pre_topc(sK7,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(sK5(sK6,X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
    | ~ r2_hidden(X1,k2_pre_topc(sK6,X0))
    | r2_hidden(X1,sK7)
    | ~ r2_hidden(sK7,sK5(sK6,X0,X1))
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK6)
    | v2_struct_0(sK6) ),
    inference(resolution,[status(thm)],[c_28,c_906])).

cnf(c_949,plain,
    ( ~ r2_hidden(sK7,sK5(sK6,X0,X1))
    | r2_hidden(X1,sK7)
    | ~ r2_hidden(X1,k2_pre_topc(sK6,X0))
    | ~ m1_subset_1(sK5(sK6,X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | v4_pre_topc(sK7,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_945,c_42,c_41,c_40])).

cnf(c_950,plain,
    ( v4_pre_topc(sK7,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(sK5(sK6,X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
    | ~ r2_hidden(X1,k2_pre_topc(sK6,X0))
    | r2_hidden(X1,sK7)
    | ~ r2_hidden(sK7,sK5(sK6,X0,X1)) ),
    inference(renaming,[status(thm)],[c_949])).

cnf(c_1233,plain,
    ( v4_pre_topc(sK7,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ r2_hidden(X1,k2_pre_topc(sK6,X0))
    | r2_hidden(X1,sK7)
    | ~ r2_hidden(sK7,sK5(sK6,X0,X1)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1097,c_950])).

cnf(c_2942,plain,
    ( v4_pre_topc(sK7,sK6)
    | ~ m1_subset_1(X0_60,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1_60,u1_struct_0(sK6))
    | ~ r2_hidden(X1_60,k2_pre_topc(sK6,X0_60))
    | r2_hidden(X1_60,sK7)
    | ~ r2_hidden(sK7,sK5(sK6,X0_60,X1_60)) ),
    inference(subtyping,[status(esa)],[c_1233])).

cnf(c_3076,plain,
    ( v4_pre_topc(sK7,sK6)
    | ~ m1_subset_1(X0_60,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK4(X1_60,sK6),u1_struct_0(sK6))
    | ~ r2_hidden(sK4(X1_60,sK6),k2_pre_topc(sK6,X0_60))
    | r2_hidden(sK4(X1_60,sK6),sK7)
    | ~ r2_hidden(sK7,sK5(sK6,X0_60,sK4(X1_60,sK6))) ),
    inference(instantiation,[status(thm)],[c_2942])).

cnf(c_3100,plain,
    ( v4_pre_topc(sK7,sK6)
    | ~ m1_subset_1(sK4(sK7,sK6),u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(sK4(sK7,sK6),k2_pre_topc(sK6,sK7))
    | r2_hidden(sK4(sK7,sK6),sK7)
    | ~ r2_hidden(sK7,sK5(sK6,sK7,sK4(sK7,sK6))) ),
    inference(instantiation,[status(thm)],[c_3076])).

cnf(c_0,plain,
    ( ~ r1_waybel_0(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v3_yellow_6(X1,X0)
    | ~ l1_waybel_0(X1,X0)
    | ~ r2_hidden(X3,k10_yellow_6(X0,X1))
    | r2_hidden(X3,k2_pre_topc(X0,X2))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_13,plain,
    ( r1_waybel_0(X0,sK3(X1,X0),X1)
    | sP0(X1,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_613,plain,
    ( sP0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_yellow_6(sK3(X0,X1),X1)
    | ~ l1_waybel_0(sK3(X0,X1),X1)
    | ~ r2_hidden(X2,k10_yellow_6(X1,sK3(X0,X1)))
    | r2_hidden(X2,k2_pre_topc(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(sK3(X0,X1))
    | ~ v4_orders_2(sK3(X0,X1))
    | ~ v7_waybel_0(sK3(X0,X1)) ),
    inference(resolution,[status(thm)],[c_0,c_13])).

cnf(c_18,plain,
    ( sP0(X0,X1)
    | ~ v2_struct_0(sK3(X0,X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_17,plain,
    ( sP0(X0,X1)
    | v4_orders_2(sK3(X0,X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_16,plain,
    ( sP0(X0,X1)
    | v7_waybel_0(sK3(X0,X1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_15,plain,
    ( sP0(X0,X1)
    | v3_yellow_6(sK3(X0,X1),X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_14,plain,
    ( sP0(X0,X1)
    | l1_waybel_0(sK3(X0,X1),X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_617,plain,
    ( v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | r2_hidden(X2,k2_pre_topc(X1,X0))
    | ~ r2_hidden(X2,k10_yellow_6(X1,sK3(X0,X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sP0(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_613,c_18,c_17,c_16,c_15,c_14])).

cnf(c_618,plain,
    ( sP0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,k10_yellow_6(X1,sK3(X0,X1)))
    | r2_hidden(X2,k2_pre_topc(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1) ),
    inference(renaming,[status(thm)],[c_617])).

cnf(c_1010,plain,
    ( sP0(X0,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ r2_hidden(X1,k10_yellow_6(sK6,sK3(X0,sK6)))
    | r2_hidden(X1,k2_pre_topc(sK6,X0))
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6) ),
    inference(resolution,[status(thm)],[c_618,c_40])).

cnf(c_1014,plain,
    ( sP0(X0,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ r2_hidden(X1,k10_yellow_6(sK6,sK3(X0,sK6)))
    | r2_hidden(X1,k2_pre_topc(sK6,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1010,c_42,c_41])).

cnf(c_2947,plain,
    ( sP0(X0_60,sK6)
    | ~ m1_subset_1(X0_60,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1_60,u1_struct_0(sK6))
    | ~ r2_hidden(X1_60,k10_yellow_6(sK6,sK3(X0_60,sK6)))
    | r2_hidden(X1_60,k2_pre_topc(sK6,X0_60)) ),
    inference(subtyping,[status(esa)],[c_1014])).

cnf(c_3078,plain,
    ( sP0(X0_60,sK6)
    | ~ m1_subset_1(X0_60,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK4(X1_60,sK6),u1_struct_0(sK6))
    | ~ r2_hidden(sK4(X1_60,sK6),k10_yellow_6(sK6,sK3(X0_60,sK6)))
    | r2_hidden(sK4(X1_60,sK6),k2_pre_topc(sK6,X0_60)) ),
    inference(instantiation,[status(thm)],[c_2947])).

cnf(c_3092,plain,
    ( sP0(sK7,sK6)
    | ~ m1_subset_1(sK4(sK7,sK6),u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(sK4(sK7,sK6),k10_yellow_6(sK6,sK3(sK7,sK6)))
    | r2_hidden(sK4(sK7,sK6),k2_pre_topc(sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_3078])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X0,sK5(X1,X0,X2))
    | ~ r2_hidden(X2,k2_pre_topc(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1116,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | r2_hidden(X0,sK5(sK6,X0,X1))
    | ~ r2_hidden(X1,k2_pre_topc(sK6,X0))
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6) ),
    inference(resolution,[status(thm)],[c_23,c_40])).

cnf(c_1120,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | r2_hidden(X0,sK5(sK6,X0,X1))
    | ~ r2_hidden(X1,k2_pre_topc(sK6,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1116,c_42,c_41])).

cnf(c_2944,plain,
    ( ~ m1_subset_1(X0_60,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1_60,u1_struct_0(sK6))
    | r2_hidden(X0_60,sK5(sK6,X0_60,X1_60))
    | ~ r2_hidden(X1_60,k2_pre_topc(sK6,X0_60)) ),
    inference(subtyping,[status(esa)],[c_1120])).

cnf(c_3079,plain,
    ( ~ m1_subset_1(X0_60,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK4(X1_60,sK6),u1_struct_0(sK6))
    | r2_hidden(X0_60,sK5(sK6,X0_60,sK4(X1_60,sK6)))
    | ~ r2_hidden(sK4(X1_60,sK6),k2_pre_topc(sK6,X0_60)) ),
    inference(instantiation,[status(thm)],[c_2944])).

cnf(c_3088,plain,
    ( ~ m1_subset_1(sK4(sK7,sK6),u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(sK4(sK7,sK6),k2_pre_topc(sK6,sK7))
    | r2_hidden(sK7,sK5(sK6,sK7,sK4(sK7,sK6))) ),
    inference(instantiation,[status(thm)],[c_3079])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,k10_yellow_6(X1,sK2(X1,X0,X2)))
    | ~ r2_hidden(X2,k2_pre_topc(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1162,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | r2_hidden(X1,k10_yellow_6(sK6,sK2(sK6,X0,X1)))
    | ~ r2_hidden(X1,k2_pre_topc(sK6,X0))
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6) ),
    inference(resolution,[status(thm)],[c_1,c_40])).

cnf(c_1166,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | r2_hidden(X1,k10_yellow_6(sK6,sK2(sK6,X0,X1)))
    | ~ r2_hidden(X1,k2_pre_topc(sK6,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1162,c_42,c_41])).

cnf(c_2943,plain,
    ( ~ m1_subset_1(X0_60,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1_60,u1_struct_0(sK6))
    | r2_hidden(X1_60,k10_yellow_6(sK6,sK2(sK6,X0_60,X1_60)))
    | ~ r2_hidden(X1_60,k2_pre_topc(sK6,X0_60)) ),
    inference(subtyping,[status(esa)],[c_1166])).

cnf(c_3047,plain,
    ( ~ m1_subset_1(X0_60,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK9,u1_struct_0(sK6))
    | r2_hidden(sK9,k10_yellow_6(sK6,sK2(sK6,X0_60,sK9)))
    | ~ r2_hidden(sK9,k2_pre_topc(sK6,X0_60)) ),
    inference(instantiation,[status(thm)],[c_2943])).

cnf(c_3049,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK9,u1_struct_0(sK6))
    | r2_hidden(sK9,k10_yellow_6(sK6,sK2(sK6,sK7,sK9)))
    | ~ r2_hidden(sK9,k2_pre_topc(sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_3047])).

cnf(c_8,plain,
    ( ~ sP1(X0,X1)
    | ~ sP0(X1,X0)
    | v4_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_20,plain,
    ( sP1(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1185,plain,
    ( sP1(sK6,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6) ),
    inference(resolution,[status(thm)],[c_20,c_40])).

cnf(c_1189,plain,
    ( sP1(sK6,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1185,c_42,c_41])).

cnf(c_1271,plain,
    ( ~ sP0(X0,sK6)
    | v4_pre_topc(X0,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(resolution,[status(thm)],[c_8,c_1189])).

cnf(c_2940,plain,
    ( ~ sP0(X0_60,sK6)
    | v4_pre_topc(X0_60,sK6)
    | ~ m1_subset_1(X0_60,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(subtyping,[status(esa)],[c_1271])).

cnf(c_2994,plain,
    ( ~ sP0(sK7,sK6)
    | v4_pre_topc(sK7,sK6)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(instantiation,[status(thm)],[c_2940])).

cnf(c_9,plain,
    ( ~ sP1(X0,X1)
    | sP0(X1,X0)
    | ~ v4_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1257,plain,
    ( sP0(X0,sK6)
    | ~ v4_pre_topc(X0,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(resolution,[status(thm)],[c_9,c_1189])).

cnf(c_2941,plain,
    ( sP0(X0_60,sK6)
    | ~ v4_pre_topc(X0_60,sK6)
    | ~ m1_subset_1(X0_60,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(subtyping,[status(esa)],[c_1257])).

cnf(c_2991,plain,
    ( sP0(sK7,sK6)
    | ~ v4_pre_topc(sK7,sK6)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(instantiation,[status(thm)],[c_2941])).

cnf(c_21,plain,
    ( ~ r2_waybel_7(X0,X1,X2)
    | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
    | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
    | ~ v3_waybel_7(X1,k3_yellow_1(k2_struct_0(X0)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(X2,k2_pre_topc(X0,X3))
    | v1_xboole_0(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_30,negated_conjecture,
    ( r2_waybel_7(sK6,sK8,sK9)
    | ~ v4_pre_topc(sK7,sK6) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_717,plain,
    ( ~ v2_waybel_0(sK8,k3_yellow_1(k2_struct_0(sK6)))
    | ~ v13_waybel_0(sK8,k3_yellow_1(k2_struct_0(sK6)))
    | ~ v3_waybel_7(sK8,k3_yellow_1(k2_struct_0(sK6)))
    | ~ v4_pre_topc(sK7,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
    | ~ m1_subset_1(sK9,u1_struct_0(sK6))
    | ~ r2_hidden(X0,sK8)
    | r2_hidden(sK9,k2_pre_topc(sK6,X0))
    | v1_xboole_0(sK8)
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK6)
    | v2_struct_0(sK6) ),
    inference(resolution,[status(thm)],[c_21,c_30])).

cnf(c_37,negated_conjecture,
    ( ~ v4_pre_topc(sK7,sK6)
    | ~ v1_xboole_0(sK8) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_36,negated_conjecture,
    ( v2_waybel_0(sK8,k3_yellow_1(k2_struct_0(sK6)))
    | ~ v4_pre_topc(sK7,sK6) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_35,negated_conjecture,
    ( v13_waybel_0(sK8,k3_yellow_1(k2_struct_0(sK6)))
    | ~ v4_pre_topc(sK7,sK6) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_34,negated_conjecture,
    ( v3_waybel_7(sK8,k3_yellow_1(k2_struct_0(sK6)))
    | ~ v4_pre_topc(sK7,sK6) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_33,negated_conjecture,
    ( ~ v4_pre_topc(sK7,sK6)
    | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_31,negated_conjecture,
    ( ~ v4_pre_topc(sK7,sK6)
    | m1_subset_1(sK9,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_721,plain,
    ( ~ v4_pre_topc(sK7,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(X0,sK8)
    | r2_hidden(sK9,k2_pre_topc(sK6,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_717,c_42,c_41,c_40,c_37,c_36,c_35,c_34,c_33,c_31])).

cnf(c_2949,plain,
    ( ~ v4_pre_topc(sK7,sK6)
    | ~ m1_subset_1(X0_60,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(X0_60,sK8)
    | r2_hidden(sK9,k2_pre_topc(sK6,X0_60)) ),
    inference(subtyping,[status(esa)],[c_721])).

cnf(c_2971,plain,
    ( ~ v4_pre_topc(sK7,sK6)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(sK7,sK8)
    | r2_hidden(sK9,k2_pre_topc(sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_2949])).

cnf(c_12,plain,
    ( sP0(X0,X1)
    | m1_subset_1(sK4(X0,X1),u1_struct_0(X1)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2954,plain,
    ( sP0(X0_60,X0_61)
    | m1_subset_1(sK4(X0_60,X0_61),u1_struct_0(X0_61)) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_2964,plain,
    ( sP0(sK7,sK6)
    | m1_subset_1(sK4(sK7,sK6),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_2954])).

cnf(c_11,plain,
    ( sP0(X0,X1)
    | r2_hidden(sK4(X0,X1),k10_yellow_6(X1,sK3(X0,X1))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2955,plain,
    ( sP0(X0_60,X0_61)
    | r2_hidden(sK4(X0_60,X0_61),k10_yellow_6(X0_61,sK3(X0_60,X0_61))) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_2961,plain,
    ( sP0(sK7,sK6)
    | r2_hidden(sK4(sK7,sK6),k10_yellow_6(sK6,sK3(sK7,sK6))) ),
    inference(instantiation,[status(thm)],[c_2955])).

cnf(c_10,plain,
    ( sP0(X0,X1)
    | ~ r2_hidden(sK4(X0,X1),X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2956,plain,
    ( sP0(X0_60,X0_61)
    | ~ r2_hidden(sK4(X0_60,X0_61),X0_60) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_2958,plain,
    ( sP0(sK7,sK6)
    | ~ r2_hidden(sK4(sK7,sK6),sK7) ),
    inference(instantiation,[status(thm)],[c_2956])).

cnf(c_29,negated_conjecture,
    ( ~ v4_pre_topc(sK7,sK6)
    | ~ r2_hidden(sK9,sK7) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1754,plain,
    ( ~ sP0(sK7,sK6)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(sK9,sK7) ),
    inference(resolution,[status(thm)],[c_29,c_1271])).

cnf(c_39,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1756,plain,
    ( ~ sP0(sK7,sK6)
    | ~ r2_hidden(sK9,sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1754,c_39])).

cnf(c_1741,plain,
    ( ~ sP0(sK7,sK6)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | m1_subset_1(sK9,u1_struct_0(sK6)) ),
    inference(resolution,[status(thm)],[c_31,c_1271])).

cnf(c_1743,plain,
    ( ~ sP0(sK7,sK6)
    | m1_subset_1(sK9,u1_struct_0(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1741,c_39])).

cnf(c_32,negated_conjecture,
    ( ~ v4_pre_topc(sK7,sK6)
    | r2_hidden(sK7,sK8) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1728,plain,
    ( ~ sP0(sK7,sK6)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | r2_hidden(sK7,sK8) ),
    inference(resolution,[status(thm)],[c_32,c_1271])).

cnf(c_1730,plain,
    ( ~ sP0(sK7,sK6)
    | r2_hidden(sK7,sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1728,c_39])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3123,c_3100,c_3092,c_3088,c_3049,c_2994,c_2991,c_2971,c_2964,c_2961,c_2958,c_1756,c_1743,c_1730,c_39])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:24:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.48/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.48/0.99  
% 1.48/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.48/0.99  
% 1.48/0.99  ------  iProver source info
% 1.48/0.99  
% 1.48/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.48/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.48/0.99  git: non_committed_changes: false
% 1.48/0.99  git: last_make_outside_of_git: false
% 1.48/0.99  
% 1.48/0.99  ------ 
% 1.48/0.99  
% 1.48/0.99  ------ Input Options
% 1.48/0.99  
% 1.48/0.99  --out_options                           all
% 1.48/0.99  --tptp_safe_out                         true
% 1.48/0.99  --problem_path                          ""
% 1.48/0.99  --include_path                          ""
% 1.48/0.99  --clausifier                            res/vclausify_rel
% 1.48/0.99  --clausifier_options                    --mode clausify
% 1.48/0.99  --stdin                                 false
% 1.48/0.99  --stats_out                             all
% 1.48/0.99  
% 1.48/0.99  ------ General Options
% 1.48/0.99  
% 1.48/0.99  --fof                                   false
% 1.48/0.99  --time_out_real                         305.
% 1.48/0.99  --time_out_virtual                      -1.
% 1.48/0.99  --symbol_type_check                     false
% 1.48/0.99  --clausify_out                          false
% 1.48/0.99  --sig_cnt_out                           false
% 1.48/0.99  --trig_cnt_out                          false
% 1.48/0.99  --trig_cnt_out_tolerance                1.
% 1.48/0.99  --trig_cnt_out_sk_spl                   false
% 1.48/0.99  --abstr_cl_out                          false
% 1.48/0.99  
% 1.48/0.99  ------ Global Options
% 1.48/0.99  
% 1.48/0.99  --schedule                              default
% 1.48/0.99  --add_important_lit                     false
% 1.48/0.99  --prop_solver_per_cl                    1000
% 1.48/0.99  --min_unsat_core                        false
% 1.48/0.99  --soft_assumptions                      false
% 1.48/0.99  --soft_lemma_size                       3
% 1.48/0.99  --prop_impl_unit_size                   0
% 1.48/0.99  --prop_impl_unit                        []
% 1.48/0.99  --share_sel_clauses                     true
% 1.48/0.99  --reset_solvers                         false
% 1.48/0.99  --bc_imp_inh                            [conj_cone]
% 1.48/0.99  --conj_cone_tolerance                   3.
% 1.48/0.99  --extra_neg_conj                        none
% 1.48/0.99  --large_theory_mode                     true
% 1.48/0.99  --prolific_symb_bound                   200
% 1.48/0.99  --lt_threshold                          2000
% 1.48/0.99  --clause_weak_htbl                      true
% 1.48/0.99  --gc_record_bc_elim                     false
% 1.48/0.99  
% 1.48/0.99  ------ Preprocessing Options
% 1.48/0.99  
% 1.48/0.99  --preprocessing_flag                    true
% 1.48/0.99  --time_out_prep_mult                    0.1
% 1.48/0.99  --splitting_mode                        input
% 1.48/0.99  --splitting_grd                         true
% 1.48/0.99  --splitting_cvd                         false
% 1.48/0.99  --splitting_cvd_svl                     false
% 1.48/0.99  --splitting_nvd                         32
% 1.48/0.99  --sub_typing                            true
% 1.48/0.99  --prep_gs_sim                           true
% 1.48/0.99  --prep_unflatten                        true
% 1.48/0.99  --prep_res_sim                          true
% 1.48/0.99  --prep_upred                            true
% 1.48/0.99  --prep_sem_filter                       exhaustive
% 1.48/0.99  --prep_sem_filter_out                   false
% 1.48/0.99  --pred_elim                             true
% 1.48/0.99  --res_sim_input                         true
% 1.48/0.99  --eq_ax_congr_red                       true
% 1.48/0.99  --pure_diseq_elim                       true
% 1.48/0.99  --brand_transform                       false
% 1.48/0.99  --non_eq_to_eq                          false
% 1.48/0.99  --prep_def_merge                        true
% 1.48/0.99  --prep_def_merge_prop_impl              false
% 1.48/0.99  --prep_def_merge_mbd                    true
% 1.48/0.99  --prep_def_merge_tr_red                 false
% 1.48/0.99  --prep_def_merge_tr_cl                  false
% 1.48/0.99  --smt_preprocessing                     true
% 1.48/0.99  --smt_ac_axioms                         fast
% 1.48/0.99  --preprocessed_out                      false
% 1.48/0.99  --preprocessed_stats                    false
% 1.48/0.99  
% 1.48/0.99  ------ Abstraction refinement Options
% 1.48/0.99  
% 1.48/0.99  --abstr_ref                             []
% 1.48/0.99  --abstr_ref_prep                        false
% 1.48/0.99  --abstr_ref_until_sat                   false
% 1.48/0.99  --abstr_ref_sig_restrict                funpre
% 1.48/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.48/0.99  --abstr_ref_under                       []
% 1.48/0.99  
% 1.48/0.99  ------ SAT Options
% 1.48/0.99  
% 1.48/0.99  --sat_mode                              false
% 1.48/0.99  --sat_fm_restart_options                ""
% 1.48/0.99  --sat_gr_def                            false
% 1.48/0.99  --sat_epr_types                         true
% 1.48/0.99  --sat_non_cyclic_types                  false
% 1.48/0.99  --sat_finite_models                     false
% 1.48/0.99  --sat_fm_lemmas                         false
% 1.48/0.99  --sat_fm_prep                           false
% 1.48/0.99  --sat_fm_uc_incr                        true
% 1.48/0.99  --sat_out_model                         small
% 1.48/0.99  --sat_out_clauses                       false
% 1.48/0.99  
% 1.48/0.99  ------ QBF Options
% 1.48/0.99  
% 1.48/0.99  --qbf_mode                              false
% 1.48/0.99  --qbf_elim_univ                         false
% 1.48/0.99  --qbf_dom_inst                          none
% 1.48/0.99  --qbf_dom_pre_inst                      false
% 1.48/0.99  --qbf_sk_in                             false
% 1.48/0.99  --qbf_pred_elim                         true
% 1.48/0.99  --qbf_split                             512
% 1.48/0.99  
% 1.48/0.99  ------ BMC1 Options
% 1.48/0.99  
% 1.48/0.99  --bmc1_incremental                      false
% 1.48/0.99  --bmc1_axioms                           reachable_all
% 1.48/0.99  --bmc1_min_bound                        0
% 1.48/0.99  --bmc1_max_bound                        -1
% 1.48/0.99  --bmc1_max_bound_default                -1
% 1.48/0.99  --bmc1_symbol_reachability              true
% 1.48/0.99  --bmc1_property_lemmas                  false
% 1.48/0.99  --bmc1_k_induction                      false
% 1.48/0.99  --bmc1_non_equiv_states                 false
% 1.48/0.99  --bmc1_deadlock                         false
% 1.48/0.99  --bmc1_ucm                              false
% 1.48/0.99  --bmc1_add_unsat_core                   none
% 1.48/0.99  --bmc1_unsat_core_children              false
% 1.48/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.48/0.99  --bmc1_out_stat                         full
% 1.48/0.99  --bmc1_ground_init                      false
% 1.48/0.99  --bmc1_pre_inst_next_state              false
% 1.48/0.99  --bmc1_pre_inst_state                   false
% 1.48/0.99  --bmc1_pre_inst_reach_state             false
% 1.48/0.99  --bmc1_out_unsat_core                   false
% 1.48/0.99  --bmc1_aig_witness_out                  false
% 1.48/0.99  --bmc1_verbose                          false
% 1.48/0.99  --bmc1_dump_clauses_tptp                false
% 1.48/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.48/0.99  --bmc1_dump_file                        -
% 1.48/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.48/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.48/0.99  --bmc1_ucm_extend_mode                  1
% 1.48/0.99  --bmc1_ucm_init_mode                    2
% 1.48/0.99  --bmc1_ucm_cone_mode                    none
% 1.48/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.48/0.99  --bmc1_ucm_relax_model                  4
% 1.48/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.48/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.48/0.99  --bmc1_ucm_layered_model                none
% 1.48/0.99  --bmc1_ucm_max_lemma_size               10
% 1.48/0.99  
% 1.48/0.99  ------ AIG Options
% 1.48/0.99  
% 1.48/0.99  --aig_mode                              false
% 1.48/0.99  
% 1.48/0.99  ------ Instantiation Options
% 1.48/0.99  
% 1.48/0.99  --instantiation_flag                    true
% 1.48/0.99  --inst_sos_flag                         false
% 1.48/0.99  --inst_sos_phase                        true
% 1.48/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.48/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.48/0.99  --inst_lit_sel_side                     num_symb
% 1.48/0.99  --inst_solver_per_active                1400
% 1.48/0.99  --inst_solver_calls_frac                1.
% 1.48/0.99  --inst_passive_queue_type               priority_queues
% 1.48/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.48/0.99  --inst_passive_queues_freq              [25;2]
% 1.48/0.99  --inst_dismatching                      true
% 1.48/0.99  --inst_eager_unprocessed_to_passive     true
% 1.48/0.99  --inst_prop_sim_given                   true
% 1.48/0.99  --inst_prop_sim_new                     false
% 1.48/0.99  --inst_subs_new                         false
% 1.48/0.99  --inst_eq_res_simp                      false
% 1.48/0.99  --inst_subs_given                       false
% 1.48/0.99  --inst_orphan_elimination               true
% 1.48/0.99  --inst_learning_loop_flag               true
% 1.48/0.99  --inst_learning_start                   3000
% 1.48/0.99  --inst_learning_factor                  2
% 1.48/0.99  --inst_start_prop_sim_after_learn       3
% 1.48/0.99  --inst_sel_renew                        solver
% 1.48/0.99  --inst_lit_activity_flag                true
% 1.48/0.99  --inst_restr_to_given                   false
% 1.48/0.99  --inst_activity_threshold               500
% 1.48/0.99  --inst_out_proof                        true
% 1.48/0.99  
% 1.48/0.99  ------ Resolution Options
% 1.48/0.99  
% 1.48/0.99  --resolution_flag                       true
% 1.48/0.99  --res_lit_sel                           adaptive
% 1.48/0.99  --res_lit_sel_side                      none
% 1.48/0.99  --res_ordering                          kbo
% 1.48/0.99  --res_to_prop_solver                    active
% 1.48/0.99  --res_prop_simpl_new                    false
% 1.48/0.99  --res_prop_simpl_given                  true
% 1.48/0.99  --res_passive_queue_type                priority_queues
% 1.48/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.48/0.99  --res_passive_queues_freq               [15;5]
% 1.48/0.99  --res_forward_subs                      full
% 1.48/0.99  --res_backward_subs                     full
% 1.48/0.99  --res_forward_subs_resolution           true
% 1.48/0.99  --res_backward_subs_resolution          true
% 1.48/0.99  --res_orphan_elimination                true
% 1.48/0.99  --res_time_limit                        2.
% 1.48/0.99  --res_out_proof                         true
% 1.48/0.99  
% 1.48/0.99  ------ Superposition Options
% 1.48/0.99  
% 1.48/0.99  --superposition_flag                    true
% 1.48/0.99  --sup_passive_queue_type                priority_queues
% 1.48/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.48/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.48/0.99  --demod_completeness_check              fast
% 1.48/0.99  --demod_use_ground                      true
% 1.48/0.99  --sup_to_prop_solver                    passive
% 1.48/0.99  --sup_prop_simpl_new                    true
% 1.48/0.99  --sup_prop_simpl_given                  true
% 1.48/0.99  --sup_fun_splitting                     false
% 1.48/0.99  --sup_smt_interval                      50000
% 1.48/0.99  
% 1.48/0.99  ------ Superposition Simplification Setup
% 1.48/0.99  
% 1.48/0.99  --sup_indices_passive                   []
% 1.48/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.48/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.48/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.48/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.48/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.48/0.99  --sup_full_bw                           [BwDemod]
% 1.48/0.99  --sup_immed_triv                        [TrivRules]
% 1.48/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.48/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.48/0.99  --sup_immed_bw_main                     []
% 1.48/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.48/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.48/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.48/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.48/0.99  
% 1.48/0.99  ------ Combination Options
% 1.48/0.99  
% 1.48/0.99  --comb_res_mult                         3
% 1.48/0.99  --comb_sup_mult                         2
% 1.48/0.99  --comb_inst_mult                        10
% 1.48/0.99  
% 1.48/0.99  ------ Debug Options
% 1.48/0.99  
% 1.48/0.99  --dbg_backtrace                         false
% 1.48/0.99  --dbg_dump_prop_clauses                 false
% 1.48/0.99  --dbg_dump_prop_clauses_file            -
% 1.48/0.99  --dbg_out_stat                          false
% 1.48/0.99  ------ Parsing...
% 1.48/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.48/0.99  
% 1.48/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e  sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 1.48/0.99  
% 1.48/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.48/0.99  ------ Proving...
% 1.48/0.99  ------ Problem Properties 
% 1.48/0.99  
% 1.48/0.99  
% 1.48/0.99  clauses                                 17
% 1.48/0.99  conjectures                             4
% 1.48/0.99  EPR                                     2
% 1.48/0.99  Horn                                    13
% 1.48/0.99  unary                                   1
% 1.48/0.99  binary                                  6
% 1.48/0.99  lits                                    61
% 1.48/0.99  lits eq                                 0
% 1.48/0.99  fd_pure                                 0
% 1.48/0.99  fd_pseudo                               0
% 1.48/0.99  fd_cond                                 0
% 1.48/0.99  fd_pseudo_cond                          0
% 1.48/0.99  AC symbols                              0
% 1.48/0.99  
% 1.48/0.99  ------ Schedule dynamic 5 is on 
% 1.48/0.99  
% 1.48/0.99  ------ no equalities: superposition off 
% 1.48/0.99  
% 1.48/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.48/0.99  
% 1.48/0.99  
% 1.48/0.99  ------ 
% 1.48/0.99  Current options:
% 1.48/0.99  ------ 
% 1.48/0.99  
% 1.48/0.99  ------ Input Options
% 1.48/0.99  
% 1.48/0.99  --out_options                           all
% 1.48/0.99  --tptp_safe_out                         true
% 1.48/0.99  --problem_path                          ""
% 1.48/0.99  --include_path                          ""
% 1.48/0.99  --clausifier                            res/vclausify_rel
% 1.48/0.99  --clausifier_options                    --mode clausify
% 1.48/0.99  --stdin                                 false
% 1.48/0.99  --stats_out                             all
% 1.48/0.99  
% 1.48/0.99  ------ General Options
% 1.48/0.99  
% 1.48/0.99  --fof                                   false
% 1.48/0.99  --time_out_real                         305.
% 1.48/0.99  --time_out_virtual                      -1.
% 1.48/0.99  --symbol_type_check                     false
% 1.48/0.99  --clausify_out                          false
% 1.48/0.99  --sig_cnt_out                           false
% 1.48/0.99  --trig_cnt_out                          false
% 1.48/0.99  --trig_cnt_out_tolerance                1.
% 1.48/0.99  --trig_cnt_out_sk_spl                   false
% 1.48/0.99  --abstr_cl_out                          false
% 1.48/0.99  
% 1.48/0.99  ------ Global Options
% 1.48/0.99  
% 1.48/0.99  --schedule                              default
% 1.48/0.99  --add_important_lit                     false
% 1.48/0.99  --prop_solver_per_cl                    1000
% 1.48/0.99  --min_unsat_core                        false
% 1.48/0.99  --soft_assumptions                      false
% 1.48/0.99  --soft_lemma_size                       3
% 1.48/0.99  --prop_impl_unit_size                   0
% 1.48/0.99  --prop_impl_unit                        []
% 1.48/0.99  --share_sel_clauses                     true
% 1.48/0.99  --reset_solvers                         false
% 1.48/0.99  --bc_imp_inh                            [conj_cone]
% 1.48/0.99  --conj_cone_tolerance                   3.
% 1.48/0.99  --extra_neg_conj                        none
% 1.48/0.99  --large_theory_mode                     true
% 1.48/0.99  --prolific_symb_bound                   200
% 1.48/0.99  --lt_threshold                          2000
% 1.48/0.99  --clause_weak_htbl                      true
% 1.48/0.99  --gc_record_bc_elim                     false
% 1.48/0.99  
% 1.48/0.99  ------ Preprocessing Options
% 1.48/0.99  
% 1.48/0.99  --preprocessing_flag                    true
% 1.48/0.99  --time_out_prep_mult                    0.1
% 1.48/0.99  --splitting_mode                        input
% 1.48/0.99  --splitting_grd                         true
% 1.48/0.99  --splitting_cvd                         false
% 1.48/0.99  --splitting_cvd_svl                     false
% 1.48/0.99  --splitting_nvd                         32
% 1.48/0.99  --sub_typing                            true
% 1.48/0.99  --prep_gs_sim                           true
% 1.48/0.99  --prep_unflatten                        true
% 1.48/0.99  --prep_res_sim                          true
% 1.48/0.99  --prep_upred                            true
% 1.48/0.99  --prep_sem_filter                       exhaustive
% 1.48/0.99  --prep_sem_filter_out                   false
% 1.48/0.99  --pred_elim                             true
% 1.48/0.99  --res_sim_input                         true
% 1.48/0.99  --eq_ax_congr_red                       true
% 1.48/0.99  --pure_diseq_elim                       true
% 1.48/0.99  --brand_transform                       false
% 1.48/0.99  --non_eq_to_eq                          false
% 1.48/0.99  --prep_def_merge                        true
% 1.48/0.99  --prep_def_merge_prop_impl              false
% 1.48/0.99  --prep_def_merge_mbd                    true
% 1.48/0.99  --prep_def_merge_tr_red                 false
% 1.48/0.99  --prep_def_merge_tr_cl                  false
% 1.48/0.99  --smt_preprocessing                     true
% 1.48/0.99  --smt_ac_axioms                         fast
% 1.48/0.99  --preprocessed_out                      false
% 1.48/0.99  --preprocessed_stats                    false
% 1.48/0.99  
% 1.48/0.99  ------ Abstraction refinement Options
% 1.48/0.99  
% 1.48/0.99  --abstr_ref                             []
% 1.48/0.99  --abstr_ref_prep                        false
% 1.48/0.99  --abstr_ref_until_sat                   false
% 1.48/0.99  --abstr_ref_sig_restrict                funpre
% 1.48/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.48/0.99  --abstr_ref_under                       []
% 1.48/0.99  
% 1.48/0.99  ------ SAT Options
% 1.48/0.99  
% 1.48/0.99  --sat_mode                              false
% 1.48/0.99  --sat_fm_restart_options                ""
% 1.48/0.99  --sat_gr_def                            false
% 1.48/0.99  --sat_epr_types                         true
% 1.48/0.99  --sat_non_cyclic_types                  false
% 1.48/0.99  --sat_finite_models                     false
% 1.48/0.99  --sat_fm_lemmas                         false
% 1.48/0.99  --sat_fm_prep                           false
% 1.48/0.99  --sat_fm_uc_incr                        true
% 1.48/0.99  --sat_out_model                         small
% 1.48/0.99  --sat_out_clauses                       false
% 1.48/0.99  
% 1.48/0.99  ------ QBF Options
% 1.48/0.99  
% 1.48/0.99  --qbf_mode                              false
% 1.48/0.99  --qbf_elim_univ                         false
% 1.48/0.99  --qbf_dom_inst                          none
% 1.48/0.99  --qbf_dom_pre_inst                      false
% 1.48/0.99  --qbf_sk_in                             false
% 1.48/0.99  --qbf_pred_elim                         true
% 1.48/0.99  --qbf_split                             512
% 1.48/0.99  
% 1.48/0.99  ------ BMC1 Options
% 1.48/0.99  
% 1.48/0.99  --bmc1_incremental                      false
% 1.48/0.99  --bmc1_axioms                           reachable_all
% 1.48/0.99  --bmc1_min_bound                        0
% 1.48/0.99  --bmc1_max_bound                        -1
% 1.48/0.99  --bmc1_max_bound_default                -1
% 1.48/0.99  --bmc1_symbol_reachability              true
% 1.48/0.99  --bmc1_property_lemmas                  false
% 1.48/0.99  --bmc1_k_induction                      false
% 1.48/0.99  --bmc1_non_equiv_states                 false
% 1.48/0.99  --bmc1_deadlock                         false
% 1.48/0.99  --bmc1_ucm                              false
% 1.48/0.99  --bmc1_add_unsat_core                   none
% 1.48/0.99  --bmc1_unsat_core_children              false
% 1.48/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.48/0.99  --bmc1_out_stat                         full
% 1.48/0.99  --bmc1_ground_init                      false
% 1.48/0.99  --bmc1_pre_inst_next_state              false
% 1.48/0.99  --bmc1_pre_inst_state                   false
% 1.48/0.99  --bmc1_pre_inst_reach_state             false
% 1.48/0.99  --bmc1_out_unsat_core                   false
% 1.48/0.99  --bmc1_aig_witness_out                  false
% 1.48/0.99  --bmc1_verbose                          false
% 1.48/0.99  --bmc1_dump_clauses_tptp                false
% 1.48/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.48/0.99  --bmc1_dump_file                        -
% 1.48/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.48/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.48/0.99  --bmc1_ucm_extend_mode                  1
% 1.48/0.99  --bmc1_ucm_init_mode                    2
% 1.48/0.99  --bmc1_ucm_cone_mode                    none
% 1.48/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.48/0.99  --bmc1_ucm_relax_model                  4
% 1.48/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.48/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.48/0.99  --bmc1_ucm_layered_model                none
% 1.48/0.99  --bmc1_ucm_max_lemma_size               10
% 1.48/0.99  
% 1.48/0.99  ------ AIG Options
% 1.48/0.99  
% 1.48/0.99  --aig_mode                              false
% 1.48/0.99  
% 1.48/0.99  ------ Instantiation Options
% 1.48/0.99  
% 1.48/0.99  --instantiation_flag                    true
% 1.48/0.99  --inst_sos_flag                         false
% 1.48/0.99  --inst_sos_phase                        true
% 1.48/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.48/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.48/0.99  --inst_lit_sel_side                     none
% 1.48/0.99  --inst_solver_per_active                1400
% 1.48/0.99  --inst_solver_calls_frac                1.
% 1.48/0.99  --inst_passive_queue_type               priority_queues
% 1.48/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.48/0.99  --inst_passive_queues_freq              [25;2]
% 1.48/0.99  --inst_dismatching                      true
% 1.48/0.99  --inst_eager_unprocessed_to_passive     true
% 1.48/0.99  --inst_prop_sim_given                   true
% 1.48/0.99  --inst_prop_sim_new                     false
% 1.48/0.99  --inst_subs_new                         false
% 1.48/0.99  --inst_eq_res_simp                      false
% 1.48/0.99  --inst_subs_given                       false
% 1.48/0.99  --inst_orphan_elimination               true
% 1.48/0.99  --inst_learning_loop_flag               true
% 1.48/0.99  --inst_learning_start                   3000
% 1.48/0.99  --inst_learning_factor                  2
% 1.48/0.99  --inst_start_prop_sim_after_learn       3
% 1.48/0.99  --inst_sel_renew                        solver
% 1.48/0.99  --inst_lit_activity_flag                true
% 1.48/0.99  --inst_restr_to_given                   false
% 1.48/0.99  --inst_activity_threshold               500
% 1.48/0.99  --inst_out_proof                        true
% 1.48/0.99  
% 1.48/0.99  ------ Resolution Options
% 1.48/0.99  
% 1.48/0.99  --resolution_flag                       false
% 1.48/0.99  --res_lit_sel                           adaptive
% 1.48/0.99  --res_lit_sel_side                      none
% 1.48/0.99  --res_ordering                          kbo
% 1.48/0.99  --res_to_prop_solver                    active
% 1.48/0.99  --res_prop_simpl_new                    false
% 1.48/0.99  --res_prop_simpl_given                  true
% 1.48/0.99  --res_passive_queue_type                priority_queues
% 1.48/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.48/0.99  --res_passive_queues_freq               [15;5]
% 1.48/0.99  --res_forward_subs                      full
% 1.48/0.99  --res_backward_subs                     full
% 1.48/0.99  --res_forward_subs_resolution           true
% 1.48/0.99  --res_backward_subs_resolution          true
% 1.48/0.99  --res_orphan_elimination                true
% 1.48/0.99  --res_time_limit                        2.
% 1.48/0.99  --res_out_proof                         true
% 1.48/0.99  
% 1.48/0.99  ------ Superposition Options
% 1.48/0.99  
% 1.48/0.99  --superposition_flag                    false
% 1.48/0.99  --sup_passive_queue_type                priority_queues
% 1.48/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.48/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.48/0.99  --demod_completeness_check              fast
% 1.48/0.99  --demod_use_ground                      true
% 1.48/0.99  --sup_to_prop_solver                    passive
% 1.48/0.99  --sup_prop_simpl_new                    true
% 1.48/0.99  --sup_prop_simpl_given                  true
% 1.48/0.99  --sup_fun_splitting                     false
% 1.48/0.99  --sup_smt_interval                      50000
% 1.48/0.99  
% 1.48/0.99  ------ Superposition Simplification Setup
% 1.48/0.99  
% 1.48/0.99  --sup_indices_passive                   []
% 1.48/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.48/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.48/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.48/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.48/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.48/0.99  --sup_full_bw                           [BwDemod]
% 1.48/0.99  --sup_immed_triv                        [TrivRules]
% 1.48/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.48/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.48/0.99  --sup_immed_bw_main                     []
% 1.48/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.48/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.48/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.48/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.48/0.99  
% 1.48/0.99  ------ Combination Options
% 1.48/0.99  
% 1.48/0.99  --comb_res_mult                         3
% 1.48/0.99  --comb_sup_mult                         2
% 1.48/0.99  --comb_inst_mult                        10
% 1.48/0.99  
% 1.48/0.99  ------ Debug Options
% 1.48/0.99  
% 1.48/0.99  --dbg_backtrace                         false
% 1.48/0.99  --dbg_dump_prop_clauses                 false
% 1.48/0.99  --dbg_dump_prop_clauses_file            -
% 1.48/0.99  --dbg_out_stat                          false
% 1.48/0.99  
% 1.48/0.99  
% 1.48/0.99  
% 1.48/0.99  
% 1.48/0.99  ------ Proving...
% 1.48/0.99  
% 1.48/0.99  
% 1.48/0.99  % SZS status Theorem for theBenchmark.p
% 1.48/0.99  
% 1.48/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 1.48/0.99  
% 1.48/0.99  fof(f14,plain,(
% 1.48/0.99    ! [X1,X0] : (sP0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,k10_yellow_6(X0,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_waybel_0(X0,X2,X1) | ~l1_waybel_0(X2,X0) | ~v3_yellow_6(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2)))),
% 1.48/0.99    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.48/0.99  
% 1.48/0.99  fof(f22,plain,(
% 1.48/0.99    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r2_hidden(X3,k10_yellow_6(X0,X2)) & m1_subset_1(X3,u1_struct_0(X0))) & r1_waybel_0(X0,X2,X1) & l1_waybel_0(X2,X0) & v3_yellow_6(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2))) & (! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,k10_yellow_6(X0,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_waybel_0(X0,X2,X1) | ~l1_waybel_0(X2,X0) | ~v3_yellow_6(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2)) | ~sP0(X1,X0)))),
% 1.48/0.99    inference(nnf_transformation,[],[f14])).
% 1.48/0.99  
% 1.48/0.99  fof(f23,plain,(
% 1.48/0.99    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (? [X3] : (~r2_hidden(X3,X0) & r2_hidden(X3,k10_yellow_6(X1,X2)) & m1_subset_1(X3,u1_struct_0(X1))) & r1_waybel_0(X1,X2,X0) & l1_waybel_0(X2,X1) & v3_yellow_6(X2,X1) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2))) & (! [X4] : (! [X5] : (r2_hidden(X5,X0) | ~r2_hidden(X5,k10_yellow_6(X1,X4)) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r1_waybel_0(X1,X4,X0) | ~l1_waybel_0(X4,X1) | ~v3_yellow_6(X4,X1) | ~v7_waybel_0(X4) | ~v4_orders_2(X4) | v2_struct_0(X4)) | ~sP0(X0,X1)))),
% 1.48/0.99    inference(rectify,[],[f22])).
% 1.48/0.99  
% 1.48/0.99  fof(f25,plain,(
% 1.48/0.99    ( ! [X2] : (! [X1,X0] : (? [X3] : (~r2_hidden(X3,X0) & r2_hidden(X3,k10_yellow_6(X1,X2)) & m1_subset_1(X3,u1_struct_0(X1))) => (~r2_hidden(sK4(X0,X1),X0) & r2_hidden(sK4(X0,X1),k10_yellow_6(X1,X2)) & m1_subset_1(sK4(X0,X1),u1_struct_0(X1))))) )),
% 1.48/0.99    introduced(choice_axiom,[])).
% 1.48/0.99  
% 1.48/0.99  fof(f24,plain,(
% 1.48/0.99    ! [X1,X0] : (? [X2] : (? [X3] : (~r2_hidden(X3,X0) & r2_hidden(X3,k10_yellow_6(X1,X2)) & m1_subset_1(X3,u1_struct_0(X1))) & r1_waybel_0(X1,X2,X0) & l1_waybel_0(X2,X1) & v3_yellow_6(X2,X1) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => (? [X3] : (~r2_hidden(X3,X0) & r2_hidden(X3,k10_yellow_6(X1,sK3(X0,X1))) & m1_subset_1(X3,u1_struct_0(X1))) & r1_waybel_0(X1,sK3(X0,X1),X0) & l1_waybel_0(sK3(X0,X1),X1) & v3_yellow_6(sK3(X0,X1),X1) & v7_waybel_0(sK3(X0,X1)) & v4_orders_2(sK3(X0,X1)) & ~v2_struct_0(sK3(X0,X1))))),
% 1.48/0.99    introduced(choice_axiom,[])).
% 1.48/0.99  
% 1.48/0.99  fof(f26,plain,(
% 1.48/0.99    ! [X0,X1] : ((sP0(X0,X1) | ((~r2_hidden(sK4(X0,X1),X0) & r2_hidden(sK4(X0,X1),k10_yellow_6(X1,sK3(X0,X1))) & m1_subset_1(sK4(X0,X1),u1_struct_0(X1))) & r1_waybel_0(X1,sK3(X0,X1),X0) & l1_waybel_0(sK3(X0,X1),X1) & v3_yellow_6(sK3(X0,X1),X1) & v7_waybel_0(sK3(X0,X1)) & v4_orders_2(sK3(X0,X1)) & ~v2_struct_0(sK3(X0,X1)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X0) | ~r2_hidden(X5,k10_yellow_6(X1,X4)) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r1_waybel_0(X1,X4,X0) | ~l1_waybel_0(X4,X1) | ~v3_yellow_6(X4,X1) | ~v7_waybel_0(X4) | ~v4_orders_2(X4) | v2_struct_0(X4)) | ~sP0(X0,X1)))),
% 1.48/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f23,f25,f24])).
% 1.48/0.99  
% 1.48/0.99  fof(f49,plain,(
% 1.48/0.99    ( ! [X4,X0,X5,X1] : (r2_hidden(X5,X0) | ~r2_hidden(X5,k10_yellow_6(X1,X4)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~r1_waybel_0(X1,X4,X0) | ~l1_waybel_0(X4,X1) | ~v3_yellow_6(X4,X1) | ~v7_waybel_0(X4) | ~v4_orders_2(X4) | v2_struct_0(X4) | ~sP0(X0,X1)) )),
% 1.48/0.99    inference(cnf_transformation,[],[f26])).
% 1.48/0.99  
% 1.48/0.99  fof(f1,axiom,(
% 1.48/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & r1_waybel_0(X0,X3,X1) & l1_waybel_0(X3,X0) & v3_yellow_6(X3,X0) & v7_waybel_0(X3) & v4_orders_2(X3) & ~v2_struct_0(X3))))))),
% 1.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.48/0.99  
% 1.48/0.99  fof(f6,plain,(
% 1.48/0.99    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & r1_waybel_0(X0,X3,X1) & l1_waybel_0(X3,X0) & v3_yellow_6(X3,X0) & v7_waybel_0(X3) & v4_orders_2(X3) & ~v2_struct_0(X3))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.48/0.99    inference(ennf_transformation,[],[f1])).
% 1.48/0.99  
% 1.48/0.99  fof(f7,plain,(
% 1.48/0.99    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & r1_waybel_0(X0,X3,X1) & l1_waybel_0(X3,X0) & v3_yellow_6(X3,X0) & v7_waybel_0(X3) & v4_orders_2(X3) & ~v2_struct_0(X3))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.48/0.99    inference(flattening,[],[f6])).
% 1.48/0.99  
% 1.48/0.99  fof(f17,plain,(
% 1.48/0.99    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ! [X3] : (~r2_hidden(X2,k10_yellow_6(X0,X3)) | ~r1_waybel_0(X0,X3,X1) | ~l1_waybel_0(X3,X0) | ~v3_yellow_6(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3))) & (? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & r1_waybel_0(X0,X3,X1) & l1_waybel_0(X3,X0) & v3_yellow_6(X3,X0) & v7_waybel_0(X3) & v4_orders_2(X3) & ~v2_struct_0(X3)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.48/0.99    inference(nnf_transformation,[],[f7])).
% 1.48/0.99  
% 1.48/0.99  fof(f18,plain,(
% 1.48/0.99    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ! [X3] : (~r2_hidden(X2,k10_yellow_6(X0,X3)) | ~r1_waybel_0(X0,X3,X1) | ~l1_waybel_0(X3,X0) | ~v3_yellow_6(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3))) & (? [X4] : (r2_hidden(X2,k10_yellow_6(X0,X4)) & r1_waybel_0(X0,X4,X1) & l1_waybel_0(X4,X0) & v3_yellow_6(X4,X0) & v7_waybel_0(X4) & v4_orders_2(X4) & ~v2_struct_0(X4)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.48/0.99    inference(rectify,[],[f17])).
% 1.48/0.99  
% 1.48/0.99  fof(f19,plain,(
% 1.48/0.99    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X2,k10_yellow_6(X0,X4)) & r1_waybel_0(X0,X4,X1) & l1_waybel_0(X4,X0) & v3_yellow_6(X4,X0) & v7_waybel_0(X4) & v4_orders_2(X4) & ~v2_struct_0(X4)) => (r2_hidden(X2,k10_yellow_6(X0,sK2(X0,X1,X2))) & r1_waybel_0(X0,sK2(X0,X1,X2),X1) & l1_waybel_0(sK2(X0,X1,X2),X0) & v3_yellow_6(sK2(X0,X1,X2),X0) & v7_waybel_0(sK2(X0,X1,X2)) & v4_orders_2(sK2(X0,X1,X2)) & ~v2_struct_0(sK2(X0,X1,X2))))),
% 1.48/0.99    introduced(choice_axiom,[])).
% 1.48/0.99  
% 1.48/0.99  fof(f20,plain,(
% 1.48/0.99    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ! [X3] : (~r2_hidden(X2,k10_yellow_6(X0,X3)) | ~r1_waybel_0(X0,X3,X1) | ~l1_waybel_0(X3,X0) | ~v3_yellow_6(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3))) & ((r2_hidden(X2,k10_yellow_6(X0,sK2(X0,X1,X2))) & r1_waybel_0(X0,sK2(X0,X1,X2),X1) & l1_waybel_0(sK2(X0,X1,X2),X0) & v3_yellow_6(sK2(X0,X1,X2),X0) & v7_waybel_0(sK2(X0,X1,X2)) & v4_orders_2(sK2(X0,X1,X2)) & ~v2_struct_0(sK2(X0,X1,X2))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.48/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f19])).
% 1.48/0.99  
% 1.48/0.99  fof(f44,plain,(
% 1.48/0.99    ( ! [X2,X0,X1] : (r1_waybel_0(X0,sK2(X0,X1,X2),X1) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.48/0.99    inference(cnf_transformation,[],[f20])).
% 1.48/0.99  
% 1.48/0.99  fof(f41,plain,(
% 1.48/0.99    ( ! [X2,X0,X1] : (v7_waybel_0(sK2(X0,X1,X2)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.48/0.99    inference(cnf_transformation,[],[f20])).
% 1.48/0.99  
% 1.48/0.99  fof(f40,plain,(
% 1.48/0.99    ( ! [X2,X0,X1] : (v4_orders_2(sK2(X0,X1,X2)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.48/0.99    inference(cnf_transformation,[],[f20])).
% 1.48/0.99  
% 1.48/0.99  fof(f39,plain,(
% 1.48/0.99    ( ! [X2,X0,X1] : (~v2_struct_0(sK2(X0,X1,X2)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.48/0.99    inference(cnf_transformation,[],[f20])).
% 1.48/0.99  
% 1.48/0.99  fof(f43,plain,(
% 1.48/0.99    ( ! [X2,X0,X1] : (l1_waybel_0(sK2(X0,X1,X2),X0) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.48/0.99    inference(cnf_transformation,[],[f20])).
% 1.48/0.99  
% 1.48/0.99  fof(f42,plain,(
% 1.48/0.99    ( ! [X2,X0,X1] : (v3_yellow_6(sK2(X0,X1,X2),X0) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.48/0.99    inference(cnf_transformation,[],[f20])).
% 1.48/0.99  
% 1.48/0.99  fof(f4,conjecture,(
% 1.48/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X2)) => (r2_hidden(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_waybel_7(X0,X2,X3) => r2_hidden(X3,X1))))))))),
% 1.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.48/0.99  
% 1.48/0.99  fof(f5,negated_conjecture,(
% 1.48/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X2)) => (r2_hidden(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_waybel_7(X0,X2,X3) => r2_hidden(X3,X1))))))))),
% 1.48/0.99    inference(negated_conjecture,[],[f4])).
% 1.48/0.99  
% 1.48/0.99  fof(f12,plain,(
% 1.48/0.99    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> ! [X2] : ((! [X3] : ((r2_hidden(X3,X1) | ~r2_waybel_7(X0,X2,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_hidden(X1,X2)) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0))) | ~v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X2)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.48/0.99    inference(ennf_transformation,[],[f5])).
% 1.48/0.99  
% 1.48/0.99  fof(f13,plain,(
% 1.48/0.99    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r2_waybel_7(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0))) | ~v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X2))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.48/0.99    inference(flattening,[],[f12])).
% 1.48/0.99  
% 1.48/0.99  fof(f31,plain,(
% 1.48/0.99    ? [X0] : (? [X1] : (((? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r2_waybel_7(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) & r2_hidden(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X2)) | ~v4_pre_topc(X1,X0)) & (! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r2_waybel_7(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0))) | ~v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X2)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.48/0.99    inference(nnf_transformation,[],[f13])).
% 1.48/0.99  
% 1.48/0.99  fof(f32,plain,(
% 1.48/0.99    ? [X0] : (? [X1] : ((? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r2_waybel_7(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) & r2_hidden(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X2)) | ~v4_pre_topc(X1,X0)) & (! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r2_waybel_7(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0))) | ~v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X2)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.48/0.99    inference(flattening,[],[f31])).
% 1.48/0.99  
% 1.48/0.99  fof(f33,plain,(
% 1.48/0.99    ? [X0] : (? [X1] : ((? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r2_waybel_7(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) & r2_hidden(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X2)) | ~v4_pre_topc(X1,X0)) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r2_waybel_7(X0,X4,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~r2_hidden(X1,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v3_waybel_7(X4,k3_yellow_1(k2_struct_0(X0))) | ~v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X4)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.48/0.99    inference(rectify,[],[f32])).
% 1.48/0.99  
% 1.48/0.99  fof(f37,plain,(
% 1.48/0.99    ( ! [X2,X0,X1] : (? [X3] : (~r2_hidden(X3,X1) & r2_waybel_7(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r2_hidden(sK9,X1) & r2_waybel_7(X0,X2,sK9) & m1_subset_1(sK9,u1_struct_0(X0)))) )),
% 1.48/0.99    introduced(choice_axiom,[])).
% 1.48/0.99  
% 1.48/0.99  fof(f36,plain,(
% 1.48/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r2_waybel_7(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) & r2_hidden(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X2)) => (? [X3] : (~r2_hidden(X3,X1) & r2_waybel_7(X0,sK8,X3) & m1_subset_1(X3,u1_struct_0(X0))) & r2_hidden(X1,sK8) & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v3_waybel_7(sK8,k3_yellow_1(k2_struct_0(X0))) & v13_waybel_0(sK8,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(sK8,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(sK8))) )),
% 1.48/0.99    introduced(choice_axiom,[])).
% 1.48/0.99  
% 1.48/0.99  fof(f35,plain,(
% 1.48/0.99    ( ! [X0] : (? [X1] : ((? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r2_waybel_7(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) & r2_hidden(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X2)) | ~v4_pre_topc(X1,X0)) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r2_waybel_7(X0,X4,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~r2_hidden(X1,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v3_waybel_7(X4,k3_yellow_1(k2_struct_0(X0))) | ~v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X4)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((? [X2] : (? [X3] : (~r2_hidden(X3,sK7) & r2_waybel_7(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) & r2_hidden(sK7,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X2)) | ~v4_pre_topc(sK7,X0)) & (! [X4] : (! [X5] : (r2_hidden(X5,sK7) | ~r2_waybel_7(X0,X4,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~r2_hidden(sK7,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v3_waybel_7(X4,k3_yellow_1(k2_struct_0(X0))) | ~v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X4)) | v4_pre_topc(sK7,X0)) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 1.48/0.99    introduced(choice_axiom,[])).
% 1.48/0.99  
% 1.48/0.99  fof(f34,plain,(
% 1.48/0.99    ? [X0] : (? [X1] : ((? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r2_waybel_7(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) & r2_hidden(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X2)) | ~v4_pre_topc(X1,X0)) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r2_waybel_7(X0,X4,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~r2_hidden(X1,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v3_waybel_7(X4,k3_yellow_1(k2_struct_0(X0))) | ~v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X4)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r2_waybel_7(sK6,X2,X3) & m1_subset_1(X3,u1_struct_0(sK6))) & r2_hidden(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))) & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(sK6))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK6))) & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(sK6))) & ~v1_xboole_0(X2)) | ~v4_pre_topc(X1,sK6)) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r2_waybel_7(sK6,X4,X5) | ~m1_subset_1(X5,u1_struct_0(sK6))) | ~r2_hidden(X1,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))) | ~v3_waybel_7(X4,k3_yellow_1(k2_struct_0(sK6))) | ~v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK6))) | ~v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK6))) | v1_xboole_0(X4)) | v4_pre_topc(X1,sK6)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))) & l1_pre_topc(sK6) & v2_pre_topc(sK6) & ~v2_struct_0(sK6))),
% 1.48/0.99    introduced(choice_axiom,[])).
% 1.48/0.99  
% 1.48/0.99  fof(f38,plain,(
% 1.48/0.99    ((((~r2_hidden(sK9,sK7) & r2_waybel_7(sK6,sK8,sK9) & m1_subset_1(sK9,u1_struct_0(sK6))) & r2_hidden(sK7,sK8) & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))) & v3_waybel_7(sK8,k3_yellow_1(k2_struct_0(sK6))) & v13_waybel_0(sK8,k3_yellow_1(k2_struct_0(sK6))) & v2_waybel_0(sK8,k3_yellow_1(k2_struct_0(sK6))) & ~v1_xboole_0(sK8)) | ~v4_pre_topc(sK7,sK6)) & (! [X4] : (! [X5] : (r2_hidden(X5,sK7) | ~r2_waybel_7(sK6,X4,X5) | ~m1_subset_1(X5,u1_struct_0(sK6))) | ~r2_hidden(sK7,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))) | ~v3_waybel_7(X4,k3_yellow_1(k2_struct_0(sK6))) | ~v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK6))) | ~v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK6))) | v1_xboole_0(X4)) | v4_pre_topc(sK7,sK6)) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))) & l1_pre_topc(sK6) & v2_pre_topc(sK6) & ~v2_struct_0(sK6)),
% 1.48/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f33,f37,f36,f35,f34])).
% 1.48/0.99  
% 1.48/0.99  fof(f70,plain,(
% 1.48/0.99    l1_pre_topc(sK6)),
% 1.48/0.99    inference(cnf_transformation,[],[f38])).
% 1.48/0.99  
% 1.48/0.99  fof(f68,plain,(
% 1.48/0.99    ~v2_struct_0(sK6)),
% 1.48/0.99    inference(cnf_transformation,[],[f38])).
% 1.48/0.99  
% 1.48/0.99  fof(f69,plain,(
% 1.48/0.99    v2_pre_topc(sK6)),
% 1.48/0.99    inference(cnf_transformation,[],[f38])).
% 1.48/0.99  
% 1.48/0.99  fof(f3,axiom,(
% 1.48/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ? [X3] : (r2_waybel_7(X0,X3,X2) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0))) & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X3))))))),
% 1.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.48/0.99  
% 1.48/0.99  fof(f10,plain,(
% 1.48/0.99    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ? [X3] : (r2_waybel_7(X0,X3,X2) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0))) & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X3))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.48/0.99    inference(ennf_transformation,[],[f3])).
% 1.48/0.99  
% 1.48/0.99  fof(f11,plain,(
% 1.48/0.99    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ? [X3] : (r2_waybel_7(X0,X3,X2) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0))) & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X3))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.48/0.99    inference(flattening,[],[f10])).
% 1.48/0.99  
% 1.48/0.99  fof(f27,plain,(
% 1.48/0.99    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ! [X3] : (~r2_waybel_7(X0,X3,X2) | ~r2_hidden(X1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0))) | ~v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X3))) & (? [X3] : (r2_waybel_7(X0,X3,X2) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0))) & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X3)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.48/0.99    inference(nnf_transformation,[],[f11])).
% 1.48/0.99  
% 1.48/0.99  fof(f28,plain,(
% 1.48/0.99    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ! [X3] : (~r2_waybel_7(X0,X3,X2) | ~r2_hidden(X1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0))) | ~v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X3))) & (? [X4] : (r2_waybel_7(X0,X4,X2) & r2_hidden(X1,X4) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v3_waybel_7(X4,k3_yellow_1(k2_struct_0(X0))) & v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X4)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.48/0.99    inference(rectify,[],[f27])).
% 1.48/0.99  
% 1.48/0.99  fof(f29,plain,(
% 1.48/0.99    ! [X2,X1,X0] : (? [X4] : (r2_waybel_7(X0,X4,X2) & r2_hidden(X1,X4) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v3_waybel_7(X4,k3_yellow_1(k2_struct_0(X0))) & v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X4)) => (r2_waybel_7(X0,sK5(X0,X1,X2),X2) & r2_hidden(X1,sK5(X0,X1,X2)) & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v3_waybel_7(sK5(X0,X1,X2),k3_yellow_1(k2_struct_0(X0))) & v13_waybel_0(sK5(X0,X1,X2),k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(sK5(X0,X1,X2),k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(sK5(X0,X1,X2))))),
% 1.48/0.99    introduced(choice_axiom,[])).
% 1.48/0.99  
% 1.48/0.99  fof(f30,plain,(
% 1.48/0.99    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ! [X3] : (~r2_waybel_7(X0,X3,X2) | ~r2_hidden(X1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0))) | ~v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X3))) & ((r2_waybel_7(X0,sK5(X0,X1,X2),X2) & r2_hidden(X1,sK5(X0,X1,X2)) & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v3_waybel_7(sK5(X0,X1,X2),k3_yellow_1(k2_struct_0(X0))) & v13_waybel_0(sK5(X0,X1,X2),k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(sK5(X0,X1,X2),k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(sK5(X0,X1,X2))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.48/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f28,f29])).
% 1.48/0.99  
% 1.48/0.99  fof(f64,plain,(
% 1.48/0.99    ( ! [X2,X0,X1] : (m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.48/0.99    inference(cnf_transformation,[],[f30])).
% 1.48/0.99  
% 1.48/0.99  fof(f60,plain,(
% 1.48/0.99    ( ! [X2,X0,X1] : (~v1_xboole_0(sK5(X0,X1,X2)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.48/0.99    inference(cnf_transformation,[],[f30])).
% 1.48/0.99  
% 1.48/0.99  fof(f61,plain,(
% 1.48/0.99    ( ! [X2,X0,X1] : (v2_waybel_0(sK5(X0,X1,X2),k3_yellow_1(k2_struct_0(X0))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.48/0.99    inference(cnf_transformation,[],[f30])).
% 1.48/0.99  
% 1.48/0.99  fof(f62,plain,(
% 1.48/0.99    ( ! [X2,X0,X1] : (v13_waybel_0(sK5(X0,X1,X2),k3_yellow_1(k2_struct_0(X0))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.48/0.99    inference(cnf_transformation,[],[f30])).
% 1.48/0.99  
% 1.48/0.99  fof(f63,plain,(
% 1.48/0.99    ( ! [X2,X0,X1] : (v3_waybel_7(sK5(X0,X1,X2),k3_yellow_1(k2_struct_0(X0))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.48/0.99    inference(cnf_transformation,[],[f30])).
% 1.48/0.99  
% 1.48/0.99  fof(f66,plain,(
% 1.48/0.99    ( ! [X2,X0,X1] : (r2_waybel_7(X0,sK5(X0,X1,X2),X2) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.48/0.99    inference(cnf_transformation,[],[f30])).
% 1.48/0.99  
% 1.48/0.99  fof(f72,plain,(
% 1.48/0.99    ( ! [X4,X5] : (r2_hidden(X5,sK7) | ~r2_waybel_7(sK6,X4,X5) | ~m1_subset_1(X5,u1_struct_0(sK6)) | ~r2_hidden(sK7,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))) | ~v3_waybel_7(X4,k3_yellow_1(k2_struct_0(sK6))) | ~v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK6))) | ~v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK6))) | v1_xboole_0(X4) | v4_pre_topc(sK7,sK6)) )),
% 1.48/0.99    inference(cnf_transformation,[],[f38])).
% 1.48/0.99  
% 1.48/0.99  fof(f46,plain,(
% 1.48/0.99    ( ! [X2,X0,X3,X1] : (r2_hidden(X2,k2_pre_topc(X0,X1)) | ~r2_hidden(X2,k10_yellow_6(X0,X3)) | ~r1_waybel_0(X0,X3,X1) | ~l1_waybel_0(X3,X0) | ~v3_yellow_6(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.48/0.99    inference(cnf_transformation,[],[f20])).
% 1.48/0.99  
% 1.48/0.99  fof(f55,plain,(
% 1.48/0.99    ( ! [X0,X1] : (sP0(X0,X1) | r1_waybel_0(X1,sK3(X0,X1),X0)) )),
% 1.48/0.99    inference(cnf_transformation,[],[f26])).
% 1.48/0.99  
% 1.48/0.99  fof(f50,plain,(
% 1.48/0.99    ( ! [X0,X1] : (sP0(X0,X1) | ~v2_struct_0(sK3(X0,X1))) )),
% 1.48/0.99    inference(cnf_transformation,[],[f26])).
% 1.48/0.99  
% 1.48/0.99  fof(f51,plain,(
% 1.48/0.99    ( ! [X0,X1] : (sP0(X0,X1) | v4_orders_2(sK3(X0,X1))) )),
% 1.48/0.99    inference(cnf_transformation,[],[f26])).
% 1.48/0.99  
% 1.48/0.99  fof(f52,plain,(
% 1.48/0.99    ( ! [X0,X1] : (sP0(X0,X1) | v7_waybel_0(sK3(X0,X1))) )),
% 1.48/0.99    inference(cnf_transformation,[],[f26])).
% 1.48/0.99  
% 1.48/0.99  fof(f53,plain,(
% 1.48/0.99    ( ! [X0,X1] : (sP0(X0,X1) | v3_yellow_6(sK3(X0,X1),X1)) )),
% 1.48/0.99    inference(cnf_transformation,[],[f26])).
% 1.48/0.99  
% 1.48/0.99  fof(f54,plain,(
% 1.48/0.99    ( ! [X0,X1] : (sP0(X0,X1) | l1_waybel_0(sK3(X0,X1),X1)) )),
% 1.48/0.99    inference(cnf_transformation,[],[f26])).
% 1.48/0.99  
% 1.48/0.99  fof(f65,plain,(
% 1.48/0.99    ( ! [X2,X0,X1] : (r2_hidden(X1,sK5(X0,X1,X2)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.48/0.99    inference(cnf_transformation,[],[f30])).
% 1.48/0.99  
% 1.48/0.99  fof(f45,plain,(
% 1.48/0.99    ( ! [X2,X0,X1] : (r2_hidden(X2,k10_yellow_6(X0,sK2(X0,X1,X2))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.48/0.99    inference(cnf_transformation,[],[f20])).
% 1.48/0.99  
% 1.48/0.99  fof(f15,plain,(
% 1.48/0.99    ! [X0,X1] : ((v4_pre_topc(X1,X0) <=> sP0(X1,X0)) | ~sP1(X0,X1))),
% 1.48/0.99    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.48/0.99  
% 1.48/0.99  fof(f21,plain,(
% 1.48/0.99    ! [X0,X1] : (((v4_pre_topc(X1,X0) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~v4_pre_topc(X1,X0))) | ~sP1(X0,X1))),
% 1.48/0.99    inference(nnf_transformation,[],[f15])).
% 1.48/0.99  
% 1.48/0.99  fof(f48,plain,(
% 1.48/0.99    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~sP0(X1,X0) | ~sP1(X0,X1)) )),
% 1.48/0.99    inference(cnf_transformation,[],[f21])).
% 1.48/0.99  
% 1.48/0.99  fof(f2,axiom,(
% 1.48/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> ! [X2] : ((l1_waybel_0(X2,X0) & v3_yellow_6(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => (r1_waybel_0(X0,X2,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,k10_yellow_6(X0,X2)) => r2_hidden(X3,X1))))))))),
% 1.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.48/0.99  
% 1.48/0.99  fof(f8,plain,(
% 1.48/0.99    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> ! [X2] : ((! [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,k10_yellow_6(X0,X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_waybel_0(X0,X2,X1)) | (~l1_waybel_0(X2,X0) | ~v3_yellow_6(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.48/0.99    inference(ennf_transformation,[],[f2])).
% 1.48/0.99  
% 1.48/0.99  fof(f9,plain,(
% 1.48/0.99    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,k10_yellow_6(X0,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_waybel_0(X0,X2,X1) | ~l1_waybel_0(X2,X0) | ~v3_yellow_6(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.48/0.99    inference(flattening,[],[f8])).
% 1.48/0.99  
% 1.48/0.99  fof(f16,plain,(
% 1.48/0.99    ! [X0] : (! [X1] : (sP1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.48/0.99    inference(definition_folding,[],[f9,f15,f14])).
% 1.48/0.99  
% 1.48/0.99  fof(f59,plain,(
% 1.48/0.99    ( ! [X0,X1] : (sP1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.48/0.99    inference(cnf_transformation,[],[f16])).
% 1.48/0.99  
% 1.48/0.99  fof(f47,plain,(
% 1.48/0.99    ( ! [X0,X1] : (sP0(X1,X0) | ~v4_pre_topc(X1,X0) | ~sP1(X0,X1)) )),
% 1.48/0.99    inference(cnf_transformation,[],[f21])).
% 1.48/0.99  
% 1.48/0.99  fof(f67,plain,(
% 1.48/0.99    ( ! [X2,X0,X3,X1] : (r2_hidden(X2,k2_pre_topc(X0,X1)) | ~r2_waybel_7(X0,X3,X2) | ~r2_hidden(X1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0))) | ~v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X3) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.48/0.99    inference(cnf_transformation,[],[f30])).
% 1.48/0.99  
% 1.48/0.99  fof(f80,plain,(
% 1.48/0.99    r2_waybel_7(sK6,sK8,sK9) | ~v4_pre_topc(sK7,sK6)),
% 1.48/0.99    inference(cnf_transformation,[],[f38])).
% 1.48/0.99  
% 1.48/0.99  fof(f73,plain,(
% 1.48/0.99    ~v1_xboole_0(sK8) | ~v4_pre_topc(sK7,sK6)),
% 1.48/0.99    inference(cnf_transformation,[],[f38])).
% 1.48/0.99  
% 1.48/0.99  fof(f74,plain,(
% 1.48/0.99    v2_waybel_0(sK8,k3_yellow_1(k2_struct_0(sK6))) | ~v4_pre_topc(sK7,sK6)),
% 1.48/0.99    inference(cnf_transformation,[],[f38])).
% 1.48/0.99  
% 1.48/0.99  fof(f75,plain,(
% 1.48/0.99    v13_waybel_0(sK8,k3_yellow_1(k2_struct_0(sK6))) | ~v4_pre_topc(sK7,sK6)),
% 1.48/0.99    inference(cnf_transformation,[],[f38])).
% 1.48/0.99  
% 1.48/0.99  fof(f76,plain,(
% 1.48/0.99    v3_waybel_7(sK8,k3_yellow_1(k2_struct_0(sK6))) | ~v4_pre_topc(sK7,sK6)),
% 1.48/0.99    inference(cnf_transformation,[],[f38])).
% 1.48/0.99  
% 1.48/0.99  fof(f77,plain,(
% 1.48/0.99    m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))) | ~v4_pre_topc(sK7,sK6)),
% 1.48/0.99    inference(cnf_transformation,[],[f38])).
% 1.48/0.99  
% 1.48/0.99  fof(f79,plain,(
% 1.48/0.99    m1_subset_1(sK9,u1_struct_0(sK6)) | ~v4_pre_topc(sK7,sK6)),
% 1.48/0.99    inference(cnf_transformation,[],[f38])).
% 1.48/0.99  
% 1.48/0.99  fof(f56,plain,(
% 1.48/0.99    ( ! [X0,X1] : (sP0(X0,X1) | m1_subset_1(sK4(X0,X1),u1_struct_0(X1))) )),
% 1.48/0.99    inference(cnf_transformation,[],[f26])).
% 1.48/0.99  
% 1.48/0.99  fof(f57,plain,(
% 1.48/0.99    ( ! [X0,X1] : (sP0(X0,X1) | r2_hidden(sK4(X0,X1),k10_yellow_6(X1,sK3(X0,X1)))) )),
% 1.48/0.99    inference(cnf_transformation,[],[f26])).
% 1.48/0.99  
% 1.48/0.99  fof(f58,plain,(
% 1.48/0.99    ( ! [X0,X1] : (sP0(X0,X1) | ~r2_hidden(sK4(X0,X1),X0)) )),
% 1.48/0.99    inference(cnf_transformation,[],[f26])).
% 1.48/0.99  
% 1.48/0.99  fof(f81,plain,(
% 1.48/0.99    ~r2_hidden(sK9,sK7) | ~v4_pre_topc(sK7,sK6)),
% 1.48/0.99    inference(cnf_transformation,[],[f38])).
% 1.48/0.99  
% 1.48/0.99  fof(f71,plain,(
% 1.48/0.99    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))),
% 1.48/0.99    inference(cnf_transformation,[],[f38])).
% 1.48/0.99  
% 1.48/0.99  fof(f78,plain,(
% 1.48/0.99    r2_hidden(sK7,sK8) | ~v4_pre_topc(sK7,sK6)),
% 1.48/0.99    inference(cnf_transformation,[],[f38])).
% 1.48/0.99  
% 1.48/0.99  cnf(c_19,plain,
% 1.48/0.99      ( ~ r1_waybel_0(X0,X1,X2)
% 1.48/0.99      | ~ sP0(X2,X0)
% 1.48/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.48/0.99      | ~ v3_yellow_6(X1,X0)
% 1.48/0.99      | ~ l1_waybel_0(X1,X0)
% 1.48/0.99      | r2_hidden(X3,X2)
% 1.48/0.99      | ~ r2_hidden(X3,k10_yellow_6(X0,X1))
% 1.48/0.99      | v2_struct_0(X1)
% 1.48/0.99      | ~ v4_orders_2(X1)
% 1.48/0.99      | ~ v7_waybel_0(X1) ),
% 1.48/0.99      inference(cnf_transformation,[],[f49]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_2,plain,
% 1.48/0.99      ( r1_waybel_0(X0,sK2(X0,X1,X2),X1)
% 1.48/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.48/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.48/0.99      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
% 1.48/0.99      | ~ v2_pre_topc(X0)
% 1.48/0.99      | ~ l1_pre_topc(X0)
% 1.48/0.99      | v2_struct_0(X0) ),
% 1.48/0.99      inference(cnf_transformation,[],[f44]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_523,plain,
% 1.48/0.99      ( ~ sP0(X0,X1)
% 1.48/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.48/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.48/0.99      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 1.48/0.99      | ~ v3_yellow_6(sK2(X1,X0,X3),X1)
% 1.48/0.99      | ~ l1_waybel_0(sK2(X1,X0,X3),X1)
% 1.48/0.99      | r2_hidden(X2,X0)
% 1.48/0.99      | ~ r2_hidden(X2,k10_yellow_6(X1,sK2(X1,X0,X3)))
% 1.48/0.99      | ~ r2_hidden(X3,k2_pre_topc(X1,X0))
% 1.48/0.99      | ~ v2_pre_topc(X1)
% 1.48/0.99      | ~ l1_pre_topc(X1)
% 1.48/0.99      | v2_struct_0(X1)
% 1.48/0.99      | v2_struct_0(sK2(X1,X0,X3))
% 1.48/0.99      | ~ v4_orders_2(sK2(X1,X0,X3))
% 1.48/0.99      | ~ v7_waybel_0(sK2(X1,X0,X3)) ),
% 1.48/0.99      inference(resolution,[status(thm)],[c_19,c_2]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_5,plain,
% 1.48/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.48/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.48/0.99      | ~ r2_hidden(X2,k2_pre_topc(X1,X0))
% 1.48/0.99      | ~ v2_pre_topc(X1)
% 1.48/0.99      | ~ l1_pre_topc(X1)
% 1.48/0.99      | v2_struct_0(X1)
% 1.48/0.99      | v7_waybel_0(sK2(X1,X0,X2)) ),
% 1.48/0.99      inference(cnf_transformation,[],[f41]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_6,plain,
% 1.48/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.48/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.48/0.99      | ~ r2_hidden(X2,k2_pre_topc(X1,X0))
% 1.48/0.99      | ~ v2_pre_topc(X1)
% 1.48/0.99      | ~ l1_pre_topc(X1)
% 1.48/0.99      | v2_struct_0(X1)
% 1.48/0.99      | v4_orders_2(sK2(X1,X0,X2)) ),
% 1.48/0.99      inference(cnf_transformation,[],[f40]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_7,plain,
% 1.48/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.48/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.48/0.99      | ~ r2_hidden(X2,k2_pre_topc(X1,X0))
% 1.48/0.99      | ~ v2_pre_topc(X1)
% 1.48/0.99      | ~ l1_pre_topc(X1)
% 1.48/0.99      | v2_struct_0(X1)
% 1.48/0.99      | ~ v2_struct_0(sK2(X1,X0,X2)) ),
% 1.48/0.99      inference(cnf_transformation,[],[f39]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_3,plain,
% 1.48/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.48/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.48/0.99      | l1_waybel_0(sK2(X1,X0,X2),X1)
% 1.48/0.99      | ~ r2_hidden(X2,k2_pre_topc(X1,X0))
% 1.48/0.99      | ~ v2_pre_topc(X1)
% 1.48/0.99      | ~ l1_pre_topc(X1)
% 1.48/0.99      | v2_struct_0(X1) ),
% 1.48/0.99      inference(cnf_transformation,[],[f43]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_4,plain,
% 1.48/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.48/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.48/0.99      | v3_yellow_6(sK2(X1,X0,X2),X1)
% 1.48/0.99      | ~ r2_hidden(X2,k2_pre_topc(X1,X0))
% 1.48/0.99      | ~ v2_pre_topc(X1)
% 1.48/0.99      | ~ l1_pre_topc(X1)
% 1.48/0.99      | v2_struct_0(X1) ),
% 1.48/0.99      inference(cnf_transformation,[],[f42]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_557,plain,
% 1.48/0.99      ( ~ sP0(X0,X1)
% 1.48/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.48/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.48/0.99      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 1.48/0.99      | r2_hidden(X2,X0)
% 1.48/0.99      | ~ r2_hidden(X2,k10_yellow_6(X1,sK2(X1,X0,X3)))
% 1.48/0.99      | ~ r2_hidden(X3,k2_pre_topc(X1,X0))
% 1.48/0.99      | ~ v2_pre_topc(X1)
% 1.48/0.99      | ~ l1_pre_topc(X1)
% 1.48/0.99      | v2_struct_0(X1) ),
% 1.48/0.99      inference(forward_subsumption_resolution,
% 1.48/0.99                [status(thm)],
% 1.48/0.99                [c_523,c_5,c_6,c_7,c_3,c_4]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_40,negated_conjecture,
% 1.48/0.99      ( l1_pre_topc(sK6) ),
% 1.48/0.99      inference(cnf_transformation,[],[f70]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_1061,plain,
% 1.48/0.99      ( ~ sP0(X0,sK6)
% 1.48/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.48/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 1.48/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK6))
% 1.48/0.99      | r2_hidden(X1,X0)
% 1.48/0.99      | ~ r2_hidden(X1,k10_yellow_6(sK6,sK2(sK6,X0,X2)))
% 1.48/0.99      | ~ r2_hidden(X2,k2_pre_topc(sK6,X0))
% 1.48/0.99      | ~ v2_pre_topc(sK6)
% 1.48/0.99      | v2_struct_0(sK6) ),
% 1.48/0.99      inference(resolution,[status(thm)],[c_557,c_40]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_42,negated_conjecture,
% 1.48/0.99      ( ~ v2_struct_0(sK6) ),
% 1.48/0.99      inference(cnf_transformation,[],[f68]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_41,negated_conjecture,
% 1.48/0.99      ( v2_pre_topc(sK6) ),
% 1.48/0.99      inference(cnf_transformation,[],[f69]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_1065,plain,
% 1.48/0.99      ( ~ sP0(X0,sK6)
% 1.48/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.48/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 1.48/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK6))
% 1.48/0.99      | r2_hidden(X1,X0)
% 1.48/0.99      | ~ r2_hidden(X1,k10_yellow_6(sK6,sK2(sK6,X0,X2)))
% 1.48/0.99      | ~ r2_hidden(X2,k2_pre_topc(sK6,X0)) ),
% 1.48/0.99      inference(global_propositional_subsumption,
% 1.48/0.99                [status(thm)],
% 1.48/0.99                [c_1061,c_42,c_41]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_2945,plain,
% 1.48/0.99      ( ~ sP0(X0_60,sK6)
% 1.48/0.99      | ~ m1_subset_1(X0_60,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.48/0.99      | ~ m1_subset_1(X1_60,u1_struct_0(sK6))
% 1.48/0.99      | ~ m1_subset_1(X2_60,u1_struct_0(sK6))
% 1.48/0.99      | r2_hidden(X1_60,X0_60)
% 1.48/0.99      | ~ r2_hidden(X1_60,k10_yellow_6(sK6,sK2(sK6,X0_60,X2_60)))
% 1.48/0.99      | ~ r2_hidden(X2_60,k2_pre_topc(sK6,X0_60)) ),
% 1.48/0.99      inference(subtyping,[status(esa)],[c_1065]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_3104,plain,
% 1.48/0.99      ( ~ sP0(X0_60,sK6)
% 1.48/0.99      | ~ m1_subset_1(X0_60,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.48/0.99      | ~ m1_subset_1(X1_60,u1_struct_0(sK6))
% 1.48/0.99      | ~ m1_subset_1(sK9,u1_struct_0(sK6))
% 1.48/0.99      | ~ r2_hidden(X1_60,k2_pre_topc(sK6,X0_60))
% 1.48/0.99      | r2_hidden(sK9,X0_60)
% 1.48/0.99      | ~ r2_hidden(sK9,k10_yellow_6(sK6,sK2(sK6,X0_60,X1_60))) ),
% 1.48/0.99      inference(instantiation,[status(thm)],[c_2945]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_3121,plain,
% 1.48/0.99      ( ~ sP0(X0_60,sK6)
% 1.48/0.99      | ~ m1_subset_1(X0_60,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.48/0.99      | ~ m1_subset_1(sK9,u1_struct_0(sK6))
% 1.48/0.99      | r2_hidden(sK9,X0_60)
% 1.48/0.99      | ~ r2_hidden(sK9,k10_yellow_6(sK6,sK2(sK6,X0_60,sK9)))
% 1.48/0.99      | ~ r2_hidden(sK9,k2_pre_topc(sK6,X0_60)) ),
% 1.48/0.99      inference(instantiation,[status(thm)],[c_3104]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_3123,plain,
% 1.48/0.99      ( ~ sP0(sK7,sK6)
% 1.48/0.99      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.48/0.99      | ~ m1_subset_1(sK9,u1_struct_0(sK6))
% 1.48/0.99      | ~ r2_hidden(sK9,k10_yellow_6(sK6,sK2(sK6,sK7,sK9)))
% 1.48/0.99      | ~ r2_hidden(sK9,k2_pre_topc(sK6,sK7))
% 1.48/0.99      | r2_hidden(sK9,sK7) ),
% 1.48/0.99      inference(instantiation,[status(thm)],[c_3121]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_24,plain,
% 1.48/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.48/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.48/0.99      | m1_subset_1(sK5(X1,X0,X2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
% 1.48/0.99      | ~ r2_hidden(X2,k2_pre_topc(X1,X0))
% 1.48/0.99      | ~ v2_pre_topc(X1)
% 1.48/0.99      | ~ l1_pre_topc(X1)
% 1.48/0.99      | v2_struct_0(X1) ),
% 1.48/0.99      inference(cnf_transformation,[],[f64]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_1093,plain,
% 1.48/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.48/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 1.48/0.99      | m1_subset_1(sK5(sK6,X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
% 1.48/0.99      | ~ r2_hidden(X1,k2_pre_topc(sK6,X0))
% 1.48/0.99      | ~ v2_pre_topc(sK6)
% 1.48/0.99      | v2_struct_0(sK6) ),
% 1.48/0.99      inference(resolution,[status(thm)],[c_24,c_40]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_1097,plain,
% 1.48/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.48/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 1.48/0.99      | m1_subset_1(sK5(sK6,X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
% 1.48/0.99      | ~ r2_hidden(X1,k2_pre_topc(sK6,X0)) ),
% 1.48/0.99      inference(global_propositional_subsumption,
% 1.48/0.99                [status(thm)],
% 1.48/0.99                [c_1093,c_42,c_41]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_28,plain,
% 1.48/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.48/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.48/0.99      | ~ r2_hidden(X2,k2_pre_topc(X1,X0))
% 1.48/0.99      | ~ v1_xboole_0(sK5(X1,X0,X2))
% 1.48/0.99      | ~ v2_pre_topc(X1)
% 1.48/0.99      | ~ l1_pre_topc(X1)
% 1.48/0.99      | v2_struct_0(X1) ),
% 1.48/0.99      inference(cnf_transformation,[],[f60]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_27,plain,
% 1.48/0.99      ( v2_waybel_0(sK5(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
% 1.48/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.48/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.48/0.99      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
% 1.48/0.99      | ~ v2_pre_topc(X0)
% 1.48/0.99      | ~ l1_pre_topc(X0)
% 1.48/0.99      | v2_struct_0(X0) ),
% 1.48/0.99      inference(cnf_transformation,[],[f61]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_26,plain,
% 1.48/0.99      ( v13_waybel_0(sK5(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
% 1.48/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.48/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.48/0.99      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
% 1.48/0.99      | ~ v2_pre_topc(X0)
% 1.48/0.99      | ~ l1_pre_topc(X0)
% 1.48/0.99      | v2_struct_0(X0) ),
% 1.48/0.99      inference(cnf_transformation,[],[f62]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_25,plain,
% 1.48/0.99      ( v3_waybel_7(sK5(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
% 1.48/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.48/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.48/0.99      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
% 1.48/0.99      | ~ v2_pre_topc(X0)
% 1.48/0.99      | ~ l1_pre_topc(X0)
% 1.48/0.99      | v2_struct_0(X0) ),
% 1.48/0.99      inference(cnf_transformation,[],[f63]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_22,plain,
% 1.48/0.99      ( r2_waybel_7(X0,sK5(X0,X1,X2),X2)
% 1.48/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.48/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.48/0.99      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
% 1.48/0.99      | ~ v2_pre_topc(X0)
% 1.48/0.99      | ~ l1_pre_topc(X0)
% 1.48/0.99      | v2_struct_0(X0) ),
% 1.48/0.99      inference(cnf_transformation,[],[f66]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_38,negated_conjecture,
% 1.48/0.99      ( ~ r2_waybel_7(sK6,X0,X1)
% 1.48/0.99      | ~ v2_waybel_0(X0,k3_yellow_1(k2_struct_0(sK6)))
% 1.48/0.99      | ~ v13_waybel_0(X0,k3_yellow_1(k2_struct_0(sK6)))
% 1.48/0.99      | ~ v3_waybel_7(X0,k3_yellow_1(k2_struct_0(sK6)))
% 1.48/0.99      | v4_pre_topc(sK7,sK6)
% 1.48/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
% 1.48/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 1.48/0.99      | r2_hidden(X1,sK7)
% 1.48/0.99      | ~ r2_hidden(sK7,X0)
% 1.48/0.99      | v1_xboole_0(X0) ),
% 1.48/0.99      inference(cnf_transformation,[],[f72]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_740,plain,
% 1.48/0.99      ( ~ v2_waybel_0(sK5(sK6,X0,X1),k3_yellow_1(k2_struct_0(sK6)))
% 1.48/0.99      | ~ v13_waybel_0(sK5(sK6,X0,X1),k3_yellow_1(k2_struct_0(sK6)))
% 1.48/0.99      | ~ v3_waybel_7(sK5(sK6,X0,X1),k3_yellow_1(k2_struct_0(sK6)))
% 1.48/0.99      | v4_pre_topc(sK7,sK6)
% 1.48/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.48/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 1.48/0.99      | ~ m1_subset_1(sK5(sK6,X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
% 1.48/0.99      | ~ r2_hidden(X1,k2_pre_topc(sK6,X0))
% 1.48/0.99      | r2_hidden(X1,sK7)
% 1.48/0.99      | ~ r2_hidden(sK7,sK5(sK6,X0,X1))
% 1.48/0.99      | v1_xboole_0(sK5(sK6,X0,X1))
% 1.48/0.99      | ~ v2_pre_topc(sK6)
% 1.48/0.99      | ~ l1_pre_topc(sK6)
% 1.48/0.99      | v2_struct_0(sK6) ),
% 1.48/0.99      inference(resolution,[status(thm)],[c_22,c_38]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_744,plain,
% 1.48/0.99      ( v1_xboole_0(sK5(sK6,X0,X1))
% 1.48/0.99      | ~ r2_hidden(sK7,sK5(sK6,X0,X1))
% 1.48/0.99      | r2_hidden(X1,sK7)
% 1.48/0.99      | ~ r2_hidden(X1,k2_pre_topc(sK6,X0))
% 1.48/0.99      | ~ m1_subset_1(sK5(sK6,X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
% 1.48/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 1.48/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.48/0.99      | v4_pre_topc(sK7,sK6)
% 1.48/0.99      | ~ v3_waybel_7(sK5(sK6,X0,X1),k3_yellow_1(k2_struct_0(sK6)))
% 1.48/0.99      | ~ v13_waybel_0(sK5(sK6,X0,X1),k3_yellow_1(k2_struct_0(sK6)))
% 1.48/0.99      | ~ v2_waybel_0(sK5(sK6,X0,X1),k3_yellow_1(k2_struct_0(sK6))) ),
% 1.48/0.99      inference(global_propositional_subsumption,
% 1.48/0.99                [status(thm)],
% 1.48/0.99                [c_740,c_42,c_41,c_40]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_745,plain,
% 1.48/0.99      ( ~ v2_waybel_0(sK5(sK6,X0,X1),k3_yellow_1(k2_struct_0(sK6)))
% 1.48/0.99      | ~ v13_waybel_0(sK5(sK6,X0,X1),k3_yellow_1(k2_struct_0(sK6)))
% 1.48/0.99      | ~ v3_waybel_7(sK5(sK6,X0,X1),k3_yellow_1(k2_struct_0(sK6)))
% 1.48/0.99      | v4_pre_topc(sK7,sK6)
% 1.48/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.48/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 1.48/0.99      | ~ m1_subset_1(sK5(sK6,X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
% 1.48/0.99      | ~ r2_hidden(X1,k2_pre_topc(sK6,X0))
% 1.48/0.99      | r2_hidden(X1,sK7)
% 1.48/0.99      | ~ r2_hidden(sK7,sK5(sK6,X0,X1))
% 1.48/0.99      | v1_xboole_0(sK5(sK6,X0,X1)) ),
% 1.48/0.99      inference(renaming,[status(thm)],[c_744]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_801,plain,
% 1.48/0.99      ( ~ v2_waybel_0(sK5(sK6,X0,X1),k3_yellow_1(k2_struct_0(sK6)))
% 1.48/0.99      | ~ v13_waybel_0(sK5(sK6,X0,X1),k3_yellow_1(k2_struct_0(sK6)))
% 1.48/0.99      | v4_pre_topc(sK7,sK6)
% 1.48/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.48/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 1.48/0.99      | ~ m1_subset_1(sK5(sK6,X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
% 1.48/0.99      | ~ r2_hidden(X1,k2_pre_topc(sK6,X0))
% 1.48/0.99      | r2_hidden(X1,sK7)
% 1.48/0.99      | ~ r2_hidden(sK7,sK5(sK6,X0,X1))
% 1.48/0.99      | v1_xboole_0(sK5(sK6,X0,X1))
% 1.48/0.99      | ~ v2_pre_topc(sK6)
% 1.48/0.99      | ~ l1_pre_topc(sK6)
% 1.48/0.99      | v2_struct_0(sK6) ),
% 1.48/0.99      inference(resolution,[status(thm)],[c_25,c_745]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_805,plain,
% 1.48/0.99      ( v1_xboole_0(sK5(sK6,X0,X1))
% 1.48/0.99      | ~ r2_hidden(sK7,sK5(sK6,X0,X1))
% 1.48/0.99      | r2_hidden(X1,sK7)
% 1.48/0.99      | ~ r2_hidden(X1,k2_pre_topc(sK6,X0))
% 1.48/0.99      | ~ m1_subset_1(sK5(sK6,X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
% 1.48/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 1.48/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.48/0.99      | v4_pre_topc(sK7,sK6)
% 1.48/0.99      | ~ v13_waybel_0(sK5(sK6,X0,X1),k3_yellow_1(k2_struct_0(sK6)))
% 1.48/0.99      | ~ v2_waybel_0(sK5(sK6,X0,X1),k3_yellow_1(k2_struct_0(sK6))) ),
% 1.48/0.99      inference(global_propositional_subsumption,
% 1.48/0.99                [status(thm)],
% 1.48/0.99                [c_801,c_42,c_41,c_40]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_806,plain,
% 1.48/0.99      ( ~ v2_waybel_0(sK5(sK6,X0,X1),k3_yellow_1(k2_struct_0(sK6)))
% 1.48/0.99      | ~ v13_waybel_0(sK5(sK6,X0,X1),k3_yellow_1(k2_struct_0(sK6)))
% 1.48/0.99      | v4_pre_topc(sK7,sK6)
% 1.48/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.48/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 1.48/0.99      | ~ m1_subset_1(sK5(sK6,X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
% 1.48/0.99      | ~ r2_hidden(X1,k2_pre_topc(sK6,X0))
% 1.48/0.99      | r2_hidden(X1,sK7)
% 1.48/0.99      | ~ r2_hidden(sK7,sK5(sK6,X0,X1))
% 1.48/0.99      | v1_xboole_0(sK5(sK6,X0,X1)) ),
% 1.48/0.99      inference(renaming,[status(thm)],[c_805]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_853,plain,
% 1.48/0.99      ( ~ v2_waybel_0(sK5(sK6,X0,X1),k3_yellow_1(k2_struct_0(sK6)))
% 1.48/0.99      | v4_pre_topc(sK7,sK6)
% 1.48/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.48/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 1.48/0.99      | ~ m1_subset_1(sK5(sK6,X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
% 1.48/0.99      | ~ r2_hidden(X1,k2_pre_topc(sK6,X0))
% 1.48/0.99      | r2_hidden(X1,sK7)
% 1.48/0.99      | ~ r2_hidden(sK7,sK5(sK6,X0,X1))
% 1.48/0.99      | v1_xboole_0(sK5(sK6,X0,X1))
% 1.48/0.99      | ~ v2_pre_topc(sK6)
% 1.48/0.99      | ~ l1_pre_topc(sK6)
% 1.48/0.99      | v2_struct_0(sK6) ),
% 1.48/0.99      inference(resolution,[status(thm)],[c_26,c_806]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_857,plain,
% 1.48/0.99      ( v1_xboole_0(sK5(sK6,X0,X1))
% 1.48/0.99      | ~ r2_hidden(sK7,sK5(sK6,X0,X1))
% 1.48/0.99      | r2_hidden(X1,sK7)
% 1.48/0.99      | ~ r2_hidden(X1,k2_pre_topc(sK6,X0))
% 1.48/0.99      | ~ m1_subset_1(sK5(sK6,X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
% 1.48/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 1.48/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.48/0.99      | v4_pre_topc(sK7,sK6)
% 1.48/0.99      | ~ v2_waybel_0(sK5(sK6,X0,X1),k3_yellow_1(k2_struct_0(sK6))) ),
% 1.48/0.99      inference(global_propositional_subsumption,
% 1.48/0.99                [status(thm)],
% 1.48/0.99                [c_853,c_42,c_41,c_40]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_858,plain,
% 1.48/0.99      ( ~ v2_waybel_0(sK5(sK6,X0,X1),k3_yellow_1(k2_struct_0(sK6)))
% 1.48/0.99      | v4_pre_topc(sK7,sK6)
% 1.48/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.48/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 1.48/0.99      | ~ m1_subset_1(sK5(sK6,X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
% 1.48/0.99      | ~ r2_hidden(X1,k2_pre_topc(sK6,X0))
% 1.48/0.99      | r2_hidden(X1,sK7)
% 1.48/0.99      | ~ r2_hidden(sK7,sK5(sK6,X0,X1))
% 1.48/0.99      | v1_xboole_0(sK5(sK6,X0,X1)) ),
% 1.48/0.99      inference(renaming,[status(thm)],[c_857]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_901,plain,
% 1.48/0.99      ( v4_pre_topc(sK7,sK6)
% 1.48/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.48/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 1.48/0.99      | ~ m1_subset_1(sK5(sK6,X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
% 1.48/0.99      | ~ r2_hidden(X1,k2_pre_topc(sK6,X0))
% 1.48/0.99      | r2_hidden(X1,sK7)
% 1.48/0.99      | ~ r2_hidden(sK7,sK5(sK6,X0,X1))
% 1.48/0.99      | v1_xboole_0(sK5(sK6,X0,X1))
% 1.48/0.99      | ~ v2_pre_topc(sK6)
% 1.48/0.99      | ~ l1_pre_topc(sK6)
% 1.48/0.99      | v2_struct_0(sK6) ),
% 1.48/0.99      inference(resolution,[status(thm)],[c_27,c_858]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_905,plain,
% 1.48/0.99      ( v1_xboole_0(sK5(sK6,X0,X1))
% 1.48/0.99      | ~ r2_hidden(sK7,sK5(sK6,X0,X1))
% 1.48/0.99      | r2_hidden(X1,sK7)
% 1.48/0.99      | ~ r2_hidden(X1,k2_pre_topc(sK6,X0))
% 1.48/0.99      | ~ m1_subset_1(sK5(sK6,X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
% 1.48/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 1.48/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.48/0.99      | v4_pre_topc(sK7,sK6) ),
% 1.48/0.99      inference(global_propositional_subsumption,
% 1.48/0.99                [status(thm)],
% 1.48/0.99                [c_901,c_42,c_41,c_40]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_906,plain,
% 1.48/0.99      ( v4_pre_topc(sK7,sK6)
% 1.48/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.48/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 1.48/0.99      | ~ m1_subset_1(sK5(sK6,X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
% 1.48/0.99      | ~ r2_hidden(X1,k2_pre_topc(sK6,X0))
% 1.48/0.99      | r2_hidden(X1,sK7)
% 1.48/0.99      | ~ r2_hidden(sK7,sK5(sK6,X0,X1))
% 1.48/0.99      | v1_xboole_0(sK5(sK6,X0,X1)) ),
% 1.48/0.99      inference(renaming,[status(thm)],[c_905]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_945,plain,
% 1.48/0.99      ( v4_pre_topc(sK7,sK6)
% 1.48/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.48/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 1.48/0.99      | ~ m1_subset_1(sK5(sK6,X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
% 1.48/0.99      | ~ r2_hidden(X1,k2_pre_topc(sK6,X0))
% 1.48/0.99      | r2_hidden(X1,sK7)
% 1.48/0.99      | ~ r2_hidden(sK7,sK5(sK6,X0,X1))
% 1.48/0.99      | ~ v2_pre_topc(sK6)
% 1.48/0.99      | ~ l1_pre_topc(sK6)
% 1.48/0.99      | v2_struct_0(sK6) ),
% 1.48/0.99      inference(resolution,[status(thm)],[c_28,c_906]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_949,plain,
% 1.48/0.99      ( ~ r2_hidden(sK7,sK5(sK6,X0,X1))
% 1.48/0.99      | r2_hidden(X1,sK7)
% 1.48/0.99      | ~ r2_hidden(X1,k2_pre_topc(sK6,X0))
% 1.48/0.99      | ~ m1_subset_1(sK5(sK6,X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
% 1.48/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 1.48/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.48/0.99      | v4_pre_topc(sK7,sK6) ),
% 1.48/0.99      inference(global_propositional_subsumption,
% 1.48/0.99                [status(thm)],
% 1.48/0.99                [c_945,c_42,c_41,c_40]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_950,plain,
% 1.48/0.99      ( v4_pre_topc(sK7,sK6)
% 1.48/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.48/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 1.48/0.99      | ~ m1_subset_1(sK5(sK6,X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
% 1.48/0.99      | ~ r2_hidden(X1,k2_pre_topc(sK6,X0))
% 1.48/0.99      | r2_hidden(X1,sK7)
% 1.48/0.99      | ~ r2_hidden(sK7,sK5(sK6,X0,X1)) ),
% 1.48/0.99      inference(renaming,[status(thm)],[c_949]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_1233,plain,
% 1.48/0.99      ( v4_pre_topc(sK7,sK6)
% 1.48/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.48/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 1.48/0.99      | ~ r2_hidden(X1,k2_pre_topc(sK6,X0))
% 1.48/0.99      | r2_hidden(X1,sK7)
% 1.48/0.99      | ~ r2_hidden(sK7,sK5(sK6,X0,X1)) ),
% 1.48/0.99      inference(backward_subsumption_resolution,
% 1.48/0.99                [status(thm)],
% 1.48/0.99                [c_1097,c_950]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_2942,plain,
% 1.48/0.99      ( v4_pre_topc(sK7,sK6)
% 1.48/0.99      | ~ m1_subset_1(X0_60,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.48/0.99      | ~ m1_subset_1(X1_60,u1_struct_0(sK6))
% 1.48/0.99      | ~ r2_hidden(X1_60,k2_pre_topc(sK6,X0_60))
% 1.48/0.99      | r2_hidden(X1_60,sK7)
% 1.48/0.99      | ~ r2_hidden(sK7,sK5(sK6,X0_60,X1_60)) ),
% 1.48/0.99      inference(subtyping,[status(esa)],[c_1233]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_3076,plain,
% 1.48/0.99      ( v4_pre_topc(sK7,sK6)
% 1.48/0.99      | ~ m1_subset_1(X0_60,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.48/0.99      | ~ m1_subset_1(sK4(X1_60,sK6),u1_struct_0(sK6))
% 1.48/0.99      | ~ r2_hidden(sK4(X1_60,sK6),k2_pre_topc(sK6,X0_60))
% 1.48/0.99      | r2_hidden(sK4(X1_60,sK6),sK7)
% 1.48/0.99      | ~ r2_hidden(sK7,sK5(sK6,X0_60,sK4(X1_60,sK6))) ),
% 1.48/0.99      inference(instantiation,[status(thm)],[c_2942]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_3100,plain,
% 1.48/0.99      ( v4_pre_topc(sK7,sK6)
% 1.48/0.99      | ~ m1_subset_1(sK4(sK7,sK6),u1_struct_0(sK6))
% 1.48/0.99      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.48/0.99      | ~ r2_hidden(sK4(sK7,sK6),k2_pre_topc(sK6,sK7))
% 1.48/0.99      | r2_hidden(sK4(sK7,sK6),sK7)
% 1.48/0.99      | ~ r2_hidden(sK7,sK5(sK6,sK7,sK4(sK7,sK6))) ),
% 1.48/0.99      inference(instantiation,[status(thm)],[c_3076]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_0,plain,
% 1.48/0.99      ( ~ r1_waybel_0(X0,X1,X2)
% 1.48/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 1.48/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.48/0.99      | ~ v3_yellow_6(X1,X0)
% 1.48/0.99      | ~ l1_waybel_0(X1,X0)
% 1.48/0.99      | ~ r2_hidden(X3,k10_yellow_6(X0,X1))
% 1.48/0.99      | r2_hidden(X3,k2_pre_topc(X0,X2))
% 1.48/0.99      | ~ v2_pre_topc(X0)
% 1.48/0.99      | ~ l1_pre_topc(X0)
% 1.48/0.99      | v2_struct_0(X0)
% 1.48/0.99      | v2_struct_0(X1)
% 1.48/0.99      | ~ v4_orders_2(X1)
% 1.48/0.99      | ~ v7_waybel_0(X1) ),
% 1.48/0.99      inference(cnf_transformation,[],[f46]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_13,plain,
% 1.48/0.99      ( r1_waybel_0(X0,sK3(X1,X0),X1) | sP0(X1,X0) ),
% 1.48/0.99      inference(cnf_transformation,[],[f55]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_613,plain,
% 1.48/0.99      ( sP0(X0,X1)
% 1.48/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.48/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.48/0.99      | ~ v3_yellow_6(sK3(X0,X1),X1)
% 1.48/0.99      | ~ l1_waybel_0(sK3(X0,X1),X1)
% 1.48/0.99      | ~ r2_hidden(X2,k10_yellow_6(X1,sK3(X0,X1)))
% 1.48/0.99      | r2_hidden(X2,k2_pre_topc(X1,X0))
% 1.48/0.99      | ~ v2_pre_topc(X1)
% 1.48/0.99      | ~ l1_pre_topc(X1)
% 1.48/0.99      | v2_struct_0(X1)
% 1.48/0.99      | v2_struct_0(sK3(X0,X1))
% 1.48/0.99      | ~ v4_orders_2(sK3(X0,X1))
% 1.48/0.99      | ~ v7_waybel_0(sK3(X0,X1)) ),
% 1.48/0.99      inference(resolution,[status(thm)],[c_0,c_13]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_18,plain,
% 1.48/0.99      ( sP0(X0,X1) | ~ v2_struct_0(sK3(X0,X1)) ),
% 1.48/0.99      inference(cnf_transformation,[],[f50]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_17,plain,
% 1.48/0.99      ( sP0(X0,X1) | v4_orders_2(sK3(X0,X1)) ),
% 1.48/0.99      inference(cnf_transformation,[],[f51]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_16,plain,
% 1.48/0.99      ( sP0(X0,X1) | v7_waybel_0(sK3(X0,X1)) ),
% 1.48/0.99      inference(cnf_transformation,[],[f52]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_15,plain,
% 1.48/0.99      ( sP0(X0,X1) | v3_yellow_6(sK3(X0,X1),X1) ),
% 1.48/0.99      inference(cnf_transformation,[],[f53]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_14,plain,
% 1.48/0.99      ( sP0(X0,X1) | l1_waybel_0(sK3(X0,X1),X1) ),
% 1.48/0.99      inference(cnf_transformation,[],[f54]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_617,plain,
% 1.48/0.99      ( v2_struct_0(X1)
% 1.48/0.99      | ~ l1_pre_topc(X1)
% 1.48/0.99      | ~ v2_pre_topc(X1)
% 1.48/0.99      | r2_hidden(X2,k2_pre_topc(X1,X0))
% 1.48/0.99      | ~ r2_hidden(X2,k10_yellow_6(X1,sK3(X0,X1)))
% 1.48/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.48/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.48/0.99      | sP0(X0,X1) ),
% 1.48/0.99      inference(global_propositional_subsumption,
% 1.48/0.99                [status(thm)],
% 1.48/0.99                [c_613,c_18,c_17,c_16,c_15,c_14]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_618,plain,
% 1.48/0.99      ( sP0(X0,X1)
% 1.48/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.48/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.48/0.99      | ~ r2_hidden(X2,k10_yellow_6(X1,sK3(X0,X1)))
% 1.48/0.99      | r2_hidden(X2,k2_pre_topc(X1,X0))
% 1.48/0.99      | ~ v2_pre_topc(X1)
% 1.48/0.99      | ~ l1_pre_topc(X1)
% 1.48/0.99      | v2_struct_0(X1) ),
% 1.48/0.99      inference(renaming,[status(thm)],[c_617]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_1010,plain,
% 1.48/0.99      ( sP0(X0,sK6)
% 1.48/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.48/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 1.48/0.99      | ~ r2_hidden(X1,k10_yellow_6(sK6,sK3(X0,sK6)))
% 1.48/0.99      | r2_hidden(X1,k2_pre_topc(sK6,X0))
% 1.48/0.99      | ~ v2_pre_topc(sK6)
% 1.48/0.99      | v2_struct_0(sK6) ),
% 1.48/0.99      inference(resolution,[status(thm)],[c_618,c_40]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_1014,plain,
% 1.48/0.99      ( sP0(X0,sK6)
% 1.48/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.48/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 1.48/0.99      | ~ r2_hidden(X1,k10_yellow_6(sK6,sK3(X0,sK6)))
% 1.48/0.99      | r2_hidden(X1,k2_pre_topc(sK6,X0)) ),
% 1.48/0.99      inference(global_propositional_subsumption,
% 1.48/0.99                [status(thm)],
% 1.48/0.99                [c_1010,c_42,c_41]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_2947,plain,
% 1.48/0.99      ( sP0(X0_60,sK6)
% 1.48/0.99      | ~ m1_subset_1(X0_60,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.48/0.99      | ~ m1_subset_1(X1_60,u1_struct_0(sK6))
% 1.48/0.99      | ~ r2_hidden(X1_60,k10_yellow_6(sK6,sK3(X0_60,sK6)))
% 1.48/0.99      | r2_hidden(X1_60,k2_pre_topc(sK6,X0_60)) ),
% 1.48/0.99      inference(subtyping,[status(esa)],[c_1014]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_3078,plain,
% 1.48/0.99      ( sP0(X0_60,sK6)
% 1.48/0.99      | ~ m1_subset_1(X0_60,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.48/0.99      | ~ m1_subset_1(sK4(X1_60,sK6),u1_struct_0(sK6))
% 1.48/0.99      | ~ r2_hidden(sK4(X1_60,sK6),k10_yellow_6(sK6,sK3(X0_60,sK6)))
% 1.48/0.99      | r2_hidden(sK4(X1_60,sK6),k2_pre_topc(sK6,X0_60)) ),
% 1.48/0.99      inference(instantiation,[status(thm)],[c_2947]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_3092,plain,
% 1.48/0.99      ( sP0(sK7,sK6)
% 1.48/0.99      | ~ m1_subset_1(sK4(sK7,sK6),u1_struct_0(sK6))
% 1.48/0.99      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.48/0.99      | ~ r2_hidden(sK4(sK7,sK6),k10_yellow_6(sK6,sK3(sK7,sK6)))
% 1.48/0.99      | r2_hidden(sK4(sK7,sK6),k2_pre_topc(sK6,sK7)) ),
% 1.48/0.99      inference(instantiation,[status(thm)],[c_3078]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_23,plain,
% 1.48/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.48/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.48/0.99      | r2_hidden(X0,sK5(X1,X0,X2))
% 1.48/0.99      | ~ r2_hidden(X2,k2_pre_topc(X1,X0))
% 1.48/0.99      | ~ v2_pre_topc(X1)
% 1.48/0.99      | ~ l1_pre_topc(X1)
% 1.48/0.99      | v2_struct_0(X1) ),
% 1.48/0.99      inference(cnf_transformation,[],[f65]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_1116,plain,
% 1.48/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.48/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 1.48/0.99      | r2_hidden(X0,sK5(sK6,X0,X1))
% 1.48/0.99      | ~ r2_hidden(X1,k2_pre_topc(sK6,X0))
% 1.48/0.99      | ~ v2_pre_topc(sK6)
% 1.48/0.99      | v2_struct_0(sK6) ),
% 1.48/0.99      inference(resolution,[status(thm)],[c_23,c_40]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_1120,plain,
% 1.48/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.48/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 1.48/0.99      | r2_hidden(X0,sK5(sK6,X0,X1))
% 1.48/0.99      | ~ r2_hidden(X1,k2_pre_topc(sK6,X0)) ),
% 1.48/0.99      inference(global_propositional_subsumption,
% 1.48/0.99                [status(thm)],
% 1.48/0.99                [c_1116,c_42,c_41]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_2944,plain,
% 1.48/0.99      ( ~ m1_subset_1(X0_60,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.48/0.99      | ~ m1_subset_1(X1_60,u1_struct_0(sK6))
% 1.48/0.99      | r2_hidden(X0_60,sK5(sK6,X0_60,X1_60))
% 1.48/0.99      | ~ r2_hidden(X1_60,k2_pre_topc(sK6,X0_60)) ),
% 1.48/0.99      inference(subtyping,[status(esa)],[c_1120]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_3079,plain,
% 1.48/0.99      ( ~ m1_subset_1(X0_60,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.48/0.99      | ~ m1_subset_1(sK4(X1_60,sK6),u1_struct_0(sK6))
% 1.48/0.99      | r2_hidden(X0_60,sK5(sK6,X0_60,sK4(X1_60,sK6)))
% 1.48/0.99      | ~ r2_hidden(sK4(X1_60,sK6),k2_pre_topc(sK6,X0_60)) ),
% 1.48/0.99      inference(instantiation,[status(thm)],[c_2944]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_3088,plain,
% 1.48/0.99      ( ~ m1_subset_1(sK4(sK7,sK6),u1_struct_0(sK6))
% 1.48/0.99      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.48/0.99      | ~ r2_hidden(sK4(sK7,sK6),k2_pre_topc(sK6,sK7))
% 1.48/0.99      | r2_hidden(sK7,sK5(sK6,sK7,sK4(sK7,sK6))) ),
% 1.48/0.99      inference(instantiation,[status(thm)],[c_3079]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_1,plain,
% 1.48/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.48/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.48/0.99      | r2_hidden(X2,k10_yellow_6(X1,sK2(X1,X0,X2)))
% 1.48/0.99      | ~ r2_hidden(X2,k2_pre_topc(X1,X0))
% 1.48/0.99      | ~ v2_pre_topc(X1)
% 1.48/0.99      | ~ l1_pre_topc(X1)
% 1.48/0.99      | v2_struct_0(X1) ),
% 1.48/0.99      inference(cnf_transformation,[],[f45]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_1162,plain,
% 1.48/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.48/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 1.48/0.99      | r2_hidden(X1,k10_yellow_6(sK6,sK2(sK6,X0,X1)))
% 1.48/0.99      | ~ r2_hidden(X1,k2_pre_topc(sK6,X0))
% 1.48/0.99      | ~ v2_pre_topc(sK6)
% 1.48/0.99      | v2_struct_0(sK6) ),
% 1.48/0.99      inference(resolution,[status(thm)],[c_1,c_40]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_1166,plain,
% 1.48/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.48/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 1.48/0.99      | r2_hidden(X1,k10_yellow_6(sK6,sK2(sK6,X0,X1)))
% 1.48/0.99      | ~ r2_hidden(X1,k2_pre_topc(sK6,X0)) ),
% 1.48/0.99      inference(global_propositional_subsumption,
% 1.48/0.99                [status(thm)],
% 1.48/0.99                [c_1162,c_42,c_41]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_2943,plain,
% 1.48/0.99      ( ~ m1_subset_1(X0_60,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.48/0.99      | ~ m1_subset_1(X1_60,u1_struct_0(sK6))
% 1.48/0.99      | r2_hidden(X1_60,k10_yellow_6(sK6,sK2(sK6,X0_60,X1_60)))
% 1.48/0.99      | ~ r2_hidden(X1_60,k2_pre_topc(sK6,X0_60)) ),
% 1.48/0.99      inference(subtyping,[status(esa)],[c_1166]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_3047,plain,
% 1.48/0.99      ( ~ m1_subset_1(X0_60,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.48/0.99      | ~ m1_subset_1(sK9,u1_struct_0(sK6))
% 1.48/0.99      | r2_hidden(sK9,k10_yellow_6(sK6,sK2(sK6,X0_60,sK9)))
% 1.48/0.99      | ~ r2_hidden(sK9,k2_pre_topc(sK6,X0_60)) ),
% 1.48/0.99      inference(instantiation,[status(thm)],[c_2943]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_3049,plain,
% 1.48/0.99      ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.48/0.99      | ~ m1_subset_1(sK9,u1_struct_0(sK6))
% 1.48/0.99      | r2_hidden(sK9,k10_yellow_6(sK6,sK2(sK6,sK7,sK9)))
% 1.48/0.99      | ~ r2_hidden(sK9,k2_pre_topc(sK6,sK7)) ),
% 1.48/0.99      inference(instantiation,[status(thm)],[c_3047]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_8,plain,
% 1.48/0.99      ( ~ sP1(X0,X1) | ~ sP0(X1,X0) | v4_pre_topc(X1,X0) ),
% 1.48/0.99      inference(cnf_transformation,[],[f48]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_20,plain,
% 1.48/0.99      ( sP1(X0,X1)
% 1.48/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.48/0.99      | ~ v2_pre_topc(X0)
% 1.48/0.99      | ~ l1_pre_topc(X0)
% 1.48/0.99      | v2_struct_0(X0) ),
% 1.48/0.99      inference(cnf_transformation,[],[f59]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_1185,plain,
% 1.48/0.99      ( sP1(sK6,X0)
% 1.48/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.48/0.99      | ~ v2_pre_topc(sK6)
% 1.48/0.99      | v2_struct_0(sK6) ),
% 1.48/0.99      inference(resolution,[status(thm)],[c_20,c_40]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_1189,plain,
% 1.48/0.99      ( sP1(sK6,X0) | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) ),
% 1.48/0.99      inference(global_propositional_subsumption,
% 1.48/0.99                [status(thm)],
% 1.48/0.99                [c_1185,c_42,c_41]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_1271,plain,
% 1.48/0.99      ( ~ sP0(X0,sK6)
% 1.48/0.99      | v4_pre_topc(X0,sK6)
% 1.48/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) ),
% 1.48/0.99      inference(resolution,[status(thm)],[c_8,c_1189]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_2940,plain,
% 1.48/0.99      ( ~ sP0(X0_60,sK6)
% 1.48/0.99      | v4_pre_topc(X0_60,sK6)
% 1.48/0.99      | ~ m1_subset_1(X0_60,k1_zfmisc_1(u1_struct_0(sK6))) ),
% 1.48/0.99      inference(subtyping,[status(esa)],[c_1271]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_2994,plain,
% 1.48/0.99      ( ~ sP0(sK7,sK6)
% 1.48/0.99      | v4_pre_topc(sK7,sK6)
% 1.48/0.99      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
% 1.48/0.99      inference(instantiation,[status(thm)],[c_2940]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_9,plain,
% 1.48/0.99      ( ~ sP1(X0,X1) | sP0(X1,X0) | ~ v4_pre_topc(X1,X0) ),
% 1.48/0.99      inference(cnf_transformation,[],[f47]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_1257,plain,
% 1.48/0.99      ( sP0(X0,sK6)
% 1.48/0.99      | ~ v4_pre_topc(X0,sK6)
% 1.48/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) ),
% 1.48/0.99      inference(resolution,[status(thm)],[c_9,c_1189]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_2941,plain,
% 1.48/0.99      ( sP0(X0_60,sK6)
% 1.48/0.99      | ~ v4_pre_topc(X0_60,sK6)
% 1.48/0.99      | ~ m1_subset_1(X0_60,k1_zfmisc_1(u1_struct_0(sK6))) ),
% 1.48/0.99      inference(subtyping,[status(esa)],[c_1257]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_2991,plain,
% 1.48/0.99      ( sP0(sK7,sK6)
% 1.48/0.99      | ~ v4_pre_topc(sK7,sK6)
% 1.48/0.99      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
% 1.48/0.99      inference(instantiation,[status(thm)],[c_2941]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_21,plain,
% 1.48/0.99      ( ~ r2_waybel_7(X0,X1,X2)
% 1.48/0.99      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
% 1.48/0.99      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
% 1.48/0.99      | ~ v3_waybel_7(X1,k3_yellow_1(k2_struct_0(X0)))
% 1.48/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 1.48/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
% 1.48/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.48/0.99      | ~ r2_hidden(X3,X1)
% 1.48/0.99      | r2_hidden(X2,k2_pre_topc(X0,X3))
% 1.48/0.99      | v1_xboole_0(X1)
% 1.48/0.99      | ~ v2_pre_topc(X0)
% 1.48/0.99      | ~ l1_pre_topc(X0)
% 1.48/0.99      | v2_struct_0(X0) ),
% 1.48/0.99      inference(cnf_transformation,[],[f67]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_30,negated_conjecture,
% 1.48/0.99      ( r2_waybel_7(sK6,sK8,sK9) | ~ v4_pre_topc(sK7,sK6) ),
% 1.48/0.99      inference(cnf_transformation,[],[f80]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_717,plain,
% 1.48/0.99      ( ~ v2_waybel_0(sK8,k3_yellow_1(k2_struct_0(sK6)))
% 1.48/0.99      | ~ v13_waybel_0(sK8,k3_yellow_1(k2_struct_0(sK6)))
% 1.48/0.99      | ~ v3_waybel_7(sK8,k3_yellow_1(k2_struct_0(sK6)))
% 1.48/0.99      | ~ v4_pre_topc(sK7,sK6)
% 1.48/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.48/0.99      | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
% 1.48/0.99      | ~ m1_subset_1(sK9,u1_struct_0(sK6))
% 1.48/0.99      | ~ r2_hidden(X0,sK8)
% 1.48/0.99      | r2_hidden(sK9,k2_pre_topc(sK6,X0))
% 1.48/0.99      | v1_xboole_0(sK8)
% 1.48/0.99      | ~ v2_pre_topc(sK6)
% 1.48/0.99      | ~ l1_pre_topc(sK6)
% 1.48/0.99      | v2_struct_0(sK6) ),
% 1.48/0.99      inference(resolution,[status(thm)],[c_21,c_30]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_37,negated_conjecture,
% 1.48/0.99      ( ~ v4_pre_topc(sK7,sK6) | ~ v1_xboole_0(sK8) ),
% 1.48/0.99      inference(cnf_transformation,[],[f73]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_36,negated_conjecture,
% 1.48/0.99      ( v2_waybel_0(sK8,k3_yellow_1(k2_struct_0(sK6)))
% 1.48/0.99      | ~ v4_pre_topc(sK7,sK6) ),
% 1.48/0.99      inference(cnf_transformation,[],[f74]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_35,negated_conjecture,
% 1.48/0.99      ( v13_waybel_0(sK8,k3_yellow_1(k2_struct_0(sK6)))
% 1.48/0.99      | ~ v4_pre_topc(sK7,sK6) ),
% 1.48/0.99      inference(cnf_transformation,[],[f75]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_34,negated_conjecture,
% 1.48/0.99      ( v3_waybel_7(sK8,k3_yellow_1(k2_struct_0(sK6)))
% 1.48/0.99      | ~ v4_pre_topc(sK7,sK6) ),
% 1.48/0.99      inference(cnf_transformation,[],[f76]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_33,negated_conjecture,
% 1.48/0.99      ( ~ v4_pre_topc(sK7,sK6)
% 1.48/0.99      | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))) ),
% 1.48/0.99      inference(cnf_transformation,[],[f77]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_31,negated_conjecture,
% 1.48/0.99      ( ~ v4_pre_topc(sK7,sK6) | m1_subset_1(sK9,u1_struct_0(sK6)) ),
% 1.48/0.99      inference(cnf_transformation,[],[f79]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_721,plain,
% 1.48/0.99      ( ~ v4_pre_topc(sK7,sK6)
% 1.48/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.48/0.99      | ~ r2_hidden(X0,sK8)
% 1.48/0.99      | r2_hidden(sK9,k2_pre_topc(sK6,X0)) ),
% 1.48/0.99      inference(global_propositional_subsumption,
% 1.48/0.99                [status(thm)],
% 1.48/0.99                [c_717,c_42,c_41,c_40,c_37,c_36,c_35,c_34,c_33,c_31]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_2949,plain,
% 1.48/0.99      ( ~ v4_pre_topc(sK7,sK6)
% 1.48/0.99      | ~ m1_subset_1(X0_60,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.48/0.99      | ~ r2_hidden(X0_60,sK8)
% 1.48/0.99      | r2_hidden(sK9,k2_pre_topc(sK6,X0_60)) ),
% 1.48/0.99      inference(subtyping,[status(esa)],[c_721]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_2971,plain,
% 1.48/0.99      ( ~ v4_pre_topc(sK7,sK6)
% 1.48/0.99      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.48/0.99      | ~ r2_hidden(sK7,sK8)
% 1.48/0.99      | r2_hidden(sK9,k2_pre_topc(sK6,sK7)) ),
% 1.48/0.99      inference(instantiation,[status(thm)],[c_2949]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_12,plain,
% 1.48/0.99      ( sP0(X0,X1) | m1_subset_1(sK4(X0,X1),u1_struct_0(X1)) ),
% 1.48/0.99      inference(cnf_transformation,[],[f56]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_2954,plain,
% 1.48/0.99      ( sP0(X0_60,X0_61)
% 1.48/0.99      | m1_subset_1(sK4(X0_60,X0_61),u1_struct_0(X0_61)) ),
% 1.48/0.99      inference(subtyping,[status(esa)],[c_12]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_2964,plain,
% 1.48/0.99      ( sP0(sK7,sK6) | m1_subset_1(sK4(sK7,sK6),u1_struct_0(sK6)) ),
% 1.48/0.99      inference(instantiation,[status(thm)],[c_2954]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_11,plain,
% 1.48/0.99      ( sP0(X0,X1) | r2_hidden(sK4(X0,X1),k10_yellow_6(X1,sK3(X0,X1))) ),
% 1.48/0.99      inference(cnf_transformation,[],[f57]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_2955,plain,
% 1.48/0.99      ( sP0(X0_60,X0_61)
% 1.48/0.99      | r2_hidden(sK4(X0_60,X0_61),k10_yellow_6(X0_61,sK3(X0_60,X0_61))) ),
% 1.48/0.99      inference(subtyping,[status(esa)],[c_11]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_2961,plain,
% 1.48/0.99      ( sP0(sK7,sK6)
% 1.48/0.99      | r2_hidden(sK4(sK7,sK6),k10_yellow_6(sK6,sK3(sK7,sK6))) ),
% 1.48/0.99      inference(instantiation,[status(thm)],[c_2955]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_10,plain,
% 1.48/0.99      ( sP0(X0,X1) | ~ r2_hidden(sK4(X0,X1),X0) ),
% 1.48/0.99      inference(cnf_transformation,[],[f58]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_2956,plain,
% 1.48/0.99      ( sP0(X0_60,X0_61) | ~ r2_hidden(sK4(X0_60,X0_61),X0_60) ),
% 1.48/0.99      inference(subtyping,[status(esa)],[c_10]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_2958,plain,
% 1.48/0.99      ( sP0(sK7,sK6) | ~ r2_hidden(sK4(sK7,sK6),sK7) ),
% 1.48/0.99      inference(instantiation,[status(thm)],[c_2956]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_29,negated_conjecture,
% 1.48/0.99      ( ~ v4_pre_topc(sK7,sK6) | ~ r2_hidden(sK9,sK7) ),
% 1.48/0.99      inference(cnf_transformation,[],[f81]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_1754,plain,
% 1.48/0.99      ( ~ sP0(sK7,sK6)
% 1.48/0.99      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.48/0.99      | ~ r2_hidden(sK9,sK7) ),
% 1.48/0.99      inference(resolution,[status(thm)],[c_29,c_1271]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_39,negated_conjecture,
% 1.48/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
% 1.48/0.99      inference(cnf_transformation,[],[f71]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_1756,plain,
% 1.48/0.99      ( ~ sP0(sK7,sK6) | ~ r2_hidden(sK9,sK7) ),
% 1.48/0.99      inference(global_propositional_subsumption,
% 1.48/0.99                [status(thm)],
% 1.48/0.99                [c_1754,c_39]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_1741,plain,
% 1.48/0.99      ( ~ sP0(sK7,sK6)
% 1.48/0.99      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.48/0.99      | m1_subset_1(sK9,u1_struct_0(sK6)) ),
% 1.48/0.99      inference(resolution,[status(thm)],[c_31,c_1271]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_1743,plain,
% 1.48/0.99      ( ~ sP0(sK7,sK6) | m1_subset_1(sK9,u1_struct_0(sK6)) ),
% 1.48/0.99      inference(global_propositional_subsumption,
% 1.48/0.99                [status(thm)],
% 1.48/0.99                [c_1741,c_39]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_32,negated_conjecture,
% 1.48/0.99      ( ~ v4_pre_topc(sK7,sK6) | r2_hidden(sK7,sK8) ),
% 1.48/0.99      inference(cnf_transformation,[],[f78]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_1728,plain,
% 1.48/0.99      ( ~ sP0(sK7,sK6)
% 1.48/0.99      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.48/0.99      | r2_hidden(sK7,sK8) ),
% 1.48/0.99      inference(resolution,[status(thm)],[c_32,c_1271]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(c_1730,plain,
% 1.48/0.99      ( ~ sP0(sK7,sK6) | r2_hidden(sK7,sK8) ),
% 1.48/0.99      inference(global_propositional_subsumption,
% 1.48/0.99                [status(thm)],
% 1.48/0.99                [c_1728,c_39]) ).
% 1.48/0.99  
% 1.48/0.99  cnf(contradiction,plain,
% 1.48/0.99      ( $false ),
% 1.48/0.99      inference(minisat,
% 1.48/0.99                [status(thm)],
% 1.48/0.99                [c_3123,c_3100,c_3092,c_3088,c_3049,c_2994,c_2991,c_2971,
% 1.48/0.99                 c_2964,c_2961,c_2958,c_1756,c_1743,c_1730,c_39]) ).
% 1.48/0.99  
% 1.48/0.99  
% 1.48/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 1.48/0.99  
% 1.48/0.99  ------                               Statistics
% 1.48/0.99  
% 1.48/0.99  ------ General
% 1.48/0.99  
% 1.48/0.99  abstr_ref_over_cycles:                  0
% 1.48/0.99  abstr_ref_under_cycles:                 0
% 1.48/0.99  gc_basic_clause_elim:                   0
% 1.48/0.99  forced_gc_time:                         0
% 1.48/0.99  parsing_time:                           0.021
% 1.48/0.99  unif_index_cands_time:                  0.
% 1.48/0.99  unif_index_add_time:                    0.
% 1.48/0.99  orderings_time:                         0.
% 1.48/0.99  out_proof_time:                         0.016
% 1.48/0.99  total_time:                             0.126
% 1.48/0.99  num_of_symbols:                         64
% 1.48/0.99  num_of_terms:                           1589
% 1.48/0.99  
% 1.48/0.99  ------ Preprocessing
% 1.48/0.99  
% 1.48/0.99  num_of_splits:                          0
% 1.48/0.99  num_of_split_atoms:                     0
% 1.48/0.99  num_of_reused_defs:                     0
% 1.48/0.99  num_eq_ax_congr_red:                    0
% 1.48/0.99  num_of_sem_filtered_clauses:            2
% 1.48/0.99  num_of_subtypes:                        4
% 1.48/0.99  monotx_restored_types:                  0
% 1.48/0.99  sat_num_of_epr_types:                   0
% 1.48/0.99  sat_num_of_non_cyclic_types:            0
% 1.48/0.99  sat_guarded_non_collapsed_types:        0
% 1.48/0.99  num_pure_diseq_elim:                    0
% 1.48/0.99  simp_replaced_by:                       0
% 1.48/0.99  res_preprocessed:                       79
% 1.48/0.99  prep_upred:                             0
% 1.48/0.99  prep_unflattend:                        0
% 1.48/0.99  smt_new_axioms:                         0
% 1.48/0.99  pred_elim_cands:                        4
% 1.48/0.99  pred_elim:                              14
% 1.48/0.99  pred_elim_cl:                           24
% 1.48/0.99  pred_elim_cycles:                       21
% 1.48/0.99  merged_defs:                            0
% 1.48/0.99  merged_defs_ncl:                        0
% 1.48/0.99  bin_hyper_res:                          0
% 1.48/0.99  prep_cycles:                            3
% 1.48/0.99  pred_elim_time:                         0.043
% 1.48/0.99  splitting_time:                         0.
% 1.48/0.99  sem_filter_time:                        0.
% 1.48/0.99  monotx_time:                            0.
% 1.48/0.99  subtype_inf_time:                       0.
% 1.48/0.99  
% 1.48/0.99  ------ Problem properties
% 1.48/0.99  
% 1.48/0.99  clauses:                                17
% 1.48/0.99  conjectures:                            4
% 1.48/0.99  epr:                                    2
% 1.48/0.99  horn:                                   13
% 1.48/0.99  ground:                                 4
% 1.48/0.99  unary:                                  1
% 1.48/0.99  binary:                                 6
% 1.48/0.99  lits:                                   61
% 1.48/0.99  lits_eq:                                0
% 1.48/0.99  fd_pure:                                0
% 1.48/0.99  fd_pseudo:                              0
% 1.48/0.99  fd_cond:                                0
% 1.48/0.99  fd_pseudo_cond:                         0
% 1.48/0.99  ac_symbols:                             0
% 1.48/0.99  
% 1.48/0.99  ------ Propositional Solver
% 1.48/0.99  
% 1.48/0.99  prop_solver_calls:                      17
% 1.48/0.99  prop_fast_solver_calls:                 1316
% 1.48/0.99  smt_solver_calls:                       0
% 1.48/0.99  smt_fast_solver_calls:                  0
% 1.48/0.99  prop_num_of_clauses:                    495
% 1.48/0.99  prop_preprocess_simplified:             2780
% 1.48/0.99  prop_fo_subsumed:                       66
% 1.48/0.99  prop_solver_time:                       0.
% 1.48/0.99  smt_solver_time:                        0.
% 1.48/0.99  smt_fast_solver_time:                   0.
% 1.48/0.99  prop_fast_solver_time:                  0.
% 1.48/0.99  prop_unsat_core_time:                   0.
% 1.48/0.99  
% 1.48/0.99  ------ QBF
% 1.48/0.99  
% 1.48/0.99  qbf_q_res:                              0
% 1.48/0.99  qbf_num_tautologies:                    0
% 1.48/0.99  qbf_prep_cycles:                        0
% 1.48/0.99  
% 1.48/0.99  ------ BMC1
% 1.48/0.99  
% 1.48/0.99  bmc1_current_bound:                     -1
% 1.48/0.99  bmc1_last_solved_bound:                 -1
% 1.48/0.99  bmc1_unsat_core_size:                   -1
% 1.48/0.99  bmc1_unsat_core_parents_size:           -1
% 1.48/0.99  bmc1_merge_next_fun:                    0
% 1.48/0.99  bmc1_unsat_core_clauses_time:           0.
% 1.48/0.99  
% 1.48/0.99  ------ Instantiation
% 1.48/0.99  
% 1.48/0.99  inst_num_of_clauses:                    32
% 1.48/0.99  inst_num_in_passive:                    2
% 1.48/0.99  inst_num_in_active:                     29
% 1.48/0.99  inst_num_in_unprocessed:                0
% 1.48/0.99  inst_num_of_loops:                      38
% 1.48/0.99  inst_num_of_learning_restarts:          0
% 1.48/0.99  inst_num_moves_active_passive:          6
% 1.48/0.99  inst_lit_activity:                      0
% 1.48/0.99  inst_lit_activity_moves:                0
% 1.48/0.99  inst_num_tautologies:                   0
% 1.48/0.99  inst_num_prop_implied:                  0
% 1.48/0.99  inst_num_existing_simplified:           0
% 1.48/0.99  inst_num_eq_res_simplified:             0
% 1.48/0.99  inst_num_child_elim:                    0
% 1.48/0.99  inst_num_of_dismatching_blockings:      0
% 1.48/0.99  inst_num_of_non_proper_insts:           8
% 1.48/0.99  inst_num_of_duplicates:                 0
% 1.48/0.99  inst_inst_num_from_inst_to_res:         0
% 1.48/0.99  inst_dismatching_checking_time:         0.
% 1.48/0.99  
% 1.48/0.99  ------ Resolution
% 1.48/0.99  
% 1.48/0.99  res_num_of_clauses:                     0
% 1.48/0.99  res_num_in_passive:                     0
% 1.48/0.99  res_num_in_active:                      0
% 1.48/0.99  res_num_of_loops:                       82
% 1.48/0.99  res_forward_subset_subsumed:            0
% 1.48/0.99  res_backward_subset_subsumed:           0
% 1.48/0.99  res_forward_subsumed:                   0
% 1.48/0.99  res_backward_subsumed:                  0
% 1.48/0.99  res_forward_subsumption_resolution:     12
% 1.48/0.99  res_backward_subsumption_resolution:    1
% 1.48/0.99  res_clause_to_clause_subsumption:       118
% 1.48/0.99  res_orphan_elimination:                 0
% 1.48/0.99  res_tautology_del:                      8
% 1.48/0.99  res_num_eq_res_simplified:              0
% 1.48/0.99  res_num_sel_changes:                    0
% 1.48/0.99  res_moves_from_active_to_pass:          0
% 1.48/0.99  
% 1.48/0.99  ------ Superposition
% 1.48/0.99  
% 1.48/0.99  sup_time_total:                         0.
% 1.48/0.99  sup_time_generating:                    0.
% 1.48/0.99  sup_time_sim_full:                      0.
% 1.48/0.99  sup_time_sim_immed:                     0.
% 1.48/0.99  
% 1.48/0.99  sup_num_of_clauses:                     0
% 1.48/0.99  sup_num_in_active:                      0
% 1.48/0.99  sup_num_in_passive:                     0
% 1.48/0.99  sup_num_of_loops:                       0
% 1.48/0.99  sup_fw_superposition:                   0
% 1.48/0.99  sup_bw_superposition:                   0
% 1.48/0.99  sup_immediate_simplified:               0
% 1.48/0.99  sup_given_eliminated:                   0
% 1.48/0.99  comparisons_done:                       0
% 1.48/0.99  comparisons_avoided:                    0
% 1.48/0.99  
% 1.48/0.99  ------ Simplifications
% 1.48/0.99  
% 1.48/0.99  
% 1.48/0.99  sim_fw_subset_subsumed:                 0
% 1.48/0.99  sim_bw_subset_subsumed:                 0
% 1.48/0.99  sim_fw_subsumed:                        0
% 1.48/0.99  sim_bw_subsumed:                        0
% 1.48/0.99  sim_fw_subsumption_res:                 0
% 1.48/0.99  sim_bw_subsumption_res:                 0
% 1.48/0.99  sim_tautology_del:                      0
% 1.48/0.99  sim_eq_tautology_del:                   0
% 1.48/0.99  sim_eq_res_simp:                        0
% 1.48/0.99  sim_fw_demodulated:                     0
% 1.48/0.99  sim_bw_demodulated:                     0
% 1.48/0.99  sim_light_normalised:                   0
% 1.48/0.99  sim_joinable_taut:                      0
% 1.48/0.99  sim_joinable_simp:                      0
% 1.48/0.99  sim_ac_normalised:                      0
% 1.48/0.99  sim_smt_subsumption:                    0
% 1.48/0.99  
%------------------------------------------------------------------------------
