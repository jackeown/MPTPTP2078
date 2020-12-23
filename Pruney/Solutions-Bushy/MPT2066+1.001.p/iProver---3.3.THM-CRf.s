%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT2066+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:07 EST 2020

% Result     : Theorem 3.28s
% Output     : CNFRefutation 3.28s
% Verified   : 
% Statistics : Number of formulae       :  227 (2336 expanded)
%              Number of clauses        :  155 ( 416 expanded)
%              Number of leaves         :   17 ( 706 expanded)
%              Depth                    :   32
%              Number of atoms          : 1319 (37555 expanded)
%              Number of equality atoms :  306 ( 508 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal clause size      :   48 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f27])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
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

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

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
    inference(nnf_transformation,[],[f14])).

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X2,k10_yellow_6(X0,X4))
          & r1_waybel_0(X0,X4,X1)
          & l1_waybel_0(X4,X0)
          & v3_yellow_6(X4,X0)
          & v7_waybel_0(X4)
          & v4_orders_2(X4)
          & ~ v2_struct_0(X4) )
     => ( r2_hidden(X2,k10_yellow_6(X0,sK1(X0,X1,X2)))
        & r1_waybel_0(X0,sK1(X0,X1,X2),X1)
        & l1_waybel_0(sK1(X0,X1,X2),X0)
        & v3_yellow_6(sK1(X0,X1,X2),X0)
        & v7_waybel_0(sK1(X0,X1,X2))
        & v4_orders_2(sK1(X0,X1,X2))
        & ~ v2_struct_0(sK1(X0,X1,X2)) ) ) ),
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
                & ( ( r2_hidden(X2,k10_yellow_6(X0,sK1(X0,X1,X2)))
                    & r1_waybel_0(X0,sK1(X0,X1,X2),X1)
                    & l1_waybel_0(sK1(X0,X1,X2),X0)
                    & v3_yellow_6(sK1(X0,X1,X2),X0)
                    & v7_waybel_0(sK1(X0,X1,X2))
                    & v4_orders_2(sK1(X0,X1,X2))
                    & ~ v2_struct_0(sK1(X0,X1,X2)) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f29,f30])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v3_yellow_6(sK1(X0,X1,X2),X0)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f20,plain,(
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

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & r2_hidden(X3,k10_yellow_6(X0,X2))
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(sK5,X1)
        & r2_hidden(sK5,k10_yellow_6(X0,X2))
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ? [X2] :
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
     => ( ? [X3] :
            ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,k10_yellow_6(X0,sK4))
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & r1_waybel_0(X0,sK4,X1)
        & l1_waybel_0(sK4,X0)
        & v3_yellow_6(sK4,X0)
        & v7_waybel_0(sK4)
        & v4_orders_2(sK4)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
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
     => ( ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(X3,sK3)
                  & r2_hidden(X3,k10_yellow_6(X0,X2))
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & r1_waybel_0(X0,X2,sK3)
              & l1_waybel_0(X2,X0)
              & v3_yellow_6(X2,X0)
              & v7_waybel_0(X2)
              & v4_orders_2(X2)
              & ~ v2_struct_0(X2) )
          | ~ v4_pre_topc(sK3,X0) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( r2_hidden(X5,sK3)
                  | ~ r2_hidden(X5,k10_yellow_6(X0,X4))
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ r1_waybel_0(X0,X4,sK3)
              | ~ l1_waybel_0(X4,X0)
              | ~ v3_yellow_6(X4,X0)
              | ~ v7_waybel_0(X4)
              | ~ v4_orders_2(X4)
              | v2_struct_0(X4) )
          | v4_pre_topc(sK3,X0) )
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
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
                    & r2_hidden(X3,k10_yellow_6(sK2,X2))
                    & m1_subset_1(X3,u1_struct_0(sK2)) )
                & r1_waybel_0(sK2,X2,X1)
                & l1_waybel_0(X2,sK2)
                & v3_yellow_6(X2,sK2)
                & v7_waybel_0(X2)
                & v4_orders_2(X2)
                & ~ v2_struct_0(X2) )
            | ~ v4_pre_topc(X1,sK2) )
          & ( ! [X4] :
                ( ! [X5] :
                    ( r2_hidden(X5,X1)
                    | ~ r2_hidden(X5,k10_yellow_6(sK2,X4))
                    | ~ m1_subset_1(X5,u1_struct_0(sK2)) )
                | ~ r1_waybel_0(sK2,X4,X1)
                | ~ l1_waybel_0(X4,sK2)
                | ~ v3_yellow_6(X4,sK2)
                | ~ v7_waybel_0(X4)
                | ~ v4_orders_2(X4)
                | v2_struct_0(X4) )
            | v4_pre_topc(X1,sK2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ( ( ~ r2_hidden(sK5,sK3)
        & r2_hidden(sK5,k10_yellow_6(sK2,sK4))
        & m1_subset_1(sK5,u1_struct_0(sK2))
        & r1_waybel_0(sK2,sK4,sK3)
        & l1_waybel_0(sK4,sK2)
        & v3_yellow_6(sK4,sK2)
        & v7_waybel_0(sK4)
        & v4_orders_2(sK4)
        & ~ v2_struct_0(sK4) )
      | ~ v4_pre_topc(sK3,sK2) )
    & ( ! [X4] :
          ( ! [X5] :
              ( r2_hidden(X5,sK3)
              | ~ r2_hidden(X5,k10_yellow_6(sK2,X4))
              | ~ m1_subset_1(X5,u1_struct_0(sK2)) )
          | ~ r1_waybel_0(sK2,X4,sK3)
          | ~ l1_waybel_0(X4,sK2)
          | ~ v3_yellow_6(X4,sK2)
          | ~ v7_waybel_0(X4)
          | ~ v4_orders_2(X4)
          | v2_struct_0(X4) )
      | v4_pre_topc(sK3,sK2) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f34,f38,f37,f36,f35])).

fof(f60,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f59,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f61,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f22])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f73,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f41])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k10_yellow_6(X0,sK1(X0,X1,X2)))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(sK1(X0,X1,X2),X0)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_waybel_0(X0,sK1(X0,X1,X2),X1)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f63,plain,(
    ! [X4,X5] :
      ( r2_hidden(X5,sK3)
      | ~ r2_hidden(X5,k10_yellow_6(sK2,X4))
      | ~ m1_subset_1(X5,u1_struct_0(sK2))
      | ~ r1_waybel_0(sK2,X4,sK3)
      | ~ l1_waybel_0(X4,sK2)
      | ~ v3_yellow_6(X4,sK2)
      | ~ v7_waybel_0(X4)
      | ~ v4_orders_2(X4)
      | v2_struct_0(X4)
      | v4_pre_topc(sK3,sK2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f62,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f39])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
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

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v7_waybel_0(sK1(X0,X1,X2))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v4_orders_2(sK1(X0,X1,X2))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(sK1(X0,X1,X2))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f54,plain,(
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
    inference(cnf_transformation,[],[f31])).

fof(f69,plain,
    ( r1_waybel_0(sK2,sK4,sK3)
    | ~ v4_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f64,plain,
    ( ~ v2_struct_0(sK4)
    | ~ v4_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f65,plain,
    ( v4_orders_2(sK4)
    | ~ v4_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f66,plain,
    ( v7_waybel_0(sK4)
    | ~ v4_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f67,plain,
    ( v3_yellow_6(sK4,sK2)
    | ~ v4_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f68,plain,
    ( l1_waybel_0(sK4,sK2)
    | ~ v4_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f72,plain,
    ( ~ r2_hidden(sK5,sK3)
    | ~ v4_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f71,plain,
    ( r2_hidden(sK5,k10_yellow_6(sK2,sK4))
    | ~ v4_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f70,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ v4_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f42,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_4,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_3414,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_11,plain,
    ( v3_yellow_6(sK1(X0,X1,X2),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_31,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_739,plain,
    ( v3_yellow_6(sK1(X0,X1,X2),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_31])).

cnf(c_740,plain,
    ( v3_yellow_6(sK1(sK2,X0,X1),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ r2_hidden(X1,k2_pre_topc(sK2,X0))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_739])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_30,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_744,plain,
    ( v3_yellow_6(sK1(sK2,X0,X1),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ r2_hidden(X1,k2_pre_topc(sK2,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_740,c_32,c_30])).

cnf(c_3400,plain,
    ( v3_yellow_6(sK1(sK2,X0,X1),sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X1,k2_pre_topc(sK2,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_744])).

cnf(c_746,plain,
    ( v3_yellow_6(sK1(sK2,X0,X1),sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X1,k2_pre_topc(sK2,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_744])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_969,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_30])).

cnf(c_970,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(k2_pre_topc(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_969])).

cnf(c_3391,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_970])).

cnf(c_16,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_3412,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4525,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) = iProver_top
    | r2_hidden(X1,k2_pre_topc(sK2,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3391,c_3412])).

cnf(c_4757,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v3_yellow_6(sK1(sK2,X0,X1),sK2) = iProver_top
    | r2_hidden(X1,k2_pre_topc(sK2,X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3400,c_746,c_4525])).

cnf(c_4758,plain,
    ( v3_yellow_6(sK1(sK2,X0,X1),sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(X1,k2_pre_topc(sK2,X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4757])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_3416,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,k10_yellow_6(X1,sK1(X1,X0,X2)))
    | ~ r2_hidden(X2,k2_pre_topc(X1,X0))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_882,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,k10_yellow_6(X1,sK1(X1,X0,X2)))
    | ~ r2_hidden(X2,k2_pre_topc(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_31])).

cnf(c_883,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r2_hidden(X1,k10_yellow_6(sK2,sK1(sK2,X0,X1)))
    | ~ r2_hidden(X1,k2_pre_topc(sK2,X0))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_882])).

cnf(c_887,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r2_hidden(X1,k10_yellow_6(sK2,sK1(sK2,X0,X1)))
    | ~ r2_hidden(X1,k2_pre_topc(sK2,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_883,c_32,c_30])).

cnf(c_3394,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X1,k10_yellow_6(sK2,sK1(sK2,X0,X1))) = iProver_top
    | r2_hidden(X1,k2_pre_topc(sK2,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_887])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_3413,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4404,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X1,X2) = iProver_top
    | r2_hidden(X1,k2_pre_topc(sK2,X0)) != iProver_top
    | r1_tarski(k10_yellow_6(sK2,sK1(sK2,X0,X1)),X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3394,c_3413])).

cnf(c_6099,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(X1,X2) = iProver_top
    | r2_hidden(X1,k2_pre_topc(sK2,X0)) != iProver_top
    | r1_tarski(k10_yellow_6(sK2,sK1(sK2,X0,X1)),X2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4404,c_4525])).

cnf(c_6109,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(X1,k10_yellow_6(sK2,sK1(sK2,X0,X1))) = iProver_top
    | r2_hidden(X1,k2_pre_topc(sK2,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3416,c_6099])).

cnf(c_10,plain,
    ( l1_waybel_0(sK1(X0,X1,X2),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_9,plain,
    ( r1_waybel_0(X0,sK1(X0,X1,X2),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_28,negated_conjecture,
    ( ~ r1_waybel_0(sK2,X0,sK3)
    | v4_pre_topc(sK3,sK2)
    | ~ v3_yellow_6(X0,sK2)
    | ~ l1_waybel_0(X0,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ r2_hidden(X1,k10_yellow_6(sK2,X0))
    | r2_hidden(X1,sK3)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_424,plain,
    ( v4_pre_topc(sK3,sK2)
    | ~ v3_yellow_6(X0,sK2)
    | ~ l1_waybel_0(X0,sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(sK2))
    | ~ r2_hidden(X4,k10_yellow_6(sK2,X0))
    | ~ r2_hidden(X3,k2_pre_topc(X2,X1))
    | r2_hidden(X4,sK3)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(X2)
    | sK1(X2,X1,X3) != X0
    | sK2 != X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_28])).

cnf(c_425,plain,
    ( v4_pre_topc(sK3,sK2)
    | ~ v3_yellow_6(sK1(sK2,sK3,X0),sK2)
    | ~ l1_waybel_0(sK1(sK2,sK3,X0),sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1,k10_yellow_6(sK2,sK1(sK2,sK3,X0)))
    | ~ r2_hidden(X0,k2_pre_topc(sK2,sK3))
    | r2_hidden(X1,sK3)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK1(sK2,sK3,X0))
    | v2_struct_0(sK2)
    | ~ v4_orders_2(sK1(sK2,sK3,X0))
    | ~ v7_waybel_0(sK1(sK2,sK3,X0))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_424])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_429,plain,
    ( ~ v7_waybel_0(sK1(sK2,sK3,X0))
    | ~ v4_orders_2(sK1(sK2,sK3,X0))
    | r2_hidden(X1,sK3)
    | ~ r2_hidden(X0,k2_pre_topc(sK2,sK3))
    | ~ r2_hidden(X1,k10_yellow_6(sK2,sK1(sK2,sK3,X0)))
    | v4_pre_topc(sK3,sK2)
    | ~ v3_yellow_6(sK1(sK2,sK3,X0),sK2)
    | ~ l1_waybel_0(sK1(sK2,sK3,X0),sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | v2_struct_0(sK1(sK2,sK3,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_425,c_32,c_31,c_30,c_29])).

cnf(c_430,plain,
    ( v4_pre_topc(sK3,sK2)
    | ~ v3_yellow_6(sK1(sK2,sK3,X0),sK2)
    | ~ l1_waybel_0(sK1(sK2,sK3,X0),sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ r2_hidden(X1,k10_yellow_6(sK2,sK1(sK2,sK3,X0)))
    | ~ r2_hidden(X0,k2_pre_topc(sK2,sK3))
    | r2_hidden(X1,sK3)
    | v2_struct_0(sK1(sK2,sK3,X0))
    | ~ v4_orders_2(sK1(sK2,sK3,X0))
    | ~ v7_waybel_0(sK1(sK2,sK3,X0)) ),
    inference(renaming,[status(thm)],[c_429])).

cnf(c_487,plain,
    ( v4_pre_topc(sK3,sK2)
    | ~ v3_yellow_6(sK1(sK2,sK3,X0),sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ r2_hidden(X4,k10_yellow_6(sK2,sK1(sK2,sK3,X0)))
    | ~ r2_hidden(X3,k2_pre_topc(X2,X1))
    | ~ r2_hidden(X0,k2_pre_topc(sK2,sK3))
    | r2_hidden(X4,sK3)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X2)
    | v2_struct_0(sK1(sK2,sK3,X0))
    | ~ v4_orders_2(sK1(sK2,sK3,X0))
    | ~ v7_waybel_0(sK1(sK2,sK3,X0))
    | ~ l1_pre_topc(X2)
    | sK1(X2,X1,X3) != sK1(sK2,sK3,X0)
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_430])).

cnf(c_488,plain,
    ( v4_pre_topc(sK3,sK2)
    | ~ v3_yellow_6(sK1(sK2,sK3,X0),sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X3,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ r2_hidden(X2,k10_yellow_6(sK2,sK1(sK2,sK3,X0)))
    | ~ r2_hidden(X3,k2_pre_topc(sK2,X1))
    | ~ r2_hidden(X0,k2_pre_topc(sK2,sK3))
    | r2_hidden(X2,sK3)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK1(sK2,sK3,X0))
    | v2_struct_0(sK2)
    | ~ v4_orders_2(sK1(sK2,sK3,X0))
    | ~ v7_waybel_0(sK1(sK2,sK3,X0))
    | ~ l1_pre_topc(sK2)
    | sK1(sK2,X1,X3) != sK1(sK2,sK3,X0) ),
    inference(unflattening,[status(thm)],[c_487])).

cnf(c_492,plain,
    ( ~ v7_waybel_0(sK1(sK2,sK3,X0))
    | ~ v4_orders_2(sK1(sK2,sK3,X0))
    | r2_hidden(X2,sK3)
    | ~ r2_hidden(X0,k2_pre_topc(sK2,sK3))
    | ~ r2_hidden(X3,k2_pre_topc(sK2,X1))
    | ~ r2_hidden(X2,k10_yellow_6(sK2,sK1(sK2,sK3,X0)))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X3,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v3_yellow_6(sK1(sK2,sK3,X0),sK2)
    | v4_pre_topc(sK3,sK2)
    | v2_struct_0(sK1(sK2,sK3,X0))
    | sK1(sK2,X1,X3) != sK1(sK2,sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_488,c_32,c_31,c_30])).

cnf(c_493,plain,
    ( v4_pre_topc(sK3,sK2)
    | ~ v3_yellow_6(sK1(sK2,sK3,X0),sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X3,u1_struct_0(sK2))
    | ~ r2_hidden(X3,k10_yellow_6(sK2,sK1(sK2,sK3,X0)))
    | ~ r2_hidden(X2,k2_pre_topc(sK2,X1))
    | ~ r2_hidden(X0,k2_pre_topc(sK2,sK3))
    | r2_hidden(X3,sK3)
    | v2_struct_0(sK1(sK2,sK3,X0))
    | ~ v4_orders_2(sK1(sK2,sK3,X0))
    | ~ v7_waybel_0(sK1(sK2,sK3,X0))
    | sK1(sK2,X1,X2) != sK1(sK2,sK3,X0) ),
    inference(renaming,[status(thm)],[c_492])).

cnf(c_3401,plain,
    ( sK1(sK2,X0,X1) != sK1(sK2,sK3,X2)
    | v4_pre_topc(sK3,sK2) = iProver_top
    | v3_yellow_6(sK1(sK2,sK3,X2),sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X3,k10_yellow_6(sK2,sK1(sK2,sK3,X2))) != iProver_top
    | r2_hidden(X1,k2_pre_topc(sK2,X0)) != iProver_top
    | r2_hidden(X2,k2_pre_topc(sK2,sK3)) != iProver_top
    | r2_hidden(X3,sK3) = iProver_top
    | v2_struct_0(sK1(sK2,sK3,X2)) = iProver_top
    | v4_orders_2(sK1(sK2,sK3,X2)) != iProver_top
    | v7_waybel_0(sK1(sK2,sK3,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_493])).

cnf(c_36,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_18,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_942,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) = X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_30])).

cnf(c_943,plain,
    ( ~ v4_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k2_pre_topc(sK2,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_942])).

cnf(c_1651,plain,
    ( ~ v3_yellow_6(sK1(sK2,sK3,X0),sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X3,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X4,u1_struct_0(sK2))
    | ~ r2_hidden(X3,k10_yellow_6(sK2,sK1(sK2,sK3,X0)))
    | ~ r2_hidden(X4,k2_pre_topc(sK2,X1))
    | ~ r2_hidden(X0,k2_pre_topc(sK2,sK3))
    | r2_hidden(X3,sK3)
    | v2_struct_0(sK1(sK2,sK3,X0))
    | ~ v4_orders_2(sK1(sK2,sK3,X0))
    | ~ v7_waybel_0(sK1(sK2,sK3,X0))
    | sK1(sK2,X1,X4) != sK1(sK2,sK3,X0)
    | k2_pre_topc(sK2,X2) = X2
    | sK2 != sK2
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_493,c_943])).

cnf(c_1652,plain,
    ( ~ v3_yellow_6(sK1(sK2,sK3,X0),sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X3,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X3,k10_yellow_6(sK2,sK1(sK2,sK3,X0)))
    | ~ r2_hidden(X2,k2_pre_topc(sK2,X1))
    | ~ r2_hidden(X0,k2_pre_topc(sK2,sK3))
    | r2_hidden(X3,sK3)
    | v2_struct_0(sK1(sK2,sK3,X0))
    | ~ v4_orders_2(sK1(sK2,sK3,X0))
    | ~ v7_waybel_0(sK1(sK2,sK3,X0))
    | sK1(sK2,X1,X2) != sK1(sK2,sK3,X0)
    | k2_pre_topc(sK2,sK3) = sK3 ),
    inference(unflattening,[status(thm)],[c_1651])).

cnf(c_1653,plain,
    ( sK1(sK2,X0,X1) != sK1(sK2,sK3,X2)
    | k2_pre_topc(sK2,sK3) = sK3
    | v3_yellow_6(sK1(sK2,sK3,X2),sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(X3,k10_yellow_6(sK2,sK1(sK2,sK3,X2))) != iProver_top
    | r2_hidden(X1,k2_pre_topc(sK2,X0)) != iProver_top
    | r2_hidden(X2,k2_pre_topc(sK2,sK3)) != iProver_top
    | r2_hidden(X3,sK3) = iProver_top
    | v2_struct_0(sK1(sK2,sK3,X2)) = iProver_top
    | v4_orders_2(sK1(sK2,sK3,X2)) != iProver_top
    | v7_waybel_0(sK1(sK2,sK3,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1652])).

cnf(c_17,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_789,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_31])).

cnf(c_790,plain,
    ( v4_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | k2_pre_topc(sK2,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_789])).

cnf(c_794,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v4_pre_topc(X0,sK2)
    | k2_pre_topc(sK2,X0) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_790,c_30])).

cnf(c_795,plain,
    ( v4_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k2_pre_topc(sK2,X0) != X0 ),
    inference(renaming,[status(thm)],[c_794])).

cnf(c_3658,plain,
    ( v4_pre_topc(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | k2_pre_topc(sK2,sK3) != sK3 ),
    inference(instantiation,[status(thm)],[c_795])).

cnf(c_3659,plain,
    ( k2_pre_topc(sK2,sK3) != sK3
    | v4_pre_topc(sK3,sK2) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3658])).

cnf(c_4858,plain,
    ( m1_subset_1(X2,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v3_yellow_6(sK1(sK2,sK3,X2),sK2) != iProver_top
    | v4_pre_topc(sK3,sK2) = iProver_top
    | sK1(sK2,X0,X1) != sK1(sK2,sK3,X2)
    | m1_subset_1(X3,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X3,k10_yellow_6(sK2,sK1(sK2,sK3,X2))) != iProver_top
    | r2_hidden(X1,k2_pre_topc(sK2,X0)) != iProver_top
    | r2_hidden(X2,k2_pre_topc(sK2,sK3)) != iProver_top
    | r2_hidden(X3,sK3) = iProver_top
    | v2_struct_0(sK1(sK2,sK3,X2)) = iProver_top
    | v4_orders_2(sK1(sK2,sK3,X2)) != iProver_top
    | v7_waybel_0(sK1(sK2,sK3,X2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3401,c_36,c_1653,c_3659,c_4525])).

cnf(c_4859,plain,
    ( sK1(sK2,X0,X1) != sK1(sK2,sK3,X2)
    | v4_pre_topc(sK3,sK2) = iProver_top
    | v3_yellow_6(sK1(sK2,sK3,X2),sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X3,k10_yellow_6(sK2,sK1(sK2,sK3,X2))) != iProver_top
    | r2_hidden(X1,k2_pre_topc(sK2,X0)) != iProver_top
    | r2_hidden(X2,k2_pre_topc(sK2,sK3)) != iProver_top
    | r2_hidden(X3,sK3) = iProver_top
    | v2_struct_0(sK1(sK2,sK3,X2)) = iProver_top
    | v4_orders_2(sK1(sK2,sK3,X2)) != iProver_top
    | v7_waybel_0(sK1(sK2,sK3,X2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4858])).

cnf(c_3404,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,k2_pre_topc(X1,X0))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v7_waybel_0(sK1(X1,X0,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_858,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,k2_pre_topc(X1,X0))
    | v2_struct_0(X1)
    | v7_waybel_0(sK1(X1,X0,X2))
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_31])).

cnf(c_859,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ r2_hidden(X1,k2_pre_topc(sK2,X0))
    | v2_struct_0(sK2)
    | v7_waybel_0(sK1(sK2,X0,X1))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_858])).

cnf(c_863,plain,
    ( v7_waybel_0(sK1(sK2,X0,X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ r2_hidden(X1,k2_pre_topc(sK2,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_859,c_32,c_30])).

cnf(c_864,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ r2_hidden(X1,k2_pre_topc(sK2,X0))
    | v7_waybel_0(sK1(sK2,X0,X1)) ),
    inference(renaming,[status(thm)],[c_863])).

cnf(c_3395,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X1,k2_pre_topc(sK2,X0)) != iProver_top
    | v7_waybel_0(sK1(sK2,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_864])).

cnf(c_4290,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X0,k2_pre_topc(sK2,sK3)) != iProver_top
    | v7_waybel_0(sK1(sK2,sK3,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3404,c_3395])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,k2_pre_topc(X1,X0))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v4_orders_2(sK1(X1,X0,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_834,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,k2_pre_topc(X1,X0))
    | v2_struct_0(X1)
    | v4_orders_2(sK1(X1,X0,X2))
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_31])).

cnf(c_835,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ r2_hidden(X1,k2_pre_topc(sK2,X0))
    | v2_struct_0(sK2)
    | v4_orders_2(sK1(sK2,X0,X1))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_834])).

cnf(c_839,plain,
    ( v4_orders_2(sK1(sK2,X0,X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ r2_hidden(X1,k2_pre_topc(sK2,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_835,c_32,c_30])).

cnf(c_840,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ r2_hidden(X1,k2_pre_topc(sK2,X0))
    | v4_orders_2(sK1(sK2,X0,X1)) ),
    inference(renaming,[status(thm)],[c_839])).

cnf(c_3396,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X1,k2_pre_topc(sK2,X0)) != iProver_top
    | v4_orders_2(sK1(sK2,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_840])).

cnf(c_841,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X1,k2_pre_topc(sK2,X0)) != iProver_top
    | v4_orders_2(sK1(sK2,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_840])).

cnf(c_4615,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(X1,k2_pre_topc(sK2,X0)) != iProver_top
    | v4_orders_2(sK1(sK2,X0,X1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3396,c_841,c_4525])).

cnf(c_4624,plain,
    ( r2_hidden(X0,k2_pre_topc(sK2,sK3)) != iProver_top
    | v4_orders_2(sK1(sK2,sK3,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3404,c_4615])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,k2_pre_topc(X1,X0))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ v2_struct_0(sK1(X1,X0,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_810,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,k2_pre_topc(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_struct_0(sK1(X1,X0,X2))
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_31])).

cnf(c_811,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ r2_hidden(X1,k2_pre_topc(sK2,X0))
    | ~ v2_struct_0(sK1(sK2,X0,X1))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_810])).

cnf(c_815,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ r2_hidden(X1,k2_pre_topc(sK2,X0))
    | ~ v2_struct_0(sK1(sK2,X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_811,c_32,c_30])).

cnf(c_3397,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X1,k2_pre_topc(sK2,X0)) != iProver_top
    | v2_struct_0(sK1(sK2,X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_815])).

cnf(c_817,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X1,k2_pre_topc(sK2,X0)) != iProver_top
    | v2_struct_0(sK1(sK2,X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_815])).

cnf(c_4681,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(X1,k2_pre_topc(sK2,X0)) != iProver_top
    | v2_struct_0(sK1(sK2,X0,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3397,c_817,c_4525])).

cnf(c_4690,plain,
    ( r2_hidden(X0,k2_pre_topc(sK2,sK3)) != iProver_top
    | v2_struct_0(sK1(sK2,sK3,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3404,c_4681])).

cnf(c_4875,plain,
    ( sK1(sK2,X0,X1) != sK1(sK2,sK3,X2)
    | v4_pre_topc(sK3,sK2) = iProver_top
    | v3_yellow_6(sK1(sK2,sK3,X2),sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X3,k10_yellow_6(sK2,sK1(sK2,sK3,X2))) != iProver_top
    | r2_hidden(X1,k2_pre_topc(sK2,X0)) != iProver_top
    | r2_hidden(X2,k2_pre_topc(sK2,sK3)) != iProver_top
    | r2_hidden(X3,sK3) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4859,c_4290,c_4624,c_4690])).

cnf(c_4879,plain,
    ( v4_pre_topc(sK3,sK2) = iProver_top
    | v3_yellow_6(sK1(sK2,sK3,X0),sK2) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(X1,k10_yellow_6(sK2,sK1(sK2,sK3,X0))) != iProver_top
    | r2_hidden(X0,k2_pre_topc(sK2,sK3)) != iProver_top
    | r2_hidden(X1,sK3) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4875])).

cnf(c_5338,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2)) = iProver_top
    | r2_hidden(X0,k2_pre_topc(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3404,c_4525])).

cnf(c_7904,plain,
    ( v4_pre_topc(sK3,sK2) = iProver_top
    | v3_yellow_6(sK1(sK2,sK3,X0),sK2) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X1,k10_yellow_6(sK2,sK1(sK2,sK3,X0))) != iProver_top
    | r2_hidden(X0,k2_pre_topc(sK2,sK3)) != iProver_top
    | r2_hidden(X1,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4879,c_36,c_5338])).

cnf(c_7917,plain,
    ( v4_pre_topc(sK3,sK2) = iProver_top
    | v3_yellow_6(sK1(sK2,sK3,X0),sK2) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(X0,k2_pre_topc(sK2,sK3)) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_6109,c_7904])).

cnf(c_4402,plain,
    ( r2_hidden(sK0(X0,X1),X2) = iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3414,c_3413])).

cnf(c_7,plain,
    ( ~ r1_waybel_0(X0,X1,X2)
    | ~ v3_yellow_6(X1,X0)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r2_hidden(X3,k10_yellow_6(X0,X1))
    | r2_hidden(X3,k2_pre_topc(X0,X2))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_22,negated_conjecture,
    ( r1_waybel_0(sK2,sK4,sK3)
    | ~ v4_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_400,plain,
    ( ~ v4_pre_topc(sK3,sK2)
    | ~ v3_yellow_6(X0,X1)
    | ~ l1_waybel_0(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(X3,k10_yellow_6(X1,X0))
    | r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(X1)
    | sK4 != X0
    | sK2 != X1
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_22])).

cnf(c_401,plain,
    ( ~ v4_pre_topc(sK3,sK2)
    | ~ v3_yellow_6(sK4,sK2)
    | ~ l1_waybel_0(sK4,sK2)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X0,k10_yellow_6(sK2,sK4))
    | r2_hidden(X0,k2_pre_topc(sK2,sK3))
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK4)
    | v2_struct_0(sK2)
    | ~ v4_orders_2(sK4)
    | ~ v7_waybel_0(sK4)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_400])).

cnf(c_27,negated_conjecture,
    ( ~ v4_pre_topc(sK3,sK2)
    | ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_26,negated_conjecture,
    ( ~ v4_pre_topc(sK3,sK2)
    | v4_orders_2(sK4) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_25,negated_conjecture,
    ( ~ v4_pre_topc(sK3,sK2)
    | v7_waybel_0(sK4) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_24,negated_conjecture,
    ( ~ v4_pre_topc(sK3,sK2)
    | v3_yellow_6(sK4,sK2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_23,negated_conjecture,
    ( ~ v4_pre_topc(sK3,sK2)
    | l1_waybel_0(sK4,sK2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_405,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ v4_pre_topc(sK3,sK2)
    | ~ r2_hidden(X0,k10_yellow_6(sK2,sK4))
    | r2_hidden(X0,k2_pre_topc(sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_401,c_32,c_31,c_30,c_29,c_27,c_26,c_25,c_24,c_23])).

cnf(c_406,plain,
    ( ~ v4_pre_topc(sK3,sK2)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ r2_hidden(X0,k10_yellow_6(sK2,sK4))
    | r2_hidden(X0,k2_pre_topc(sK2,sK3)) ),
    inference(renaming,[status(thm)],[c_405])).

cnf(c_3402,plain,
    ( v4_pre_topc(sK3,sK2) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X0,k10_yellow_6(sK2,sK4)) != iProver_top
    | r2_hidden(X0,k2_pre_topc(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_406])).

cnf(c_4967,plain,
    ( v4_pre_topc(sK3,sK2) != iProver_top
    | m1_subset_1(sK0(X0,X1),u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK0(X0,X1),k2_pre_topc(sK2,sK3)) = iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k10_yellow_6(sK2,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4402,c_3402])).

cnf(c_7436,plain,
    ( v4_pre_topc(sK3,sK2) != iProver_top
    | m1_subset_1(sK0(X0,X1),u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK0(X0,X1),X2) = iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k10_yellow_6(sK2,sK4)) != iProver_top
    | r1_tarski(k2_pre_topc(sK2,sK3),X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4967,c_3413])).

cnf(c_19,negated_conjecture,
    ( ~ v4_pre_topc(sK3,sK2)
    | ~ r2_hidden(sK5,sK3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_48,plain,
    ( v4_pre_topc(sK3,sK2) != iProver_top
    | r2_hidden(sK5,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2857,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3709,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_2857])).

cnf(c_3906,plain,
    ( ~ v4_pre_topc(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | k2_pre_topc(sK2,sK3) = sK3 ),
    inference(instantiation,[status(thm)],[c_943])).

cnf(c_3907,plain,
    ( k2_pre_topc(sK2,sK3) = sK3
    | v4_pre_topc(sK3,sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3906])).

cnf(c_20,negated_conjecture,
    ( ~ v4_pre_topc(sK3,sK2)
    | r2_hidden(sK5,k10_yellow_6(sK2,sK4)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_3410,plain,
    ( v4_pre_topc(sK3,sK2) != iProver_top
    | r2_hidden(sK5,k10_yellow_6(sK2,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4156,plain,
    ( v4_pre_topc(sK3,sK2) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK5,k2_pre_topc(sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3410,c_3402])).

cnf(c_21,negated_conjecture,
    ( ~ v4_pre_topc(sK3,sK2)
    | m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_46,plain,
    ( v4_pre_topc(sK3,sK2) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_47,plain,
    ( v4_pre_topc(sK3,sK2) != iProver_top
    | r2_hidden(sK5,k10_yellow_6(sK2,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3979,plain,
    ( ~ v4_pre_topc(sK3,sK2)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ r2_hidden(sK5,k10_yellow_6(sK2,sK4))
    | r2_hidden(sK5,k2_pre_topc(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_406])).

cnf(c_3980,plain,
    ( v4_pre_topc(sK3,sK2) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK5,k10_yellow_6(sK2,sK4)) != iProver_top
    | r2_hidden(sK5,k2_pre_topc(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3979])).

cnf(c_4176,plain,
    ( v4_pre_topc(sK3,sK2) != iProver_top
    | r2_hidden(sK5,k2_pre_topc(sK2,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4156,c_46,c_47,c_3980])).

cnf(c_2858,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3759,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_2858])).

cnf(c_4120,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_3759])).

cnf(c_5543,plain,
    ( k2_pre_topc(sK2,sK3) != sK3
    | sK3 = k2_pre_topc(sK2,sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_4120])).

cnf(c_4201,plain,
    ( r2_hidden(sK5,X0)
    | ~ r2_hidden(sK5,k2_pre_topc(sK2,sK3))
    | ~ r1_tarski(k2_pre_topc(sK2,sK3),X0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_5615,plain,
    ( ~ r2_hidden(sK5,k2_pre_topc(sK2,sK3))
    | r2_hidden(sK5,sK3)
    | ~ r1_tarski(k2_pre_topc(sK2,sK3),sK3) ),
    inference(instantiation,[status(thm)],[c_4201])).

cnf(c_5616,plain,
    ( r2_hidden(sK5,k2_pre_topc(sK2,sK3)) != iProver_top
    | r2_hidden(sK5,sK3) = iProver_top
    | r1_tarski(k2_pre_topc(sK2,sK3),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5615])).

cnf(c_2859,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,X2)
    | X2 != X1 ),
    theory(equality)).

cnf(c_3747,plain,
    ( ~ r1_tarski(k2_pre_topc(sK2,sK3),X0)
    | r1_tarski(k2_pre_topc(sK2,sK3),sK3)
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_2859])).

cnf(c_6557,plain,
    ( ~ r1_tarski(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK3))
    | r1_tarski(k2_pre_topc(sK2,sK3),sK3)
    | sK3 != k2_pre_topc(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_3747])).

cnf(c_6559,plain,
    ( sK3 != k2_pre_topc(sK2,sK3)
    | r1_tarski(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK3)) != iProver_top
    | r1_tarski(k2_pre_topc(sK2,sK3),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6557])).

cnf(c_4089,plain,
    ( r2_hidden(sK0(X0,k2_pre_topc(sK2,sK3)),X0)
    | r1_tarski(X0,k2_pre_topc(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_8013,plain,
    ( r2_hidden(sK0(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK3)),k2_pre_topc(sK2,sK3))
    | r1_tarski(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_4089])).

cnf(c_8015,plain,
    ( r2_hidden(sK0(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK3)),k2_pre_topc(sK2,sK3)) = iProver_top
    | r1_tarski(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8013])).

cnf(c_3,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_4090,plain,
    ( ~ r2_hidden(sK0(X0,k2_pre_topc(sK2,sK3)),k2_pre_topc(sK2,sK3))
    | r1_tarski(X0,k2_pre_topc(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_8014,plain,
    ( ~ r2_hidden(sK0(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK3)),k2_pre_topc(sK2,sK3))
    | r1_tarski(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_4090])).

cnf(c_8017,plain,
    ( r2_hidden(sK0(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK3)),k2_pre_topc(sK2,sK3)) != iProver_top
    | r1_tarski(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8014])).

cnf(c_8380,plain,
    ( v4_pre_topc(sK3,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7436,c_36,c_48,c_3709,c_3907,c_4176,c_5543,c_5616,c_6559,c_8015,c_8017])).

cnf(c_11774,plain,
    ( v3_yellow_6(sK1(sK2,sK3,X0),sK2) != iProver_top
    | r2_hidden(X0,k2_pre_topc(sK2,sK3)) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7917,c_36,c_48,c_3709,c_3907,c_4176,c_5338,c_5543,c_5616,c_6559,c_8015,c_8017])).

cnf(c_11783,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(X0,k2_pre_topc(sK2,sK3)) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4758,c_11774])).

cnf(c_11917,plain,
    ( r2_hidden(X0,k2_pre_topc(sK2,sK3)) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11783,c_36])).

cnf(c_11925,plain,
    ( r2_hidden(sK0(k2_pre_topc(sK2,sK3),X0),sK3) = iProver_top
    | r1_tarski(k2_pre_topc(sK2,sK3),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3414,c_11917])).

cnf(c_3415,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_11961,plain,
    ( r1_tarski(k2_pre_topc(sK2,sK3),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_11925,c_3415])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_3698,plain,
    ( ~ r1_tarski(k2_pre_topc(sK2,sK3),sK3)
    | ~ r1_tarski(sK3,k2_pre_topc(sK2,sK3))
    | k2_pre_topc(sK2,sK3) = sK3 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_3699,plain,
    ( k2_pre_topc(sK2,sK3) = sK3
    | r1_tarski(k2_pre_topc(sK2,sK3),sK3) != iProver_top
    | r1_tarski(sK3,k2_pre_topc(sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3698])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_957,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_30])).

cnf(c_958,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(X0,k2_pre_topc(sK2,X0)) ),
    inference(unflattening,[status(thm)],[c_957])).

cnf(c_3655,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(sK3,k2_pre_topc(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_958])).

cnf(c_3656,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(sK3,k2_pre_topc(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3655])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11961,c_8380,c_3699,c_3659,c_3656,c_36])).


%------------------------------------------------------------------------------
