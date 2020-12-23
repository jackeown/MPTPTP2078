%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT2030+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:03 EST 2020

% Result     : Theorem 1.21s
% Output     : CNFRefutation 1.21s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 336 expanded)
%              Number of clauses        :   47 (  63 expanded)
%              Number of leaves         :   13 ( 115 expanded)
%              Depth                    :   24
%              Number of atoms          :  668 (3017 expanded)
%              Number of equality atoms :   25 (  25 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal clause size      :   24 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f45,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
             => r2_waybel_0(X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
              | ~ r1_waybel_0(X0,X1,X2) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
              | ~ r1_waybel_0(X0,X1,X2) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_0(X0,X1,X2)
      | ~ r1_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f6,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
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
    inference(negated_conjecture,[],[f6])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r3_waybel_9(X0,X1,X2)
              & r2_hidden(X2,k10_yellow_6(X0,X1))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r3_waybel_9(X0,X1,X2)
              & r2_hidden(X2,k10_yellow_6(X0,X1))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r3_waybel_9(X0,X1,X2)
          & r2_hidden(X2,k10_yellow_6(X0,X1))
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ~ r3_waybel_9(X0,X1,sK6)
        & r2_hidden(sK6,k10_yellow_6(X0,X1))
        & m1_subset_1(sK6,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r3_waybel_9(X0,X1,X2)
              & r2_hidden(X2,k10_yellow_6(X0,X1))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ~ r3_waybel_9(X0,sK5,X2)
            & r2_hidden(X2,k10_yellow_6(X0,sK5))
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & l1_waybel_0(sK5,X0)
        & v7_waybel_0(sK5)
        & v4_orders_2(sK5)
        & ~ v2_struct_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r3_waybel_9(X0,X1,X2)
                & r2_hidden(X2,k10_yellow_6(X0,X1))
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r3_waybel_9(sK4,X1,X2)
              & r2_hidden(X2,k10_yellow_6(sK4,X1))
              & m1_subset_1(X2,u1_struct_0(sK4)) )
          & l1_waybel_0(X1,sK4)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK4)
      & v2_pre_topc(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ~ r3_waybel_9(sK4,sK5,sK6)
    & r2_hidden(sK6,k10_yellow_6(sK4,sK5))
    & m1_subset_1(sK6,u1_struct_0(sK4))
    & l1_waybel_0(sK5,sK4)
    & v7_waybel_0(sK5)
    & v4_orders_2(sK5)
    & ~ v2_struct_0(sK5)
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f18,f32,f31,f30])).

fof(f52,plain,(
    v7_waybel_0(sK5) ),
    inference(cnf_transformation,[],[f33])).

fof(f50,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f33])).

fof(f51,plain,(
    v4_orders_2(sK5) ),
    inference(cnf_transformation,[],[f33])).

fof(f49,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f47,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f53,plain,(
    l1_waybel_0(sK5,sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f55,plain,(
    r2_hidden(sK6,k10_yellow_6(sK4,sK5)) ),
    inference(cnf_transformation,[],[f33])).

fof(f1,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f9,plain,(
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
    inference(flattening,[],[f8])).

fof(f19,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f21,plain,(
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
    inference(rectify,[],[f20])).

fof(f24,plain,(
    ! [X6,X1,X0] :
      ( ? [X7] :
          ( ~ r1_waybel_0(X0,X1,X7)
          & m1_connsp_2(X7,X0,X6) )
     => ( ~ r1_waybel_0(X0,X1,sK2(X0,X1,X6))
        & m1_connsp_2(sK2(X0,X1,X6),X0,X6) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_waybel_0(X0,X1,X4)
          & m1_connsp_2(X4,X0,X3) )
     => ( ~ r1_waybel_0(X0,X1,sK1(X0,X1,X2))
        & m1_connsp_2(sK1(X0,X1,X2),X0,X3) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
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
              & m1_connsp_2(X4,X0,sK0(X0,X1,X2)) )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ! [X5] :
              ( r1_waybel_0(X0,X1,X5)
              | ~ m1_connsp_2(X5,X0,sK0(X0,X1,X2)) )
          | r2_hidden(sK0(X0,X1,X2),X2) )
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k10_yellow_6(X0,X1) = X2
                  | ( ( ( ~ r1_waybel_0(X0,X1,sK1(X0,X1,X2))
                        & m1_connsp_2(sK1(X0,X1,X2),X0,sK0(X0,X1,X2)) )
                      | ~ r2_hidden(sK0(X0,X1,X2),X2) )
                    & ( ! [X5] :
                          ( r1_waybel_0(X0,X1,X5)
                          | ~ m1_connsp_2(X5,X0,sK0(X0,X1,X2)) )
                      | r2_hidden(sK0(X0,X1,X2),X2) )
                    & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) )
                & ( ! [X6] :
                      ( ( ( r2_hidden(X6,X2)
                          | ( ~ r1_waybel_0(X0,X1,sK2(X0,X1,X6))
                            & m1_connsp_2(sK2(X0,X1,X6),X0,X6) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f24,f23,f22])).

fof(f34,plain,(
    ! [X6,X2,X0,X8,X1] :
      ( r1_waybel_0(X0,X1,X8)
      | ~ m1_connsp_2(X8,X0,X6)
      | ~ r2_hidden(X6,X2)
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
    inference(cnf_transformation,[],[f25])).

fof(f59,plain,(
    ! [X6,X0,X8,X1] :
      ( r1_waybel_0(X0,X1,X8)
      | ~ m1_connsp_2(X8,X0,X6)
      | ~ r2_hidden(X6,k10_yellow_6(X0,X1))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f34])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f48,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f54,plain,(
    m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f33])).

fof(f2,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_waybel_0(X0,X1,X3)
          & m1_connsp_2(X3,X0,X2) )
     => ( ~ r2_waybel_0(X0,X1,sK3(X0,X1,X2))
        & m1_connsp_2(sK3(X0,X1,X2),X0,X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_waybel_9(X0,X1,X2)
                  | ( ~ r2_waybel_0(X0,X1,sK3(X0,X1,X2))
                    & m1_connsp_2(sK3(X0,X1,X2),X0,X2) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f28])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r3_waybel_9(X0,X1,X2)
      | ~ r2_waybel_0(X0,X1,sK3(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f56,plain,(
    ~ r3_waybel_9(sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f33])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r3_waybel_9(X0,X1,X2)
      | m1_connsp_2(sK3(X0,X1,X2),X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_11,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_12,plain,
    ( r2_waybel_0(X0,X1,X2)
    | ~ r1_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_252,plain,
    ( r2_waybel_0(X0,X1,X2)
    | ~ r1_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(resolution,[status(thm)],[c_11,c_12])).

cnf(c_17,negated_conjecture,
    ( v7_waybel_0(sK5) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_492,plain,
    ( r2_waybel_0(X0,X1,X2)
    | ~ r1_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_252,c_17])).

cnf(c_493,plain,
    ( r2_waybel_0(X0,sK5,X1)
    | ~ r1_waybel_0(X0,sK5,X1)
    | ~ l1_waybel_0(sK5,X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK5)
    | ~ v4_orders_2(sK5) ),
    inference(unflattening,[status(thm)],[c_492])).

cnf(c_19,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_18,negated_conjecture,
    ( v4_orders_2(sK5) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_497,plain,
    ( r2_waybel_0(X0,sK5,X1)
    | ~ r1_waybel_0(X0,sK5,X1)
    | ~ l1_waybel_0(sK5,X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_493,c_19,c_18])).

cnf(c_20,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1165,plain,
    ( r2_waybel_0(X0,sK5,X1)
    | ~ r1_waybel_0(X0,sK5,X1)
    | ~ l1_waybel_0(sK5,X0)
    | v2_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_497,c_20])).

cnf(c_1166,plain,
    ( r2_waybel_0(sK4,sK5,X0)
    | ~ r1_waybel_0(sK4,sK5,X0)
    | ~ l1_waybel_0(sK5,sK4)
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_1165])).

cnf(c_22,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_16,negated_conjecture,
    ( l1_waybel_0(sK5,sK4) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1170,plain,
    ( r2_waybel_0(sK4,sK5,X0)
    | ~ r1_waybel_0(sK4,sK5,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1166,c_22,c_16])).

cnf(c_1642,plain,
    ( r2_waybel_0(sK4,sK5,X0_51)
    | ~ r1_waybel_0(sK4,sK5,X0_51) ),
    inference(subtyping,[status(esa)],[c_1170])).

cnf(c_2080,plain,
    ( r2_waybel_0(sK4,sK5,sK3(sK4,sK5,sK6))
    | ~ r1_waybel_0(sK4,sK5,sK3(sK4,sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_1642])).

cnf(c_14,negated_conjecture,
    ( r2_hidden(sK6,k10_yellow_6(sK4,sK5)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_6,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r1_waybel_0(X1,X3,X0)
    | ~ l1_waybel_0(X3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(k10_yellow_6(X1,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k10_yellow_6(X1,X3))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_770,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r1_waybel_0(X1,X3,X0)
    | ~ l1_waybel_0(X3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(k10_yellow_6(X1,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k10_yellow_6(X1,X3))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ v4_orders_2(X3)
    | sK5 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_17])).

cnf(c_771,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r1_waybel_0(X1,sK5,X0)
    | ~ l1_waybel_0(sK5,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(k10_yellow_6(X1,sK5),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k10_yellow_6(X1,sK5))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(sK5)
    | ~ v4_orders_2(sK5) ),
    inference(unflattening,[status(thm)],[c_770])).

cnf(c_775,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r1_waybel_0(X1,sK5,X0)
    | ~ l1_waybel_0(sK5,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(k10_yellow_6(X1,sK5),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k10_yellow_6(X1,sK5))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_771,c_19,c_18])).

cnf(c_10,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(k10_yellow_6(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_702,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(k10_yellow_6(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_17])).

cnf(c_703,plain,
    ( ~ l1_waybel_0(sK5,X0)
    | m1_subset_1(k10_yellow_6(X0,sK5),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK5)
    | ~ v4_orders_2(sK5) ),
    inference(unflattening,[status(thm)],[c_702])).

cnf(c_707,plain,
    ( ~ l1_waybel_0(sK5,X0)
    | m1_subset_1(k10_yellow_6(X0,sK5),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_703,c_19,c_18])).

cnf(c_790,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r1_waybel_0(X1,sK5,X0)
    | ~ l1_waybel_0(sK5,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,k10_yellow_6(X1,sK5))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_775,c_707])).

cnf(c_21,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1065,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r1_waybel_0(X1,sK5,X0)
    | ~ l1_waybel_0(sK5,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,k10_yellow_6(X1,sK5))
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_790,c_21])).

cnf(c_1066,plain,
    ( ~ m1_connsp_2(X0,sK4,X1)
    | r1_waybel_0(sK4,sK5,X0)
    | ~ l1_waybel_0(sK5,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ r2_hidden(X1,k10_yellow_6(sK4,sK5))
    | ~ l1_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_1065])).

cnf(c_1070,plain,
    ( r1_waybel_0(sK4,sK5,X0)
    | ~ m1_connsp_2(X0,sK4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ r2_hidden(X1,k10_yellow_6(sK4,sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1066,c_22,c_20,c_16])).

cnf(c_1071,plain,
    ( ~ m1_connsp_2(X0,sK4,X1)
    | r1_waybel_0(sK4,sK5,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ r2_hidden(X1,k10_yellow_6(sK4,sK5)) ),
    inference(renaming,[status(thm)],[c_1070])).

cnf(c_1406,plain,
    ( ~ m1_connsp_2(X0,sK4,X1)
    | r1_waybel_0(sK4,sK5,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | k10_yellow_6(sK4,sK5) != k10_yellow_6(sK4,sK5)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_1071])).

cnf(c_1407,plain,
    ( ~ m1_connsp_2(X0,sK4,sK6)
    | r1_waybel_0(sK4,sK5,X0)
    | ~ m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_1406])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1411,plain,
    ( r1_waybel_0(sK4,sK5,X0)
    | ~ m1_connsp_2(X0,sK4,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1407,c_15])).

cnf(c_1412,plain,
    ( ~ m1_connsp_2(X0,sK4,sK6)
    | r1_waybel_0(sK4,sK5,X0) ),
    inference(renaming,[status(thm)],[c_1411])).

cnf(c_1639,plain,
    ( ~ m1_connsp_2(X0_51,sK4,sK6)
    | r1_waybel_0(sK4,sK5,X0_51) ),
    inference(subtyping,[status(esa)],[c_1412])).

cnf(c_2030,plain,
    ( ~ m1_connsp_2(sK3(sK4,sK5,sK6),sK4,sK6)
    | r1_waybel_0(sK4,sK5,sK3(sK4,sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_1639])).

cnf(c_7,plain,
    ( ~ r2_waybel_0(X0,X1,sK3(X0,X1,X2))
    | r3_waybel_9(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_13,negated_conjecture,
    ( ~ r3_waybel_9(sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_457,plain,
    ( ~ r2_waybel_0(X0,X1,sK3(X0,X1,X2))
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK6 != X2
    | sK5 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_13])).

cnf(c_458,plain,
    ( ~ r2_waybel_0(sK4,sK5,sK3(sK4,sK5,sK6))
    | ~ l1_waybel_0(sK5,sK4)
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_457])).

cnf(c_8,plain,
    ( r3_waybel_9(X0,X1,X2)
    | m1_connsp_2(sK3(X0,X1,X2),X0,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_446,plain,
    ( m1_connsp_2(sK3(X0,X1,X2),X0,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK6 != X2
    | sK5 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_13])).

cnf(c_447,plain,
    ( m1_connsp_2(sK3(sK4,sK5,sK6),sK4,sK6)
    | ~ l1_waybel_0(sK5,sK4)
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_446])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2080,c_2030,c_458,c_447,c_15,c_16,c_19,c_20,c_21,c_22])).


%------------------------------------------------------------------------------
