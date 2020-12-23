%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT2054+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:05 EST 2020

% Result     : Theorem 3.03s
% Output     : CNFRefutation 3.03s
% Verified   : 
% Statistics : Number of formulae       :  258 (2177 expanded)
%              Number of clauses        :  164 ( 440 expanded)
%              Number of leaves         :   21 ( 603 expanded)
%              Depth                    :   33
%              Number of atoms          : 1474 (20883 expanded)
%              Number of equality atoms :  178 ( 290 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal clause size      :   24 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
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
              <=> r2_waybel_7(X0,k2_yellow19(X0,X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
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
                <=> r2_waybel_7(X0,k2_yellow19(X0,X1),X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k10_yellow_6(X0,X1))
              <~> r2_waybel_7(X0,k2_yellow19(X0,X1),X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k10_yellow_6(X0,X1))
              <~> r2_waybel_7(X0,k2_yellow19(X0,X1),X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f56,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
                | ~ r2_hidden(X2,k10_yellow_6(X0,X1)) )
              & ( r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
                | r2_hidden(X2,k10_yellow_6(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f57,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
                | ~ r2_hidden(X2,k10_yellow_6(X0,X1)) )
              & ( r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
                | r2_hidden(X2,k10_yellow_6(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f56])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
            | ~ r2_hidden(X2,k10_yellow_6(X0,X1)) )
          & ( r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
            | r2_hidden(X2,k10_yellow_6(X0,X1)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( ~ r2_waybel_7(X0,k2_yellow19(X0,X1),sK6)
          | ~ r2_hidden(sK6,k10_yellow_6(X0,X1)) )
        & ( r2_waybel_7(X0,k2_yellow19(X0,X1),sK6)
          | r2_hidden(sK6,k10_yellow_6(X0,X1)) )
        & m1_subset_1(sK6,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
                | ~ r2_hidden(X2,k10_yellow_6(X0,X1)) )
              & ( r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
                | r2_hidden(X2,k10_yellow_6(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ( ~ r2_waybel_7(X0,k2_yellow19(X0,sK5),X2)
              | ~ r2_hidden(X2,k10_yellow_6(X0,sK5)) )
            & ( r2_waybel_7(X0,k2_yellow19(X0,sK5),X2)
              | r2_hidden(X2,k10_yellow_6(X0,sK5)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & l1_waybel_0(sK5,X0)
        & v7_waybel_0(sK5)
        & v4_orders_2(sK5)
        & ~ v2_struct_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
                  | ~ r2_hidden(X2,k10_yellow_6(X0,X1)) )
                & ( r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
                  | r2_hidden(X2,k10_yellow_6(X0,X1)) )
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
              ( ( ~ r2_waybel_7(sK4,k2_yellow19(sK4,X1),X2)
                | ~ r2_hidden(X2,k10_yellow_6(sK4,X1)) )
              & ( r2_waybel_7(sK4,k2_yellow19(sK4,X1),X2)
                | r2_hidden(X2,k10_yellow_6(sK4,X1)) )
              & m1_subset_1(X2,u1_struct_0(sK4)) )
          & l1_waybel_0(X1,sK4)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK4)
      & v2_pre_topc(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,
    ( ( ~ r2_waybel_7(sK4,k2_yellow19(sK4,sK5),sK6)
      | ~ r2_hidden(sK6,k10_yellow_6(sK4,sK5)) )
    & ( r2_waybel_7(sK4,k2_yellow19(sK4,sK5),sK6)
      | r2_hidden(sK6,k10_yellow_6(sK4,sK5)) )
    & m1_subset_1(sK6,u1_struct_0(sK4))
    & l1_waybel_0(sK5,sK4)
    & v7_waybel_0(sK5)
    & v4_orders_2(sK5)
    & ~ v2_struct_0(sK5)
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f57,f60,f59,f58])).

fof(f95,plain,(
    l1_waybel_0(sK5,sK4) ),
    inference(cnf_transformation,[],[f61])).

fof(f4,axiom,(
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

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f76,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f94,plain,(
    v7_waybel_0(sK5) ),
    inference(cnf_transformation,[],[f61])).

fof(f92,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f61])).

fof(f93,plain,(
    v4_orders_2(sK5) ),
    inference(cnf_transformation,[],[f61])).

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

fof(f16,plain,(
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

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f44,plain,(
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
    inference(rectify,[],[f43])).

fof(f47,plain,(
    ! [X6,X1,X0] :
      ( ? [X7] :
          ( ~ r1_waybel_0(X0,X1,X7)
          & m1_connsp_2(X7,X0,X6) )
     => ( ~ r1_waybel_0(X0,X1,sK2(X0,X1,X6))
        & m1_connsp_2(sK2(X0,X1,X6),X0,X6) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_waybel_0(X0,X1,X4)
          & m1_connsp_2(X4,X0,X3) )
     => ( ~ r1_waybel_0(X0,X1,sK1(X0,X1,X2))
        & m1_connsp_2(sK1(X0,X1,X2),X0,X3) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
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

fof(f48,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f44,f47,f46,f45])).

fof(f63,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,X2)
      | m1_connsp_2(sK2(X0,X1,X6),X0,X6)
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
    inference(cnf_transformation,[],[f48])).

fof(f100,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(X6,k10_yellow_6(X0,X1))
      | m1_connsp_2(sK2(X0,X1,X6),X0,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f63])).

fof(f89,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f61])).

fof(f90,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f61])).

fof(f91,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f61])).

fof(f97,plain,
    ( r2_waybel_7(sK4,k2_yellow19(sK4,sK5),sK6)
    | r2_hidden(sK6,k10_yellow_6(sK4,sK5)) ),
    inference(cnf_transformation,[],[f61])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ~ r2_hidden(X1,k1_tops_1(X0,X2)) )
                & ( r2_hidden(X1,k1_tops_1(X0,X2))
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f77,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f12,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X1,X0,X2)
      | ~ r2_hidden(X2,X1)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f34])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1,X2] :
          ( r2_waybel_7(X0,X1,X2)
        <=> ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r2_hidden(X2,X3)
                  & v3_pre_topc(X3,X0) )
               => r2_hidden(X3,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_waybel_7(X0,X1,X2)
        <=> ! [X3] :
              ( r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X3)
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_waybel_7(X0,X1,X2)
        <=> ! [X3] :
              ( r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X3)
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_waybel_7(X0,X1,X2)
            | ? [X3] :
                ( ~ r2_hidden(X3,X1)
                & r2_hidden(X2,X3)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & ( ! [X3] :
                ( r2_hidden(X3,X1)
                | ~ r2_hidden(X2,X3)
                | ~ v3_pre_topc(X3,X0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r2_waybel_7(X0,X1,X2) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_waybel_7(X0,X1,X2)
            | ? [X3] :
                ( ~ r2_hidden(X3,X1)
                & r2_hidden(X2,X3)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & ( ! [X4] :
                ( r2_hidden(X4,X1)
                | ~ r2_hidden(X2,X4)
                | ~ v3_pre_topc(X4,X0)
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r2_waybel_7(X0,X1,X2) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f50])).

fof(f52,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & r2_hidden(X2,X3)
          & v3_pre_topc(X3,X0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r2_hidden(sK3(X0,X1,X2),X1)
        & r2_hidden(X2,sK3(X0,X1,X2))
        & v3_pre_topc(sK3(X0,X1,X2),X0)
        & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_waybel_7(X0,X1,X2)
            | ( ~ r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(X2,sK3(X0,X1,X2))
              & v3_pre_topc(sK3(X0,X1,X2),X0)
              & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
          & ( ! [X4] :
                ( r2_hidden(X4,X1)
                | ~ r2_hidden(X2,X4)
                | ~ v3_pre_topc(X4,X0)
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r2_waybel_7(X0,X1,X2) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f51,f52])).

fof(f71,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X2,X4)
      | ~ v3_pre_topc(X4,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_waybel_7(X0,X1,X2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f96,plain,(
    m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f61])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_7(X0,X1,X2)
      | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f98,plain,
    ( ~ r2_waybel_7(sK4,k2_yellow19(sK4,sK5),sK6)
    | ~ r2_hidden(sK6,k10_yellow_6(sK4,sK5)) ),
    inference(cnf_transformation,[],[f61])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_7(X0,X1,X2)
      | v3_pre_topc(sK3(X0,X1,X2),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_7(X0,X1,X2)
      | r2_hidden(X2,sK3(X0,X1,X2))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_7(X0,X1,X2)
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f78,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r2_hidden(X2,k2_yellow19(X0,X1))
            <=> ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & r1_waybel_0(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k2_yellow19(X0,X1))
            <=> ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k2_yellow19(X0,X1))
            <=> ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_yellow19(X0,X1))
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                | ~ r1_waybel_0(X0,X1,X2) )
              & ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  & r1_waybel_0(X0,X1,X2) )
                | ~ r2_hidden(X2,k2_yellow19(X0,X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_yellow19(X0,X1))
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                | ~ r1_waybel_0(X0,X1,X2) )
              & ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  & r1_waybel_0(X0,X1,X2) )
                | ~ r2_hidden(X2,k2_yellow19(X0,X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f54])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k2_yellow19(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f62,plain,(
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
    inference(cnf_transformation,[],[f48])).

fof(f101,plain,(
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
    inference(equality_resolution,[],[f62])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( r1_waybel_0(X0,X1,X2)
      | ~ r2_hidden(X2,k2_yellow19(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2,X3] :
              ( r1_tarski(X2,X3)
             => ( ( r2_waybel_0(X0,X1,X2)
                 => r2_waybel_0(X0,X1,X3) )
                & ( r1_waybel_0(X0,X1,X2)
                 => r1_waybel_0(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ( ( r2_waybel_0(X0,X1,X3)
                  | ~ r2_waybel_0(X0,X1,X2) )
                & ( r1_waybel_0(X0,X1,X3)
                  | ~ r1_waybel_0(X0,X1,X2) ) )
              | ~ r1_tarski(X2,X3) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ( ( r2_waybel_0(X0,X1,X3)
                  | ~ r2_waybel_0(X0,X1,X2) )
                & ( r1_waybel_0(X0,X1,X3)
                  | ~ r1_waybel_0(X0,X1,X2) ) )
              | ~ r1_tarski(X2,X3) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_waybel_0(X0,X1,X3)
      | ~ r1_waybel_0(X0,X1,X2)
      | ~ r1_tarski(X2,X3)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f64,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,X2)
      | ~ r1_waybel_0(X0,X1,sK2(X0,X1,X6))
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
    inference(cnf_transformation,[],[f48])).

fof(f99,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(X6,k10_yellow_6(X0,X1))
      | ~ r1_waybel_0(X0,X1,sK2(X0,X1,X6))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f64])).

cnf(c_30,negated_conjecture,
    ( l1_waybel_0(sK5,sK4) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_14,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(k10_yellow_6(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_31,negated_conjecture,
    ( v7_waybel_0(sK5) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1258,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(k10_yellow_6(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_31])).

cnf(c_1259,plain,
    ( ~ l1_waybel_0(sK5,X0)
    | m1_subset_1(k10_yellow_6(X0,sK5),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK5)
    | ~ v4_orders_2(sK5) ),
    inference(unflattening,[status(thm)],[c_1258])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_32,negated_conjecture,
    ( v4_orders_2(sK5) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1263,plain,
    ( ~ l1_waybel_0(sK5,X0)
    | m1_subset_1(k10_yellow_6(X0,sK5),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1259,c_33,c_32])).

cnf(c_5,plain,
    ( m1_connsp_2(sK2(X0,X1,X2),X0,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | r2_hidden(X2,k10_yellow_6(X0,X1))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1075,plain,
    ( m1_connsp_2(sK2(X0,X1,X2),X0,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | r2_hidden(X2,k10_yellow_6(X0,X1))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_31])).

cnf(c_1076,plain,
    ( m1_connsp_2(sK2(X0,sK5,X1),X0,X1)
    | ~ l1_waybel_0(sK5,X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k10_yellow_6(X0,sK5),k1_zfmisc_1(u1_struct_0(X0)))
    | r2_hidden(X1,k10_yellow_6(X0,sK5))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK5)
    | ~ v4_orders_2(sK5) ),
    inference(unflattening,[status(thm)],[c_1075])).

cnf(c_1080,plain,
    ( m1_connsp_2(sK2(X0,sK5,X1),X0,X1)
    | ~ l1_waybel_0(sK5,X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k10_yellow_6(X0,sK5),k1_zfmisc_1(u1_struct_0(X0)))
    | r2_hidden(X1,k10_yellow_6(X0,sK5))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1076,c_33,c_32])).

cnf(c_1281,plain,
    ( m1_connsp_2(sK2(X0,sK5,X1),X0,X1)
    | ~ l1_waybel_0(sK5,X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r2_hidden(X1,k10_yellow_6(X0,sK5))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1263,c_1080])).

cnf(c_1549,plain,
    ( m1_connsp_2(sK2(X0,sK5,X1),X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r2_hidden(X1,k10_yellow_6(X0,sK5))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | sK5 != sK5
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_1281])).

cnf(c_1550,plain,
    ( m1_connsp_2(sK2(sK4,sK5,X0),sK4,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r2_hidden(X0,k10_yellow_6(sK4,sK5))
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_1549])).

cnf(c_36,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_35,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_34,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1554,plain,
    ( r2_hidden(X0,k10_yellow_6(sK4,sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_connsp_2(sK2(sK4,sK5,X0),sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1550,c_36,c_35,c_34])).

cnf(c_1555,plain,
    ( m1_connsp_2(sK2(sK4,sK5,X0),sK4,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r2_hidden(X0,k10_yellow_6(sK4,sK5)) ),
    inference(renaming,[status(thm)],[c_1554])).

cnf(c_4139,plain,
    ( m1_connsp_2(sK2(sK4,sK5,X0),sK4,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,k10_yellow_6(sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1555])).

cnf(c_28,negated_conjecture,
    ( r2_waybel_7(sK4,k2_yellow19(sK4,sK5),sK6)
    | r2_hidden(sK6,k10_yellow_6(sK4,sK5)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_4146,plain,
    ( r2_waybel_7(sK4,k2_yellow19(sK4,sK5),sK6) = iProver_top
    | r2_hidden(sK6,k10_yellow_6(sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_8,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_17,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_225,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8,c_17])).

cnf(c_1865,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_225,c_35])).

cnf(c_1866,plain,
    ( ~ m1_connsp_2(X0,sK4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | r2_hidden(X1,k1_tops_1(sK4,X0))
    | ~ l1_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_1865])).

cnf(c_1870,plain,
    ( ~ m1_connsp_2(X0,sK4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | r2_hidden(X1,k1_tops_1(sK4,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1866,c_36,c_34])).

cnf(c_4127,plain,
    ( m1_connsp_2(X0,sK4,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X1,k1_tops_1(sK4,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1870])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2014,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_34])).

cnf(c_2015,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(k1_tops_1(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(unflattening,[status(thm)],[c_2014])).

cnf(c_4122,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(k1_tops_1(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2015])).

cnf(c_24,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1886,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,X0)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_35])).

cnf(c_1887,plain,
    ( m1_connsp_2(X0,sK4,X1)
    | ~ v3_pre_topc(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ r2_hidden(X1,X0)
    | ~ l1_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_1886])).

cnf(c_1891,plain,
    ( m1_connsp_2(X0,sK4,X1)
    | ~ v3_pre_topc(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ r2_hidden(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1887,c_36,c_34])).

cnf(c_23,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1907,plain,
    ( m1_connsp_2(X0,sK4,X1)
    | ~ v3_pre_topc(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X1,X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1891,c_23])).

cnf(c_4126,plain,
    ( m1_connsp_2(X0,sK4,X1) = iProver_top
    | v3_pre_topc(X0,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1907])).

cnf(c_4820,plain,
    ( m1_connsp_2(k1_tops_1(sK4,X0),sK4,X1) = iProver_top
    | v3_pre_topc(k1_tops_1(sK4,X0),sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(X1,k1_tops_1(sK4,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4122,c_4126])).

cnf(c_2016,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(k1_tops_1(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2015])).

cnf(c_18,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1752,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_35])).

cnf(c_1753,plain,
    ( v3_pre_topc(k1_tops_1(sK4,X0),sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_1752])).

cnf(c_1757,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | v3_pre_topc(k1_tops_1(sK4,X0),sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1753,c_34])).

cnf(c_1758,plain,
    ( v3_pre_topc(k1_tops_1(sK4,X0),sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(renaming,[status(thm)],[c_1757])).

cnf(c_2033,plain,
    ( m1_connsp_2(X0,sK4,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X1,X0)
    | k1_tops_1(sK4,X2) != X0
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_1907,c_1758])).

cnf(c_2034,plain,
    ( m1_connsp_2(k1_tops_1(sK4,X0),sK4,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(k1_tops_1(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X1,k1_tops_1(sK4,X0)) ),
    inference(unflattening,[status(thm)],[c_2033])).

cnf(c_2035,plain,
    ( m1_connsp_2(k1_tops_1(sK4,X0),sK4,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(k1_tops_1(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(X1,k1_tops_1(sK4,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2034])).

cnf(c_4915,plain,
    ( m1_connsp_2(k1_tops_1(sK4,X0),sK4,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(X1,k1_tops_1(sK4,X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4820,c_2016,c_2035])).

cnf(c_13,plain,
    ( ~ r2_waybel_7(X0,X1,X2)
    | ~ v3_pre_topc(X3,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X2,X3)
    | r2_hidden(X3,X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1770,plain,
    ( ~ r2_waybel_7(X0,X1,X2)
    | ~ v3_pre_topc(X3,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X2,X3)
    | r2_hidden(X3,X1)
    | ~ l1_pre_topc(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_35])).

cnf(c_1771,plain,
    ( ~ r2_waybel_7(sK4,X0,X1)
    | ~ v3_pre_topc(X2,sK4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X1,X2)
    | r2_hidden(X2,X0)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_1770])).

cnf(c_1773,plain,
    ( r2_hidden(X2,X0)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v3_pre_topc(X2,sK4)
    | ~ r2_waybel_7(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1771,c_34])).

cnf(c_1774,plain,
    ( ~ r2_waybel_7(sK4,X0,X1)
    | ~ v3_pre_topc(X2,sK4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X1,X2)
    | r2_hidden(X2,X0) ),
    inference(renaming,[status(thm)],[c_1773])).

cnf(c_4132,plain,
    ( r2_waybel_7(sK4,X0,X1) != iProver_top
    | v3_pre_topc(X2,sK4) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(X1,X2) != iProver_top
    | r2_hidden(X2,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1774])).

cnf(c_4922,plain,
    ( r2_waybel_7(sK4,X0,X1) != iProver_top
    | v3_pre_topc(k1_tops_1(sK4,X2),sK4) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(X1,k1_tops_1(sK4,X2)) != iProver_top
    | r2_hidden(k1_tops_1(sK4,X2),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4122,c_4132])).

cnf(c_2075,plain,
    ( ~ r2_waybel_7(sK4,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X1,X3)
    | r2_hidden(X3,X0)
    | k1_tops_1(sK4,X2) != X3
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_1758,c_1774])).

cnf(c_2076,plain,
    ( ~ r2_waybel_7(sK4,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(k1_tops_1(sK4,X2),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X1,k1_tops_1(sK4,X2))
    | r2_hidden(k1_tops_1(sK4,X2),X0) ),
    inference(unflattening,[status(thm)],[c_2075])).

cnf(c_2090,plain,
    ( ~ r2_waybel_7(sK4,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X1,k1_tops_1(sK4,X2))
    | r2_hidden(k1_tops_1(sK4,X2),X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2076,c_2015])).

cnf(c_2095,plain,
    ( r2_waybel_7(sK4,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(X1,k1_tops_1(sK4,X2)) != iProver_top
    | r2_hidden(k1_tops_1(sK4,X2),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2090])).

cnf(c_5580,plain,
    ( r2_waybel_7(sK4,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(X1,k1_tops_1(sK4,X2)) != iProver_top
    | r2_hidden(k1_tops_1(sK4,X2),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4922,c_2095])).

cnf(c_5586,plain,
    ( r2_waybel_7(sK4,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(X1,k1_tops_1(sK4,k1_tops_1(sK4,X2))) != iProver_top
    | r2_hidden(k1_tops_1(sK4,k1_tops_1(sK4,X2)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4122,c_5580])).

cnf(c_5595,plain,
    ( r2_waybel_7(sK4,X0,X1) != iProver_top
    | m1_connsp_2(k1_tops_1(sK4,X2),sK4,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(k1_tops_1(sK4,k1_tops_1(sK4,X2)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4127,c_5586])).

cnf(c_5785,plain,
    ( r2_waybel_7(sK4,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X1,k1_tops_1(sK4,X2)) != iProver_top
    | r2_hidden(k1_tops_1(sK4,k1_tops_1(sK4,X2)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4915,c_5595])).

cnf(c_8161,plain,
    ( r2_waybel_7(sK4,X0,X1) != iProver_top
    | m1_connsp_2(X2,sK4,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(k1_tops_1(sK4,k1_tops_1(sK4,X2)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4127,c_5785])).

cnf(c_8226,plain,
    ( m1_connsp_2(X0,sK4,sK6) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(k1_tops_1(sK4,k1_tops_1(sK4,X0)),k2_yellow19(sK4,sK5)) = iProver_top
    | r2_hidden(sK6,k10_yellow_6(sK4,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4146,c_8161])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_44,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_12,plain,
    ( r2_waybel_7(X0,X1,X2)
    | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_27,negated_conjecture,
    ( ~ r2_waybel_7(sK4,k2_yellow19(sK4,sK5),sK6)
    | ~ r2_hidden(sK6,k10_yellow_6(sK4,sK5)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_279,plain,
    ( ~ r2_hidden(sK6,k10_yellow_6(sK4,sK5))
    | ~ r2_waybel_7(sK4,k2_yellow19(sK4,sK5),sK6) ),
    inference(prop_impl,[status(thm)],[c_27])).

cnf(c_280,plain,
    ( ~ r2_waybel_7(sK4,k2_yellow19(sK4,sK5),sK6)
    | ~ r2_hidden(sK6,k10_yellow_6(sK4,sK5)) ),
    inference(renaming,[status(thm)],[c_279])).

cnf(c_951,plain,
    ( m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(sK6,k10_yellow_6(sK4,sK5))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k2_yellow19(sK4,sK5) != X1
    | sK6 != X2
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_280])).

cnf(c_952,plain,
    ( m1_subset_1(sK3(sK4,k2_yellow19(sK4,sK5),sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK6,k10_yellow_6(sK4,sK5))
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_951])).

cnf(c_954,plain,
    ( m1_subset_1(sK3(sK4,k2_yellow19(sK4,sK5),sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK6,k10_yellow_6(sK4,sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_952,c_35,c_34])).

cnf(c_956,plain,
    ( m1_subset_1(sK3(sK4,k2_yellow19(sK4,sK5),sK6),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | r2_hidden(sK6,k10_yellow_6(sK4,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_954])).

cnf(c_11,plain,
    ( r2_waybel_7(X0,X1,X2)
    | v3_pre_topc(sK3(X0,X1,X2),X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_965,plain,
    ( v3_pre_topc(sK3(X0,X1,X2),X0)
    | ~ r2_hidden(sK6,k10_yellow_6(sK4,sK5))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k2_yellow19(sK4,sK5) != X1
    | sK6 != X2
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_280])).

cnf(c_966,plain,
    ( v3_pre_topc(sK3(sK4,k2_yellow19(sK4,sK5),sK6),sK4)
    | ~ r2_hidden(sK6,k10_yellow_6(sK4,sK5))
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_965])).

cnf(c_968,plain,
    ( v3_pre_topc(sK3(sK4,k2_yellow19(sK4,sK5),sK6),sK4)
    | ~ r2_hidden(sK6,k10_yellow_6(sK4,sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_966,c_35,c_34])).

cnf(c_970,plain,
    ( v3_pre_topc(sK3(sK4,k2_yellow19(sK4,sK5),sK6),sK4) = iProver_top
    | r2_hidden(sK6,k10_yellow_6(sK4,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_968])).

cnf(c_10,plain,
    ( r2_waybel_7(X0,X1,X2)
    | r2_hidden(X2,sK3(X0,X1,X2))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_979,plain,
    ( r2_hidden(X0,sK3(X1,X2,X0))
    | ~ r2_hidden(sK6,k10_yellow_6(sK4,sK5))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k2_yellow19(sK4,sK5) != X2
    | sK6 != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_280])).

cnf(c_980,plain,
    ( r2_hidden(sK6,sK3(sK4,k2_yellow19(sK4,sK5),sK6))
    | ~ r2_hidden(sK6,k10_yellow_6(sK4,sK5))
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_979])).

cnf(c_982,plain,
    ( r2_hidden(sK6,sK3(sK4,k2_yellow19(sK4,sK5),sK6))
    | ~ r2_hidden(sK6,k10_yellow_6(sK4,sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_980,c_35,c_34])).

cnf(c_984,plain,
    ( r2_hidden(sK6,sK3(sK4,k2_yellow19(sK4,sK5),sK6)) = iProver_top
    | r2_hidden(sK6,k10_yellow_6(sK4,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_982])).

cnf(c_9,plain,
    ( r2_waybel_7(X0,X1,X2)
    | ~ r2_hidden(sK3(X0,X1,X2),X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_993,plain,
    ( ~ r2_hidden(sK3(X0,X1,X2),X1)
    | ~ r2_hidden(sK6,k10_yellow_6(sK4,sK5))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k2_yellow19(sK4,sK5) != X1
    | sK6 != X2
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_280])).

cnf(c_994,plain,
    ( ~ r2_hidden(sK3(sK4,k2_yellow19(sK4,sK5),sK6),k2_yellow19(sK4,sK5))
    | ~ r2_hidden(sK6,k10_yellow_6(sK4,sK5))
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_993])).

cnf(c_996,plain,
    ( ~ r2_hidden(sK3(sK4,k2_yellow19(sK4,sK5),sK6),k2_yellow19(sK4,sK5))
    | ~ r2_hidden(sK6,k10_yellow_6(sK4,sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_994,c_35,c_34])).

cnf(c_998,plain,
    ( r2_hidden(sK3(sK4,k2_yellow19(sK4,sK5),sK6),k2_yellow19(sK4,sK5)) != iProver_top
    | r2_hidden(sK6,k10_yellow_6(sK4,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_996])).

cnf(c_1915,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_35])).

cnf(c_1916,plain,
    ( ~ m1_connsp_2(X0,sK4,X1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ l1_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_1915])).

cnf(c_1920,plain,
    ( ~ m1_connsp_2(X0,sK4,X1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1916,c_36,c_34])).

cnf(c_4266,plain,
    ( ~ m1_connsp_2(X0,sK4,sK6)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1920])).

cnf(c_4267,plain,
    ( m1_connsp_2(X0,sK4,sK6) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4266])).

cnf(c_16,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_19,plain,
    ( ~ r1_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | r2_hidden(X2,k2_yellow19(X0,X1))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_593,plain,
    ( ~ r1_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | r2_hidden(X2,k2_yellow19(X0,X1))
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(resolution,[status(thm)],[c_16,c_19])).

cnf(c_1433,plain,
    ( ~ r1_waybel_0(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | r2_hidden(X2,k2_yellow19(X0,X1))
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK5 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_593,c_30])).

cnf(c_1434,plain,
    ( ~ r1_waybel_0(sK4,sK5,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(X0,k2_yellow19(sK4,sK5))
    | ~ l1_pre_topc(sK4)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_1433])).

cnf(c_1438,plain,
    ( r2_hidden(X0,k2_yellow19(sK4,sK5))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_waybel_0(sK4,sK5,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1434,c_36,c_34,c_33])).

cnf(c_1439,plain,
    ( ~ r1_waybel_0(sK4,sK5,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(X0,k2_yellow19(sK4,sK5)) ),
    inference(renaming,[status(thm)],[c_1438])).

cnf(c_4563,plain,
    ( ~ r1_waybel_0(sK4,sK5,sK3(sK4,k2_yellow19(sK4,sK5),sK6))
    | ~ m1_subset_1(sK3(sK4,k2_yellow19(sK4,sK5),sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(sK3(sK4,k2_yellow19(sK4,sK5),sK6),k2_yellow19(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_1439])).

cnf(c_4564,plain,
    ( r1_waybel_0(sK4,sK5,sK3(sK4,k2_yellow19(sK4,sK5),sK6)) != iProver_top
    | m1_subset_1(sK3(sK4,k2_yellow19(sK4,sK5),sK6),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(sK3(sK4,k2_yellow19(sK4,sK5),sK6),k2_yellow19(sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4563])).

cnf(c_4357,plain,
    ( m1_connsp_2(sK3(sK4,k2_yellow19(sK4,sK5),sK6),sK4,X0)
    | ~ v3_pre_topc(sK3(sK4,k2_yellow19(sK4,sK5),sK6),sK4)
    | ~ m1_subset_1(sK3(sK4,k2_yellow19(sK4,sK5),sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X0,sK3(sK4,k2_yellow19(sK4,sK5),sK6)) ),
    inference(instantiation,[status(thm)],[c_1907])).

cnf(c_5165,plain,
    ( m1_connsp_2(sK3(sK4,k2_yellow19(sK4,sK5),sK6),sK4,sK6)
    | ~ v3_pre_topc(sK3(sK4,k2_yellow19(sK4,sK5),sK6),sK4)
    | ~ m1_subset_1(sK3(sK4,k2_yellow19(sK4,sK5),sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK6,sK3(sK4,k2_yellow19(sK4,sK5),sK6)) ),
    inference(instantiation,[status(thm)],[c_4357])).

cnf(c_5166,plain,
    ( m1_connsp_2(sK3(sK4,k2_yellow19(sK4,sK5),sK6),sK4,sK6) = iProver_top
    | v3_pre_topc(sK3(sK4,k2_yellow19(sK4,sK5),sK6),sK4) != iProver_top
    | m1_subset_1(sK3(sK4,k2_yellow19(sK4,sK5),sK6),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(sK6,sK3(sK4,k2_yellow19(sK4,sK5),sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5165])).

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
    inference(cnf_transformation,[],[f101])).

cnf(c_1326,plain,
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
    inference(resolution_lifted,[status(thm)],[c_6,c_31])).

cnf(c_1327,plain,
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
    inference(unflattening,[status(thm)],[c_1326])).

cnf(c_1331,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r1_waybel_0(X1,sK5,X0)
    | ~ l1_waybel_0(sK5,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(k10_yellow_6(X1,sK5),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k10_yellow_6(X1,sK5))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1327,c_33,c_32])).

cnf(c_1346,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r1_waybel_0(X1,sK5,X0)
    | ~ l1_waybel_0(sK5,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,k10_yellow_6(X1,sK5))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1331,c_1263])).

cnf(c_1629,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r1_waybel_0(X1,sK5,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,k10_yellow_6(X1,sK5))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | sK5 != sK5
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_1346])).

cnf(c_1630,plain,
    ( ~ m1_connsp_2(X0,sK4,X1)
    | r1_waybel_0(sK4,sK5,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ r2_hidden(X1,k10_yellow_6(sK4,sK5))
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_1629])).

cnf(c_1634,plain,
    ( ~ r2_hidden(X1,k10_yellow_6(sK4,sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | r1_waybel_0(sK4,sK5,X0)
    | ~ m1_connsp_2(X0,sK4,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1630,c_36,c_35,c_34])).

cnf(c_1635,plain,
    ( ~ m1_connsp_2(X0,sK4,X1)
    | r1_waybel_0(sK4,sK5,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ r2_hidden(X1,k10_yellow_6(sK4,sK5)) ),
    inference(renaming,[status(thm)],[c_1634])).

cnf(c_4278,plain,
    ( ~ m1_connsp_2(X0,sK4,sK6)
    | r1_waybel_0(sK4,sK5,X0)
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ r2_hidden(sK6,k10_yellow_6(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_1635])).

cnf(c_6341,plain,
    ( ~ m1_connsp_2(sK3(sK4,k2_yellow19(sK4,sK5),sK6),sK4,sK6)
    | r1_waybel_0(sK4,sK5,sK3(sK4,k2_yellow19(sK4,sK5),sK6))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ r2_hidden(sK6,k10_yellow_6(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_4278])).

cnf(c_6345,plain,
    ( m1_connsp_2(sK3(sK4,k2_yellow19(sK4,sK5),sK6),sK4,sK6) != iProver_top
    | r1_waybel_0(sK4,sK5,sK3(sK4,k2_yellow19(sK4,sK5),sK6)) = iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK6,k10_yellow_6(sK4,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6341])).

cnf(c_8232,plain,
    ( r2_hidden(k1_tops_1(sK4,k1_tops_1(sK4,X0)),k2_yellow19(sK4,sK5)) = iProver_top
    | m1_connsp_2(X0,sK4,sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8226,c_44,c_956,c_970,c_984,c_998,c_4267,c_4564,c_5166,c_6345])).

cnf(c_8233,plain,
    ( m1_connsp_2(X0,sK4,sK6) != iProver_top
    | r2_hidden(k1_tops_1(sK4,k1_tops_1(sK4,X0)),k2_yellow19(sK4,sK5)) = iProver_top ),
    inference(renaming,[status(thm)],[c_8232])).

cnf(c_21,plain,
    ( r1_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ r2_hidden(X2,k2_yellow19(X0,X1))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_570,plain,
    ( r1_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ r2_hidden(X2,k2_yellow19(X0,X1))
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(resolution,[status(thm)],[c_16,c_21])).

cnf(c_1454,plain,
    ( r1_waybel_0(X0,X1,X2)
    | ~ r2_hidden(X2,k2_yellow19(X0,X1))
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK5 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_570,c_30])).

cnf(c_1455,plain,
    ( r1_waybel_0(sK4,sK5,X0)
    | ~ r2_hidden(X0,k2_yellow19(sK4,sK5))
    | ~ l1_pre_topc(sK4)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_1454])).

cnf(c_1459,plain,
    ( ~ r2_hidden(X0,k2_yellow19(sK4,sK5))
    | r1_waybel_0(sK4,sK5,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1455,c_36,c_34,c_33])).

cnf(c_1460,plain,
    ( r1_waybel_0(sK4,sK5,X0)
    | ~ r2_hidden(X0,k2_yellow19(sK4,sK5)) ),
    inference(renaming,[status(thm)],[c_1459])).

cnf(c_4143,plain,
    ( r1_waybel_0(sK4,sK5,X0) = iProver_top
    | r2_hidden(X0,k2_yellow19(sK4,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1460])).

cnf(c_8239,plain,
    ( m1_connsp_2(X0,sK4,sK6) != iProver_top
    | r1_waybel_0(sK4,sK5,k1_tops_1(sK4,k1_tops_1(sK4,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_8233,c_4143])).

cnf(c_22,plain,
    ( r1_tarski(k1_tops_1(X0,X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_26,plain,
    ( ~ r1_waybel_0(X0,X1,X2)
    | r1_waybel_0(X0,X1,X3)
    | ~ r1_tarski(X2,X3)
    | ~ l1_waybel_0(X1,X0)
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_546,plain,
    ( ~ r1_waybel_0(X0,X1,X2)
    | r1_waybel_0(X0,X1,X3)
    | ~ r1_tarski(X2,X3)
    | ~ l1_waybel_0(X1,X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(resolution,[status(thm)],[c_16,c_26])).

cnf(c_1472,plain,
    ( ~ r1_waybel_0(X0,X1,X2)
    | r1_waybel_0(X0,X1,X3)
    | ~ r1_tarski(X2,X3)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK5 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_546,c_30])).

cnf(c_1473,plain,
    ( ~ r1_waybel_0(sK4,sK5,X0)
    | r1_waybel_0(sK4,sK5,X1)
    | ~ r1_tarski(X0,X1)
    | ~ l1_pre_topc(sK4)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_1472])).

cnf(c_1475,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_waybel_0(sK4,sK5,X1)
    | ~ r1_waybel_0(sK4,sK5,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1473,c_36,c_34,c_33])).

cnf(c_1476,plain,
    ( ~ r1_waybel_0(sK4,sK5,X0)
    | r1_waybel_0(sK4,sK5,X1)
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_1475])).

cnf(c_1729,plain,
    ( ~ r1_waybel_0(sK4,sK5,X0)
    | r1_waybel_0(sK4,sK5,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X3)
    | X1 != X2
    | k1_tops_1(X3,X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_1476])).

cnf(c_1730,plain,
    ( r1_waybel_0(sK4,sK5,X0)
    | ~ r1_waybel_0(sK4,sK5,k1_tops_1(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_1729])).

cnf(c_1999,plain,
    ( r1_waybel_0(sK4,sK5,X0)
    | ~ r1_waybel_0(sK4,sK5,k1_tops_1(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1730,c_34])).

cnf(c_2000,plain,
    ( r1_waybel_0(sK4,sK5,X0)
    | ~ r1_waybel_0(sK4,sK5,k1_tops_1(sK4,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(unflattening,[status(thm)],[c_1999])).

cnf(c_4123,plain,
    ( r1_waybel_0(sK4,sK5,X0) = iProver_top
    | r1_waybel_0(sK4,sK5,k1_tops_1(sK4,X0)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2000])).

cnf(c_8323,plain,
    ( m1_connsp_2(X0,sK4,sK6) != iProver_top
    | r1_waybel_0(sK4,sK5,k1_tops_1(sK4,X0)) = iProver_top
    | m1_subset_1(k1_tops_1(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8239,c_4123])).

cnf(c_8746,plain,
    ( r1_waybel_0(sK4,sK5,k1_tops_1(sK4,X0)) = iProver_top
    | m1_connsp_2(X0,sK4,sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8323,c_44,c_2016,c_4267])).

cnf(c_8747,plain,
    ( m1_connsp_2(X0,sK4,sK6) != iProver_top
    | r1_waybel_0(sK4,sK5,k1_tops_1(sK4,X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_8746])).

cnf(c_8752,plain,
    ( m1_connsp_2(X0,sK4,sK6) != iProver_top
    | r1_waybel_0(sK4,sK5,X0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8747,c_4123])).

cnf(c_8757,plain,
    ( r1_waybel_0(sK4,sK5,X0) = iProver_top
    | m1_connsp_2(X0,sK4,sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8752,c_44,c_4267])).

cnf(c_8758,plain,
    ( m1_connsp_2(X0,sK4,sK6) != iProver_top
    | r1_waybel_0(sK4,sK5,X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_8757])).

cnf(c_8763,plain,
    ( r1_waybel_0(sK4,sK5,sK2(sK4,sK5,sK6)) = iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK6,k10_yellow_6(sK4,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4139,c_8758])).

cnf(c_4,plain,
    ( ~ r1_waybel_0(X0,X1,sK2(X0,X1,X2))
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | r2_hidden(X2,k10_yellow_6(X0,X1))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1111,plain,
    ( ~ r1_waybel_0(X0,X1,sK2(X0,X1,X2))
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | r2_hidden(X2,k10_yellow_6(X0,X1))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_31])).

cnf(c_1112,plain,
    ( ~ r1_waybel_0(X0,sK5,sK2(X0,sK5,X1))
    | ~ l1_waybel_0(sK5,X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k10_yellow_6(X0,sK5),k1_zfmisc_1(u1_struct_0(X0)))
    | r2_hidden(X1,k10_yellow_6(X0,sK5))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK5)
    | ~ v4_orders_2(sK5) ),
    inference(unflattening,[status(thm)],[c_1111])).

cnf(c_1116,plain,
    ( ~ r1_waybel_0(X0,sK5,sK2(X0,sK5,X1))
    | ~ l1_waybel_0(sK5,X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k10_yellow_6(X0,sK5),k1_zfmisc_1(u1_struct_0(X0)))
    | r2_hidden(X1,k10_yellow_6(X0,sK5))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1112,c_33,c_32])).

cnf(c_1282,plain,
    ( ~ r1_waybel_0(X0,sK5,sK2(X0,sK5,X1))
    | ~ l1_waybel_0(sK5,X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r2_hidden(X1,k10_yellow_6(X0,sK5))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1263,c_1116])).

cnf(c_1528,plain,
    ( ~ r1_waybel_0(X0,sK5,sK2(X0,sK5,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r2_hidden(X1,k10_yellow_6(X0,sK5))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | sK5 != sK5
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_1282])).

cnf(c_1529,plain,
    ( ~ r1_waybel_0(sK4,sK5,sK2(sK4,sK5,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r2_hidden(X0,k10_yellow_6(sK4,sK5))
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_1528])).

cnf(c_1533,plain,
    ( r2_hidden(X0,k10_yellow_6(sK4,sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r1_waybel_0(sK4,sK5,sK2(sK4,sK5,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1529,c_36,c_35,c_34])).

cnf(c_1534,plain,
    ( ~ r1_waybel_0(sK4,sK5,sK2(sK4,sK5,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r2_hidden(X0,k10_yellow_6(sK4,sK5)) ),
    inference(renaming,[status(thm)],[c_1533])).

cnf(c_4243,plain,
    ( ~ r1_waybel_0(sK4,sK5,sK2(sK4,sK5,sK6))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | r2_hidden(sK6,k10_yellow_6(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_1534])).

cnf(c_4244,plain,
    ( r1_waybel_0(sK4,sK5,sK2(sK4,sK5,sK6)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK6,k10_yellow_6(sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4243])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8763,c_6345,c_5166,c_4564,c_4244,c_998,c_984,c_970,c_956,c_44])).


%------------------------------------------------------------------------------
