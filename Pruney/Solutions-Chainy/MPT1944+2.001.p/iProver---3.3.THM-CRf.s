%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:18 EST 2020

% Result     : Theorem 2.34s
% Output     : CNFRefutation 2.34s
% Verified   : 
% Statistics : Number of formulae       :  180 (1114 expanded)
%              Number of clauses        :  113 ( 285 expanded)
%              Number of leaves         :   18 ( 305 expanded)
%              Depth                    :   27
%              Number of atoms          : 1029 (8513 expanded)
%              Number of equality atoms :   90 ( 179 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal clause size      :   24 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v1_yellow_6(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v1_yellow_6(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1))
          & l1_waybel_0(X1,X0)
          & v1_yellow_6(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1))
          & l1_waybel_0(X1,X0)
          & v1_yellow_6(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1))
          & l1_waybel_0(X1,X0)
          & v1_yellow_6(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
     => ( ~ r2_hidden(k4_yellow_6(X0,sK7),k10_yellow_6(X0,sK7))
        & l1_waybel_0(sK7,X0)
        & v1_yellow_6(sK7,X0)
        & v7_waybel_0(sK7)
        & v4_orders_2(sK7)
        & ~ v2_struct_0(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1))
            & l1_waybel_0(X1,X0)
            & v1_yellow_6(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ r2_hidden(k4_yellow_6(sK6,X1),k10_yellow_6(sK6,X1))
          & l1_waybel_0(X1,sK6)
          & v1_yellow_6(X1,sK6)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK6)
      & v2_pre_topc(sK6)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ~ r2_hidden(k4_yellow_6(sK6,sK7),k10_yellow_6(sK6,sK7))
    & l1_waybel_0(sK7,sK6)
    & v1_yellow_6(sK7,sK6)
    & v7_waybel_0(sK7)
    & v4_orders_2(sK7)
    & ~ v2_struct_0(sK7)
    & l1_pre_topc(sK6)
    & v2_pre_topc(sK6)
    & ~ v2_struct_0(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f28,f44,f43])).

fof(f70,plain,(
    v7_waybel_0(sK7) ),
    inference(cnf_transformation,[],[f45])).

fof(f68,plain,(
    ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f45])).

fof(f69,plain,(
    v4_orders_2(sK7) ),
    inference(cnf_transformation,[],[f45])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
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

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f38,plain,(
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
    inference(rectify,[],[f37])).

fof(f41,plain,(
    ! [X6,X1,X0] :
      ( ? [X7] :
          ( ~ r1_waybel_0(X0,X1,X7)
          & m1_connsp_2(X7,X0,X6) )
     => ( ~ r1_waybel_0(X0,X1,sK5(X0,X1,X6))
        & m1_connsp_2(sK5(X0,X1,X6),X0,X6) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_waybel_0(X0,X1,X4)
          & m1_connsp_2(X4,X0,X3) )
     => ( ~ r1_waybel_0(X0,X1,sK4(X0,X1,X2))
        & m1_connsp_2(sK4(X0,X1,X2),X0,X3) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
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
              & m1_connsp_2(X4,X0,sK3(X0,X1,X2)) )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ! [X5] :
              ( r1_waybel_0(X0,X1,X5)
              | ~ m1_connsp_2(X5,X0,sK3(X0,X1,X2)) )
          | r2_hidden(sK3(X0,X1,X2),X2) )
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k10_yellow_6(X0,X1) = X2
                  | ( ( ( ~ r1_waybel_0(X0,X1,sK4(X0,X1,X2))
                        & m1_connsp_2(sK4(X0,X1,X2),X0,sK3(X0,X1,X2)) )
                      | ~ r2_hidden(sK3(X0,X1,X2),X2) )
                    & ( ! [X5] :
                          ( r1_waybel_0(X0,X1,X5)
                          | ~ m1_connsp_2(X5,X0,sK3(X0,X1,X2)) )
                      | r2_hidden(sK3(X0,X1,X2),X2) )
                    & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) )
                & ( ! [X6] :
                      ( ( ( r2_hidden(X6,X2)
                          | ( ~ r1_waybel_0(X0,X1,sK5(X0,X1,X6))
                            & m1_connsp_2(sK5(X0,X1,X6),X0,X6) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f38,f41,f40,f39])).

fof(f57,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,X2)
      | m1_connsp_2(sK5(X0,X1,X6),X0,X6)
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
    inference(cnf_transformation,[],[f42])).

fof(f75,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(X6,k10_yellow_6(X0,X1))
      | m1_connsp_2(sK5(X0,X1,X6),X0,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f57])).

fof(f66,plain,(
    v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f45])).

fof(f65,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f45])).

fof(f67,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f45])).

fof(f72,plain,(
    l1_waybel_0(sK7,sK6) ),
    inference(cnf_transformation,[],[f45])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( m1_connsp_2(X1,X0,X2)
               => r2_hidden(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,X1)
              | ~ m1_connsp_2(X1,X0,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,X1)
              | ~ m1_connsp_2(X1,X0,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ m1_connsp_2(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f1,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] : m1_subset_1(sK0(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f1,f29])).

fof(f46,plain,(
    ! [X0] : m1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f30])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f47,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ? [X3] :
                  ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r1_orders_2(X1,X3,X4)
                       => r2_hidden(k2_waybel_0(X0,X1,X4),X2) ) )
                  & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ? [X3] :
                  ( ! [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      | ~ r1_orders_2(X1,X3,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ? [X3] :
                  ( ! [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      | ~ r1_orders_2(X1,X3,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_waybel_0(X0,X1,X2)
                | ! [X3] :
                    ( ? [X4] :
                        ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        & r1_orders_2(X1,X3,X4)
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ? [X3] :
                    ( ! [X4] :
                        ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        | ~ r1_orders_2(X1,X3,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) )
                | ~ r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_waybel_0(X0,X1,X2)
                | ! [X3] :
                    ( ? [X4] :
                        ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        & r1_orders_2(X1,X3,X4)
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ? [X5] :
                    ( ! [X6] :
                        ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
                        | ~ r1_orders_2(X1,X5,X6)
                        | ~ m1_subset_1(X6,u1_struct_0(X1)) )
                    & m1_subset_1(X5,u1_struct_0(X1)) )
                | ~ r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f31])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
              | ~ r1_orders_2(X1,X5,X6)
              | ~ m1_subset_1(X6,u1_struct_0(X1)) )
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ! [X6] :
            ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
            | ~ r1_orders_2(X1,sK2(X0,X1,X2),X6)
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
          & r1_orders_2(X1,X3,X4)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_hidden(k2_waybel_0(X0,X1,sK1(X0,X1,X2,X3)),X2)
        & r1_orders_2(X1,X3,sK1(X0,X1,X2,X3))
        & m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_waybel_0(X0,X1,X2)
                | ! [X3] :
                    ( ( ~ r2_hidden(k2_waybel_0(X0,X1,sK1(X0,X1,X2,X3)),X2)
                      & r1_orders_2(X1,X3,sK1(X0,X1,X2,X3))
                      & m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ( ! [X6] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
                      | ~ r1_orders_2(X1,sK2(X0,X1,X2),X6)
                      | ~ m1_subset_1(X6,u1_struct_0(X1)) )
                  & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) )
                | ~ r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f32,f34,f33])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_waybel_0(X0,X1,X2)
      | m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v1_yellow_6(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => k2_waybel_0(X0,X1,X2) = k4_yellow_6(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_waybel_0(X0,X1,X2) = k4_yellow_6(X0,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v1_yellow_6(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_waybel_0(X0,X1,X2) = k4_yellow_6(X0,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v1_yellow_6(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k2_waybel_0(X0,X1,X2) = k4_yellow_6(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v1_yellow_6(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f71,plain,(
    v1_yellow_6(sK7,sK6) ),
    inference(cnf_transformation,[],[f45])).

fof(f58,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,X2)
      | ~ r1_waybel_0(X0,X1,sK5(X0,X1,X6))
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
    inference(cnf_transformation,[],[f42])).

fof(f74,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(X6,k10_yellow_6(X0,X1))
      | ~ r1_waybel_0(X0,X1,sK5(X0,X1,X6))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f58])).

fof(f73,plain,(
    ~ r2_hidden(k4_yellow_6(sK6,sK7),k10_yellow_6(sK6,sK7)) ),
    inference(cnf_transformation,[],[f45])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l1_waybel_0(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_waybel_0(X0,X1,X2)
      | ~ r2_hidden(k2_waybel_0(X0,X1,sK1(X0,X1,X2,X3)),X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_17,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(k10_yellow_6(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_22,negated_conjecture,
    ( v7_waybel_0(sK7) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_844,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(k10_yellow_6(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_22])).

cnf(c_845,plain,
    ( ~ l1_waybel_0(sK7,X0)
    | m1_subset_1(k10_yellow_6(X0,sK7),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v4_orders_2(sK7)
    | v2_struct_0(X0)
    | v2_struct_0(sK7)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_844])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_23,negated_conjecture,
    ( v4_orders_2(sK7) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_849,plain,
    ( v2_struct_0(X0)
    | ~ l1_waybel_0(sK7,X0)
    | m1_subset_1(k10_yellow_6(X0,sK7),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_845,c_24,c_23])).

cnf(c_850,plain,
    ( ~ l1_waybel_0(sK7,X0)
    | m1_subset_1(k10_yellow_6(X0,sK7),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(renaming,[status(thm)],[c_849])).

cnf(c_15,plain,
    ( m1_connsp_2(sK5(X0,X1,X2),X0,X2)
    | ~ l1_waybel_0(X1,X0)
    | r2_hidden(X2,k10_yellow_6(X0,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_661,plain,
    ( m1_connsp_2(sK5(X0,X1,X2),X0,X2)
    | ~ l1_waybel_0(X1,X0)
    | r2_hidden(X2,k10_yellow_6(X0,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v4_orders_2(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_22])).

cnf(c_662,plain,
    ( m1_connsp_2(sK5(X0,sK7,X1),X0,X1)
    | ~ l1_waybel_0(sK7,X0)
    | r2_hidden(X1,k10_yellow_6(X0,sK7))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k10_yellow_6(X0,sK7),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v4_orders_2(sK7)
    | v2_struct_0(X0)
    | v2_struct_0(sK7)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_661])).

cnf(c_666,plain,
    ( v2_struct_0(X0)
    | m1_connsp_2(sK5(X0,sK7,X1),X0,X1)
    | ~ l1_waybel_0(sK7,X0)
    | r2_hidden(X1,k10_yellow_6(X0,sK7))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k10_yellow_6(X0,sK7),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_662,c_24,c_23])).

cnf(c_667,plain,
    ( m1_connsp_2(sK5(X0,sK7,X1),X0,X1)
    | ~ l1_waybel_0(sK7,X0)
    | r2_hidden(X1,k10_yellow_6(X0,sK7))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k10_yellow_6(X0,sK7),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(renaming,[status(thm)],[c_666])).

cnf(c_868,plain,
    ( m1_connsp_2(sK5(X0,sK7,X1),X0,X1)
    | ~ l1_waybel_0(sK7,X0)
    | r2_hidden(X1,k10_yellow_6(X0,sK7))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_850,c_667])).

cnf(c_26,negated_conjecture,
    ( v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1025,plain,
    ( m1_connsp_2(sK5(X0,sK7,X1),X0,X1)
    | ~ l1_waybel_0(sK7,X0)
    | r2_hidden(X1,k10_yellow_6(X0,sK7))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_868,c_26])).

cnf(c_1026,plain,
    ( m1_connsp_2(sK5(sK6,sK7,X0),sK6,X0)
    | ~ l1_waybel_0(sK7,sK6)
    | r2_hidden(X0,k10_yellow_6(sK6,sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK6) ),
    inference(unflattening,[status(thm)],[c_1025])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_25,negated_conjecture,
    ( l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_20,negated_conjecture,
    ( l1_waybel_0(sK7,sK6) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1030,plain,
    ( m1_connsp_2(sK5(sK6,sK7,X0),sK6,X0)
    | r2_hidden(X0,k10_yellow_6(sK6,sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1026,c_27,c_25,c_20])).

cnf(c_2872,plain,
    ( m1_connsp_2(sK5(sK6,sK7,X0_55),sK6,X0_55)
    | r2_hidden(X0_55,k10_yellow_6(sK6,sK7))
    | ~ m1_subset_1(X0_55,u1_struct_0(sK6)) ),
    inference(subtyping,[status(esa)],[c_1030])).

cnf(c_3240,plain,
    ( m1_connsp_2(sK5(sK6,sK7,X0_55),sK6,X0_55) = iProver_top
    | r2_hidden(X0_55,k10_yellow_6(sK6,sK7)) = iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2872])).

cnf(c_3,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r2_hidden(X2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_175,plain,
    ( r2_hidden(X2,X0)
    | ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3,c_2])).

cnf(c_176,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r2_hidden(X2,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_175])).

cnf(c_1156,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r2_hidden(X2,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_176,c_26])).

cnf(c_1157,plain,
    ( ~ m1_connsp_2(X0,sK6,X1)
    | r2_hidden(X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK6) ),
    inference(unflattening,[status(thm)],[c_1156])).

cnf(c_1161,plain,
    ( ~ m1_connsp_2(X0,sK6,X1)
    | r2_hidden(X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1157,c_27,c_25])).

cnf(c_2866,plain,
    ( ~ m1_connsp_2(X0_55,sK6,X1_55)
    | r2_hidden(X1_55,X0_55)
    | ~ m1_subset_1(X1_55,u1_struct_0(sK6)) ),
    inference(subtyping,[status(esa)],[c_1161])).

cnf(c_3246,plain,
    ( m1_connsp_2(X0_55,sK6,X1_55) != iProver_top
    | r2_hidden(X1_55,X0_55) = iProver_top
    | m1_subset_1(X1_55,u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2866])).

cnf(c_3695,plain,
    ( r2_hidden(X0_55,sK5(sK6,sK7,X0_55)) = iProver_top
    | r2_hidden(X0_55,k10_yellow_6(sK6,sK7)) = iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3240,c_3246])).

cnf(c_0,plain,
    ( m1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_2877,plain,
    ( m1_subset_1(sK0(X0_56),X0_56) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_3235,plain,
    ( m1_subset_1(sK0(X0_56),X0_56) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2877])).

cnf(c_1,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_6,plain,
    ( r1_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X1))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_401,plain,
    ( r1_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X1))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_1,c_6])).

cnf(c_1266,plain,
    ( r1_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X1))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_401,c_25])).

cnf(c_1267,plain,
    ( r1_waybel_0(sK6,X0,X1)
    | ~ l1_waybel_0(X0,sK6)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK1(sK6,X0,X1,X2),u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_1266])).

cnf(c_1271,plain,
    ( v2_struct_0(X0)
    | m1_subset_1(sK1(sK6,X0,X1,X2),u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_waybel_0(X0,sK6)
    | r1_waybel_0(sK6,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1267,c_27])).

cnf(c_1272,plain,
    ( r1_waybel_0(sK6,X0,X1)
    | ~ l1_waybel_0(X0,sK6)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK1(sK6,X0,X1,X2),u1_struct_0(X0))
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_1271])).

cnf(c_1512,plain,
    ( r1_waybel_0(sK6,X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK1(sK6,X0,X1,X2),u1_struct_0(X0))
    | v2_struct_0(X0)
    | sK7 != X0
    | sK6 != sK6 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_1272])).

cnf(c_1513,plain,
    ( r1_waybel_0(sK6,sK7,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | m1_subset_1(sK1(sK6,sK7,X0,X1),u1_struct_0(sK7))
    | v2_struct_0(sK7) ),
    inference(unflattening,[status(thm)],[c_1512])).

cnf(c_1517,plain,
    ( m1_subset_1(sK1(sK6,sK7,X0,X1),u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | r1_waybel_0(sK6,sK7,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1513,c_24])).

cnf(c_1518,plain,
    ( r1_waybel_0(sK6,sK7,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | m1_subset_1(sK1(sK6,sK7,X0,X1),u1_struct_0(sK7)) ),
    inference(renaming,[status(thm)],[c_1517])).

cnf(c_2861,plain,
    ( r1_waybel_0(sK6,sK7,X0_55)
    | ~ m1_subset_1(X1_55,u1_struct_0(sK7))
    | m1_subset_1(sK1(sK6,sK7,X0_55,X1_55),u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_1518])).

cnf(c_3251,plain,
    ( r1_waybel_0(sK6,sK7,X0_55) = iProver_top
    | m1_subset_1(X1_55,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK1(sK6,sK7,X0_55,X1_55),u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2861])).

cnf(c_18,plain,
    ( ~ v1_yellow_6(X0,X1)
    | ~ l1_waybel_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_struct_0(X1)
    | k2_waybel_0(X1,X0,X2) = k4_yellow_6(X1,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_21,negated_conjecture,
    ( v1_yellow_6(sK7,sK6) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_316,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | k2_waybel_0(X1,X0,X2) = k4_yellow_6(X1,X0)
    | sK7 != X0
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_21])).

cnf(c_317,plain,
    ( ~ l1_waybel_0(sK7,sK6)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ v4_orders_2(sK7)
    | ~ v7_waybel_0(sK7)
    | v2_struct_0(sK7)
    | v2_struct_0(sK6)
    | ~ l1_struct_0(sK6)
    | k2_waybel_0(sK6,sK7,X0) = k4_yellow_6(sK6,sK7) ),
    inference(unflattening,[status(thm)],[c_316])).

cnf(c_89,plain,
    ( ~ l1_pre_topc(sK6)
    | l1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_321,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | k2_waybel_0(sK6,sK7,X0) = k4_yellow_6(sK6,sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_317,c_27,c_25,c_24,c_23,c_22,c_20,c_89])).

cnf(c_2875,plain,
    ( ~ m1_subset_1(X0_55,u1_struct_0(sK7))
    | k2_waybel_0(sK6,sK7,X0_55) = k4_yellow_6(sK6,sK7) ),
    inference(subtyping,[status(esa)],[c_321])).

cnf(c_3237,plain,
    ( k2_waybel_0(sK6,sK7,X0_55) = k4_yellow_6(sK6,sK7)
    | m1_subset_1(X0_55,u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2875])).

cnf(c_3774,plain,
    ( k2_waybel_0(sK6,sK7,sK1(sK6,sK7,X0_55,X1_55)) = k4_yellow_6(sK6,sK7)
    | r1_waybel_0(sK6,sK7,X0_55) = iProver_top
    | m1_subset_1(X1_55,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3251,c_3237])).

cnf(c_4017,plain,
    ( k2_waybel_0(sK6,sK7,sK1(sK6,sK7,X0_55,sK0(u1_struct_0(sK7)))) = k4_yellow_6(sK6,sK7)
    | r1_waybel_0(sK6,sK7,X0_55) = iProver_top ),
    inference(superposition,[status(thm)],[c_3235,c_3774])).

cnf(c_14,plain,
    ( ~ r1_waybel_0(X0,X1,sK5(X0,X1,X2))
    | ~ l1_waybel_0(X1,X0)
    | r2_hidden(X2,k10_yellow_6(X0,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_697,plain,
    ( ~ r1_waybel_0(X0,X1,sK5(X0,X1,X2))
    | ~ l1_waybel_0(X1,X0)
    | r2_hidden(X2,k10_yellow_6(X0,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v4_orders_2(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_22])).

cnf(c_698,plain,
    ( ~ r1_waybel_0(X0,sK7,sK5(X0,sK7,X1))
    | ~ l1_waybel_0(sK7,X0)
    | r2_hidden(X1,k10_yellow_6(X0,sK7))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k10_yellow_6(X0,sK7),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v4_orders_2(sK7)
    | v2_struct_0(X0)
    | v2_struct_0(sK7)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_697])).

cnf(c_702,plain,
    ( v2_struct_0(X0)
    | ~ r1_waybel_0(X0,sK7,sK5(X0,sK7,X1))
    | ~ l1_waybel_0(sK7,X0)
    | r2_hidden(X1,k10_yellow_6(X0,sK7))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k10_yellow_6(X0,sK7),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_698,c_24,c_23])).

cnf(c_703,plain,
    ( ~ r1_waybel_0(X0,sK7,sK5(X0,sK7,X1))
    | ~ l1_waybel_0(sK7,X0)
    | r2_hidden(X1,k10_yellow_6(X0,sK7))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k10_yellow_6(X0,sK7),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(renaming,[status(thm)],[c_702])).

cnf(c_869,plain,
    ( ~ r1_waybel_0(X0,sK7,sK5(X0,sK7,X1))
    | ~ l1_waybel_0(sK7,X0)
    | r2_hidden(X1,k10_yellow_6(X0,sK7))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_850,c_703])).

cnf(c_1004,plain,
    ( ~ r1_waybel_0(X0,sK7,sK5(X0,sK7,X1))
    | ~ l1_waybel_0(sK7,X0)
    | r2_hidden(X1,k10_yellow_6(X0,sK7))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_869,c_26])).

cnf(c_1005,plain,
    ( ~ r1_waybel_0(sK6,sK7,sK5(sK6,sK7,X0))
    | ~ l1_waybel_0(sK7,sK6)
    | r2_hidden(X0,k10_yellow_6(sK6,sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK6) ),
    inference(unflattening,[status(thm)],[c_1004])).

cnf(c_1009,plain,
    ( ~ r1_waybel_0(sK6,sK7,sK5(sK6,sK7,X0))
    | r2_hidden(X0,k10_yellow_6(sK6,sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1005,c_27,c_25,c_20])).

cnf(c_2873,plain,
    ( ~ r1_waybel_0(sK6,sK7,sK5(sK6,sK7,X0_55))
    | r2_hidden(X0_55,k10_yellow_6(sK6,sK7))
    | ~ m1_subset_1(X0_55,u1_struct_0(sK6)) ),
    inference(subtyping,[status(esa)],[c_1009])).

cnf(c_3239,plain,
    ( r1_waybel_0(sK6,sK7,sK5(sK6,sK7,X0_55)) != iProver_top
    | r2_hidden(X0_55,k10_yellow_6(sK6,sK7)) = iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2873])).

cnf(c_4058,plain,
    ( k2_waybel_0(sK6,sK7,sK1(sK6,sK7,sK5(sK6,sK7,X0_55),sK0(u1_struct_0(sK7)))) = k4_yellow_6(sK6,sK7)
    | r2_hidden(X0_55,k10_yellow_6(sK6,sK7)) = iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4017,c_3239])).

cnf(c_19,negated_conjecture,
    ( ~ r2_hidden(k4_yellow_6(sK6,sK7),k10_yellow_6(sK6,sK7)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2876,negated_conjecture,
    ( ~ r2_hidden(k4_yellow_6(sK6,sK7),k10_yellow_6(sK6,sK7)) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_3236,plain,
    ( r2_hidden(k4_yellow_6(sK6,sK7),k10_yellow_6(sK6,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2876])).

cnf(c_4137,plain,
    ( k2_waybel_0(sK6,sK7,sK1(sK6,sK7,sK5(sK6,sK7,k4_yellow_6(sK6,sK7)),sK0(u1_struct_0(sK7)))) = k4_yellow_6(sK6,sK7)
    | m1_subset_1(k4_yellow_6(sK6,sK7),u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4058,c_3236])).

cnf(c_3413,plain,
    ( m1_subset_1(sK0(u1_struct_0(sK7)),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_2877])).

cnf(c_3416,plain,
    ( m1_subset_1(sK0(u1_struct_0(sK7)),u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3413])).

cnf(c_3631,plain,
    ( k2_waybel_0(sK6,sK7,sK0(u1_struct_0(sK7))) = k4_yellow_6(sK6,sK7) ),
    inference(superposition,[status(thm)],[c_3235,c_3237])).

cnf(c_9,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(k2_waybel_0(X1,X0,X2),u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_480,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(k2_waybel_0(X1,X0,X2),u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X3)
    | X1 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_9])).

cnf(c_481,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(k2_waybel_0(X1,X0,X2),u1_struct_0(X1))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_480])).

cnf(c_1341,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(k2_waybel_0(X1,X0,X2),u1_struct_0(X1))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_481,c_25])).

cnf(c_1342,plain,
    ( ~ l1_waybel_0(X0,sK6)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(k2_waybel_0(sK6,X0,X1),u1_struct_0(sK6))
    | v2_struct_0(X0)
    | v2_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_1341])).

cnf(c_1346,plain,
    ( v2_struct_0(X0)
    | m1_subset_1(k2_waybel_0(sK6,X0,X1),u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_waybel_0(X0,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1342,c_27])).

cnf(c_1347,plain,
    ( ~ l1_waybel_0(X0,sK6)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(k2_waybel_0(sK6,X0,X1),u1_struct_0(sK6))
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_1346])).

cnf(c_1476,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k2_waybel_0(sK6,X1,X0),u1_struct_0(sK6))
    | v2_struct_0(X1)
    | sK7 != X1
    | sK6 != sK6 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_1347])).

cnf(c_1477,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | m1_subset_1(k2_waybel_0(sK6,sK7,X0),u1_struct_0(sK6))
    | v2_struct_0(sK7) ),
    inference(unflattening,[status(thm)],[c_1476])).

cnf(c_1481,plain,
    ( m1_subset_1(k2_waybel_0(sK6,sK7,X0),u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1477,c_24])).

cnf(c_1482,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | m1_subset_1(k2_waybel_0(sK6,sK7,X0),u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_1481])).

cnf(c_2863,plain,
    ( ~ m1_subset_1(X0_55,u1_struct_0(sK7))
    | m1_subset_1(k2_waybel_0(sK6,sK7,X0_55),u1_struct_0(sK6)) ),
    inference(subtyping,[status(esa)],[c_1482])).

cnf(c_3249,plain,
    ( m1_subset_1(X0_55,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(k2_waybel_0(sK6,sK7,X0_55),u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2863])).

cnf(c_3639,plain,
    ( m1_subset_1(k4_yellow_6(sK6,sK7),u1_struct_0(sK6)) = iProver_top
    | m1_subset_1(sK0(u1_struct_0(sK7)),u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3631,c_3249])).

cnf(c_4263,plain,
    ( k2_waybel_0(sK6,sK7,sK1(sK6,sK7,sK5(sK6,sK7,k4_yellow_6(sK6,sK7)),sK0(u1_struct_0(sK7)))) = k4_yellow_6(sK6,sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4137,c_3416,c_3639])).

cnf(c_4,plain,
    ( r1_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ r2_hidden(k2_waybel_0(X0,X1,sK1(X0,X1,X2,X3)),X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_427,plain,
    ( r1_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ r2_hidden(k2_waybel_0(X0,X1,sK1(X0,X1,X2,X3)),X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_1,c_4])).

cnf(c_1241,plain,
    ( r1_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ r2_hidden(k2_waybel_0(X0,X1,sK1(X0,X1,X2,X3)),X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_427,c_25])).

cnf(c_1242,plain,
    ( r1_waybel_0(sK6,X0,X1)
    | ~ l1_waybel_0(X0,sK6)
    | ~ r2_hidden(k2_waybel_0(sK6,X0,sK1(sK6,X0,X1,X2)),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_1241])).

cnf(c_1246,plain,
    ( v2_struct_0(X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(k2_waybel_0(sK6,X0,sK1(sK6,X0,X1,X2)),X1)
    | ~ l1_waybel_0(X0,sK6)
    | r1_waybel_0(sK6,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1242,c_27])).

cnf(c_1247,plain,
    ( r1_waybel_0(sK6,X0,X1)
    | ~ l1_waybel_0(X0,sK6)
    | ~ r2_hidden(k2_waybel_0(sK6,X0,sK1(sK6,X0,X1,X2)),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_1246])).

cnf(c_1533,plain,
    ( r1_waybel_0(sK6,X0,X1)
    | ~ r2_hidden(k2_waybel_0(sK6,X0,sK1(sK6,X0,X1,X2)),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | sK7 != X0
    | sK6 != sK6 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_1247])).

cnf(c_1534,plain,
    ( r1_waybel_0(sK6,sK7,X0)
    | ~ r2_hidden(k2_waybel_0(sK6,sK7,sK1(sK6,sK7,X0,X1)),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | v2_struct_0(sK7) ),
    inference(unflattening,[status(thm)],[c_1533])).

cnf(c_1538,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ r2_hidden(k2_waybel_0(sK6,sK7,sK1(sK6,sK7,X0,X1)),X0)
    | r1_waybel_0(sK6,sK7,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1534,c_24])).

cnf(c_1539,plain,
    ( r1_waybel_0(sK6,sK7,X0)
    | ~ r2_hidden(k2_waybel_0(sK6,sK7,sK1(sK6,sK7,X0,X1)),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK7)) ),
    inference(renaming,[status(thm)],[c_1538])).

cnf(c_2860,plain,
    ( r1_waybel_0(sK6,sK7,X0_55)
    | ~ r2_hidden(k2_waybel_0(sK6,sK7,sK1(sK6,sK7,X0_55,X1_55)),X0_55)
    | ~ m1_subset_1(X1_55,u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_1539])).

cnf(c_3252,plain,
    ( r1_waybel_0(sK6,sK7,X0_55) = iProver_top
    | r2_hidden(k2_waybel_0(sK6,sK7,sK1(sK6,sK7,X0_55,X1_55)),X0_55) != iProver_top
    | m1_subset_1(X1_55,u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2860])).

cnf(c_4266,plain,
    ( r1_waybel_0(sK6,sK7,sK5(sK6,sK7,k4_yellow_6(sK6,sK7))) = iProver_top
    | r2_hidden(k4_yellow_6(sK6,sK7),sK5(sK6,sK7,k4_yellow_6(sK6,sK7))) != iProver_top
    | m1_subset_1(sK0(u1_struct_0(sK7)),u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4263,c_3252])).

cnf(c_1773,plain,
    ( ~ r1_waybel_0(sK6,sK7,sK5(sK6,sK7,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | k4_yellow_6(sK6,sK7) != X0
    | k10_yellow_6(sK6,sK7) != k10_yellow_6(sK6,sK7) ),
    inference(resolution_lifted,[status(thm)],[c_19,c_1009])).

cnf(c_1774,plain,
    ( ~ r1_waybel_0(sK6,sK7,sK5(sK6,sK7,k4_yellow_6(sK6,sK7)))
    | ~ m1_subset_1(k4_yellow_6(sK6,sK7),u1_struct_0(sK6)) ),
    inference(unflattening,[status(thm)],[c_1773])).

cnf(c_1775,plain,
    ( r1_waybel_0(sK6,sK7,sK5(sK6,sK7,k4_yellow_6(sK6,sK7))) != iProver_top
    | m1_subset_1(k4_yellow_6(sK6,sK7),u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1774])).

cnf(c_4276,plain,
    ( r2_hidden(k4_yellow_6(sK6,sK7),sK5(sK6,sK7,k4_yellow_6(sK6,sK7))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4266,c_1775,c_3416,c_3639])).

cnf(c_4281,plain,
    ( r2_hidden(k4_yellow_6(sK6,sK7),k10_yellow_6(sK6,sK7)) = iProver_top
    | m1_subset_1(k4_yellow_6(sK6,sK7),u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3695,c_4276])).

cnf(c_36,plain,
    ( r2_hidden(k4_yellow_6(sK6,sK7),k10_yellow_6(sK6,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4281,c_3639,c_3416,c_36])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:40:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.34/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/1.00  
% 2.34/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.34/1.00  
% 2.34/1.00  ------  iProver source info
% 2.34/1.00  
% 2.34/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.34/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.34/1.00  git: non_committed_changes: false
% 2.34/1.00  git: last_make_outside_of_git: false
% 2.34/1.00  
% 2.34/1.00  ------ 
% 2.34/1.00  
% 2.34/1.00  ------ Input Options
% 2.34/1.00  
% 2.34/1.00  --out_options                           all
% 2.34/1.00  --tptp_safe_out                         true
% 2.34/1.00  --problem_path                          ""
% 2.34/1.00  --include_path                          ""
% 2.34/1.00  --clausifier                            res/vclausify_rel
% 2.34/1.00  --clausifier_options                    --mode clausify
% 2.34/1.00  --stdin                                 false
% 2.34/1.00  --stats_out                             all
% 2.34/1.00  
% 2.34/1.00  ------ General Options
% 2.34/1.00  
% 2.34/1.00  --fof                                   false
% 2.34/1.00  --time_out_real                         305.
% 2.34/1.00  --time_out_virtual                      -1.
% 2.34/1.00  --symbol_type_check                     false
% 2.34/1.00  --clausify_out                          false
% 2.34/1.00  --sig_cnt_out                           false
% 2.34/1.00  --trig_cnt_out                          false
% 2.34/1.00  --trig_cnt_out_tolerance                1.
% 2.34/1.00  --trig_cnt_out_sk_spl                   false
% 2.34/1.00  --abstr_cl_out                          false
% 2.34/1.00  
% 2.34/1.00  ------ Global Options
% 2.34/1.00  
% 2.34/1.00  --schedule                              default
% 2.34/1.00  --add_important_lit                     false
% 2.34/1.00  --prop_solver_per_cl                    1000
% 2.34/1.00  --min_unsat_core                        false
% 2.34/1.00  --soft_assumptions                      false
% 2.34/1.00  --soft_lemma_size                       3
% 2.34/1.00  --prop_impl_unit_size                   0
% 2.34/1.00  --prop_impl_unit                        []
% 2.34/1.00  --share_sel_clauses                     true
% 2.34/1.00  --reset_solvers                         false
% 2.34/1.00  --bc_imp_inh                            [conj_cone]
% 2.34/1.00  --conj_cone_tolerance                   3.
% 2.34/1.00  --extra_neg_conj                        none
% 2.34/1.00  --large_theory_mode                     true
% 2.34/1.00  --prolific_symb_bound                   200
% 2.34/1.00  --lt_threshold                          2000
% 2.34/1.00  --clause_weak_htbl                      true
% 2.34/1.00  --gc_record_bc_elim                     false
% 2.34/1.00  
% 2.34/1.00  ------ Preprocessing Options
% 2.34/1.00  
% 2.34/1.00  --preprocessing_flag                    true
% 2.34/1.00  --time_out_prep_mult                    0.1
% 2.34/1.00  --splitting_mode                        input
% 2.34/1.00  --splitting_grd                         true
% 2.34/1.00  --splitting_cvd                         false
% 2.34/1.00  --splitting_cvd_svl                     false
% 2.34/1.00  --splitting_nvd                         32
% 2.34/1.00  --sub_typing                            true
% 2.34/1.00  --prep_gs_sim                           true
% 2.34/1.00  --prep_unflatten                        true
% 2.34/1.00  --prep_res_sim                          true
% 2.34/1.00  --prep_upred                            true
% 2.34/1.00  --prep_sem_filter                       exhaustive
% 2.34/1.00  --prep_sem_filter_out                   false
% 2.34/1.00  --pred_elim                             true
% 2.34/1.00  --res_sim_input                         true
% 2.34/1.00  --eq_ax_congr_red                       true
% 2.34/1.00  --pure_diseq_elim                       true
% 2.34/1.00  --brand_transform                       false
% 2.34/1.00  --non_eq_to_eq                          false
% 2.34/1.00  --prep_def_merge                        true
% 2.34/1.00  --prep_def_merge_prop_impl              false
% 2.34/1.00  --prep_def_merge_mbd                    true
% 2.34/1.00  --prep_def_merge_tr_red                 false
% 2.34/1.00  --prep_def_merge_tr_cl                  false
% 2.34/1.00  --smt_preprocessing                     true
% 2.34/1.00  --smt_ac_axioms                         fast
% 2.34/1.00  --preprocessed_out                      false
% 2.34/1.00  --preprocessed_stats                    false
% 2.34/1.00  
% 2.34/1.00  ------ Abstraction refinement Options
% 2.34/1.00  
% 2.34/1.00  --abstr_ref                             []
% 2.34/1.00  --abstr_ref_prep                        false
% 2.34/1.00  --abstr_ref_until_sat                   false
% 2.34/1.00  --abstr_ref_sig_restrict                funpre
% 2.34/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.34/1.00  --abstr_ref_under                       []
% 2.34/1.00  
% 2.34/1.00  ------ SAT Options
% 2.34/1.00  
% 2.34/1.00  --sat_mode                              false
% 2.34/1.00  --sat_fm_restart_options                ""
% 2.34/1.00  --sat_gr_def                            false
% 2.34/1.00  --sat_epr_types                         true
% 2.34/1.00  --sat_non_cyclic_types                  false
% 2.34/1.00  --sat_finite_models                     false
% 2.34/1.00  --sat_fm_lemmas                         false
% 2.34/1.00  --sat_fm_prep                           false
% 2.34/1.00  --sat_fm_uc_incr                        true
% 2.34/1.00  --sat_out_model                         small
% 2.34/1.00  --sat_out_clauses                       false
% 2.34/1.00  
% 2.34/1.00  ------ QBF Options
% 2.34/1.00  
% 2.34/1.00  --qbf_mode                              false
% 2.34/1.00  --qbf_elim_univ                         false
% 2.34/1.00  --qbf_dom_inst                          none
% 2.34/1.00  --qbf_dom_pre_inst                      false
% 2.34/1.00  --qbf_sk_in                             false
% 2.34/1.00  --qbf_pred_elim                         true
% 2.34/1.00  --qbf_split                             512
% 2.34/1.00  
% 2.34/1.00  ------ BMC1 Options
% 2.34/1.00  
% 2.34/1.00  --bmc1_incremental                      false
% 2.34/1.00  --bmc1_axioms                           reachable_all
% 2.34/1.00  --bmc1_min_bound                        0
% 2.34/1.00  --bmc1_max_bound                        -1
% 2.34/1.00  --bmc1_max_bound_default                -1
% 2.34/1.00  --bmc1_symbol_reachability              true
% 2.34/1.00  --bmc1_property_lemmas                  false
% 2.34/1.00  --bmc1_k_induction                      false
% 2.34/1.00  --bmc1_non_equiv_states                 false
% 2.34/1.00  --bmc1_deadlock                         false
% 2.34/1.00  --bmc1_ucm                              false
% 2.34/1.00  --bmc1_add_unsat_core                   none
% 2.34/1.00  --bmc1_unsat_core_children              false
% 2.34/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.34/1.00  --bmc1_out_stat                         full
% 2.34/1.00  --bmc1_ground_init                      false
% 2.34/1.00  --bmc1_pre_inst_next_state              false
% 2.34/1.00  --bmc1_pre_inst_state                   false
% 2.34/1.00  --bmc1_pre_inst_reach_state             false
% 2.34/1.00  --bmc1_out_unsat_core                   false
% 2.34/1.00  --bmc1_aig_witness_out                  false
% 2.34/1.00  --bmc1_verbose                          false
% 2.34/1.00  --bmc1_dump_clauses_tptp                false
% 2.34/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.34/1.00  --bmc1_dump_file                        -
% 2.34/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.34/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.34/1.00  --bmc1_ucm_extend_mode                  1
% 2.34/1.00  --bmc1_ucm_init_mode                    2
% 2.34/1.00  --bmc1_ucm_cone_mode                    none
% 2.34/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.34/1.00  --bmc1_ucm_relax_model                  4
% 2.34/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.34/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.34/1.00  --bmc1_ucm_layered_model                none
% 2.34/1.00  --bmc1_ucm_max_lemma_size               10
% 2.34/1.00  
% 2.34/1.00  ------ AIG Options
% 2.34/1.00  
% 2.34/1.00  --aig_mode                              false
% 2.34/1.00  
% 2.34/1.00  ------ Instantiation Options
% 2.34/1.00  
% 2.34/1.00  --instantiation_flag                    true
% 2.34/1.00  --inst_sos_flag                         false
% 2.34/1.00  --inst_sos_phase                        true
% 2.34/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.34/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.34/1.00  --inst_lit_sel_side                     num_symb
% 2.34/1.00  --inst_solver_per_active                1400
% 2.34/1.00  --inst_solver_calls_frac                1.
% 2.34/1.00  --inst_passive_queue_type               priority_queues
% 2.34/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.34/1.00  --inst_passive_queues_freq              [25;2]
% 2.34/1.00  --inst_dismatching                      true
% 2.34/1.00  --inst_eager_unprocessed_to_passive     true
% 2.34/1.00  --inst_prop_sim_given                   true
% 2.34/1.00  --inst_prop_sim_new                     false
% 2.34/1.00  --inst_subs_new                         false
% 2.34/1.00  --inst_eq_res_simp                      false
% 2.34/1.00  --inst_subs_given                       false
% 2.34/1.00  --inst_orphan_elimination               true
% 2.34/1.00  --inst_learning_loop_flag               true
% 2.34/1.00  --inst_learning_start                   3000
% 2.34/1.00  --inst_learning_factor                  2
% 2.34/1.00  --inst_start_prop_sim_after_learn       3
% 2.34/1.00  --inst_sel_renew                        solver
% 2.34/1.00  --inst_lit_activity_flag                true
% 2.34/1.00  --inst_restr_to_given                   false
% 2.34/1.00  --inst_activity_threshold               500
% 2.34/1.00  --inst_out_proof                        true
% 2.34/1.00  
% 2.34/1.00  ------ Resolution Options
% 2.34/1.00  
% 2.34/1.00  --resolution_flag                       true
% 2.34/1.00  --res_lit_sel                           adaptive
% 2.34/1.00  --res_lit_sel_side                      none
% 2.34/1.00  --res_ordering                          kbo
% 2.34/1.00  --res_to_prop_solver                    active
% 2.34/1.00  --res_prop_simpl_new                    false
% 2.34/1.00  --res_prop_simpl_given                  true
% 2.34/1.00  --res_passive_queue_type                priority_queues
% 2.34/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.34/1.00  --res_passive_queues_freq               [15;5]
% 2.34/1.00  --res_forward_subs                      full
% 2.34/1.00  --res_backward_subs                     full
% 2.34/1.00  --res_forward_subs_resolution           true
% 2.34/1.00  --res_backward_subs_resolution          true
% 2.34/1.00  --res_orphan_elimination                true
% 2.34/1.00  --res_time_limit                        2.
% 2.34/1.00  --res_out_proof                         true
% 2.34/1.00  
% 2.34/1.00  ------ Superposition Options
% 2.34/1.00  
% 2.34/1.00  --superposition_flag                    true
% 2.34/1.00  --sup_passive_queue_type                priority_queues
% 2.34/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.34/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.34/1.00  --demod_completeness_check              fast
% 2.34/1.00  --demod_use_ground                      true
% 2.34/1.00  --sup_to_prop_solver                    passive
% 2.34/1.00  --sup_prop_simpl_new                    true
% 2.34/1.00  --sup_prop_simpl_given                  true
% 2.34/1.00  --sup_fun_splitting                     false
% 2.34/1.00  --sup_smt_interval                      50000
% 2.34/1.00  
% 2.34/1.00  ------ Superposition Simplification Setup
% 2.34/1.00  
% 2.34/1.00  --sup_indices_passive                   []
% 2.34/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.34/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.34/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.34/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.34/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.34/1.00  --sup_full_bw                           [BwDemod]
% 2.34/1.00  --sup_immed_triv                        [TrivRules]
% 2.34/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.34/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.34/1.00  --sup_immed_bw_main                     []
% 2.34/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.34/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.34/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.34/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.34/1.00  
% 2.34/1.00  ------ Combination Options
% 2.34/1.00  
% 2.34/1.00  --comb_res_mult                         3
% 2.34/1.00  --comb_sup_mult                         2
% 2.34/1.00  --comb_inst_mult                        10
% 2.34/1.00  
% 2.34/1.00  ------ Debug Options
% 2.34/1.00  
% 2.34/1.00  --dbg_backtrace                         false
% 2.34/1.00  --dbg_dump_prop_clauses                 false
% 2.34/1.00  --dbg_dump_prop_clauses_file            -
% 2.34/1.00  --dbg_out_stat                          false
% 2.34/1.00  ------ Parsing...
% 2.34/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.34/1.00  
% 2.34/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 9 0s  sf_e  pe_s  pe_e 
% 2.34/1.00  
% 2.34/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.34/1.00  
% 2.34/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.34/1.00  ------ Proving...
% 2.34/1.00  ------ Problem Properties 
% 2.34/1.00  
% 2.34/1.00  
% 2.34/1.00  clauses                                 18
% 2.34/1.00  conjectures                             1
% 2.34/1.00  EPR                                     0
% 2.34/1.00  Horn                                    12
% 2.34/1.00  unary                                   3
% 2.34/1.00  binary                                  3
% 2.34/1.00  lits                                    51
% 2.34/1.00  lits eq                                 5
% 2.34/1.00  fd_pure                                 0
% 2.34/1.00  fd_pseudo                               0
% 2.34/1.00  fd_cond                                 4
% 2.34/1.00  fd_pseudo_cond                          0
% 2.34/1.00  AC symbols                              0
% 2.34/1.00  
% 2.34/1.00  ------ Schedule dynamic 5 is on 
% 2.34/1.00  
% 2.34/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.34/1.00  
% 2.34/1.00  
% 2.34/1.00  ------ 
% 2.34/1.00  Current options:
% 2.34/1.00  ------ 
% 2.34/1.00  
% 2.34/1.00  ------ Input Options
% 2.34/1.00  
% 2.34/1.00  --out_options                           all
% 2.34/1.00  --tptp_safe_out                         true
% 2.34/1.00  --problem_path                          ""
% 2.34/1.00  --include_path                          ""
% 2.34/1.00  --clausifier                            res/vclausify_rel
% 2.34/1.00  --clausifier_options                    --mode clausify
% 2.34/1.00  --stdin                                 false
% 2.34/1.00  --stats_out                             all
% 2.34/1.00  
% 2.34/1.00  ------ General Options
% 2.34/1.00  
% 2.34/1.00  --fof                                   false
% 2.34/1.00  --time_out_real                         305.
% 2.34/1.00  --time_out_virtual                      -1.
% 2.34/1.00  --symbol_type_check                     false
% 2.34/1.00  --clausify_out                          false
% 2.34/1.00  --sig_cnt_out                           false
% 2.34/1.00  --trig_cnt_out                          false
% 2.34/1.00  --trig_cnt_out_tolerance                1.
% 2.34/1.00  --trig_cnt_out_sk_spl                   false
% 2.34/1.00  --abstr_cl_out                          false
% 2.34/1.00  
% 2.34/1.00  ------ Global Options
% 2.34/1.00  
% 2.34/1.00  --schedule                              default
% 2.34/1.00  --add_important_lit                     false
% 2.34/1.00  --prop_solver_per_cl                    1000
% 2.34/1.00  --min_unsat_core                        false
% 2.34/1.00  --soft_assumptions                      false
% 2.34/1.00  --soft_lemma_size                       3
% 2.34/1.00  --prop_impl_unit_size                   0
% 2.34/1.00  --prop_impl_unit                        []
% 2.34/1.00  --share_sel_clauses                     true
% 2.34/1.00  --reset_solvers                         false
% 2.34/1.00  --bc_imp_inh                            [conj_cone]
% 2.34/1.00  --conj_cone_tolerance                   3.
% 2.34/1.00  --extra_neg_conj                        none
% 2.34/1.00  --large_theory_mode                     true
% 2.34/1.00  --prolific_symb_bound                   200
% 2.34/1.00  --lt_threshold                          2000
% 2.34/1.00  --clause_weak_htbl                      true
% 2.34/1.00  --gc_record_bc_elim                     false
% 2.34/1.00  
% 2.34/1.00  ------ Preprocessing Options
% 2.34/1.00  
% 2.34/1.00  --preprocessing_flag                    true
% 2.34/1.00  --time_out_prep_mult                    0.1
% 2.34/1.00  --splitting_mode                        input
% 2.34/1.00  --splitting_grd                         true
% 2.34/1.00  --splitting_cvd                         false
% 2.34/1.00  --splitting_cvd_svl                     false
% 2.34/1.00  --splitting_nvd                         32
% 2.34/1.00  --sub_typing                            true
% 2.34/1.00  --prep_gs_sim                           true
% 2.34/1.00  --prep_unflatten                        true
% 2.34/1.00  --prep_res_sim                          true
% 2.34/1.00  --prep_upred                            true
% 2.34/1.00  --prep_sem_filter                       exhaustive
% 2.34/1.00  --prep_sem_filter_out                   false
% 2.34/1.00  --pred_elim                             true
% 2.34/1.00  --res_sim_input                         true
% 2.34/1.00  --eq_ax_congr_red                       true
% 2.34/1.00  --pure_diseq_elim                       true
% 2.34/1.00  --brand_transform                       false
% 2.34/1.00  --non_eq_to_eq                          false
% 2.34/1.00  --prep_def_merge                        true
% 2.34/1.00  --prep_def_merge_prop_impl              false
% 2.34/1.00  --prep_def_merge_mbd                    true
% 2.34/1.00  --prep_def_merge_tr_red                 false
% 2.34/1.00  --prep_def_merge_tr_cl                  false
% 2.34/1.00  --smt_preprocessing                     true
% 2.34/1.00  --smt_ac_axioms                         fast
% 2.34/1.00  --preprocessed_out                      false
% 2.34/1.00  --preprocessed_stats                    false
% 2.34/1.00  
% 2.34/1.00  ------ Abstraction refinement Options
% 2.34/1.00  
% 2.34/1.00  --abstr_ref                             []
% 2.34/1.00  --abstr_ref_prep                        false
% 2.34/1.00  --abstr_ref_until_sat                   false
% 2.34/1.00  --abstr_ref_sig_restrict                funpre
% 2.34/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.34/1.00  --abstr_ref_under                       []
% 2.34/1.00  
% 2.34/1.00  ------ SAT Options
% 2.34/1.00  
% 2.34/1.00  --sat_mode                              false
% 2.34/1.00  --sat_fm_restart_options                ""
% 2.34/1.00  --sat_gr_def                            false
% 2.34/1.00  --sat_epr_types                         true
% 2.34/1.00  --sat_non_cyclic_types                  false
% 2.34/1.00  --sat_finite_models                     false
% 2.34/1.00  --sat_fm_lemmas                         false
% 2.34/1.00  --sat_fm_prep                           false
% 2.34/1.00  --sat_fm_uc_incr                        true
% 2.34/1.00  --sat_out_model                         small
% 2.34/1.00  --sat_out_clauses                       false
% 2.34/1.00  
% 2.34/1.00  ------ QBF Options
% 2.34/1.00  
% 2.34/1.00  --qbf_mode                              false
% 2.34/1.00  --qbf_elim_univ                         false
% 2.34/1.00  --qbf_dom_inst                          none
% 2.34/1.00  --qbf_dom_pre_inst                      false
% 2.34/1.00  --qbf_sk_in                             false
% 2.34/1.00  --qbf_pred_elim                         true
% 2.34/1.00  --qbf_split                             512
% 2.34/1.00  
% 2.34/1.00  ------ BMC1 Options
% 2.34/1.00  
% 2.34/1.00  --bmc1_incremental                      false
% 2.34/1.00  --bmc1_axioms                           reachable_all
% 2.34/1.00  --bmc1_min_bound                        0
% 2.34/1.00  --bmc1_max_bound                        -1
% 2.34/1.00  --bmc1_max_bound_default                -1
% 2.34/1.00  --bmc1_symbol_reachability              true
% 2.34/1.00  --bmc1_property_lemmas                  false
% 2.34/1.00  --bmc1_k_induction                      false
% 2.34/1.00  --bmc1_non_equiv_states                 false
% 2.34/1.00  --bmc1_deadlock                         false
% 2.34/1.00  --bmc1_ucm                              false
% 2.34/1.00  --bmc1_add_unsat_core                   none
% 2.34/1.00  --bmc1_unsat_core_children              false
% 2.34/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.34/1.00  --bmc1_out_stat                         full
% 2.34/1.00  --bmc1_ground_init                      false
% 2.34/1.00  --bmc1_pre_inst_next_state              false
% 2.34/1.00  --bmc1_pre_inst_state                   false
% 2.34/1.00  --bmc1_pre_inst_reach_state             false
% 2.34/1.00  --bmc1_out_unsat_core                   false
% 2.34/1.00  --bmc1_aig_witness_out                  false
% 2.34/1.00  --bmc1_verbose                          false
% 2.34/1.00  --bmc1_dump_clauses_tptp                false
% 2.34/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.34/1.00  --bmc1_dump_file                        -
% 2.34/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.34/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.34/1.00  --bmc1_ucm_extend_mode                  1
% 2.34/1.00  --bmc1_ucm_init_mode                    2
% 2.34/1.00  --bmc1_ucm_cone_mode                    none
% 2.34/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.34/1.00  --bmc1_ucm_relax_model                  4
% 2.34/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.34/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.34/1.00  --bmc1_ucm_layered_model                none
% 2.34/1.00  --bmc1_ucm_max_lemma_size               10
% 2.34/1.00  
% 2.34/1.00  ------ AIG Options
% 2.34/1.00  
% 2.34/1.00  --aig_mode                              false
% 2.34/1.00  
% 2.34/1.00  ------ Instantiation Options
% 2.34/1.00  
% 2.34/1.00  --instantiation_flag                    true
% 2.34/1.00  --inst_sos_flag                         false
% 2.34/1.00  --inst_sos_phase                        true
% 2.34/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.34/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.34/1.00  --inst_lit_sel_side                     none
% 2.34/1.00  --inst_solver_per_active                1400
% 2.34/1.00  --inst_solver_calls_frac                1.
% 2.34/1.00  --inst_passive_queue_type               priority_queues
% 2.34/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.34/1.00  --inst_passive_queues_freq              [25;2]
% 2.34/1.00  --inst_dismatching                      true
% 2.34/1.00  --inst_eager_unprocessed_to_passive     true
% 2.34/1.00  --inst_prop_sim_given                   true
% 2.34/1.00  --inst_prop_sim_new                     false
% 2.34/1.00  --inst_subs_new                         false
% 2.34/1.00  --inst_eq_res_simp                      false
% 2.34/1.00  --inst_subs_given                       false
% 2.34/1.00  --inst_orphan_elimination               true
% 2.34/1.00  --inst_learning_loop_flag               true
% 2.34/1.00  --inst_learning_start                   3000
% 2.34/1.00  --inst_learning_factor                  2
% 2.34/1.00  --inst_start_prop_sim_after_learn       3
% 2.34/1.00  --inst_sel_renew                        solver
% 2.34/1.00  --inst_lit_activity_flag                true
% 2.34/1.00  --inst_restr_to_given                   false
% 2.34/1.00  --inst_activity_threshold               500
% 2.34/1.00  --inst_out_proof                        true
% 2.34/1.00  
% 2.34/1.00  ------ Resolution Options
% 2.34/1.00  
% 2.34/1.00  --resolution_flag                       false
% 2.34/1.00  --res_lit_sel                           adaptive
% 2.34/1.00  --res_lit_sel_side                      none
% 2.34/1.00  --res_ordering                          kbo
% 2.34/1.00  --res_to_prop_solver                    active
% 2.34/1.00  --res_prop_simpl_new                    false
% 2.34/1.00  --res_prop_simpl_given                  true
% 2.34/1.00  --res_passive_queue_type                priority_queues
% 2.34/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.34/1.00  --res_passive_queues_freq               [15;5]
% 2.34/1.00  --res_forward_subs                      full
% 2.34/1.00  --res_backward_subs                     full
% 2.34/1.00  --res_forward_subs_resolution           true
% 2.34/1.00  --res_backward_subs_resolution          true
% 2.34/1.00  --res_orphan_elimination                true
% 2.34/1.00  --res_time_limit                        2.
% 2.34/1.00  --res_out_proof                         true
% 2.34/1.00  
% 2.34/1.00  ------ Superposition Options
% 2.34/1.00  
% 2.34/1.00  --superposition_flag                    true
% 2.34/1.00  --sup_passive_queue_type                priority_queues
% 2.34/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.34/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.34/1.00  --demod_completeness_check              fast
% 2.34/1.00  --demod_use_ground                      true
% 2.34/1.00  --sup_to_prop_solver                    passive
% 2.34/1.00  --sup_prop_simpl_new                    true
% 2.34/1.00  --sup_prop_simpl_given                  true
% 2.34/1.00  --sup_fun_splitting                     false
% 2.34/1.00  --sup_smt_interval                      50000
% 2.34/1.00  
% 2.34/1.00  ------ Superposition Simplification Setup
% 2.34/1.00  
% 2.34/1.00  --sup_indices_passive                   []
% 2.34/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.34/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.34/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.34/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.34/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.34/1.00  --sup_full_bw                           [BwDemod]
% 2.34/1.00  --sup_immed_triv                        [TrivRules]
% 2.34/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.34/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.34/1.00  --sup_immed_bw_main                     []
% 2.34/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.34/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.34/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.34/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.34/1.00  
% 2.34/1.00  ------ Combination Options
% 2.34/1.00  
% 2.34/1.00  --comb_res_mult                         3
% 2.34/1.00  --comb_sup_mult                         2
% 2.34/1.00  --comb_inst_mult                        10
% 2.34/1.00  
% 2.34/1.00  ------ Debug Options
% 2.34/1.00  
% 2.34/1.00  --dbg_backtrace                         false
% 2.34/1.00  --dbg_dump_prop_clauses                 false
% 2.34/1.00  --dbg_dump_prop_clauses_file            -
% 2.34/1.00  --dbg_out_stat                          false
% 2.34/1.00  
% 2.34/1.00  
% 2.34/1.00  
% 2.34/1.00  
% 2.34/1.00  ------ Proving...
% 2.34/1.00  
% 2.34/1.00  
% 2.34/1.00  % SZS status Theorem for theBenchmark.p
% 2.34/1.00  
% 2.34/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.34/1.00  
% 2.34/1.00  fof(f8,axiom,(
% 2.34/1.00    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.34/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.34/1.00  
% 2.34/1.00  fof(f23,plain,(
% 2.34/1.00    ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.34/1.00    inference(ennf_transformation,[],[f8])).
% 2.34/1.00  
% 2.34/1.00  fof(f24,plain,(
% 2.34/1.00    ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.34/1.00    inference(flattening,[],[f23])).
% 2.34/1.00  
% 2.34/1.00  fof(f63,plain,(
% 2.34/1.00    ( ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.34/1.00    inference(cnf_transformation,[],[f24])).
% 2.34/1.00  
% 2.34/1.00  fof(f10,conjecture,(
% 2.34/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v1_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1))))),
% 2.34/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.34/1.00  
% 2.34/1.00  fof(f11,negated_conjecture,(
% 2.34/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v1_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1))))),
% 2.34/1.00    inference(negated_conjecture,[],[f10])).
% 2.34/1.00  
% 2.34/1.00  fof(f27,plain,(
% 2.34/1.00    ? [X0] : (? [X1] : (~r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1)) & (l1_waybel_0(X1,X0) & v1_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.34/1.00    inference(ennf_transformation,[],[f11])).
% 2.34/1.00  
% 2.34/1.00  fof(f28,plain,(
% 2.34/1.00    ? [X0] : (? [X1] : (~r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1)) & l1_waybel_0(X1,X0) & v1_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.34/1.00    inference(flattening,[],[f27])).
% 2.34/1.00  
% 2.34/1.00  fof(f44,plain,(
% 2.34/1.00    ( ! [X0] : (? [X1] : (~r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1)) & l1_waybel_0(X1,X0) & v1_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (~r2_hidden(k4_yellow_6(X0,sK7),k10_yellow_6(X0,sK7)) & l1_waybel_0(sK7,X0) & v1_yellow_6(sK7,X0) & v7_waybel_0(sK7) & v4_orders_2(sK7) & ~v2_struct_0(sK7))) )),
% 2.34/1.00    introduced(choice_axiom,[])).
% 2.34/1.00  
% 2.34/1.00  fof(f43,plain,(
% 2.34/1.00    ? [X0] : (? [X1] : (~r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1)) & l1_waybel_0(X1,X0) & v1_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (~r2_hidden(k4_yellow_6(sK6,X1),k10_yellow_6(sK6,X1)) & l1_waybel_0(X1,sK6) & v1_yellow_6(X1,sK6) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK6) & v2_pre_topc(sK6) & ~v2_struct_0(sK6))),
% 2.34/1.00    introduced(choice_axiom,[])).
% 2.34/1.00  
% 2.34/1.00  fof(f45,plain,(
% 2.34/1.00    (~r2_hidden(k4_yellow_6(sK6,sK7),k10_yellow_6(sK6,sK7)) & l1_waybel_0(sK7,sK6) & v1_yellow_6(sK7,sK6) & v7_waybel_0(sK7) & v4_orders_2(sK7) & ~v2_struct_0(sK7)) & l1_pre_topc(sK6) & v2_pre_topc(sK6) & ~v2_struct_0(sK6)),
% 2.34/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f28,f44,f43])).
% 2.34/1.00  
% 2.34/1.00  fof(f70,plain,(
% 2.34/1.00    v7_waybel_0(sK7)),
% 2.34/1.00    inference(cnf_transformation,[],[f45])).
% 2.34/1.00  
% 2.34/1.00  fof(f68,plain,(
% 2.34/1.00    ~v2_struct_0(sK7)),
% 2.34/1.00    inference(cnf_transformation,[],[f45])).
% 2.34/1.00  
% 2.34/1.00  fof(f69,plain,(
% 2.34/1.00    v4_orders_2(sK7)),
% 2.34/1.00    inference(cnf_transformation,[],[f45])).
% 2.34/1.00  
% 2.34/1.00  fof(f7,axiom,(
% 2.34/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (k10_yellow_6(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) <=> ! [X4] : (m1_connsp_2(X4,X0,X3) => r1_waybel_0(X0,X1,X4))))))))),
% 2.34/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.34/1.00  
% 2.34/1.00  fof(f21,plain,(
% 2.34/1.00    ! [X0] : (! [X1] : (! [X2] : ((k10_yellow_6(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3))) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.34/1.00    inference(ennf_transformation,[],[f7])).
% 2.34/1.00  
% 2.34/1.00  fof(f22,plain,(
% 2.34/1.00    ! [X0] : (! [X1] : (! [X2] : ((k10_yellow_6(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3))) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.34/1.00    inference(flattening,[],[f21])).
% 2.34/1.00  
% 2.34/1.00  fof(f36,plain,(
% 2.34/1.00    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | ? [X3] : (((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | r2_hidden(X3,X2))) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3))) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.34/1.00    inference(nnf_transformation,[],[f22])).
% 2.34/1.00  
% 2.34/1.00  fof(f37,plain,(
% 2.34/1.00    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | ? [X3] : ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | r2_hidden(X3,X2)) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3))) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.34/1.00    inference(flattening,[],[f36])).
% 2.34/1.00  
% 2.34/1.00  fof(f38,plain,(
% 2.34/1.00    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | ? [X3] : ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,X3)) | r2_hidden(X3,X2)) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X6] : (((r2_hidden(X6,X2) | ? [X7] : (~r1_waybel_0(X0,X1,X7) & m1_connsp_2(X7,X0,X6))) & (! [X8] : (r1_waybel_0(X0,X1,X8) | ~m1_connsp_2(X8,X0,X6)) | ~r2_hidden(X6,X2))) | ~m1_subset_1(X6,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.34/1.00    inference(rectify,[],[f37])).
% 2.34/1.00  
% 2.34/1.00  fof(f41,plain,(
% 2.34/1.00    ! [X6,X1,X0] : (? [X7] : (~r1_waybel_0(X0,X1,X7) & m1_connsp_2(X7,X0,X6)) => (~r1_waybel_0(X0,X1,sK5(X0,X1,X6)) & m1_connsp_2(sK5(X0,X1,X6),X0,X6)))),
% 2.34/1.00    introduced(choice_axiom,[])).
% 2.34/1.00  
% 2.34/1.00  fof(f40,plain,(
% 2.34/1.00    ( ! [X3] : (! [X2,X1,X0] : (? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) => (~r1_waybel_0(X0,X1,sK4(X0,X1,X2)) & m1_connsp_2(sK4(X0,X1,X2),X0,X3)))) )),
% 2.34/1.00    introduced(choice_axiom,[])).
% 2.34/1.00  
% 2.34/1.00  fof(f39,plain,(
% 2.34/1.00    ! [X2,X1,X0] : (? [X3] : ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,X3)) | r2_hidden(X3,X2)) & m1_subset_1(X3,u1_struct_0(X0))) => ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,sK3(X0,X1,X2))) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,sK3(X0,X1,X2))) | r2_hidden(sK3(X0,X1,X2),X2)) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))))),
% 2.34/1.00    introduced(choice_axiom,[])).
% 2.34/1.00  
% 2.34/1.00  fof(f42,plain,(
% 2.34/1.00    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | (((~r1_waybel_0(X0,X1,sK4(X0,X1,X2)) & m1_connsp_2(sK4(X0,X1,X2),X0,sK3(X0,X1,X2))) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,sK3(X0,X1,X2))) | r2_hidden(sK3(X0,X1,X2),X2)) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)))) & (! [X6] : (((r2_hidden(X6,X2) | (~r1_waybel_0(X0,X1,sK5(X0,X1,X6)) & m1_connsp_2(sK5(X0,X1,X6),X0,X6))) & (! [X8] : (r1_waybel_0(X0,X1,X8) | ~m1_connsp_2(X8,X0,X6)) | ~r2_hidden(X6,X2))) | ~m1_subset_1(X6,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.34/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f38,f41,f40,f39])).
% 2.34/1.00  
% 2.34/1.00  fof(f57,plain,(
% 2.34/1.00    ( ! [X6,X2,X0,X1] : (r2_hidden(X6,X2) | m1_connsp_2(sK5(X0,X1,X6),X0,X6) | ~m1_subset_1(X6,u1_struct_0(X0)) | k10_yellow_6(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.34/1.00    inference(cnf_transformation,[],[f42])).
% 2.34/1.00  
% 2.34/1.00  fof(f75,plain,(
% 2.34/1.00    ( ! [X6,X0,X1] : (r2_hidden(X6,k10_yellow_6(X0,X1)) | m1_connsp_2(sK5(X0,X1,X6),X0,X6) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.34/1.00    inference(equality_resolution,[],[f57])).
% 2.34/1.00  
% 2.34/1.00  fof(f66,plain,(
% 2.34/1.00    v2_pre_topc(sK6)),
% 2.34/1.00    inference(cnf_transformation,[],[f45])).
% 2.34/1.00  
% 2.34/1.00  fof(f65,plain,(
% 2.34/1.00    ~v2_struct_0(sK6)),
% 2.34/1.00    inference(cnf_transformation,[],[f45])).
% 2.34/1.00  
% 2.34/1.00  fof(f67,plain,(
% 2.34/1.00    l1_pre_topc(sK6)),
% 2.34/1.00    inference(cnf_transformation,[],[f45])).
% 2.34/1.00  
% 2.34/1.00  fof(f72,plain,(
% 2.34/1.00    l1_waybel_0(sK7,sK6)),
% 2.34/1.00    inference(cnf_transformation,[],[f45])).
% 2.34/1.00  
% 2.34/1.00  fof(f4,axiom,(
% 2.34/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (m1_connsp_2(X1,X0,X2) => r2_hidden(X2,X1)))))),
% 2.34/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.34/1.00  
% 2.34/1.00  fof(f15,plain,(
% 2.34/1.00    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.34/1.00    inference(ennf_transformation,[],[f4])).
% 2.34/1.00  
% 2.34/1.00  fof(f16,plain,(
% 2.34/1.00    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.34/1.00    inference(flattening,[],[f15])).
% 2.34/1.00  
% 2.34/1.00  fof(f49,plain,(
% 2.34/1.00    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.34/1.00    inference(cnf_transformation,[],[f16])).
% 2.34/1.00  
% 2.34/1.00  fof(f3,axiom,(
% 2.34/1.00    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.34/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.34/1.00  
% 2.34/1.00  fof(f13,plain,(
% 2.34/1.00    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.34/1.00    inference(ennf_transformation,[],[f3])).
% 2.34/1.00  
% 2.34/1.00  fof(f14,plain,(
% 2.34/1.00    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.34/1.00    inference(flattening,[],[f13])).
% 2.34/1.00  
% 2.34/1.00  fof(f48,plain,(
% 2.34/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.34/1.00    inference(cnf_transformation,[],[f14])).
% 2.34/1.00  
% 2.34/1.00  fof(f1,axiom,(
% 2.34/1.00    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 2.34/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.34/1.00  
% 2.34/1.00  fof(f29,plain,(
% 2.34/1.00    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK0(X0),X0))),
% 2.34/1.00    introduced(choice_axiom,[])).
% 2.34/1.00  
% 2.34/1.00  fof(f30,plain,(
% 2.34/1.00    ! [X0] : m1_subset_1(sK0(X0),X0)),
% 2.34/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f1,f29])).
% 2.34/1.00  
% 2.34/1.00  fof(f46,plain,(
% 2.34/1.00    ( ! [X0] : (m1_subset_1(sK0(X0),X0)) )),
% 2.34/1.00    inference(cnf_transformation,[],[f30])).
% 2.34/1.00  
% 2.34/1.00  fof(f2,axiom,(
% 2.34/1.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.34/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.34/1.00  
% 2.34/1.00  fof(f12,plain,(
% 2.34/1.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.34/1.00    inference(ennf_transformation,[],[f2])).
% 2.34/1.00  
% 2.34/1.00  fof(f47,plain,(
% 2.34/1.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.34/1.00    inference(cnf_transformation,[],[f12])).
% 2.34/1.00  
% 2.34/1.00  fof(f5,axiom,(
% 2.34/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r1_waybel_0(X0,X1,X2) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r1_orders_2(X1,X3,X4) => r2_hidden(k2_waybel_0(X0,X1,X4),X2))) & m1_subset_1(X3,u1_struct_0(X1))))))),
% 2.34/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.34/1.00  
% 2.34/1.00  fof(f17,plain,(
% 2.34/1.00    ! [X0] : (! [X1] : (! [X2] : (r1_waybel_0(X0,X1,X2) <=> ? [X3] : (! [X4] : ((r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4)) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.34/1.00    inference(ennf_transformation,[],[f5])).
% 2.34/1.00  
% 2.34/1.00  fof(f18,plain,(
% 2.34/1.00    ! [X0] : (! [X1] : (! [X2] : (r1_waybel_0(X0,X1,X2) <=> ? [X3] : (! [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.34/1.00    inference(flattening,[],[f17])).
% 2.34/1.00  
% 2.34/1.00  fof(f31,plain,(
% 2.34/1.00    ! [X0] : (! [X1] : (! [X2] : ((r1_waybel_0(X0,X1,X2) | ! [X3] : (? [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) | ~r1_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.34/1.00    inference(nnf_transformation,[],[f18])).
% 2.34/1.00  
% 2.34/1.00  fof(f32,plain,(
% 2.34/1.00    ! [X0] : (! [X1] : (! [X2] : ((r1_waybel_0(X0,X1,X2) | ! [X3] : (? [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (! [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) | ~r1_orders_2(X1,X5,X6) | ~m1_subset_1(X6,u1_struct_0(X1))) & m1_subset_1(X5,u1_struct_0(X1))) | ~r1_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.34/1.00    inference(rectify,[],[f31])).
% 2.34/1.00  
% 2.34/1.00  fof(f34,plain,(
% 2.34/1.00    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) | ~r1_orders_2(X1,X5,X6) | ~m1_subset_1(X6,u1_struct_0(X1))) & m1_subset_1(X5,u1_struct_0(X1))) => (! [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) | ~r1_orders_2(X1,sK2(X0,X1,X2),X6) | ~m1_subset_1(X6,u1_struct_0(X1))) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))))),
% 2.34/1.00    introduced(choice_axiom,[])).
% 2.34/1.00  
% 2.34/1.00  fof(f33,plain,(
% 2.34/1.00    ! [X3,X2,X1,X0] : (? [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) => (~r2_hidden(k2_waybel_0(X0,X1,sK1(X0,X1,X2,X3)),X2) & r1_orders_2(X1,X3,sK1(X0,X1,X2,X3)) & m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X1))))),
% 2.34/1.00    introduced(choice_axiom,[])).
% 2.34/1.00  
% 2.34/1.00  fof(f35,plain,(
% 2.34/1.00    ! [X0] : (! [X1] : (! [X2] : ((r1_waybel_0(X0,X1,X2) | ! [X3] : ((~r2_hidden(k2_waybel_0(X0,X1,sK1(X0,X1,X2,X3)),X2) & r1_orders_2(X1,X3,sK1(X0,X1,X2,X3)) & m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((! [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) | ~r1_orders_2(X1,sK2(X0,X1,X2),X6) | ~m1_subset_1(X6,u1_struct_0(X1))) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))) | ~r1_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.34/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f32,f34,f33])).
% 2.34/1.00  
% 2.34/1.00  fof(f52,plain,(
% 2.34/1.00    ( ! [X2,X0,X3,X1] : (r1_waybel_0(X0,X1,X2) | m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.34/1.00    inference(cnf_transformation,[],[f35])).
% 2.34/1.00  
% 2.34/1.00  fof(f9,axiom,(
% 2.34/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v1_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => k2_waybel_0(X0,X1,X2) = k4_yellow_6(X0,X1))))),
% 2.34/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.34/1.00  
% 2.34/1.00  fof(f25,plain,(
% 2.34/1.00    ! [X0] : (! [X1] : (! [X2] : (k2_waybel_0(X0,X1,X2) = k4_yellow_6(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~l1_waybel_0(X1,X0) | ~v1_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.34/1.00    inference(ennf_transformation,[],[f9])).
% 2.34/1.00  
% 2.34/1.00  fof(f26,plain,(
% 2.34/1.00    ! [X0] : (! [X1] : (! [X2] : (k2_waybel_0(X0,X1,X2) = k4_yellow_6(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~l1_waybel_0(X1,X0) | ~v1_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.34/1.00    inference(flattening,[],[f25])).
% 2.34/1.00  
% 2.34/1.00  fof(f64,plain,(
% 2.34/1.00    ( ! [X2,X0,X1] : (k2_waybel_0(X0,X1,X2) = k4_yellow_6(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | ~v1_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.34/1.00    inference(cnf_transformation,[],[f26])).
% 2.34/1.00  
% 2.34/1.00  fof(f71,plain,(
% 2.34/1.00    v1_yellow_6(sK7,sK6)),
% 2.34/1.00    inference(cnf_transformation,[],[f45])).
% 2.34/1.00  
% 2.34/1.00  fof(f58,plain,(
% 2.34/1.00    ( ! [X6,X2,X0,X1] : (r2_hidden(X6,X2) | ~r1_waybel_0(X0,X1,sK5(X0,X1,X6)) | ~m1_subset_1(X6,u1_struct_0(X0)) | k10_yellow_6(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.34/1.00    inference(cnf_transformation,[],[f42])).
% 2.34/1.00  
% 2.34/1.00  fof(f74,plain,(
% 2.34/1.00    ( ! [X6,X0,X1] : (r2_hidden(X6,k10_yellow_6(X0,X1)) | ~r1_waybel_0(X0,X1,sK5(X0,X1,X6)) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.34/1.00    inference(equality_resolution,[],[f58])).
% 2.34/1.00  
% 2.34/1.00  fof(f73,plain,(
% 2.34/1.00    ~r2_hidden(k4_yellow_6(sK6,sK7),k10_yellow_6(sK6,sK7))),
% 2.34/1.00    inference(cnf_transformation,[],[f45])).
% 2.34/1.00  
% 2.34/1.00  fof(f6,axiom,(
% 2.34/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X1)) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0)))),
% 2.34/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.34/1.00  
% 2.34/1.00  fof(f19,plain,(
% 2.34/1.00    ! [X0,X1,X2] : (m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.34/1.00    inference(ennf_transformation,[],[f6])).
% 2.34/1.00  
% 2.34/1.00  fof(f20,plain,(
% 2.34/1.00    ! [X0,X1,X2] : (m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.34/1.00    inference(flattening,[],[f19])).
% 2.34/1.00  
% 2.34/1.00  fof(f55,plain,(
% 2.34/1.00    ( ! [X2,X0,X1] : (m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.34/1.00    inference(cnf_transformation,[],[f20])).
% 2.34/1.00  
% 2.34/1.00  fof(f54,plain,(
% 2.34/1.00    ( ! [X2,X0,X3,X1] : (r1_waybel_0(X0,X1,X2) | ~r2_hidden(k2_waybel_0(X0,X1,sK1(X0,X1,X2,X3)),X2) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.34/1.00    inference(cnf_transformation,[],[f35])).
% 2.34/1.00  
% 2.34/1.00  cnf(c_17,plain,
% 2.34/1.00      ( ~ l1_waybel_0(X0,X1)
% 2.34/1.00      | m1_subset_1(k10_yellow_6(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.34/1.00      | ~ v4_orders_2(X0)
% 2.34/1.00      | ~ v7_waybel_0(X0)
% 2.34/1.00      | v2_struct_0(X1)
% 2.34/1.00      | v2_struct_0(X0)
% 2.34/1.00      | ~ v2_pre_topc(X1)
% 2.34/1.00      | ~ l1_pre_topc(X1) ),
% 2.34/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_22,negated_conjecture,
% 2.34/1.00      ( v7_waybel_0(sK7) ),
% 2.34/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_844,plain,
% 2.34/1.00      ( ~ l1_waybel_0(X0,X1)
% 2.34/1.00      | m1_subset_1(k10_yellow_6(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.34/1.00      | ~ v4_orders_2(X0)
% 2.34/1.00      | v2_struct_0(X0)
% 2.34/1.00      | v2_struct_0(X1)
% 2.34/1.00      | ~ v2_pre_topc(X1)
% 2.34/1.00      | ~ l1_pre_topc(X1)
% 2.34/1.00      | sK7 != X0 ),
% 2.34/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_22]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_845,plain,
% 2.34/1.00      ( ~ l1_waybel_0(sK7,X0)
% 2.34/1.00      | m1_subset_1(k10_yellow_6(X0,sK7),k1_zfmisc_1(u1_struct_0(X0)))
% 2.34/1.00      | ~ v4_orders_2(sK7)
% 2.34/1.00      | v2_struct_0(X0)
% 2.34/1.00      | v2_struct_0(sK7)
% 2.34/1.00      | ~ v2_pre_topc(X0)
% 2.34/1.00      | ~ l1_pre_topc(X0) ),
% 2.34/1.00      inference(unflattening,[status(thm)],[c_844]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_24,negated_conjecture,
% 2.34/1.00      ( ~ v2_struct_0(sK7) ),
% 2.34/1.00      inference(cnf_transformation,[],[f68]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_23,negated_conjecture,
% 2.34/1.00      ( v4_orders_2(sK7) ),
% 2.34/1.00      inference(cnf_transformation,[],[f69]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_849,plain,
% 2.34/1.00      ( v2_struct_0(X0)
% 2.34/1.00      | ~ l1_waybel_0(sK7,X0)
% 2.34/1.00      | m1_subset_1(k10_yellow_6(X0,sK7),k1_zfmisc_1(u1_struct_0(X0)))
% 2.34/1.00      | ~ v2_pre_topc(X0)
% 2.34/1.00      | ~ l1_pre_topc(X0) ),
% 2.34/1.00      inference(global_propositional_subsumption,
% 2.34/1.00                [status(thm)],
% 2.34/1.00                [c_845,c_24,c_23]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_850,plain,
% 2.34/1.00      ( ~ l1_waybel_0(sK7,X0)
% 2.34/1.00      | m1_subset_1(k10_yellow_6(X0,sK7),k1_zfmisc_1(u1_struct_0(X0)))
% 2.34/1.00      | v2_struct_0(X0)
% 2.34/1.00      | ~ v2_pre_topc(X0)
% 2.34/1.00      | ~ l1_pre_topc(X0) ),
% 2.34/1.00      inference(renaming,[status(thm)],[c_849]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_15,plain,
% 2.34/1.00      ( m1_connsp_2(sK5(X0,X1,X2),X0,X2)
% 2.34/1.00      | ~ l1_waybel_0(X1,X0)
% 2.34/1.00      | r2_hidden(X2,k10_yellow_6(X0,X1))
% 2.34/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.34/1.00      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 2.34/1.00      | ~ v4_orders_2(X1)
% 2.34/1.00      | ~ v7_waybel_0(X1)
% 2.34/1.00      | v2_struct_0(X0)
% 2.34/1.00      | v2_struct_0(X1)
% 2.34/1.00      | ~ v2_pre_topc(X0)
% 2.34/1.00      | ~ l1_pre_topc(X0) ),
% 2.34/1.00      inference(cnf_transformation,[],[f75]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_661,plain,
% 2.34/1.00      ( m1_connsp_2(sK5(X0,X1,X2),X0,X2)
% 2.34/1.00      | ~ l1_waybel_0(X1,X0)
% 2.34/1.00      | r2_hidden(X2,k10_yellow_6(X0,X1))
% 2.34/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.34/1.00      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 2.34/1.00      | ~ v4_orders_2(X1)
% 2.34/1.00      | v2_struct_0(X0)
% 2.34/1.00      | v2_struct_0(X1)
% 2.34/1.00      | ~ v2_pre_topc(X0)
% 2.34/1.00      | ~ l1_pre_topc(X0)
% 2.34/1.00      | sK7 != X1 ),
% 2.34/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_22]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_662,plain,
% 2.34/1.00      ( m1_connsp_2(sK5(X0,sK7,X1),X0,X1)
% 2.34/1.00      | ~ l1_waybel_0(sK7,X0)
% 2.34/1.00      | r2_hidden(X1,k10_yellow_6(X0,sK7))
% 2.34/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.34/1.00      | ~ m1_subset_1(k10_yellow_6(X0,sK7),k1_zfmisc_1(u1_struct_0(X0)))
% 2.34/1.00      | ~ v4_orders_2(sK7)
% 2.34/1.00      | v2_struct_0(X0)
% 2.34/1.00      | v2_struct_0(sK7)
% 2.34/1.00      | ~ v2_pre_topc(X0)
% 2.34/1.00      | ~ l1_pre_topc(X0) ),
% 2.34/1.00      inference(unflattening,[status(thm)],[c_661]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_666,plain,
% 2.34/1.00      ( v2_struct_0(X0)
% 2.34/1.00      | m1_connsp_2(sK5(X0,sK7,X1),X0,X1)
% 2.34/1.00      | ~ l1_waybel_0(sK7,X0)
% 2.34/1.00      | r2_hidden(X1,k10_yellow_6(X0,sK7))
% 2.34/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.34/1.00      | ~ m1_subset_1(k10_yellow_6(X0,sK7),k1_zfmisc_1(u1_struct_0(X0)))
% 2.34/1.00      | ~ v2_pre_topc(X0)
% 2.34/1.00      | ~ l1_pre_topc(X0) ),
% 2.34/1.00      inference(global_propositional_subsumption,
% 2.34/1.00                [status(thm)],
% 2.34/1.00                [c_662,c_24,c_23]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_667,plain,
% 2.34/1.00      ( m1_connsp_2(sK5(X0,sK7,X1),X0,X1)
% 2.34/1.00      | ~ l1_waybel_0(sK7,X0)
% 2.34/1.00      | r2_hidden(X1,k10_yellow_6(X0,sK7))
% 2.34/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.34/1.00      | ~ m1_subset_1(k10_yellow_6(X0,sK7),k1_zfmisc_1(u1_struct_0(X0)))
% 2.34/1.00      | v2_struct_0(X0)
% 2.34/1.00      | ~ v2_pre_topc(X0)
% 2.34/1.00      | ~ l1_pre_topc(X0) ),
% 2.34/1.00      inference(renaming,[status(thm)],[c_666]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_868,plain,
% 2.34/1.00      ( m1_connsp_2(sK5(X0,sK7,X1),X0,X1)
% 2.34/1.00      | ~ l1_waybel_0(sK7,X0)
% 2.34/1.00      | r2_hidden(X1,k10_yellow_6(X0,sK7))
% 2.34/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.34/1.00      | v2_struct_0(X0)
% 2.34/1.00      | ~ v2_pre_topc(X0)
% 2.34/1.00      | ~ l1_pre_topc(X0) ),
% 2.34/1.00      inference(backward_subsumption_resolution,
% 2.34/1.00                [status(thm)],
% 2.34/1.00                [c_850,c_667]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_26,negated_conjecture,
% 2.34/1.00      ( v2_pre_topc(sK6) ),
% 2.34/1.00      inference(cnf_transformation,[],[f66]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_1025,plain,
% 2.34/1.00      ( m1_connsp_2(sK5(X0,sK7,X1),X0,X1)
% 2.34/1.00      | ~ l1_waybel_0(sK7,X0)
% 2.34/1.00      | r2_hidden(X1,k10_yellow_6(X0,sK7))
% 2.34/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.34/1.00      | v2_struct_0(X0)
% 2.34/1.00      | ~ l1_pre_topc(X0)
% 2.34/1.00      | sK6 != X0 ),
% 2.34/1.00      inference(resolution_lifted,[status(thm)],[c_868,c_26]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_1026,plain,
% 2.34/1.00      ( m1_connsp_2(sK5(sK6,sK7,X0),sK6,X0)
% 2.34/1.00      | ~ l1_waybel_0(sK7,sK6)
% 2.34/1.00      | r2_hidden(X0,k10_yellow_6(sK6,sK7))
% 2.34/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 2.34/1.00      | v2_struct_0(sK6)
% 2.34/1.00      | ~ l1_pre_topc(sK6) ),
% 2.34/1.00      inference(unflattening,[status(thm)],[c_1025]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_27,negated_conjecture,
% 2.34/1.00      ( ~ v2_struct_0(sK6) ),
% 2.34/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_25,negated_conjecture,
% 2.34/1.00      ( l1_pre_topc(sK6) ),
% 2.34/1.00      inference(cnf_transformation,[],[f67]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_20,negated_conjecture,
% 2.34/1.00      ( l1_waybel_0(sK7,sK6) ),
% 2.34/1.00      inference(cnf_transformation,[],[f72]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_1030,plain,
% 2.34/1.00      ( m1_connsp_2(sK5(sK6,sK7,X0),sK6,X0)
% 2.34/1.00      | r2_hidden(X0,k10_yellow_6(sK6,sK7))
% 2.34/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
% 2.34/1.00      inference(global_propositional_subsumption,
% 2.34/1.00                [status(thm)],
% 2.34/1.00                [c_1026,c_27,c_25,c_20]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_2872,plain,
% 2.34/1.00      ( m1_connsp_2(sK5(sK6,sK7,X0_55),sK6,X0_55)
% 2.34/1.00      | r2_hidden(X0_55,k10_yellow_6(sK6,sK7))
% 2.34/1.00      | ~ m1_subset_1(X0_55,u1_struct_0(sK6)) ),
% 2.34/1.00      inference(subtyping,[status(esa)],[c_1030]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_3240,plain,
% 2.34/1.00      ( m1_connsp_2(sK5(sK6,sK7,X0_55),sK6,X0_55) = iProver_top
% 2.34/1.00      | r2_hidden(X0_55,k10_yellow_6(sK6,sK7)) = iProver_top
% 2.34/1.00      | m1_subset_1(X0_55,u1_struct_0(sK6)) != iProver_top ),
% 2.34/1.00      inference(predicate_to_equality,[status(thm)],[c_2872]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_3,plain,
% 2.34/1.00      ( ~ m1_connsp_2(X0,X1,X2)
% 2.34/1.00      | r2_hidden(X2,X0)
% 2.34/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.34/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.34/1.00      | v2_struct_0(X1)
% 2.34/1.00      | ~ v2_pre_topc(X1)
% 2.34/1.00      | ~ l1_pre_topc(X1) ),
% 2.34/1.00      inference(cnf_transformation,[],[f49]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_2,plain,
% 2.34/1.00      ( ~ m1_connsp_2(X0,X1,X2)
% 2.34/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.34/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.34/1.00      | v2_struct_0(X1)
% 2.34/1.00      | ~ v2_pre_topc(X1)
% 2.34/1.00      | ~ l1_pre_topc(X1) ),
% 2.34/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_175,plain,
% 2.34/1.00      ( r2_hidden(X2,X0)
% 2.34/1.00      | ~ m1_connsp_2(X0,X1,X2)
% 2.34/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.34/1.00      | v2_struct_0(X1)
% 2.34/1.00      | ~ v2_pre_topc(X1)
% 2.34/1.00      | ~ l1_pre_topc(X1) ),
% 2.34/1.00      inference(global_propositional_subsumption,[status(thm)],[c_3,c_2]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_176,plain,
% 2.34/1.00      ( ~ m1_connsp_2(X0,X1,X2)
% 2.34/1.00      | r2_hidden(X2,X0)
% 2.34/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.34/1.00      | v2_struct_0(X1)
% 2.34/1.00      | ~ v2_pre_topc(X1)
% 2.34/1.00      | ~ l1_pre_topc(X1) ),
% 2.34/1.00      inference(renaming,[status(thm)],[c_175]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_1156,plain,
% 2.34/1.00      ( ~ m1_connsp_2(X0,X1,X2)
% 2.34/1.00      | r2_hidden(X2,X0)
% 2.34/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.34/1.00      | v2_struct_0(X1)
% 2.34/1.00      | ~ l1_pre_topc(X1)
% 2.34/1.00      | sK6 != X1 ),
% 2.34/1.00      inference(resolution_lifted,[status(thm)],[c_176,c_26]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_1157,plain,
% 2.34/1.00      ( ~ m1_connsp_2(X0,sK6,X1)
% 2.34/1.00      | r2_hidden(X1,X0)
% 2.34/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 2.34/1.00      | v2_struct_0(sK6)
% 2.34/1.00      | ~ l1_pre_topc(sK6) ),
% 2.34/1.00      inference(unflattening,[status(thm)],[c_1156]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_1161,plain,
% 2.34/1.00      ( ~ m1_connsp_2(X0,sK6,X1)
% 2.34/1.00      | r2_hidden(X1,X0)
% 2.34/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK6)) ),
% 2.34/1.00      inference(global_propositional_subsumption,
% 2.34/1.00                [status(thm)],
% 2.34/1.00                [c_1157,c_27,c_25]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_2866,plain,
% 2.34/1.00      ( ~ m1_connsp_2(X0_55,sK6,X1_55)
% 2.34/1.00      | r2_hidden(X1_55,X0_55)
% 2.34/1.00      | ~ m1_subset_1(X1_55,u1_struct_0(sK6)) ),
% 2.34/1.00      inference(subtyping,[status(esa)],[c_1161]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_3246,plain,
% 2.34/1.00      ( m1_connsp_2(X0_55,sK6,X1_55) != iProver_top
% 2.34/1.00      | r2_hidden(X1_55,X0_55) = iProver_top
% 2.34/1.00      | m1_subset_1(X1_55,u1_struct_0(sK6)) != iProver_top ),
% 2.34/1.00      inference(predicate_to_equality,[status(thm)],[c_2866]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_3695,plain,
% 2.34/1.00      ( r2_hidden(X0_55,sK5(sK6,sK7,X0_55)) = iProver_top
% 2.34/1.00      | r2_hidden(X0_55,k10_yellow_6(sK6,sK7)) = iProver_top
% 2.34/1.00      | m1_subset_1(X0_55,u1_struct_0(sK6)) != iProver_top ),
% 2.34/1.00      inference(superposition,[status(thm)],[c_3240,c_3246]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_0,plain,
% 2.34/1.00      ( m1_subset_1(sK0(X0),X0) ),
% 2.34/1.00      inference(cnf_transformation,[],[f46]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_2877,plain,
% 2.34/1.00      ( m1_subset_1(sK0(X0_56),X0_56) ),
% 2.34/1.00      inference(subtyping,[status(esa)],[c_0]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_3235,plain,
% 2.34/1.00      ( m1_subset_1(sK0(X0_56),X0_56) = iProver_top ),
% 2.34/1.00      inference(predicate_to_equality,[status(thm)],[c_2877]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_1,plain,
% 2.34/1.00      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.34/1.00      inference(cnf_transformation,[],[f47]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_6,plain,
% 2.34/1.00      ( r1_waybel_0(X0,X1,X2)
% 2.34/1.00      | ~ l1_waybel_0(X1,X0)
% 2.34/1.00      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 2.34/1.00      | m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X1))
% 2.34/1.00      | v2_struct_0(X0)
% 2.34/1.00      | v2_struct_0(X1)
% 2.34/1.00      | ~ l1_struct_0(X0) ),
% 2.34/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_401,plain,
% 2.34/1.00      ( r1_waybel_0(X0,X1,X2)
% 2.34/1.00      | ~ l1_waybel_0(X1,X0)
% 2.34/1.00      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 2.34/1.00      | m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X1))
% 2.34/1.00      | v2_struct_0(X0)
% 2.34/1.00      | v2_struct_0(X1)
% 2.34/1.00      | ~ l1_pre_topc(X0) ),
% 2.34/1.00      inference(resolution,[status(thm)],[c_1,c_6]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_1266,plain,
% 2.34/1.00      ( r1_waybel_0(X0,X1,X2)
% 2.34/1.00      | ~ l1_waybel_0(X1,X0)
% 2.34/1.00      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 2.34/1.00      | m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X1))
% 2.34/1.00      | v2_struct_0(X0)
% 2.34/1.00      | v2_struct_0(X1)
% 2.34/1.00      | sK6 != X0 ),
% 2.34/1.00      inference(resolution_lifted,[status(thm)],[c_401,c_25]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_1267,plain,
% 2.34/1.00      ( r1_waybel_0(sK6,X0,X1)
% 2.34/1.00      | ~ l1_waybel_0(X0,sK6)
% 2.34/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.34/1.00      | m1_subset_1(sK1(sK6,X0,X1,X2),u1_struct_0(X0))
% 2.34/1.00      | v2_struct_0(X0)
% 2.34/1.00      | v2_struct_0(sK6) ),
% 2.34/1.00      inference(unflattening,[status(thm)],[c_1266]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_1271,plain,
% 2.34/1.00      ( v2_struct_0(X0)
% 2.34/1.00      | m1_subset_1(sK1(sK6,X0,X1,X2),u1_struct_0(X0))
% 2.34/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.34/1.00      | ~ l1_waybel_0(X0,sK6)
% 2.34/1.00      | r1_waybel_0(sK6,X0,X1) ),
% 2.34/1.00      inference(global_propositional_subsumption,
% 2.34/1.00                [status(thm)],
% 2.34/1.00                [c_1267,c_27]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_1272,plain,
% 2.34/1.00      ( r1_waybel_0(sK6,X0,X1)
% 2.34/1.00      | ~ l1_waybel_0(X0,sK6)
% 2.34/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.34/1.00      | m1_subset_1(sK1(sK6,X0,X1,X2),u1_struct_0(X0))
% 2.34/1.00      | v2_struct_0(X0) ),
% 2.34/1.00      inference(renaming,[status(thm)],[c_1271]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_1512,plain,
% 2.34/1.00      ( r1_waybel_0(sK6,X0,X1)
% 2.34/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.34/1.00      | m1_subset_1(sK1(sK6,X0,X1,X2),u1_struct_0(X0))
% 2.34/1.00      | v2_struct_0(X0)
% 2.34/1.00      | sK7 != X0
% 2.34/1.00      | sK6 != sK6 ),
% 2.34/1.00      inference(resolution_lifted,[status(thm)],[c_20,c_1272]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_1513,plain,
% 2.34/1.00      ( r1_waybel_0(sK6,sK7,X0)
% 2.34/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 2.34/1.00      | m1_subset_1(sK1(sK6,sK7,X0,X1),u1_struct_0(sK7))
% 2.34/1.00      | v2_struct_0(sK7) ),
% 2.34/1.00      inference(unflattening,[status(thm)],[c_1512]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_1517,plain,
% 2.34/1.00      ( m1_subset_1(sK1(sK6,sK7,X0,X1),u1_struct_0(sK7))
% 2.34/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 2.34/1.00      | r1_waybel_0(sK6,sK7,X0) ),
% 2.34/1.00      inference(global_propositional_subsumption,
% 2.34/1.00                [status(thm)],
% 2.34/1.00                [c_1513,c_24]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_1518,plain,
% 2.34/1.00      ( r1_waybel_0(sK6,sK7,X0)
% 2.34/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 2.34/1.00      | m1_subset_1(sK1(sK6,sK7,X0,X1),u1_struct_0(sK7)) ),
% 2.34/1.00      inference(renaming,[status(thm)],[c_1517]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_2861,plain,
% 2.34/1.00      ( r1_waybel_0(sK6,sK7,X0_55)
% 2.34/1.00      | ~ m1_subset_1(X1_55,u1_struct_0(sK7))
% 2.34/1.00      | m1_subset_1(sK1(sK6,sK7,X0_55,X1_55),u1_struct_0(sK7)) ),
% 2.34/1.00      inference(subtyping,[status(esa)],[c_1518]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_3251,plain,
% 2.34/1.00      ( r1_waybel_0(sK6,sK7,X0_55) = iProver_top
% 2.34/1.00      | m1_subset_1(X1_55,u1_struct_0(sK7)) != iProver_top
% 2.34/1.00      | m1_subset_1(sK1(sK6,sK7,X0_55,X1_55),u1_struct_0(sK7)) = iProver_top ),
% 2.34/1.00      inference(predicate_to_equality,[status(thm)],[c_2861]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_18,plain,
% 2.34/1.00      ( ~ v1_yellow_6(X0,X1)
% 2.34/1.00      | ~ l1_waybel_0(X0,X1)
% 2.34/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.34/1.00      | ~ v4_orders_2(X0)
% 2.34/1.00      | ~ v7_waybel_0(X0)
% 2.34/1.00      | v2_struct_0(X1)
% 2.34/1.00      | v2_struct_0(X0)
% 2.34/1.00      | ~ l1_struct_0(X1)
% 2.34/1.00      | k2_waybel_0(X1,X0,X2) = k4_yellow_6(X1,X0) ),
% 2.34/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_21,negated_conjecture,
% 2.34/1.00      ( v1_yellow_6(sK7,sK6) ),
% 2.34/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_316,plain,
% 2.34/1.00      ( ~ l1_waybel_0(X0,X1)
% 2.34/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.34/1.00      | ~ v4_orders_2(X0)
% 2.34/1.00      | ~ v7_waybel_0(X0)
% 2.34/1.00      | v2_struct_0(X0)
% 2.34/1.00      | v2_struct_0(X1)
% 2.34/1.00      | ~ l1_struct_0(X1)
% 2.34/1.00      | k2_waybel_0(X1,X0,X2) = k4_yellow_6(X1,X0)
% 2.34/1.00      | sK7 != X0
% 2.34/1.00      | sK6 != X1 ),
% 2.34/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_21]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_317,plain,
% 2.34/1.00      ( ~ l1_waybel_0(sK7,sK6)
% 2.34/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 2.34/1.00      | ~ v4_orders_2(sK7)
% 2.34/1.00      | ~ v7_waybel_0(sK7)
% 2.34/1.00      | v2_struct_0(sK7)
% 2.34/1.00      | v2_struct_0(sK6)
% 2.34/1.00      | ~ l1_struct_0(sK6)
% 2.34/1.00      | k2_waybel_0(sK6,sK7,X0) = k4_yellow_6(sK6,sK7) ),
% 2.34/1.00      inference(unflattening,[status(thm)],[c_316]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_89,plain,
% 2.34/1.00      ( ~ l1_pre_topc(sK6) | l1_struct_0(sK6) ),
% 2.34/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_321,plain,
% 2.34/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 2.34/1.00      | k2_waybel_0(sK6,sK7,X0) = k4_yellow_6(sK6,sK7) ),
% 2.34/1.00      inference(global_propositional_subsumption,
% 2.34/1.00                [status(thm)],
% 2.34/1.00                [c_317,c_27,c_25,c_24,c_23,c_22,c_20,c_89]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_2875,plain,
% 2.34/1.00      ( ~ m1_subset_1(X0_55,u1_struct_0(sK7))
% 2.34/1.00      | k2_waybel_0(sK6,sK7,X0_55) = k4_yellow_6(sK6,sK7) ),
% 2.34/1.00      inference(subtyping,[status(esa)],[c_321]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_3237,plain,
% 2.34/1.00      ( k2_waybel_0(sK6,sK7,X0_55) = k4_yellow_6(sK6,sK7)
% 2.34/1.00      | m1_subset_1(X0_55,u1_struct_0(sK7)) != iProver_top ),
% 2.34/1.00      inference(predicate_to_equality,[status(thm)],[c_2875]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_3774,plain,
% 2.34/1.00      ( k2_waybel_0(sK6,sK7,sK1(sK6,sK7,X0_55,X1_55)) = k4_yellow_6(sK6,sK7)
% 2.34/1.00      | r1_waybel_0(sK6,sK7,X0_55) = iProver_top
% 2.34/1.00      | m1_subset_1(X1_55,u1_struct_0(sK7)) != iProver_top ),
% 2.34/1.00      inference(superposition,[status(thm)],[c_3251,c_3237]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_4017,plain,
% 2.34/1.00      ( k2_waybel_0(sK6,sK7,sK1(sK6,sK7,X0_55,sK0(u1_struct_0(sK7)))) = k4_yellow_6(sK6,sK7)
% 2.34/1.00      | r1_waybel_0(sK6,sK7,X0_55) = iProver_top ),
% 2.34/1.00      inference(superposition,[status(thm)],[c_3235,c_3774]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_14,plain,
% 2.34/1.00      ( ~ r1_waybel_0(X0,X1,sK5(X0,X1,X2))
% 2.34/1.00      | ~ l1_waybel_0(X1,X0)
% 2.34/1.00      | r2_hidden(X2,k10_yellow_6(X0,X1))
% 2.34/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.34/1.00      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 2.34/1.00      | ~ v4_orders_2(X1)
% 2.34/1.00      | ~ v7_waybel_0(X1)
% 2.34/1.00      | v2_struct_0(X0)
% 2.34/1.00      | v2_struct_0(X1)
% 2.34/1.00      | ~ v2_pre_topc(X0)
% 2.34/1.00      | ~ l1_pre_topc(X0) ),
% 2.34/1.00      inference(cnf_transformation,[],[f74]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_697,plain,
% 2.34/1.00      ( ~ r1_waybel_0(X0,X1,sK5(X0,X1,X2))
% 2.34/1.00      | ~ l1_waybel_0(X1,X0)
% 2.34/1.00      | r2_hidden(X2,k10_yellow_6(X0,X1))
% 2.34/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.34/1.00      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 2.34/1.00      | ~ v4_orders_2(X1)
% 2.34/1.00      | v2_struct_0(X0)
% 2.34/1.00      | v2_struct_0(X1)
% 2.34/1.00      | ~ v2_pre_topc(X0)
% 2.34/1.00      | ~ l1_pre_topc(X0)
% 2.34/1.00      | sK7 != X1 ),
% 2.34/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_22]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_698,plain,
% 2.34/1.00      ( ~ r1_waybel_0(X0,sK7,sK5(X0,sK7,X1))
% 2.34/1.00      | ~ l1_waybel_0(sK7,X0)
% 2.34/1.00      | r2_hidden(X1,k10_yellow_6(X0,sK7))
% 2.34/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.34/1.00      | ~ m1_subset_1(k10_yellow_6(X0,sK7),k1_zfmisc_1(u1_struct_0(X0)))
% 2.34/1.00      | ~ v4_orders_2(sK7)
% 2.34/1.00      | v2_struct_0(X0)
% 2.34/1.00      | v2_struct_0(sK7)
% 2.34/1.00      | ~ v2_pre_topc(X0)
% 2.34/1.00      | ~ l1_pre_topc(X0) ),
% 2.34/1.00      inference(unflattening,[status(thm)],[c_697]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_702,plain,
% 2.34/1.00      ( v2_struct_0(X0)
% 2.34/1.00      | ~ r1_waybel_0(X0,sK7,sK5(X0,sK7,X1))
% 2.34/1.00      | ~ l1_waybel_0(sK7,X0)
% 2.34/1.00      | r2_hidden(X1,k10_yellow_6(X0,sK7))
% 2.34/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.34/1.00      | ~ m1_subset_1(k10_yellow_6(X0,sK7),k1_zfmisc_1(u1_struct_0(X0)))
% 2.34/1.00      | ~ v2_pre_topc(X0)
% 2.34/1.00      | ~ l1_pre_topc(X0) ),
% 2.34/1.00      inference(global_propositional_subsumption,
% 2.34/1.00                [status(thm)],
% 2.34/1.00                [c_698,c_24,c_23]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_703,plain,
% 2.34/1.00      ( ~ r1_waybel_0(X0,sK7,sK5(X0,sK7,X1))
% 2.34/1.00      | ~ l1_waybel_0(sK7,X0)
% 2.34/1.00      | r2_hidden(X1,k10_yellow_6(X0,sK7))
% 2.34/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.34/1.00      | ~ m1_subset_1(k10_yellow_6(X0,sK7),k1_zfmisc_1(u1_struct_0(X0)))
% 2.34/1.00      | v2_struct_0(X0)
% 2.34/1.00      | ~ v2_pre_topc(X0)
% 2.34/1.00      | ~ l1_pre_topc(X0) ),
% 2.34/1.00      inference(renaming,[status(thm)],[c_702]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_869,plain,
% 2.34/1.00      ( ~ r1_waybel_0(X0,sK7,sK5(X0,sK7,X1))
% 2.34/1.00      | ~ l1_waybel_0(sK7,X0)
% 2.34/1.00      | r2_hidden(X1,k10_yellow_6(X0,sK7))
% 2.34/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.34/1.00      | v2_struct_0(X0)
% 2.34/1.00      | ~ v2_pre_topc(X0)
% 2.34/1.00      | ~ l1_pre_topc(X0) ),
% 2.34/1.00      inference(backward_subsumption_resolution,
% 2.34/1.00                [status(thm)],
% 2.34/1.00                [c_850,c_703]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_1004,plain,
% 2.34/1.00      ( ~ r1_waybel_0(X0,sK7,sK5(X0,sK7,X1))
% 2.34/1.00      | ~ l1_waybel_0(sK7,X0)
% 2.34/1.00      | r2_hidden(X1,k10_yellow_6(X0,sK7))
% 2.34/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.34/1.00      | v2_struct_0(X0)
% 2.34/1.00      | ~ l1_pre_topc(X0)
% 2.34/1.00      | sK6 != X0 ),
% 2.34/1.00      inference(resolution_lifted,[status(thm)],[c_869,c_26]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_1005,plain,
% 2.34/1.00      ( ~ r1_waybel_0(sK6,sK7,sK5(sK6,sK7,X0))
% 2.34/1.00      | ~ l1_waybel_0(sK7,sK6)
% 2.34/1.00      | r2_hidden(X0,k10_yellow_6(sK6,sK7))
% 2.34/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 2.34/1.00      | v2_struct_0(sK6)
% 2.34/1.00      | ~ l1_pre_topc(sK6) ),
% 2.34/1.00      inference(unflattening,[status(thm)],[c_1004]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_1009,plain,
% 2.34/1.00      ( ~ r1_waybel_0(sK6,sK7,sK5(sK6,sK7,X0))
% 2.34/1.00      | r2_hidden(X0,k10_yellow_6(sK6,sK7))
% 2.34/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
% 2.34/1.00      inference(global_propositional_subsumption,
% 2.34/1.00                [status(thm)],
% 2.34/1.00                [c_1005,c_27,c_25,c_20]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_2873,plain,
% 2.34/1.00      ( ~ r1_waybel_0(sK6,sK7,sK5(sK6,sK7,X0_55))
% 2.34/1.00      | r2_hidden(X0_55,k10_yellow_6(sK6,sK7))
% 2.34/1.00      | ~ m1_subset_1(X0_55,u1_struct_0(sK6)) ),
% 2.34/1.00      inference(subtyping,[status(esa)],[c_1009]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_3239,plain,
% 2.34/1.00      ( r1_waybel_0(sK6,sK7,sK5(sK6,sK7,X0_55)) != iProver_top
% 2.34/1.00      | r2_hidden(X0_55,k10_yellow_6(sK6,sK7)) = iProver_top
% 2.34/1.00      | m1_subset_1(X0_55,u1_struct_0(sK6)) != iProver_top ),
% 2.34/1.00      inference(predicate_to_equality,[status(thm)],[c_2873]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_4058,plain,
% 2.34/1.00      ( k2_waybel_0(sK6,sK7,sK1(sK6,sK7,sK5(sK6,sK7,X0_55),sK0(u1_struct_0(sK7)))) = k4_yellow_6(sK6,sK7)
% 2.34/1.00      | r2_hidden(X0_55,k10_yellow_6(sK6,sK7)) = iProver_top
% 2.34/1.00      | m1_subset_1(X0_55,u1_struct_0(sK6)) != iProver_top ),
% 2.34/1.00      inference(superposition,[status(thm)],[c_4017,c_3239]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_19,negated_conjecture,
% 2.34/1.00      ( ~ r2_hidden(k4_yellow_6(sK6,sK7),k10_yellow_6(sK6,sK7)) ),
% 2.34/1.00      inference(cnf_transformation,[],[f73]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_2876,negated_conjecture,
% 2.34/1.00      ( ~ r2_hidden(k4_yellow_6(sK6,sK7),k10_yellow_6(sK6,sK7)) ),
% 2.34/1.00      inference(subtyping,[status(esa)],[c_19]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_3236,plain,
% 2.34/1.00      ( r2_hidden(k4_yellow_6(sK6,sK7),k10_yellow_6(sK6,sK7)) != iProver_top ),
% 2.34/1.00      inference(predicate_to_equality,[status(thm)],[c_2876]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_4137,plain,
% 2.34/1.00      ( k2_waybel_0(sK6,sK7,sK1(sK6,sK7,sK5(sK6,sK7,k4_yellow_6(sK6,sK7)),sK0(u1_struct_0(sK7)))) = k4_yellow_6(sK6,sK7)
% 2.34/1.00      | m1_subset_1(k4_yellow_6(sK6,sK7),u1_struct_0(sK6)) != iProver_top ),
% 2.34/1.00      inference(superposition,[status(thm)],[c_4058,c_3236]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_3413,plain,
% 2.34/1.00      ( m1_subset_1(sK0(u1_struct_0(sK7)),u1_struct_0(sK7)) ),
% 2.34/1.00      inference(instantiation,[status(thm)],[c_2877]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_3416,plain,
% 2.34/1.00      ( m1_subset_1(sK0(u1_struct_0(sK7)),u1_struct_0(sK7)) = iProver_top ),
% 2.34/1.00      inference(predicate_to_equality,[status(thm)],[c_3413]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_3631,plain,
% 2.34/1.00      ( k2_waybel_0(sK6,sK7,sK0(u1_struct_0(sK7))) = k4_yellow_6(sK6,sK7) ),
% 2.34/1.00      inference(superposition,[status(thm)],[c_3235,c_3237]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_9,plain,
% 2.34/1.00      ( ~ l1_waybel_0(X0,X1)
% 2.34/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.34/1.00      | m1_subset_1(k2_waybel_0(X1,X0,X2),u1_struct_0(X1))
% 2.34/1.00      | v2_struct_0(X1)
% 2.34/1.00      | v2_struct_0(X0)
% 2.34/1.00      | ~ l1_struct_0(X1) ),
% 2.34/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_480,plain,
% 2.34/1.00      ( ~ l1_waybel_0(X0,X1)
% 2.34/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.34/1.00      | m1_subset_1(k2_waybel_0(X1,X0,X2),u1_struct_0(X1))
% 2.34/1.00      | v2_struct_0(X1)
% 2.34/1.00      | v2_struct_0(X0)
% 2.34/1.00      | ~ l1_pre_topc(X3)
% 2.34/1.00      | X1 != X3 ),
% 2.34/1.00      inference(resolution_lifted,[status(thm)],[c_1,c_9]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_481,plain,
% 2.34/1.00      ( ~ l1_waybel_0(X0,X1)
% 2.34/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.34/1.00      | m1_subset_1(k2_waybel_0(X1,X0,X2),u1_struct_0(X1))
% 2.34/1.00      | v2_struct_0(X0)
% 2.34/1.00      | v2_struct_0(X1)
% 2.34/1.00      | ~ l1_pre_topc(X1) ),
% 2.34/1.00      inference(unflattening,[status(thm)],[c_480]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_1341,plain,
% 2.34/1.00      ( ~ l1_waybel_0(X0,X1)
% 2.34/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.34/1.00      | m1_subset_1(k2_waybel_0(X1,X0,X2),u1_struct_0(X1))
% 2.34/1.00      | v2_struct_0(X0)
% 2.34/1.00      | v2_struct_0(X1)
% 2.34/1.00      | sK6 != X1 ),
% 2.34/1.00      inference(resolution_lifted,[status(thm)],[c_481,c_25]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_1342,plain,
% 2.34/1.00      ( ~ l1_waybel_0(X0,sK6)
% 2.34/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.34/1.00      | m1_subset_1(k2_waybel_0(sK6,X0,X1),u1_struct_0(sK6))
% 2.34/1.00      | v2_struct_0(X0)
% 2.34/1.00      | v2_struct_0(sK6) ),
% 2.34/1.00      inference(unflattening,[status(thm)],[c_1341]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_1346,plain,
% 2.34/1.00      ( v2_struct_0(X0)
% 2.34/1.00      | m1_subset_1(k2_waybel_0(sK6,X0,X1),u1_struct_0(sK6))
% 2.34/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.34/1.00      | ~ l1_waybel_0(X0,sK6) ),
% 2.34/1.00      inference(global_propositional_subsumption,
% 2.34/1.00                [status(thm)],
% 2.34/1.00                [c_1342,c_27]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_1347,plain,
% 2.34/1.00      ( ~ l1_waybel_0(X0,sK6)
% 2.34/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.34/1.00      | m1_subset_1(k2_waybel_0(sK6,X0,X1),u1_struct_0(sK6))
% 2.34/1.00      | v2_struct_0(X0) ),
% 2.34/1.00      inference(renaming,[status(thm)],[c_1346]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_1476,plain,
% 2.34/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.34/1.00      | m1_subset_1(k2_waybel_0(sK6,X1,X0),u1_struct_0(sK6))
% 2.34/1.00      | v2_struct_0(X1)
% 2.34/1.00      | sK7 != X1
% 2.34/1.00      | sK6 != sK6 ),
% 2.34/1.00      inference(resolution_lifted,[status(thm)],[c_20,c_1347]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_1477,plain,
% 2.34/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 2.34/1.00      | m1_subset_1(k2_waybel_0(sK6,sK7,X0),u1_struct_0(sK6))
% 2.34/1.00      | v2_struct_0(sK7) ),
% 2.34/1.00      inference(unflattening,[status(thm)],[c_1476]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_1481,plain,
% 2.34/1.00      ( m1_subset_1(k2_waybel_0(sK6,sK7,X0),u1_struct_0(sK6))
% 2.34/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK7)) ),
% 2.34/1.00      inference(global_propositional_subsumption,
% 2.34/1.00                [status(thm)],
% 2.34/1.00                [c_1477,c_24]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_1482,plain,
% 2.34/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 2.34/1.00      | m1_subset_1(k2_waybel_0(sK6,sK7,X0),u1_struct_0(sK6)) ),
% 2.34/1.00      inference(renaming,[status(thm)],[c_1481]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_2863,plain,
% 2.34/1.00      ( ~ m1_subset_1(X0_55,u1_struct_0(sK7))
% 2.34/1.00      | m1_subset_1(k2_waybel_0(sK6,sK7,X0_55),u1_struct_0(sK6)) ),
% 2.34/1.00      inference(subtyping,[status(esa)],[c_1482]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_3249,plain,
% 2.34/1.00      ( m1_subset_1(X0_55,u1_struct_0(sK7)) != iProver_top
% 2.34/1.00      | m1_subset_1(k2_waybel_0(sK6,sK7,X0_55),u1_struct_0(sK6)) = iProver_top ),
% 2.34/1.00      inference(predicate_to_equality,[status(thm)],[c_2863]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_3639,plain,
% 2.34/1.00      ( m1_subset_1(k4_yellow_6(sK6,sK7),u1_struct_0(sK6)) = iProver_top
% 2.34/1.00      | m1_subset_1(sK0(u1_struct_0(sK7)),u1_struct_0(sK7)) != iProver_top ),
% 2.34/1.00      inference(superposition,[status(thm)],[c_3631,c_3249]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_4263,plain,
% 2.34/1.00      ( k2_waybel_0(sK6,sK7,sK1(sK6,sK7,sK5(sK6,sK7,k4_yellow_6(sK6,sK7)),sK0(u1_struct_0(sK7)))) = k4_yellow_6(sK6,sK7) ),
% 2.34/1.00      inference(global_propositional_subsumption,
% 2.34/1.00                [status(thm)],
% 2.34/1.00                [c_4137,c_3416,c_3639]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_4,plain,
% 2.34/1.00      ( r1_waybel_0(X0,X1,X2)
% 2.34/1.00      | ~ l1_waybel_0(X1,X0)
% 2.34/1.00      | ~ r2_hidden(k2_waybel_0(X0,X1,sK1(X0,X1,X2,X3)),X2)
% 2.34/1.00      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 2.34/1.00      | v2_struct_0(X0)
% 2.34/1.00      | v2_struct_0(X1)
% 2.34/1.00      | ~ l1_struct_0(X0) ),
% 2.34/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_427,plain,
% 2.34/1.00      ( r1_waybel_0(X0,X1,X2)
% 2.34/1.00      | ~ l1_waybel_0(X1,X0)
% 2.34/1.00      | ~ r2_hidden(k2_waybel_0(X0,X1,sK1(X0,X1,X2,X3)),X2)
% 2.34/1.00      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 2.34/1.00      | v2_struct_0(X0)
% 2.34/1.00      | v2_struct_0(X1)
% 2.34/1.00      | ~ l1_pre_topc(X0) ),
% 2.34/1.00      inference(resolution,[status(thm)],[c_1,c_4]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_1241,plain,
% 2.34/1.00      ( r1_waybel_0(X0,X1,X2)
% 2.34/1.00      | ~ l1_waybel_0(X1,X0)
% 2.34/1.00      | ~ r2_hidden(k2_waybel_0(X0,X1,sK1(X0,X1,X2,X3)),X2)
% 2.34/1.00      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 2.34/1.00      | v2_struct_0(X0)
% 2.34/1.00      | v2_struct_0(X1)
% 2.34/1.00      | sK6 != X0 ),
% 2.34/1.00      inference(resolution_lifted,[status(thm)],[c_427,c_25]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_1242,plain,
% 2.34/1.00      ( r1_waybel_0(sK6,X0,X1)
% 2.34/1.00      | ~ l1_waybel_0(X0,sK6)
% 2.34/1.00      | ~ r2_hidden(k2_waybel_0(sK6,X0,sK1(sK6,X0,X1,X2)),X1)
% 2.34/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.34/1.00      | v2_struct_0(X0)
% 2.34/1.00      | v2_struct_0(sK6) ),
% 2.34/1.00      inference(unflattening,[status(thm)],[c_1241]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_1246,plain,
% 2.34/1.00      ( v2_struct_0(X0)
% 2.34/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.34/1.00      | ~ r2_hidden(k2_waybel_0(sK6,X0,sK1(sK6,X0,X1,X2)),X1)
% 2.34/1.00      | ~ l1_waybel_0(X0,sK6)
% 2.34/1.00      | r1_waybel_0(sK6,X0,X1) ),
% 2.34/1.00      inference(global_propositional_subsumption,
% 2.34/1.00                [status(thm)],
% 2.34/1.00                [c_1242,c_27]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_1247,plain,
% 2.34/1.00      ( r1_waybel_0(sK6,X0,X1)
% 2.34/1.00      | ~ l1_waybel_0(X0,sK6)
% 2.34/1.00      | ~ r2_hidden(k2_waybel_0(sK6,X0,sK1(sK6,X0,X1,X2)),X1)
% 2.34/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.34/1.00      | v2_struct_0(X0) ),
% 2.34/1.00      inference(renaming,[status(thm)],[c_1246]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_1533,plain,
% 2.34/1.00      ( r1_waybel_0(sK6,X0,X1)
% 2.34/1.00      | ~ r2_hidden(k2_waybel_0(sK6,X0,sK1(sK6,X0,X1,X2)),X1)
% 2.34/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.34/1.00      | v2_struct_0(X0)
% 2.34/1.00      | sK7 != X0
% 2.34/1.00      | sK6 != sK6 ),
% 2.34/1.00      inference(resolution_lifted,[status(thm)],[c_20,c_1247]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_1534,plain,
% 2.34/1.00      ( r1_waybel_0(sK6,sK7,X0)
% 2.34/1.00      | ~ r2_hidden(k2_waybel_0(sK6,sK7,sK1(sK6,sK7,X0,X1)),X0)
% 2.34/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 2.34/1.00      | v2_struct_0(sK7) ),
% 2.34/1.00      inference(unflattening,[status(thm)],[c_1533]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_1538,plain,
% 2.34/1.00      ( ~ m1_subset_1(X1,u1_struct_0(sK7))
% 2.34/1.00      | ~ r2_hidden(k2_waybel_0(sK6,sK7,sK1(sK6,sK7,X0,X1)),X0)
% 2.34/1.00      | r1_waybel_0(sK6,sK7,X0) ),
% 2.34/1.00      inference(global_propositional_subsumption,
% 2.34/1.00                [status(thm)],
% 2.34/1.00                [c_1534,c_24]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_1539,plain,
% 2.34/1.00      ( r1_waybel_0(sK6,sK7,X0)
% 2.34/1.00      | ~ r2_hidden(k2_waybel_0(sK6,sK7,sK1(sK6,sK7,X0,X1)),X0)
% 2.34/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK7)) ),
% 2.34/1.00      inference(renaming,[status(thm)],[c_1538]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_2860,plain,
% 2.34/1.00      ( r1_waybel_0(sK6,sK7,X0_55)
% 2.34/1.00      | ~ r2_hidden(k2_waybel_0(sK6,sK7,sK1(sK6,sK7,X0_55,X1_55)),X0_55)
% 2.34/1.00      | ~ m1_subset_1(X1_55,u1_struct_0(sK7)) ),
% 2.34/1.00      inference(subtyping,[status(esa)],[c_1539]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_3252,plain,
% 2.34/1.00      ( r1_waybel_0(sK6,sK7,X0_55) = iProver_top
% 2.34/1.00      | r2_hidden(k2_waybel_0(sK6,sK7,sK1(sK6,sK7,X0_55,X1_55)),X0_55) != iProver_top
% 2.34/1.00      | m1_subset_1(X1_55,u1_struct_0(sK7)) != iProver_top ),
% 2.34/1.00      inference(predicate_to_equality,[status(thm)],[c_2860]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_4266,plain,
% 2.34/1.00      ( r1_waybel_0(sK6,sK7,sK5(sK6,sK7,k4_yellow_6(sK6,sK7))) = iProver_top
% 2.34/1.00      | r2_hidden(k4_yellow_6(sK6,sK7),sK5(sK6,sK7,k4_yellow_6(sK6,sK7))) != iProver_top
% 2.34/1.00      | m1_subset_1(sK0(u1_struct_0(sK7)),u1_struct_0(sK7)) != iProver_top ),
% 2.34/1.00      inference(superposition,[status(thm)],[c_4263,c_3252]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_1773,plain,
% 2.34/1.00      ( ~ r1_waybel_0(sK6,sK7,sK5(sK6,sK7,X0))
% 2.34/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 2.34/1.00      | k4_yellow_6(sK6,sK7) != X0
% 2.34/1.00      | k10_yellow_6(sK6,sK7) != k10_yellow_6(sK6,sK7) ),
% 2.34/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_1009]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_1774,plain,
% 2.34/1.00      ( ~ r1_waybel_0(sK6,sK7,sK5(sK6,sK7,k4_yellow_6(sK6,sK7)))
% 2.34/1.00      | ~ m1_subset_1(k4_yellow_6(sK6,sK7),u1_struct_0(sK6)) ),
% 2.34/1.00      inference(unflattening,[status(thm)],[c_1773]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_1775,plain,
% 2.34/1.00      ( r1_waybel_0(sK6,sK7,sK5(sK6,sK7,k4_yellow_6(sK6,sK7))) != iProver_top
% 2.34/1.00      | m1_subset_1(k4_yellow_6(sK6,sK7),u1_struct_0(sK6)) != iProver_top ),
% 2.34/1.00      inference(predicate_to_equality,[status(thm)],[c_1774]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_4276,plain,
% 2.34/1.00      ( r2_hidden(k4_yellow_6(sK6,sK7),sK5(sK6,sK7,k4_yellow_6(sK6,sK7))) != iProver_top ),
% 2.34/1.00      inference(global_propositional_subsumption,
% 2.34/1.00                [status(thm)],
% 2.34/1.00                [c_4266,c_1775,c_3416,c_3639]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_4281,plain,
% 2.34/1.00      ( r2_hidden(k4_yellow_6(sK6,sK7),k10_yellow_6(sK6,sK7)) = iProver_top
% 2.34/1.00      | m1_subset_1(k4_yellow_6(sK6,sK7),u1_struct_0(sK6)) != iProver_top ),
% 2.34/1.00      inference(superposition,[status(thm)],[c_3695,c_4276]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_36,plain,
% 2.34/1.00      ( r2_hidden(k4_yellow_6(sK6,sK7),k10_yellow_6(sK6,sK7)) != iProver_top ),
% 2.34/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(contradiction,plain,
% 2.34/1.00      ( $false ),
% 2.34/1.00      inference(minisat,[status(thm)],[c_4281,c_3639,c_3416,c_36]) ).
% 2.34/1.00  
% 2.34/1.00  
% 2.34/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.34/1.00  
% 2.34/1.00  ------                               Statistics
% 2.34/1.00  
% 2.34/1.00  ------ General
% 2.34/1.00  
% 2.34/1.00  abstr_ref_over_cycles:                  0
% 2.34/1.00  abstr_ref_under_cycles:                 0
% 2.34/1.00  gc_basic_clause_elim:                   0
% 2.34/1.00  forced_gc_time:                         0
% 2.34/1.00  parsing_time:                           0.01
% 2.34/1.00  unif_index_cands_time:                  0.
% 2.34/1.00  unif_index_add_time:                    0.
% 2.34/1.00  orderings_time:                         0.
% 2.34/1.00  out_proof_time:                         0.014
% 2.34/1.00  total_time:                             0.143
% 2.34/1.00  num_of_symbols:                         57
% 2.34/1.00  num_of_terms:                           3256
% 2.34/1.00  
% 2.34/1.00  ------ Preprocessing
% 2.34/1.00  
% 2.34/1.00  num_of_splits:                          0
% 2.34/1.00  num_of_split_atoms:                     0
% 2.34/1.00  num_of_reused_defs:                     0
% 2.34/1.00  num_eq_ax_congr_red:                    59
% 2.34/1.00  num_of_sem_filtered_clauses:            1
% 2.34/1.00  num_of_subtypes:                        3
% 2.34/1.00  monotx_restored_types:                  1
% 2.34/1.00  sat_num_of_epr_types:                   0
% 2.34/1.00  sat_num_of_non_cyclic_types:            0
% 2.34/1.00  sat_guarded_non_collapsed_types:        0
% 2.34/1.00  num_pure_diseq_elim:                    0
% 2.34/1.00  simp_replaced_by:                       0
% 2.34/1.00  res_preprocessed:                       99
% 2.34/1.00  prep_upred:                             0
% 2.34/1.00  prep_unflattend:                        149
% 2.34/1.00  smt_new_axioms:                         0
% 2.34/1.00  pred_elim_cands:                        4
% 2.34/1.00  pred_elim:                              9
% 2.34/1.00  pred_elim_cl:                           10
% 2.34/1.00  pred_elim_cycles:                       15
% 2.34/1.00  merged_defs:                            0
% 2.34/1.00  merged_defs_ncl:                        0
% 2.34/1.00  bin_hyper_res:                          0
% 2.34/1.00  prep_cycles:                            4
% 2.34/1.00  pred_elim_time:                         0.053
% 2.34/1.00  splitting_time:                         0.
% 2.34/1.00  sem_filter_time:                        0.
% 2.34/1.00  monotx_time:                            0.001
% 2.34/1.00  subtype_inf_time:                       0.001
% 2.34/1.00  
% 2.34/1.00  ------ Problem properties
% 2.34/1.00  
% 2.34/1.00  clauses:                                18
% 2.34/1.00  conjectures:                            1
% 2.34/1.00  epr:                                    0
% 2.34/1.00  horn:                                   12
% 2.34/1.00  ground:                                 2
% 2.34/1.00  unary:                                  3
% 2.34/1.00  binary:                                 3
% 2.34/1.00  lits:                                   51
% 2.34/1.00  lits_eq:                                5
% 2.34/1.00  fd_pure:                                0
% 2.34/1.00  fd_pseudo:                              0
% 2.34/1.00  fd_cond:                                4
% 2.34/1.00  fd_pseudo_cond:                         0
% 2.34/1.00  ac_symbols:                             0
% 2.34/1.00  
% 2.34/1.00  ------ Propositional Solver
% 2.34/1.00  
% 2.34/1.00  prop_solver_calls:                      27
% 2.34/1.00  prop_fast_solver_calls:                 1548
% 2.34/1.00  smt_solver_calls:                       0
% 2.34/1.00  smt_fast_solver_calls:                  0
% 2.34/1.00  prop_num_of_clauses:                    979
% 2.34/1.00  prop_preprocess_simplified:             3913
% 2.34/1.00  prop_fo_subsumed:                       86
% 2.34/1.00  prop_solver_time:                       0.
% 2.34/1.00  smt_solver_time:                        0.
% 2.34/1.00  smt_fast_solver_time:                   0.
% 2.34/1.00  prop_fast_solver_time:                  0.
% 2.34/1.00  prop_unsat_core_time:                   0.
% 2.34/1.00  
% 2.34/1.00  ------ QBF
% 2.34/1.00  
% 2.34/1.00  qbf_q_res:                              0
% 2.34/1.00  qbf_num_tautologies:                    0
% 2.34/1.00  qbf_prep_cycles:                        0
% 2.34/1.00  
% 2.34/1.00  ------ BMC1
% 2.34/1.00  
% 2.34/1.00  bmc1_current_bound:                     -1
% 2.34/1.00  bmc1_last_solved_bound:                 -1
% 2.34/1.00  bmc1_unsat_core_size:                   -1
% 2.34/1.00  bmc1_unsat_core_parents_size:           -1
% 2.34/1.00  bmc1_merge_next_fun:                    0
% 2.34/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.34/1.00  
% 2.34/1.00  ------ Instantiation
% 2.34/1.00  
% 2.34/1.00  inst_num_of_clauses:                    140
% 2.34/1.00  inst_num_in_passive:                    10
% 2.34/1.00  inst_num_in_active:                     103
% 2.34/1.00  inst_num_in_unprocessed:                27
% 2.34/1.00  inst_num_of_loops:                      150
% 2.34/1.00  inst_num_of_learning_restarts:          0
% 2.34/1.00  inst_num_moves_active_passive:          44
% 2.34/1.00  inst_lit_activity:                      0
% 2.34/1.00  inst_lit_activity_moves:                0
% 2.34/1.00  inst_num_tautologies:                   0
% 2.34/1.00  inst_num_prop_implied:                  0
% 2.34/1.00  inst_num_existing_simplified:           0
% 2.34/1.00  inst_num_eq_res_simplified:             0
% 2.34/1.00  inst_num_child_elim:                    0
% 2.34/1.00  inst_num_of_dismatching_blockings:      11
% 2.34/1.00  inst_num_of_non_proper_insts:           123
% 2.34/1.00  inst_num_of_duplicates:                 0
% 2.34/1.00  inst_inst_num_from_inst_to_res:         0
% 2.34/1.00  inst_dismatching_checking_time:         0.
% 2.34/1.00  
% 2.34/1.00  ------ Resolution
% 2.34/1.00  
% 2.34/1.00  res_num_of_clauses:                     0
% 2.34/1.00  res_num_in_passive:                     0
% 2.34/1.00  res_num_in_active:                      0
% 2.34/1.00  res_num_of_loops:                       103
% 2.34/1.00  res_forward_subset_subsumed:            16
% 2.34/1.00  res_backward_subset_subsumed:           0
% 2.34/1.00  res_forward_subsumed:                   2
% 2.34/1.00  res_backward_subsumed:                  0
% 2.34/1.00  res_forward_subsumption_resolution:     1
% 2.34/1.00  res_backward_subsumption_resolution:    3
% 2.34/1.00  res_clause_to_clause_subsumption:       155
% 2.34/1.00  res_orphan_elimination:                 0
% 2.34/1.00  res_tautology_del:                      32
% 2.34/1.00  res_num_eq_res_simplified:              0
% 2.34/1.00  res_num_sel_changes:                    0
% 2.34/1.00  res_moves_from_active_to_pass:          0
% 2.34/1.00  
% 2.34/1.00  ------ Superposition
% 2.34/1.00  
% 2.34/1.00  sup_time_total:                         0.
% 2.34/1.00  sup_time_generating:                    0.
% 2.34/1.00  sup_time_sim_full:                      0.
% 2.34/1.00  sup_time_sim_immed:                     0.
% 2.34/1.00  
% 2.34/1.00  sup_num_of_clauses:                     41
% 2.34/1.00  sup_num_in_active:                      30
% 2.34/1.00  sup_num_in_passive:                     11
% 2.34/1.00  sup_num_of_loops:                       29
% 2.34/1.00  sup_fw_superposition:                   7
% 2.34/1.00  sup_bw_superposition:                   20
% 2.34/1.00  sup_immediate_simplified:               2
% 2.34/1.00  sup_given_eliminated:                   0
% 2.34/1.00  comparisons_done:                       0
% 2.34/1.00  comparisons_avoided:                    0
% 2.34/1.00  
% 2.34/1.00  ------ Simplifications
% 2.34/1.00  
% 2.34/1.00  
% 2.34/1.00  sim_fw_subset_subsumed:                 2
% 2.34/1.00  sim_bw_subset_subsumed:                 0
% 2.34/1.00  sim_fw_subsumed:                        0
% 2.34/1.00  sim_bw_subsumed:                        0
% 2.34/1.00  sim_fw_subsumption_res:                 0
% 2.34/1.00  sim_bw_subsumption_res:                 0
% 2.34/1.00  sim_tautology_del:                      2
% 2.34/1.00  sim_eq_tautology_del:                   0
% 2.34/1.00  sim_eq_res_simp:                        0
% 2.34/1.00  sim_fw_demodulated:                     0
% 2.34/1.00  sim_bw_demodulated:                     0
% 2.34/1.00  sim_light_normalised:                   0
% 2.34/1.00  sim_joinable_taut:                      0
% 2.34/1.00  sim_joinable_simp:                      0
% 2.34/1.00  sim_ac_normalised:                      0
% 2.34/1.00  sim_smt_subsumption:                    0
% 2.34/1.00  
%------------------------------------------------------------------------------
