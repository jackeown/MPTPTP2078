%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:18 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :  199 (1758 expanded)
%              Number of clauses        :  134 ( 366 expanded)
%              Number of leaves         :   15 ( 585 expanded)
%              Depth                    :   24
%              Number of atoms          : 1171 (13689 expanded)
%              Number of equality atoms :  131 ( 244 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal clause size      :   24 (   5 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
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

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f8,conjecture,(
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
             => r1_tarski(k10_yellow_6(X0,X1),k10_yellow_6(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
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
                ( m2_yellow_6(X2,X0,X1)
               => r1_tarski(k10_yellow_6(X0,X1),k10_yellow_6(X0,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k10_yellow_6(X0,X1),k10_yellow_6(X0,X2))
              & m2_yellow_6(X2,X0,X1) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k10_yellow_6(X0,X1),k10_yellow_6(X0,X2))
              & m2_yellow_6(X2,X0,X1) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k10_yellow_6(X0,X1),k10_yellow_6(X0,X2))
          & m2_yellow_6(X2,X0,X1) )
     => ( ~ r1_tarski(k10_yellow_6(X0,X1),k10_yellow_6(X0,sK6))
        & m2_yellow_6(sK6,X0,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k10_yellow_6(X0,X1),k10_yellow_6(X0,X2))
              & m2_yellow_6(X2,X0,X1) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ~ r1_tarski(k10_yellow_6(X0,sK5),k10_yellow_6(X0,X2))
            & m2_yellow_6(X2,X0,sK5) )
        & l1_waybel_0(sK5,X0)
        & v7_waybel_0(sK5)
        & v4_orders_2(sK5)
        & ~ v2_struct_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k10_yellow_6(X0,X1),k10_yellow_6(X0,X2))
                & m2_yellow_6(X2,X0,X1) )
            & l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k10_yellow_6(sK4,X1),k10_yellow_6(sK4,X2))
              & m2_yellow_6(X2,sK4,X1) )
          & l1_waybel_0(X1,sK4)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK4)
      & v2_pre_topc(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ~ r1_tarski(k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6))
    & m2_yellow_6(sK6,sK4,sK5)
    & l1_waybel_0(sK5,sK4)
    & v7_waybel_0(sK5)
    & v4_orders_2(sK5)
    & ~ v2_struct_0(sK5)
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f24,f37,f36,f35])).

fof(f59,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f58,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f60,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f4,axiom,(
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

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f4])).

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
    inference(flattening,[],[f15])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f33,plain,(
    ! [X6,X1,X0] :
      ( ? [X7] :
          ( ~ r1_waybel_0(X0,X1,X7)
          & m1_connsp_2(X7,X0,X6) )
     => ( ~ r1_waybel_0(X0,X1,sK3(X0,X1,X6))
        & m1_connsp_2(sK3(X0,X1,X6),X0,X6) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_waybel_0(X0,X1,X4)
          & m1_connsp_2(X4,X0,X3) )
     => ( ~ r1_waybel_0(X0,X1,sK2(X0,X1,X2))
        & m1_connsp_2(sK2(X0,X1,X2),X0,X3) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
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
              & m1_connsp_2(X4,X0,sK1(X0,X1,X2)) )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ! [X5] :
              ( r1_waybel_0(X0,X1,X5)
              | ~ m1_connsp_2(X5,X0,sK1(X0,X1,X2)) )
          | r2_hidden(sK1(X0,X1,X2),X2) )
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k10_yellow_6(X0,X1) = X2
                  | ( ( ( ~ r1_waybel_0(X0,X1,sK2(X0,X1,X2))
                        & m1_connsp_2(sK2(X0,X1,X2),X0,sK1(X0,X1,X2)) )
                      | ~ r2_hidden(sK1(X0,X1,X2),X2) )
                    & ( ! [X5] :
                          ( r1_waybel_0(X0,X1,X5)
                          | ~ m1_connsp_2(X5,X0,sK1(X0,X1,X2)) )
                      | r2_hidden(sK1(X0,X1,X2),X2) )
                    & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) )
                & ( ! [X6] :
                      ( ( ( r2_hidden(X6,X2)
                          | ( ~ r1_waybel_0(X0,X1,sK3(X0,X1,X6))
                            & m1_connsp_2(sK3(X0,X1,X6),X0,X6) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f30,f33,f32,f31])).

fof(f46,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,X2)
      | m1_connsp_2(sK3(X0,X1,X6),X0,X6)
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
    inference(cnf_transformation,[],[f34])).

fof(f68,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(X6,k10_yellow_6(X0,X1))
      | m1_connsp_2(sK3(X0,X1,X6),X0,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v7_waybel_0(X2)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f65,plain,(
    m2_yellow_6(sK6,sK4,sK5) ),
    inference(cnf_transformation,[],[f38])).

fof(f61,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f38])).

fof(f62,plain,(
    v4_orders_2(sK5) ),
    inference(cnf_transformation,[],[f38])).

fof(f63,plain,(
    v7_waybel_0(sK5) ),
    inference(cnf_transformation,[],[f38])).

fof(f64,plain,(
    l1_waybel_0(sK5,sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f42,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(X2)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v4_orders_2(X2)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(X2,X0)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                 => r2_hidden(X3,X2) ) )
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f10])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,X0) )
     => ( ~ r2_hidden(sK0(X0,X1,X2),X2)
        & r2_hidden(sK0(X0,X1,X2),X1)
        & m1_subset_1(sK0(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ( ~ r2_hidden(sK0(X0,X1,X2),X2)
            & r2_hidden(sK0(X0,X1,X2),X1)
            & m1_subset_1(sK0(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f25])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | m1_subset_1(sK0(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f66,plain,(
    ~ r1_tarski(k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6)) ),
    inference(cnf_transformation,[],[f38])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f45,plain,(
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
    inference(cnf_transformation,[],[f34])).

fof(f69,plain,(
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
    inference(equality_resolution,[],[f45])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ~ r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ~ r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ~ r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_waybel_0(X0,X1,X2)
                | r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
              & ( ~ r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
                | ~ r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
      | ~ r1_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f7])).

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

fof(f57,plain,(
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

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_waybel_0(X0,X1,X2)
      | r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f47,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,X2)
      | ~ r1_waybel_0(X0,X1,sK3(X0,X1,X6))
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
    inference(cnf_transformation,[],[f34])).

fof(f67,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(X6,k10_yellow_6(X0,X1))
      | ~ r1_waybel_0(X0,X1,sK3(X0,X1,X6))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r2_hidden(sK0(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_13,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(k10_yellow_6(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_26,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_634,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(k10_yellow_6(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_26])).

cnf(c_635,plain,
    ( ~ l1_waybel_0(X0,sK4)
    | m1_subset_1(k10_yellow_6(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_634])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_25,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_639,plain,
    ( ~ l1_waybel_0(X0,sK4)
    | m1_subset_1(k10_yellow_6(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_635,c_27,c_25])).

cnf(c_11,plain,
    ( m1_connsp_2(sK3(X0,X1,X2),X0,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | r2_hidden(X2,k10_yellow_6(X0,X1))
    | ~ v2_pre_topc(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_490,plain,
    ( m1_connsp_2(sK3(X0,X1,X2),X0,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | r2_hidden(X2,k10_yellow_6(X0,X1))
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_26])).

cnf(c_491,plain,
    ( m1_connsp_2(sK3(sK4,X0,X1),sK4,X1)
    | ~ l1_waybel_0(X0,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(k10_yellow_6(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(X1,k10_yellow_6(sK4,X0))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_490])).

cnf(c_495,plain,
    ( m1_connsp_2(sK3(sK4,X0,X1),sK4,X1)
    | ~ l1_waybel_0(X0,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(k10_yellow_6(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(X1,k10_yellow_6(sK4,X0))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_491,c_27,c_25])).

cnf(c_657,plain,
    ( m1_connsp_2(sK3(sK4,X0,X1),sK4,X1)
    | ~ l1_waybel_0(X0,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | r2_hidden(X1,k10_yellow_6(sK4,X0))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_639,c_495])).

cnf(c_15,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | v7_waybel_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_20,negated_conjecture,
    ( m2_yellow_6(sK6,sK4,sK5) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_397,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v7_waybel_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | sK6 != X2
    | sK5 != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_20])).

cnf(c_398,plain,
    ( ~ l1_waybel_0(sK5,sK4)
    | ~ v4_orders_2(sK5)
    | v7_waybel_0(sK6)
    | ~ v7_waybel_0(sK5)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | ~ l1_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_397])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_23,negated_conjecture,
    ( v4_orders_2(sK5) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_22,negated_conjecture,
    ( v7_waybel_0(sK5) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_21,negated_conjecture,
    ( l1_waybel_0(sK5,sK4) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_3,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_73,plain,
    ( ~ l1_pre_topc(sK4)
    | l1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_400,plain,
    ( v7_waybel_0(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_398,c_27,c_25,c_24,c_23,c_22,c_21,c_73])).

cnf(c_1580,plain,
    ( m1_connsp_2(sK3(sK4,X0,X1),sK4,X1)
    | ~ l1_waybel_0(X0,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | r2_hidden(X1,k10_yellow_6(sK4,X0))
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_657,c_400])).

cnf(c_1581,plain,
    ( m1_connsp_2(sK3(sK4,sK6,X0),sK4,X0)
    | ~ l1_waybel_0(sK6,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r2_hidden(X0,k10_yellow_6(sK4,sK6))
    | ~ v4_orders_2(sK6)
    | v2_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_1580])).

cnf(c_17,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_375,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | sK6 != X2
    | sK5 != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_20])).

cnf(c_376,plain,
    ( ~ l1_waybel_0(sK5,sK4)
    | ~ v4_orders_2(sK5)
    | ~ v7_waybel_0(sK5)
    | ~ v2_struct_0(sK6)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | ~ l1_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_375])).

cnf(c_16,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v4_orders_2(X2)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_386,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ v4_orders_2(X0)
    | v4_orders_2(X2)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | sK6 != X2
    | sK5 != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_20])).

cnf(c_387,plain,
    ( ~ l1_waybel_0(sK5,sK4)
    | v4_orders_2(sK6)
    | ~ v4_orders_2(sK5)
    | ~ v7_waybel_0(sK5)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | ~ l1_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_386])).

cnf(c_14,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | l1_waybel_0(X0,X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_408,plain,
    ( ~ l1_waybel_0(X0,X1)
    | l1_waybel_0(X2,X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | sK6 != X2
    | sK5 != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_20])).

cnf(c_409,plain,
    ( l1_waybel_0(sK6,sK4)
    | ~ l1_waybel_0(sK5,sK4)
    | ~ v4_orders_2(sK5)
    | ~ v7_waybel_0(sK5)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | ~ l1_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_408])).

cnf(c_1585,plain,
    ( m1_connsp_2(sK3(sK4,sK6,X0),sK4,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r2_hidden(X0,k10_yellow_6(sK4,sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1581,c_27,c_25,c_24,c_23,c_22,c_21,c_73,c_376,c_387,c_409])).

cnf(c_6696,plain,
    ( m1_connsp_2(sK3(sK4,sK6,X0_58),sK4,X0_58)
    | ~ m1_subset_1(X0_58,u1_struct_0(sK4))
    | r2_hidden(X0_58,k10_yellow_6(sK4,sK6)) ),
    inference(subtyping,[status(esa)],[c_1585])).

cnf(c_7352,plain,
    ( m1_connsp_2(sK3(sK4,sK6,X0_58),sK4,X0_58) = iProver_top
    | m1_subset_1(X0_58,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0_58,k10_yellow_6(sK4,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6696])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | m1_subset_1(sK0(X1,X2,X0),X1)
    | r1_tarski(X2,X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_19,negated_conjecture,
    ( ~ r1_tarski(k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_300,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | m1_subset_1(sK0(X1,X2,X0),X1)
    | k10_yellow_6(sK4,sK6) != X0
    | k10_yellow_6(sK4,sK5) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_19])).

cnf(c_301,plain,
    ( m1_subset_1(sK0(X0,k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6)),X0)
    | ~ m1_subset_1(k10_yellow_6(sK4,sK6),k1_zfmisc_1(X0))
    | ~ m1_subset_1(k10_yellow_6(sK4,sK5),k1_zfmisc_1(X0)) ),
    inference(unflattening,[status(thm)],[c_300])).

cnf(c_6708,plain,
    ( m1_subset_1(sK0(X0_56,k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6)),X0_56)
    | ~ m1_subset_1(k10_yellow_6(sK4,sK6),k1_zfmisc_1(X0_56))
    | ~ m1_subset_1(k10_yellow_6(sK4,sK5),k1_zfmisc_1(X0_56)) ),
    inference(subtyping,[status(esa)],[c_301])).

cnf(c_7340,plain,
    ( m1_subset_1(sK0(X0_56,k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6)),X0_56) = iProver_top
    | m1_subset_1(k10_yellow_6(sK4,sK6),k1_zfmisc_1(X0_56)) != iProver_top
    | m1_subset_1(k10_yellow_6(sK4,sK5),k1_zfmisc_1(X0_56)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6708])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | r2_hidden(sK0(X1,X2,X0),X2)
    | r1_tarski(X2,X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_315,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | r2_hidden(sK0(X1,X2,X0),X2)
    | k10_yellow_6(sK4,sK6) != X0
    | k10_yellow_6(sK4,sK5) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_19])).

cnf(c_316,plain,
    ( ~ m1_subset_1(k10_yellow_6(sK4,sK6),k1_zfmisc_1(X0))
    | ~ m1_subset_1(k10_yellow_6(sK4,sK5),k1_zfmisc_1(X0))
    | r2_hidden(sK0(X0,k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6)),k10_yellow_6(sK4,sK5)) ),
    inference(unflattening,[status(thm)],[c_315])).

cnf(c_6707,plain,
    ( ~ m1_subset_1(k10_yellow_6(sK4,sK6),k1_zfmisc_1(X0_56))
    | ~ m1_subset_1(k10_yellow_6(sK4,sK5),k1_zfmisc_1(X0_56))
    | r2_hidden(sK0(X0_56,k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6)),k10_yellow_6(sK4,sK5)) ),
    inference(subtyping,[status(esa)],[c_316])).

cnf(c_7341,plain,
    ( m1_subset_1(k10_yellow_6(sK4,sK6),k1_zfmisc_1(X0_56)) != iProver_top
    | m1_subset_1(k10_yellow_6(sK4,sK5),k1_zfmisc_1(X0_56)) != iProver_top
    | r2_hidden(sK0(X0_56,k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6)),k10_yellow_6(sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6707])).

cnf(c_12,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r1_waybel_0(X1,X3,X0)
    | ~ l1_waybel_0(X3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(k10_yellow_6(X1,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k10_yellow_6(X1,X3))
    | ~ v2_pre_topc(X1)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_669,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r1_waybel_0(X1,X3,X0)
    | ~ l1_waybel_0(X3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(k10_yellow_6(X1,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k10_yellow_6(X1,X3))
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_26])).

cnf(c_670,plain,
    ( ~ m1_connsp_2(X0,sK4,X1)
    | r1_waybel_0(sK4,X2,X0)
    | ~ l1_waybel_0(X2,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(k10_yellow_6(sK4,X2),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X1,k10_yellow_6(sK4,X2))
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | v2_struct_0(X2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_669])).

cnf(c_674,plain,
    ( ~ m1_connsp_2(X0,sK4,X1)
    | r1_waybel_0(sK4,X2,X0)
    | ~ l1_waybel_0(X2,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(k10_yellow_6(sK4,X2),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X1,k10_yellow_6(sK4,X2))
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | v2_struct_0(X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_670,c_27,c_25])).

cnf(c_689,plain,
    ( ~ m1_connsp_2(X0,sK4,X1)
    | r1_waybel_0(sK4,X2,X0)
    | ~ l1_waybel_0(X2,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ r2_hidden(X1,k10_yellow_6(sK4,X2))
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | v2_struct_0(X2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_674,c_639])).

cnf(c_1714,plain,
    ( ~ m1_connsp_2(X0,sK4,X1)
    | r1_waybel_0(sK4,X2,X0)
    | ~ l1_waybel_0(X2,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ r2_hidden(X1,k10_yellow_6(sK4,X2))
    | ~ v4_orders_2(X2)
    | v2_struct_0(X2)
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_689,c_22])).

cnf(c_1715,plain,
    ( ~ m1_connsp_2(X0,sK4,X1)
    | r1_waybel_0(sK4,sK5,X0)
    | ~ l1_waybel_0(sK5,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ r2_hidden(X1,k10_yellow_6(sK4,sK5))
    | ~ v4_orders_2(sK5)
    | v2_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_1714])).

cnf(c_1719,plain,
    ( r1_waybel_0(sK4,sK5,X0)
    | ~ m1_connsp_2(X0,sK4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ r2_hidden(X1,k10_yellow_6(sK4,sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1715,c_24,c_23,c_21])).

cnf(c_1720,plain,
    ( ~ m1_connsp_2(X0,sK4,X1)
    | r1_waybel_0(sK4,sK5,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ r2_hidden(X1,k10_yellow_6(sK4,sK5)) ),
    inference(renaming,[status(thm)],[c_1719])).

cnf(c_6690,plain,
    ( ~ m1_connsp_2(X0_57,sK4,X0_58)
    | r1_waybel_0(sK4,sK5,X0_57)
    | ~ m1_subset_1(X0_58,u1_struct_0(sK4))
    | ~ r2_hidden(X0_58,k10_yellow_6(sK4,sK5)) ),
    inference(subtyping,[status(esa)],[c_1720])).

cnf(c_7358,plain,
    ( m1_connsp_2(X0_57,sK4,X0_58) != iProver_top
    | r1_waybel_0(sK4,sK5,X0_57) = iProver_top
    | m1_subset_1(X0_58,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0_58,k10_yellow_6(sK4,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6690])).

cnf(c_7640,plain,
    ( m1_connsp_2(X0_57,sK4,sK0(X0_56,k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6))) != iProver_top
    | r1_waybel_0(sK4,sK5,X0_57) = iProver_top
    | m1_subset_1(sK0(X0_56,k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6)),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(k10_yellow_6(sK4,sK6),k1_zfmisc_1(X0_56)) != iProver_top
    | m1_subset_1(k10_yellow_6(sK4,sK5),k1_zfmisc_1(X0_56)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7341,c_7358])).

cnf(c_8041,plain,
    ( m1_connsp_2(X0_57,sK4,sK0(u1_struct_0(sK4),k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6))) != iProver_top
    | r1_waybel_0(sK4,sK5,X0_57) = iProver_top
    | m1_subset_1(k10_yellow_6(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(k10_yellow_6(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7340,c_7640])).

cnf(c_28,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_30,plain,
    ( l1_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_31,plain,
    ( v2_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_32,plain,
    ( v4_orders_2(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_33,plain,
    ( v7_waybel_0(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_34,plain,
    ( l1_waybel_0(sK5,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_72,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_74,plain,
    ( l1_pre_topc(sK4) != iProver_top
    | l1_struct_0(sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_72])).

cnf(c_377,plain,
    ( l1_waybel_0(sK5,sK4) != iProver_top
    | v4_orders_2(sK5) != iProver_top
    | v7_waybel_0(sK5) != iProver_top
    | v2_struct_0(sK6) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_376])).

cnf(c_388,plain,
    ( l1_waybel_0(sK5,sK4) != iProver_top
    | v4_orders_2(sK6) = iProver_top
    | v4_orders_2(sK5) != iProver_top
    | v7_waybel_0(sK5) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_387])).

cnf(c_410,plain,
    ( l1_waybel_0(sK6,sK4) = iProver_top
    | l1_waybel_0(sK5,sK4) != iProver_top
    | v4_orders_2(sK5) != iProver_top
    | v7_waybel_0(sK5) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_409])).

cnf(c_1479,plain,
    ( ~ l1_waybel_0(X0,sK4)
    | m1_subset_1(k10_yellow_6(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_639,c_22])).

cnf(c_1480,plain,
    ( ~ l1_waybel_0(sK5,sK4)
    | m1_subset_1(k10_yellow_6(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v4_orders_2(sK5)
    | v2_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_1479])).

cnf(c_1481,plain,
    ( l1_waybel_0(sK5,sK4) != iProver_top
    | m1_subset_1(k10_yellow_6(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | v4_orders_2(sK5) != iProver_top
    | v2_struct_0(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1480])).

cnf(c_1601,plain,
    ( ~ l1_waybel_0(X0,sK4)
    | m1_subset_1(k10_yellow_6(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_639,c_400])).

cnf(c_1602,plain,
    ( ~ l1_waybel_0(sK6,sK4)
    | m1_subset_1(k10_yellow_6(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v4_orders_2(sK6)
    | v2_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_1601])).

cnf(c_1603,plain,
    ( l1_waybel_0(sK6,sK4) != iProver_top
    | m1_subset_1(k10_yellow_6(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | v4_orders_2(sK6) != iProver_top
    | v2_struct_0(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1602])).

cnf(c_8133,plain,
    ( m1_connsp_2(X0_57,sK4,sK0(u1_struct_0(sK4),k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6))) != iProver_top
    | r1_waybel_0(sK4,sK5,X0_57) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8041,c_28,c_30,c_31,c_32,c_33,c_34,c_74,c_377,c_388,c_410,c_1481,c_1603])).

cnf(c_8148,plain,
    ( r1_waybel_0(sK4,sK5,sK3(sK4,sK6,sK0(u1_struct_0(sK4),k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6)))) = iProver_top
    | m1_subset_1(sK0(u1_struct_0(sK4),k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6)),u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK0(u1_struct_0(sK4),k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6)),k10_yellow_6(sK4,sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7352,c_8133])).

cnf(c_5,plain,
    ( ~ r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
    | ~ r1_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_430,plain,
    ( ~ r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
    | ~ r1_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_3,c_5])).

cnf(c_870,plain,
    ( ~ r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
    | ~ r1_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_430,c_25])).

cnf(c_871,plain,
    ( ~ r2_waybel_0(sK4,X0,k6_subset_1(u1_struct_0(sK4),X1))
    | ~ r1_waybel_0(sK4,X0,X1)
    | ~ l1_waybel_0(X0,sK4)
    | v2_struct_0(X0)
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_870])).

cnf(c_875,plain,
    ( v2_struct_0(X0)
    | ~ l1_waybel_0(X0,sK4)
    | ~ r1_waybel_0(sK4,X0,X1)
    | ~ r2_waybel_0(sK4,X0,k6_subset_1(u1_struct_0(sK4),X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_871,c_27])).

cnf(c_876,plain,
    ( ~ r2_waybel_0(sK4,X0,k6_subset_1(u1_struct_0(sK4),X1))
    | ~ r1_waybel_0(sK4,X0,X1)
    | ~ l1_waybel_0(X0,sK4)
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_875])).

cnf(c_1832,plain,
    ( ~ r2_waybel_0(sK4,X0,k6_subset_1(u1_struct_0(sK4),X1))
    | ~ r1_waybel_0(sK4,X0,X1)
    | v2_struct_0(X0)
    | sK5 != X0
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_876])).

cnf(c_1833,plain,
    ( ~ r2_waybel_0(sK4,sK5,k6_subset_1(u1_struct_0(sK4),X0))
    | ~ r1_waybel_0(sK4,sK5,X0)
    | v2_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_1832])).

cnf(c_4349,plain,
    ( ~ r1_waybel_0(sK4,sK5,X0)
    | ~ r2_waybel_0(sK4,sK5,k6_subset_1(u1_struct_0(sK4),X0)) ),
    inference(prop_impl,[status(thm)],[c_24,c_1833])).

cnf(c_4350,plain,
    ( ~ r2_waybel_0(sK4,sK5,k6_subset_1(u1_struct_0(sK4),X0))
    | ~ r1_waybel_0(sK4,sK5,X0) ),
    inference(renaming,[status(thm)],[c_4349])).

cnf(c_6688,plain,
    ( ~ r2_waybel_0(sK4,sK5,k6_subset_1(u1_struct_0(sK4),X0_57))
    | ~ r1_waybel_0(sK4,sK5,X0_57) ),
    inference(subtyping,[status(esa)],[c_4350])).

cnf(c_7966,plain,
    ( ~ r2_waybel_0(sK4,sK5,k6_subset_1(u1_struct_0(sK4),sK3(sK4,sK6,sK0(u1_struct_0(sK4),k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6)))))
    | ~ r1_waybel_0(sK4,sK5,sK3(sK4,sK6,sK0(u1_struct_0(sK4),k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6)))) ),
    inference(instantiation,[status(thm)],[c_6688])).

cnf(c_7967,plain,
    ( r2_waybel_0(sK4,sK5,k6_subset_1(u1_struct_0(sK4),sK3(sK4,sK6,sK0(u1_struct_0(sK4),k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6))))) != iProver_top
    | r1_waybel_0(sK4,sK5,sK3(sK4,sK6,sK0(u1_struct_0(sK4),k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7966])).

cnf(c_18,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ r2_waybel_0(X1,X0,X3)
    | r2_waybel_0(X1,X2,X3)
    | ~ l1_waybel_0(X2,X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_357,plain,
    ( ~ r2_waybel_0(X0,X1,X2)
    | r2_waybel_0(X0,X3,X2)
    | ~ l1_waybel_0(X3,X0)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | v2_struct_0(X3)
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | sK6 != X1
    | sK5 != X3
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_20])).

cnf(c_358,plain,
    ( ~ r2_waybel_0(sK4,sK6,X0)
    | r2_waybel_0(sK4,sK5,X0)
    | ~ l1_waybel_0(sK5,sK4)
    | ~ v4_orders_2(sK5)
    | ~ v7_waybel_0(sK5)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | ~ l1_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_357])).

cnf(c_362,plain,
    ( ~ r2_waybel_0(sK4,sK6,X0)
    | r2_waybel_0(sK4,sK5,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_358,c_27,c_25,c_24,c_23,c_22,c_21,c_73])).

cnf(c_6705,plain,
    ( ~ r2_waybel_0(sK4,sK6,X0_55)
    | r2_waybel_0(sK4,sK5,X0_55) ),
    inference(subtyping,[status(esa)],[c_362])).

cnf(c_7904,plain,
    ( ~ r2_waybel_0(sK4,sK6,k6_subset_1(u1_struct_0(sK4),sK3(sK4,sK6,sK0(u1_struct_0(sK4),k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6)))))
    | r2_waybel_0(sK4,sK5,k6_subset_1(u1_struct_0(sK4),sK3(sK4,sK6,sK0(u1_struct_0(sK4),k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6))))) ),
    inference(instantiation,[status(thm)],[c_6705])).

cnf(c_7905,plain,
    ( r2_waybel_0(sK4,sK6,k6_subset_1(u1_struct_0(sK4),sK3(sK4,sK6,sK0(u1_struct_0(sK4),k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6))))) != iProver_top
    | r2_waybel_0(sK4,sK5,k6_subset_1(u1_struct_0(sK4),sK3(sK4,sK6,sK0(u1_struct_0(sK4),k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7904])).

cnf(c_411,plain,
    ( l1_waybel_0(sK6,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_409,c_27,c_25,c_24,c_23,c_22,c_21,c_73])).

cnf(c_4,plain,
    ( r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
    | r1_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_453,plain,
    ( r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
    | r1_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_3,c_4])).

cnf(c_848,plain,
    ( r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
    | r1_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_453,c_25])).

cnf(c_849,plain,
    ( r2_waybel_0(sK4,X0,k6_subset_1(u1_struct_0(sK4),X1))
    | r1_waybel_0(sK4,X0,X1)
    | ~ l1_waybel_0(X0,sK4)
    | v2_struct_0(X0)
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_848])).

cnf(c_853,plain,
    ( v2_struct_0(X0)
    | ~ l1_waybel_0(X0,sK4)
    | r1_waybel_0(sK4,X0,X1)
    | r2_waybel_0(sK4,X0,k6_subset_1(u1_struct_0(sK4),X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_849,c_27])).

cnf(c_854,plain,
    ( r2_waybel_0(sK4,X0,k6_subset_1(u1_struct_0(sK4),X1))
    | r1_waybel_0(sK4,X0,X1)
    | ~ l1_waybel_0(X0,sK4)
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_853])).

cnf(c_1886,plain,
    ( r2_waybel_0(sK4,X0,k6_subset_1(u1_struct_0(sK4),X1))
    | r1_waybel_0(sK4,X0,X1)
    | v2_struct_0(X0)
    | sK6 != X0
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_411,c_854])).

cnf(c_1887,plain,
    ( r2_waybel_0(sK4,sK6,k6_subset_1(u1_struct_0(sK4),X0))
    | r1_waybel_0(sK4,sK6,X0)
    | v2_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_1886])).

cnf(c_4355,plain,
    ( r1_waybel_0(sK4,sK6,X0)
    | r2_waybel_0(sK4,sK6,k6_subset_1(u1_struct_0(sK4),X0)) ),
    inference(prop_impl,[status(thm)],[c_27,c_25,c_24,c_23,c_22,c_21,c_73,c_376,c_1887])).

cnf(c_4356,plain,
    ( r2_waybel_0(sK4,sK6,k6_subset_1(u1_struct_0(sK4),X0))
    | r1_waybel_0(sK4,sK6,X0) ),
    inference(renaming,[status(thm)],[c_4355])).

cnf(c_6685,plain,
    ( r2_waybel_0(sK4,sK6,k6_subset_1(u1_struct_0(sK4),X0_57))
    | r1_waybel_0(sK4,sK6,X0_57) ),
    inference(subtyping,[status(esa)],[c_4356])).

cnf(c_7791,plain,
    ( r2_waybel_0(sK4,sK6,k6_subset_1(u1_struct_0(sK4),sK3(sK4,sK6,sK0(u1_struct_0(sK4),k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6)))))
    | r1_waybel_0(sK4,sK6,sK3(sK4,sK6,sK0(u1_struct_0(sK4),k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6)))) ),
    inference(instantiation,[status(thm)],[c_6685])).

cnf(c_7792,plain,
    ( r2_waybel_0(sK4,sK6,k6_subset_1(u1_struct_0(sK4),sK3(sK4,sK6,sK0(u1_struct_0(sK4),k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6))))) = iProver_top
    | r1_waybel_0(sK4,sK6,sK3(sK4,sK6,sK0(u1_struct_0(sK4),k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7791])).

cnf(c_10,plain,
    ( ~ r1_waybel_0(X0,X1,sK3(X0,X1,X2))
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | r2_hidden(X2,k10_yellow_6(X0,X1))
    | ~ v2_pre_topc(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_526,plain,
    ( ~ r1_waybel_0(X0,X1,sK3(X0,X1,X2))
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | r2_hidden(X2,k10_yellow_6(X0,X1))
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_26])).

cnf(c_527,plain,
    ( ~ r1_waybel_0(sK4,X0,sK3(sK4,X0,X1))
    | ~ l1_waybel_0(X0,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(k10_yellow_6(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(X1,k10_yellow_6(sK4,X0))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_526])).

cnf(c_531,plain,
    ( ~ r1_waybel_0(sK4,X0,sK3(sK4,X0,X1))
    | ~ l1_waybel_0(X0,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(k10_yellow_6(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(X1,k10_yellow_6(sK4,X0))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_527,c_27,c_25])).

cnf(c_658,plain,
    ( ~ r1_waybel_0(sK4,X0,sK3(sK4,X0,X1))
    | ~ l1_waybel_0(X0,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | r2_hidden(X1,k10_yellow_6(sK4,X0))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_639,c_531])).

cnf(c_1559,plain,
    ( ~ r1_waybel_0(sK4,X0,sK3(sK4,X0,X1))
    | ~ l1_waybel_0(X0,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | r2_hidden(X1,k10_yellow_6(sK4,X0))
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_658,c_400])).

cnf(c_1560,plain,
    ( ~ r1_waybel_0(sK4,sK6,sK3(sK4,sK6,X0))
    | ~ l1_waybel_0(sK6,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r2_hidden(X0,k10_yellow_6(sK4,sK6))
    | ~ v4_orders_2(sK6)
    | v2_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_1559])).

cnf(c_1564,plain,
    ( ~ r1_waybel_0(sK4,sK6,sK3(sK4,sK6,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r2_hidden(X0,k10_yellow_6(sK4,sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1560,c_27,c_25,c_24,c_23,c_22,c_21,c_73,c_376,c_387,c_409])).

cnf(c_6697,plain,
    ( ~ r1_waybel_0(sK4,sK6,sK3(sK4,sK6,X0_58))
    | ~ m1_subset_1(X0_58,u1_struct_0(sK4))
    | r2_hidden(X0_58,k10_yellow_6(sK4,sK6)) ),
    inference(subtyping,[status(esa)],[c_1564])).

cnf(c_7661,plain,
    ( ~ r1_waybel_0(sK4,sK6,sK3(sK4,sK6,sK0(u1_struct_0(sK4),k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6))))
    | ~ m1_subset_1(sK0(u1_struct_0(sK4),k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6)),u1_struct_0(sK4))
    | r2_hidden(sK0(u1_struct_0(sK4),k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6)),k10_yellow_6(sK4,sK6)) ),
    inference(instantiation,[status(thm)],[c_6697])).

cnf(c_7662,plain,
    ( r1_waybel_0(sK4,sK6,sK3(sK4,sK6,sK0(u1_struct_0(sK4),k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6)))) != iProver_top
    | m1_subset_1(sK0(u1_struct_0(sK4),k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6)),u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK0(u1_struct_0(sK4),k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6)),k10_yellow_6(sK4,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7661])).

cnf(c_7586,plain,
    ( m1_subset_1(sK0(u1_struct_0(sK4),k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6)),u1_struct_0(sK4))
    | ~ m1_subset_1(k10_yellow_6(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(k10_yellow_6(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_6708])).

cnf(c_7587,plain,
    ( m1_subset_1(sK0(u1_struct_0(sK4),k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6)),u1_struct_0(sK4)) = iProver_top
    | m1_subset_1(k10_yellow_6(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(k10_yellow_6(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7586])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(sK0(X1,X2,X0),X0)
    | r1_tarski(X2,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_330,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(sK0(X1,X2,X0),X0)
    | k10_yellow_6(sK4,sK6) != X0
    | k10_yellow_6(sK4,sK5) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_19])).

cnf(c_331,plain,
    ( ~ m1_subset_1(k10_yellow_6(sK4,sK6),k1_zfmisc_1(X0))
    | ~ m1_subset_1(k10_yellow_6(sK4,sK5),k1_zfmisc_1(X0))
    | ~ r2_hidden(sK0(X0,k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6)),k10_yellow_6(sK4,sK6)) ),
    inference(unflattening,[status(thm)],[c_330])).

cnf(c_6706,plain,
    ( ~ m1_subset_1(k10_yellow_6(sK4,sK6),k1_zfmisc_1(X0_56))
    | ~ m1_subset_1(k10_yellow_6(sK4,sK5),k1_zfmisc_1(X0_56))
    | ~ r2_hidden(sK0(X0_56,k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6)),k10_yellow_6(sK4,sK6)) ),
    inference(subtyping,[status(esa)],[c_331])).

cnf(c_7580,plain,
    ( ~ m1_subset_1(k10_yellow_6(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(k10_yellow_6(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK0(u1_struct_0(sK4),k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6)),k10_yellow_6(sK4,sK6)) ),
    inference(instantiation,[status(thm)],[c_6706])).

cnf(c_7581,plain,
    ( m1_subset_1(k10_yellow_6(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(k10_yellow_6(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(sK0(u1_struct_0(sK4),k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6)),k10_yellow_6(sK4,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7580])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8148,c_7967,c_7905,c_7792,c_7662,c_7587,c_7581,c_1603,c_1481,c_410,c_388,c_377,c_74,c_34,c_33,c_32,c_31,c_30,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:21:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.17/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/0.99  
% 2.17/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.17/0.99  
% 2.17/0.99  ------  iProver source info
% 2.17/0.99  
% 2.17/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.17/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.17/0.99  git: non_committed_changes: false
% 2.17/0.99  git: last_make_outside_of_git: false
% 2.17/0.99  
% 2.17/0.99  ------ 
% 2.17/0.99  
% 2.17/0.99  ------ Input Options
% 2.17/0.99  
% 2.17/0.99  --out_options                           all
% 2.17/0.99  --tptp_safe_out                         true
% 2.17/0.99  --problem_path                          ""
% 2.17/0.99  --include_path                          ""
% 2.17/0.99  --clausifier                            res/vclausify_rel
% 2.17/0.99  --clausifier_options                    --mode clausify
% 2.17/0.99  --stdin                                 false
% 2.17/0.99  --stats_out                             all
% 2.17/0.99  
% 2.17/0.99  ------ General Options
% 2.17/0.99  
% 2.17/0.99  --fof                                   false
% 2.17/0.99  --time_out_real                         305.
% 2.17/0.99  --time_out_virtual                      -1.
% 2.17/0.99  --symbol_type_check                     false
% 2.17/0.99  --clausify_out                          false
% 2.17/0.99  --sig_cnt_out                           false
% 2.17/0.99  --trig_cnt_out                          false
% 2.17/0.99  --trig_cnt_out_tolerance                1.
% 2.17/0.99  --trig_cnt_out_sk_spl                   false
% 2.17/0.99  --abstr_cl_out                          false
% 2.17/0.99  
% 2.17/0.99  ------ Global Options
% 2.17/0.99  
% 2.17/0.99  --schedule                              default
% 2.17/0.99  --add_important_lit                     false
% 2.17/0.99  --prop_solver_per_cl                    1000
% 2.17/0.99  --min_unsat_core                        false
% 2.17/0.99  --soft_assumptions                      false
% 2.17/0.99  --soft_lemma_size                       3
% 2.17/0.99  --prop_impl_unit_size                   0
% 2.17/0.99  --prop_impl_unit                        []
% 2.17/0.99  --share_sel_clauses                     true
% 2.17/0.99  --reset_solvers                         false
% 2.17/0.99  --bc_imp_inh                            [conj_cone]
% 2.17/0.99  --conj_cone_tolerance                   3.
% 2.17/0.99  --extra_neg_conj                        none
% 2.17/0.99  --large_theory_mode                     true
% 2.17/0.99  --prolific_symb_bound                   200
% 2.17/0.99  --lt_threshold                          2000
% 2.17/0.99  --clause_weak_htbl                      true
% 2.17/0.99  --gc_record_bc_elim                     false
% 2.17/0.99  
% 2.17/0.99  ------ Preprocessing Options
% 2.17/0.99  
% 2.17/0.99  --preprocessing_flag                    true
% 2.17/0.99  --time_out_prep_mult                    0.1
% 2.17/0.99  --splitting_mode                        input
% 2.17/0.99  --splitting_grd                         true
% 2.17/0.99  --splitting_cvd                         false
% 2.17/0.99  --splitting_cvd_svl                     false
% 2.17/0.99  --splitting_nvd                         32
% 2.17/0.99  --sub_typing                            true
% 2.17/0.99  --prep_gs_sim                           true
% 2.17/0.99  --prep_unflatten                        true
% 2.17/0.99  --prep_res_sim                          true
% 2.17/0.99  --prep_upred                            true
% 2.17/0.99  --prep_sem_filter                       exhaustive
% 2.17/0.99  --prep_sem_filter_out                   false
% 2.17/0.99  --pred_elim                             true
% 2.17/0.99  --res_sim_input                         true
% 2.17/0.99  --eq_ax_congr_red                       true
% 2.17/0.99  --pure_diseq_elim                       true
% 2.17/0.99  --brand_transform                       false
% 2.17/0.99  --non_eq_to_eq                          false
% 2.17/0.99  --prep_def_merge                        true
% 2.17/0.99  --prep_def_merge_prop_impl              false
% 2.17/0.99  --prep_def_merge_mbd                    true
% 2.17/0.99  --prep_def_merge_tr_red                 false
% 2.17/0.99  --prep_def_merge_tr_cl                  false
% 2.17/0.99  --smt_preprocessing                     true
% 2.17/0.99  --smt_ac_axioms                         fast
% 2.17/0.99  --preprocessed_out                      false
% 2.17/0.99  --preprocessed_stats                    false
% 2.17/0.99  
% 2.17/0.99  ------ Abstraction refinement Options
% 2.17/0.99  
% 2.17/0.99  --abstr_ref                             []
% 2.17/0.99  --abstr_ref_prep                        false
% 2.17/0.99  --abstr_ref_until_sat                   false
% 2.17/0.99  --abstr_ref_sig_restrict                funpre
% 2.17/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.17/0.99  --abstr_ref_under                       []
% 2.17/0.99  
% 2.17/0.99  ------ SAT Options
% 2.17/0.99  
% 2.17/0.99  --sat_mode                              false
% 2.17/0.99  --sat_fm_restart_options                ""
% 2.17/0.99  --sat_gr_def                            false
% 2.17/0.99  --sat_epr_types                         true
% 2.17/0.99  --sat_non_cyclic_types                  false
% 2.17/0.99  --sat_finite_models                     false
% 2.17/0.99  --sat_fm_lemmas                         false
% 2.17/0.99  --sat_fm_prep                           false
% 2.17/0.99  --sat_fm_uc_incr                        true
% 2.17/0.99  --sat_out_model                         small
% 2.17/0.99  --sat_out_clauses                       false
% 2.17/0.99  
% 2.17/0.99  ------ QBF Options
% 2.17/0.99  
% 2.17/0.99  --qbf_mode                              false
% 2.17/0.99  --qbf_elim_univ                         false
% 2.17/0.99  --qbf_dom_inst                          none
% 2.17/0.99  --qbf_dom_pre_inst                      false
% 2.17/0.99  --qbf_sk_in                             false
% 2.17/0.99  --qbf_pred_elim                         true
% 2.17/0.99  --qbf_split                             512
% 2.17/0.99  
% 2.17/0.99  ------ BMC1 Options
% 2.17/0.99  
% 2.17/0.99  --bmc1_incremental                      false
% 2.17/0.99  --bmc1_axioms                           reachable_all
% 2.17/0.99  --bmc1_min_bound                        0
% 2.17/0.99  --bmc1_max_bound                        -1
% 2.17/0.99  --bmc1_max_bound_default                -1
% 2.17/0.99  --bmc1_symbol_reachability              true
% 2.17/0.99  --bmc1_property_lemmas                  false
% 2.17/0.99  --bmc1_k_induction                      false
% 2.17/0.99  --bmc1_non_equiv_states                 false
% 2.17/0.99  --bmc1_deadlock                         false
% 2.17/0.99  --bmc1_ucm                              false
% 2.17/0.99  --bmc1_add_unsat_core                   none
% 2.17/0.99  --bmc1_unsat_core_children              false
% 2.17/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.17/0.99  --bmc1_out_stat                         full
% 2.17/0.99  --bmc1_ground_init                      false
% 2.17/0.99  --bmc1_pre_inst_next_state              false
% 2.17/0.99  --bmc1_pre_inst_state                   false
% 2.17/0.99  --bmc1_pre_inst_reach_state             false
% 2.17/0.99  --bmc1_out_unsat_core                   false
% 2.17/0.99  --bmc1_aig_witness_out                  false
% 2.17/0.99  --bmc1_verbose                          false
% 2.17/0.99  --bmc1_dump_clauses_tptp                false
% 2.17/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.17/0.99  --bmc1_dump_file                        -
% 2.17/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.17/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.17/0.99  --bmc1_ucm_extend_mode                  1
% 2.17/0.99  --bmc1_ucm_init_mode                    2
% 2.17/0.99  --bmc1_ucm_cone_mode                    none
% 2.17/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.17/0.99  --bmc1_ucm_relax_model                  4
% 2.17/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.17/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.17/0.99  --bmc1_ucm_layered_model                none
% 2.17/0.99  --bmc1_ucm_max_lemma_size               10
% 2.17/0.99  
% 2.17/0.99  ------ AIG Options
% 2.17/0.99  
% 2.17/0.99  --aig_mode                              false
% 2.17/0.99  
% 2.17/0.99  ------ Instantiation Options
% 2.17/0.99  
% 2.17/0.99  --instantiation_flag                    true
% 2.17/0.99  --inst_sos_flag                         false
% 2.17/0.99  --inst_sos_phase                        true
% 2.17/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.17/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.17/0.99  --inst_lit_sel_side                     num_symb
% 2.17/0.99  --inst_solver_per_active                1400
% 2.17/0.99  --inst_solver_calls_frac                1.
% 2.17/0.99  --inst_passive_queue_type               priority_queues
% 2.17/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.17/0.99  --inst_passive_queues_freq              [25;2]
% 2.17/0.99  --inst_dismatching                      true
% 2.17/0.99  --inst_eager_unprocessed_to_passive     true
% 2.17/0.99  --inst_prop_sim_given                   true
% 2.17/0.99  --inst_prop_sim_new                     false
% 2.17/0.99  --inst_subs_new                         false
% 2.17/0.99  --inst_eq_res_simp                      false
% 2.17/0.99  --inst_subs_given                       false
% 2.17/0.99  --inst_orphan_elimination               true
% 2.17/0.99  --inst_learning_loop_flag               true
% 2.17/0.99  --inst_learning_start                   3000
% 2.17/0.99  --inst_learning_factor                  2
% 2.17/0.99  --inst_start_prop_sim_after_learn       3
% 2.17/0.99  --inst_sel_renew                        solver
% 2.17/0.99  --inst_lit_activity_flag                true
% 2.17/0.99  --inst_restr_to_given                   false
% 2.17/0.99  --inst_activity_threshold               500
% 2.17/0.99  --inst_out_proof                        true
% 2.17/0.99  
% 2.17/0.99  ------ Resolution Options
% 2.17/0.99  
% 2.17/0.99  --resolution_flag                       true
% 2.17/0.99  --res_lit_sel                           adaptive
% 2.17/0.99  --res_lit_sel_side                      none
% 2.17/0.99  --res_ordering                          kbo
% 2.17/0.99  --res_to_prop_solver                    active
% 2.17/0.99  --res_prop_simpl_new                    false
% 2.17/0.99  --res_prop_simpl_given                  true
% 2.17/0.99  --res_passive_queue_type                priority_queues
% 2.17/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.17/0.99  --res_passive_queues_freq               [15;5]
% 2.17/0.99  --res_forward_subs                      full
% 2.17/0.99  --res_backward_subs                     full
% 2.17/0.99  --res_forward_subs_resolution           true
% 2.17/0.99  --res_backward_subs_resolution          true
% 2.17/0.99  --res_orphan_elimination                true
% 2.17/0.99  --res_time_limit                        2.
% 2.17/0.99  --res_out_proof                         true
% 2.17/0.99  
% 2.17/0.99  ------ Superposition Options
% 2.17/0.99  
% 2.17/0.99  --superposition_flag                    true
% 2.17/0.99  --sup_passive_queue_type                priority_queues
% 2.17/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.17/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.17/0.99  --demod_completeness_check              fast
% 2.17/0.99  --demod_use_ground                      true
% 2.17/0.99  --sup_to_prop_solver                    passive
% 2.17/0.99  --sup_prop_simpl_new                    true
% 2.17/0.99  --sup_prop_simpl_given                  true
% 2.17/0.99  --sup_fun_splitting                     false
% 2.17/0.99  --sup_smt_interval                      50000
% 2.17/0.99  
% 2.17/0.99  ------ Superposition Simplification Setup
% 2.17/0.99  
% 2.17/0.99  --sup_indices_passive                   []
% 2.17/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.17/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.17/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.17/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.17/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.17/0.99  --sup_full_bw                           [BwDemod]
% 2.17/0.99  --sup_immed_triv                        [TrivRules]
% 2.17/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.17/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.17/0.99  --sup_immed_bw_main                     []
% 2.17/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.17/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.17/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.17/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.17/0.99  
% 2.17/0.99  ------ Combination Options
% 2.17/0.99  
% 2.17/0.99  --comb_res_mult                         3
% 2.17/0.99  --comb_sup_mult                         2
% 2.17/0.99  --comb_inst_mult                        10
% 2.17/0.99  
% 2.17/0.99  ------ Debug Options
% 2.17/0.99  
% 2.17/0.99  --dbg_backtrace                         false
% 2.17/0.99  --dbg_dump_prop_clauses                 false
% 2.17/0.99  --dbg_dump_prop_clauses_file            -
% 2.17/0.99  --dbg_out_stat                          false
% 2.17/0.99  ------ Parsing...
% 2.17/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.17/0.99  
% 2.17/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 9 0s  sf_e  pe_s  pe_e 
% 2.17/0.99  
% 2.17/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.17/0.99  
% 2.17/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.17/0.99  ------ Proving...
% 2.17/0.99  ------ Problem Properties 
% 2.17/0.99  
% 2.17/0.99  
% 2.17/0.99  clauses                                 24
% 2.17/0.99  conjectures                             0
% 2.17/0.99  EPR                                     1
% 2.17/0.99  Horn                                    14
% 2.17/0.99  unary                                   2
% 2.17/0.99  binary                                  5
% 2.17/0.99  lits                                    73
% 2.17/0.99  lits eq                                 8
% 2.17/0.99  fd_pure                                 0
% 2.17/0.99  fd_pseudo                               0
% 2.17/0.99  fd_cond                                 8
% 2.17/0.99  fd_pseudo_cond                          0
% 2.17/0.99  AC symbols                              0
% 2.17/0.99  
% 2.17/0.99  ------ Schedule dynamic 5 is on 
% 2.17/0.99  
% 2.17/0.99  ------ no conjectures: strip conj schedule 
% 2.17/0.99  
% 2.17/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" stripped conjectures Time Limit: 10.
% 2.17/0.99  
% 2.17/0.99  
% 2.17/0.99  ------ 
% 2.17/0.99  Current options:
% 2.17/0.99  ------ 
% 2.17/0.99  
% 2.17/0.99  ------ Input Options
% 2.17/0.99  
% 2.17/0.99  --out_options                           all
% 2.17/0.99  --tptp_safe_out                         true
% 2.17/0.99  --problem_path                          ""
% 2.17/0.99  --include_path                          ""
% 2.17/0.99  --clausifier                            res/vclausify_rel
% 2.17/0.99  --clausifier_options                    --mode clausify
% 2.17/0.99  --stdin                                 false
% 2.17/0.99  --stats_out                             all
% 2.17/0.99  
% 2.17/0.99  ------ General Options
% 2.17/0.99  
% 2.17/0.99  --fof                                   false
% 2.17/0.99  --time_out_real                         305.
% 2.17/0.99  --time_out_virtual                      -1.
% 2.17/0.99  --symbol_type_check                     false
% 2.17/0.99  --clausify_out                          false
% 2.17/0.99  --sig_cnt_out                           false
% 2.17/0.99  --trig_cnt_out                          false
% 2.17/0.99  --trig_cnt_out_tolerance                1.
% 2.17/0.99  --trig_cnt_out_sk_spl                   false
% 2.17/0.99  --abstr_cl_out                          false
% 2.17/0.99  
% 2.17/0.99  ------ Global Options
% 2.17/0.99  
% 2.17/0.99  --schedule                              default
% 2.17/0.99  --add_important_lit                     false
% 2.17/0.99  --prop_solver_per_cl                    1000
% 2.17/0.99  --min_unsat_core                        false
% 2.17/0.99  --soft_assumptions                      false
% 2.17/0.99  --soft_lemma_size                       3
% 2.17/0.99  --prop_impl_unit_size                   0
% 2.17/0.99  --prop_impl_unit                        []
% 2.17/0.99  --share_sel_clauses                     true
% 2.17/0.99  --reset_solvers                         false
% 2.17/0.99  --bc_imp_inh                            [conj_cone]
% 2.17/0.99  --conj_cone_tolerance                   3.
% 2.17/0.99  --extra_neg_conj                        none
% 2.17/0.99  --large_theory_mode                     true
% 2.17/0.99  --prolific_symb_bound                   200
% 2.17/0.99  --lt_threshold                          2000
% 2.17/0.99  --clause_weak_htbl                      true
% 2.17/0.99  --gc_record_bc_elim                     false
% 2.17/0.99  
% 2.17/0.99  ------ Preprocessing Options
% 2.17/0.99  
% 2.17/0.99  --preprocessing_flag                    true
% 2.17/0.99  --time_out_prep_mult                    0.1
% 2.17/0.99  --splitting_mode                        input
% 2.17/0.99  --splitting_grd                         true
% 2.17/0.99  --splitting_cvd                         false
% 2.17/0.99  --splitting_cvd_svl                     false
% 2.17/0.99  --splitting_nvd                         32
% 2.17/0.99  --sub_typing                            true
% 2.17/0.99  --prep_gs_sim                           true
% 2.17/0.99  --prep_unflatten                        true
% 2.17/0.99  --prep_res_sim                          true
% 2.17/0.99  --prep_upred                            true
% 2.17/0.99  --prep_sem_filter                       exhaustive
% 2.17/0.99  --prep_sem_filter_out                   false
% 2.17/0.99  --pred_elim                             true
% 2.17/0.99  --res_sim_input                         true
% 2.17/0.99  --eq_ax_congr_red                       true
% 2.17/0.99  --pure_diseq_elim                       true
% 2.17/0.99  --brand_transform                       false
% 2.17/0.99  --non_eq_to_eq                          false
% 2.17/0.99  --prep_def_merge                        true
% 2.17/0.99  --prep_def_merge_prop_impl              false
% 2.17/0.99  --prep_def_merge_mbd                    true
% 2.17/0.99  --prep_def_merge_tr_red                 false
% 2.17/0.99  --prep_def_merge_tr_cl                  false
% 2.17/0.99  --smt_preprocessing                     true
% 2.17/0.99  --smt_ac_axioms                         fast
% 2.17/0.99  --preprocessed_out                      false
% 2.17/0.99  --preprocessed_stats                    false
% 2.17/0.99  
% 2.17/0.99  ------ Abstraction refinement Options
% 2.17/0.99  
% 2.17/0.99  --abstr_ref                             []
% 2.17/0.99  --abstr_ref_prep                        false
% 2.17/0.99  --abstr_ref_until_sat                   false
% 2.17/0.99  --abstr_ref_sig_restrict                funpre
% 2.17/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.17/0.99  --abstr_ref_under                       []
% 2.17/0.99  
% 2.17/0.99  ------ SAT Options
% 2.17/0.99  
% 2.17/0.99  --sat_mode                              false
% 2.17/0.99  --sat_fm_restart_options                ""
% 2.17/0.99  --sat_gr_def                            false
% 2.17/0.99  --sat_epr_types                         true
% 2.17/0.99  --sat_non_cyclic_types                  false
% 2.17/0.99  --sat_finite_models                     false
% 2.17/0.99  --sat_fm_lemmas                         false
% 2.17/0.99  --sat_fm_prep                           false
% 2.17/0.99  --sat_fm_uc_incr                        true
% 2.17/0.99  --sat_out_model                         small
% 2.17/0.99  --sat_out_clauses                       false
% 2.17/0.99  
% 2.17/0.99  ------ QBF Options
% 2.17/0.99  
% 2.17/0.99  --qbf_mode                              false
% 2.17/0.99  --qbf_elim_univ                         false
% 2.17/0.99  --qbf_dom_inst                          none
% 2.17/0.99  --qbf_dom_pre_inst                      false
% 2.17/0.99  --qbf_sk_in                             false
% 2.17/0.99  --qbf_pred_elim                         true
% 2.17/0.99  --qbf_split                             512
% 2.17/0.99  
% 2.17/0.99  ------ BMC1 Options
% 2.17/0.99  
% 2.17/0.99  --bmc1_incremental                      false
% 2.17/0.99  --bmc1_axioms                           reachable_all
% 2.17/0.99  --bmc1_min_bound                        0
% 2.17/0.99  --bmc1_max_bound                        -1
% 2.17/0.99  --bmc1_max_bound_default                -1
% 2.17/0.99  --bmc1_symbol_reachability              true
% 2.17/0.99  --bmc1_property_lemmas                  false
% 2.17/0.99  --bmc1_k_induction                      false
% 2.17/0.99  --bmc1_non_equiv_states                 false
% 2.17/0.99  --bmc1_deadlock                         false
% 2.17/0.99  --bmc1_ucm                              false
% 2.17/0.99  --bmc1_add_unsat_core                   none
% 2.17/0.99  --bmc1_unsat_core_children              false
% 2.17/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.17/0.99  --bmc1_out_stat                         full
% 2.17/0.99  --bmc1_ground_init                      false
% 2.17/0.99  --bmc1_pre_inst_next_state              false
% 2.17/0.99  --bmc1_pre_inst_state                   false
% 2.17/0.99  --bmc1_pre_inst_reach_state             false
% 2.17/0.99  --bmc1_out_unsat_core                   false
% 2.17/0.99  --bmc1_aig_witness_out                  false
% 2.17/0.99  --bmc1_verbose                          false
% 2.17/0.99  --bmc1_dump_clauses_tptp                false
% 2.17/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.17/0.99  --bmc1_dump_file                        -
% 2.17/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.17/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.17/0.99  --bmc1_ucm_extend_mode                  1
% 2.17/0.99  --bmc1_ucm_init_mode                    2
% 2.17/0.99  --bmc1_ucm_cone_mode                    none
% 2.17/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.17/0.99  --bmc1_ucm_relax_model                  4
% 2.17/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.17/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.17/0.99  --bmc1_ucm_layered_model                none
% 2.17/0.99  --bmc1_ucm_max_lemma_size               10
% 2.17/0.99  
% 2.17/0.99  ------ AIG Options
% 2.17/0.99  
% 2.17/0.99  --aig_mode                              false
% 2.17/0.99  
% 2.17/0.99  ------ Instantiation Options
% 2.17/0.99  
% 2.17/0.99  --instantiation_flag                    true
% 2.17/0.99  --inst_sos_flag                         false
% 2.17/0.99  --inst_sos_phase                        true
% 2.17/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.17/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.17/0.99  --inst_lit_sel_side                     none
% 2.17/0.99  --inst_solver_per_active                1400
% 2.17/0.99  --inst_solver_calls_frac                1.
% 2.17/0.99  --inst_passive_queue_type               priority_queues
% 2.17/0.99  --inst_passive_queues                   [[-num_var];[+age;-num_symb]]
% 2.17/0.99  --inst_passive_queues_freq              [25;2]
% 2.17/0.99  --inst_dismatching                      true
% 2.17/0.99  --inst_eager_unprocessed_to_passive     true
% 2.17/0.99  --inst_prop_sim_given                   true
% 2.17/0.99  --inst_prop_sim_new                     false
% 2.17/0.99  --inst_subs_new                         false
% 2.17/0.99  --inst_eq_res_simp                      false
% 2.17/0.99  --inst_subs_given                       false
% 2.17/0.99  --inst_orphan_elimination               true
% 2.17/0.99  --inst_learning_loop_flag               true
% 2.17/0.99  --inst_learning_start                   3000
% 2.17/0.99  --inst_learning_factor                  2
% 2.17/0.99  --inst_start_prop_sim_after_learn       3
% 2.17/0.99  --inst_sel_renew                        solver
% 2.17/0.99  --inst_lit_activity_flag                true
% 2.17/0.99  --inst_restr_to_given                   false
% 2.17/0.99  --inst_activity_threshold               500
% 2.17/0.99  --inst_out_proof                        true
% 2.17/0.99  
% 2.17/0.99  ------ Resolution Options
% 2.17/0.99  
% 2.17/0.99  --resolution_flag                       false
% 2.17/0.99  --res_lit_sel                           adaptive
% 2.17/0.99  --res_lit_sel_side                      none
% 2.17/0.99  --res_ordering                          kbo
% 2.17/0.99  --res_to_prop_solver                    active
% 2.17/0.99  --res_prop_simpl_new                    false
% 2.17/0.99  --res_prop_simpl_given                  true
% 2.17/0.99  --res_passive_queue_type                priority_queues
% 2.17/0.99  --res_passive_queues                    [[-num_symb];[+age;-num_symb]]
% 2.17/0.99  --res_passive_queues_freq               [15;5]
% 2.17/0.99  --res_forward_subs                      full
% 2.17/0.99  --res_backward_subs                     full
% 2.17/0.99  --res_forward_subs_resolution           true
% 2.17/0.99  --res_backward_subs_resolution          true
% 2.17/0.99  --res_orphan_elimination                true
% 2.17/0.99  --res_time_limit                        2.
% 2.17/0.99  --res_out_proof                         true
% 2.17/0.99  
% 2.17/0.99  ------ Superposition Options
% 2.17/0.99  
% 2.17/0.99  --superposition_flag                    true
% 2.17/0.99  --sup_passive_queue_type                priority_queues
% 2.17/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.17/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.17/0.99  --demod_completeness_check              fast
% 2.17/0.99  --demod_use_ground                      true
% 2.17/0.99  --sup_to_prop_solver                    passive
% 2.17/0.99  --sup_prop_simpl_new                    true
% 2.17/0.99  --sup_prop_simpl_given                  true
% 2.17/0.99  --sup_fun_splitting                     false
% 2.17/0.99  --sup_smt_interval                      50000
% 2.17/0.99  
% 2.17/0.99  ------ Superposition Simplification Setup
% 2.17/0.99  
% 2.17/0.99  --sup_indices_passive                   []
% 2.17/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.17/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.17/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.17/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.17/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.17/0.99  --sup_full_bw                           [BwDemod]
% 2.17/0.99  --sup_immed_triv                        [TrivRules]
% 2.17/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.17/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.17/0.99  --sup_immed_bw_main                     []
% 2.17/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.17/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.17/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.17/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.17/0.99  
% 2.17/0.99  ------ Combination Options
% 2.17/0.99  
% 2.17/0.99  --comb_res_mult                         3
% 2.17/0.99  --comb_sup_mult                         2
% 2.17/0.99  --comb_inst_mult                        10
% 2.17/0.99  
% 2.17/0.99  ------ Debug Options
% 2.17/0.99  
% 2.17/0.99  --dbg_backtrace                         false
% 2.17/0.99  --dbg_dump_prop_clauses                 false
% 2.17/0.99  --dbg_dump_prop_clauses_file            -
% 2.17/0.99  --dbg_out_stat                          false
% 2.17/0.99  
% 2.17/0.99  
% 2.17/0.99  
% 2.17/0.99  
% 2.17/0.99  ------ Proving...
% 2.17/0.99  
% 2.17/0.99  
% 2.17/0.99  % SZS status Theorem for theBenchmark.p
% 2.17/0.99  
% 2.17/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.17/0.99  
% 2.17/0.99  fof(f5,axiom,(
% 2.17/0.99    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.17/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/0.99  
% 2.17/0.99  fof(f17,plain,(
% 2.17/0.99    ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.17/0.99    inference(ennf_transformation,[],[f5])).
% 2.17/0.99  
% 2.17/0.99  fof(f18,plain,(
% 2.17/0.99    ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.17/0.99    inference(flattening,[],[f17])).
% 2.17/0.99  
% 2.17/0.99  fof(f52,plain,(
% 2.17/0.99    ( ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.17/0.99    inference(cnf_transformation,[],[f18])).
% 2.17/0.99  
% 2.17/0.99  fof(f8,conjecture,(
% 2.17/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m2_yellow_6(X2,X0,X1) => r1_tarski(k10_yellow_6(X0,X1),k10_yellow_6(X0,X2)))))),
% 2.17/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/0.99  
% 2.17/0.99  fof(f9,negated_conjecture,(
% 2.17/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m2_yellow_6(X2,X0,X1) => r1_tarski(k10_yellow_6(X0,X1),k10_yellow_6(X0,X2)))))),
% 2.17/0.99    inference(negated_conjecture,[],[f8])).
% 2.17/0.99  
% 2.17/0.99  fof(f23,plain,(
% 2.17/0.99    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k10_yellow_6(X0,X1),k10_yellow_6(X0,X2)) & m2_yellow_6(X2,X0,X1)) & (l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.17/0.99    inference(ennf_transformation,[],[f9])).
% 2.17/0.99  
% 2.17/0.99  fof(f24,plain,(
% 2.17/0.99    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k10_yellow_6(X0,X1),k10_yellow_6(X0,X2)) & m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.17/0.99    inference(flattening,[],[f23])).
% 2.17/0.99  
% 2.17/0.99  fof(f37,plain,(
% 2.17/0.99    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k10_yellow_6(X0,X1),k10_yellow_6(X0,X2)) & m2_yellow_6(X2,X0,X1)) => (~r1_tarski(k10_yellow_6(X0,X1),k10_yellow_6(X0,sK6)) & m2_yellow_6(sK6,X0,X1))) )),
% 2.17/0.99    introduced(choice_axiom,[])).
% 2.17/0.99  
% 2.17/0.99  fof(f36,plain,(
% 2.17/0.99    ( ! [X0] : (? [X1] : (? [X2] : (~r1_tarski(k10_yellow_6(X0,X1),k10_yellow_6(X0,X2)) & m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (? [X2] : (~r1_tarski(k10_yellow_6(X0,sK5),k10_yellow_6(X0,X2)) & m2_yellow_6(X2,X0,sK5)) & l1_waybel_0(sK5,X0) & v7_waybel_0(sK5) & v4_orders_2(sK5) & ~v2_struct_0(sK5))) )),
% 2.17/0.99    introduced(choice_axiom,[])).
% 2.17/0.99  
% 2.17/0.99  fof(f35,plain,(
% 2.17/0.99    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k10_yellow_6(X0,X1),k10_yellow_6(X0,X2)) & m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k10_yellow_6(sK4,X1),k10_yellow_6(sK4,X2)) & m2_yellow_6(X2,sK4,X1)) & l1_waybel_0(X1,sK4) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4))),
% 2.17/0.99    introduced(choice_axiom,[])).
% 2.17/0.99  
% 2.17/0.99  fof(f38,plain,(
% 2.17/0.99    ((~r1_tarski(k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6)) & m2_yellow_6(sK6,sK4,sK5)) & l1_waybel_0(sK5,sK4) & v7_waybel_0(sK5) & v4_orders_2(sK5) & ~v2_struct_0(sK5)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4)),
% 2.17/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f24,f37,f36,f35])).
% 2.17/0.99  
% 2.17/0.99  fof(f59,plain,(
% 2.17/0.99    v2_pre_topc(sK4)),
% 2.17/0.99    inference(cnf_transformation,[],[f38])).
% 2.17/0.99  
% 2.17/0.99  fof(f58,plain,(
% 2.17/0.99    ~v2_struct_0(sK4)),
% 2.17/0.99    inference(cnf_transformation,[],[f38])).
% 2.17/0.99  
% 2.17/0.99  fof(f60,plain,(
% 2.17/0.99    l1_pre_topc(sK4)),
% 2.17/0.99    inference(cnf_transformation,[],[f38])).
% 2.17/0.99  
% 2.17/0.99  fof(f4,axiom,(
% 2.17/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (k10_yellow_6(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) <=> ! [X4] : (m1_connsp_2(X4,X0,X3) => r1_waybel_0(X0,X1,X4))))))))),
% 2.17/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/0.99  
% 2.17/0.99  fof(f15,plain,(
% 2.17/0.99    ! [X0] : (! [X1] : (! [X2] : ((k10_yellow_6(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3))) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.17/0.99    inference(ennf_transformation,[],[f4])).
% 2.17/0.99  
% 2.17/0.99  fof(f16,plain,(
% 2.17/0.99    ! [X0] : (! [X1] : (! [X2] : ((k10_yellow_6(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3))) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.17/0.99    inference(flattening,[],[f15])).
% 2.17/0.99  
% 2.17/0.99  fof(f28,plain,(
% 2.17/0.99    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | ? [X3] : (((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | r2_hidden(X3,X2))) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3))) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.17/0.99    inference(nnf_transformation,[],[f16])).
% 2.17/0.99  
% 2.17/0.99  fof(f29,plain,(
% 2.17/0.99    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | ? [X3] : ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | r2_hidden(X3,X2)) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3))) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.17/0.99    inference(flattening,[],[f28])).
% 2.17/0.99  
% 2.17/0.99  fof(f30,plain,(
% 2.17/0.99    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | ? [X3] : ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,X3)) | r2_hidden(X3,X2)) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X6] : (((r2_hidden(X6,X2) | ? [X7] : (~r1_waybel_0(X0,X1,X7) & m1_connsp_2(X7,X0,X6))) & (! [X8] : (r1_waybel_0(X0,X1,X8) | ~m1_connsp_2(X8,X0,X6)) | ~r2_hidden(X6,X2))) | ~m1_subset_1(X6,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.17/0.99    inference(rectify,[],[f29])).
% 2.17/0.99  
% 2.17/0.99  fof(f33,plain,(
% 2.17/0.99    ! [X6,X1,X0] : (? [X7] : (~r1_waybel_0(X0,X1,X7) & m1_connsp_2(X7,X0,X6)) => (~r1_waybel_0(X0,X1,sK3(X0,X1,X6)) & m1_connsp_2(sK3(X0,X1,X6),X0,X6)))),
% 2.17/0.99    introduced(choice_axiom,[])).
% 2.17/0.99  
% 2.17/0.99  fof(f32,plain,(
% 2.17/0.99    ( ! [X3] : (! [X2,X1,X0] : (? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) => (~r1_waybel_0(X0,X1,sK2(X0,X1,X2)) & m1_connsp_2(sK2(X0,X1,X2),X0,X3)))) )),
% 2.17/0.99    introduced(choice_axiom,[])).
% 2.17/0.99  
% 2.17/0.99  fof(f31,plain,(
% 2.17/0.99    ! [X2,X1,X0] : (? [X3] : ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,X3)) | r2_hidden(X3,X2)) & m1_subset_1(X3,u1_struct_0(X0))) => ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,sK1(X0,X1,X2))) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,sK1(X0,X1,X2))) | r2_hidden(sK1(X0,X1,X2),X2)) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))))),
% 2.17/0.99    introduced(choice_axiom,[])).
% 2.17/0.99  
% 2.17/0.99  fof(f34,plain,(
% 2.17/0.99    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | (((~r1_waybel_0(X0,X1,sK2(X0,X1,X2)) & m1_connsp_2(sK2(X0,X1,X2),X0,sK1(X0,X1,X2))) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,sK1(X0,X1,X2))) | r2_hidden(sK1(X0,X1,X2),X2)) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)))) & (! [X6] : (((r2_hidden(X6,X2) | (~r1_waybel_0(X0,X1,sK3(X0,X1,X6)) & m1_connsp_2(sK3(X0,X1,X6),X0,X6))) & (! [X8] : (r1_waybel_0(X0,X1,X8) | ~m1_connsp_2(X8,X0,X6)) | ~r2_hidden(X6,X2))) | ~m1_subset_1(X6,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.17/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f30,f33,f32,f31])).
% 2.17/0.99  
% 2.17/0.99  fof(f46,plain,(
% 2.17/0.99    ( ! [X6,X2,X0,X1] : (r2_hidden(X6,X2) | m1_connsp_2(sK3(X0,X1,X6),X0,X6) | ~m1_subset_1(X6,u1_struct_0(X0)) | k10_yellow_6(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.17/0.99    inference(cnf_transformation,[],[f34])).
% 2.17/0.99  
% 2.17/0.99  fof(f68,plain,(
% 2.17/0.99    ( ! [X6,X0,X1] : (r2_hidden(X6,k10_yellow_6(X0,X1)) | m1_connsp_2(sK3(X0,X1,X6),X0,X6) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.17/0.99    inference(equality_resolution,[],[f46])).
% 2.17/0.99  
% 2.17/0.99  fof(f6,axiom,(
% 2.17/0.99    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_yellow_6(X2,X0,X1) => (l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2))))),
% 2.17/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/0.99  
% 2.17/0.99  fof(f19,plain,(
% 2.17/0.99    ! [X0,X1] : (! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.17/0.99    inference(ennf_transformation,[],[f6])).
% 2.17/0.99  
% 2.17/0.99  fof(f20,plain,(
% 2.17/0.99    ! [X0,X1] : (! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.17/0.99    inference(flattening,[],[f19])).
% 2.17/0.99  
% 2.17/0.99  fof(f55,plain,(
% 2.17/0.99    ( ! [X2,X0,X1] : (v7_waybel_0(X2) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.17/0.99    inference(cnf_transformation,[],[f20])).
% 2.17/0.99  
% 2.17/0.99  fof(f65,plain,(
% 2.17/0.99    m2_yellow_6(sK6,sK4,sK5)),
% 2.17/0.99    inference(cnf_transformation,[],[f38])).
% 2.17/0.99  
% 2.17/0.99  fof(f61,plain,(
% 2.17/0.99    ~v2_struct_0(sK5)),
% 2.17/0.99    inference(cnf_transformation,[],[f38])).
% 2.17/0.99  
% 2.17/0.99  fof(f62,plain,(
% 2.17/0.99    v4_orders_2(sK5)),
% 2.17/0.99    inference(cnf_transformation,[],[f38])).
% 2.17/0.99  
% 2.17/0.99  fof(f63,plain,(
% 2.17/0.99    v7_waybel_0(sK5)),
% 2.17/0.99    inference(cnf_transformation,[],[f38])).
% 2.17/0.99  
% 2.17/0.99  fof(f64,plain,(
% 2.17/0.99    l1_waybel_0(sK5,sK4)),
% 2.17/0.99    inference(cnf_transformation,[],[f38])).
% 2.17/0.99  
% 2.17/0.99  fof(f2,axiom,(
% 2.17/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.17/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/0.99  
% 2.17/0.99  fof(f12,plain,(
% 2.17/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.17/0.99    inference(ennf_transformation,[],[f2])).
% 2.17/0.99  
% 2.17/0.99  fof(f42,plain,(
% 2.17/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.17/0.99    inference(cnf_transformation,[],[f12])).
% 2.17/0.99  
% 2.17/0.99  fof(f53,plain,(
% 2.17/0.99    ( ! [X2,X0,X1] : (~v2_struct_0(X2) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.17/0.99    inference(cnf_transformation,[],[f20])).
% 2.17/0.99  
% 2.17/0.99  fof(f54,plain,(
% 2.17/0.99    ( ! [X2,X0,X1] : (v4_orders_2(X2) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.17/0.99    inference(cnf_transformation,[],[f20])).
% 2.17/0.99  
% 2.17/0.99  fof(f56,plain,(
% 2.17/0.99    ( ! [X2,X0,X1] : (l1_waybel_0(X2,X0) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.17/0.99    inference(cnf_transformation,[],[f20])).
% 2.17/0.99  
% 2.17/0.99  fof(f1,axiom,(
% 2.17/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) => r2_hidden(X3,X2))) => r1_tarski(X1,X2))))),
% 2.17/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/0.99  
% 2.17/0.99  fof(f10,plain,(
% 2.17/0.99    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) | ? [X3] : ((~r2_hidden(X3,X2) & r2_hidden(X3,X1)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.17/0.99    inference(ennf_transformation,[],[f1])).
% 2.17/0.99  
% 2.17/0.99  fof(f11,plain,(
% 2.17/0.99    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | ? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.17/0.99    inference(flattening,[],[f10])).
% 2.17/0.99  
% 2.17/0.99  fof(f25,plain,(
% 2.17/0.99    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) => (~r2_hidden(sK0(X0,X1,X2),X2) & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),X0)))),
% 2.17/0.99    introduced(choice_axiom,[])).
% 2.17/0.99  
% 2.17/0.99  fof(f26,plain,(
% 2.17/0.99    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | (~r2_hidden(sK0(X0,X1,X2),X2) & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.17/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f25])).
% 2.17/0.99  
% 2.17/0.99  fof(f39,plain,(
% 2.17/0.99    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | m1_subset_1(sK0(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.17/0.99    inference(cnf_transformation,[],[f26])).
% 2.17/0.99  
% 2.17/0.99  fof(f66,plain,(
% 2.17/0.99    ~r1_tarski(k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6))),
% 2.17/0.99    inference(cnf_transformation,[],[f38])).
% 2.17/0.99  
% 2.17/0.99  fof(f40,plain,(
% 2.17/0.99    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | r2_hidden(sK0(X0,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.17/0.99    inference(cnf_transformation,[],[f26])).
% 2.17/0.99  
% 2.17/0.99  fof(f45,plain,(
% 2.17/0.99    ( ! [X6,X2,X0,X8,X1] : (r1_waybel_0(X0,X1,X8) | ~m1_connsp_2(X8,X0,X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X0)) | k10_yellow_6(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.17/0.99    inference(cnf_transformation,[],[f34])).
% 2.17/0.99  
% 2.17/0.99  fof(f69,plain,(
% 2.17/0.99    ( ! [X6,X0,X8,X1] : (r1_waybel_0(X0,X1,X8) | ~m1_connsp_2(X8,X0,X6) | ~r2_hidden(X6,k10_yellow_6(X0,X1)) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.17/0.99    inference(equality_resolution,[],[f45])).
% 2.17/0.99  
% 2.17/0.99  fof(f3,axiom,(
% 2.17/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r1_waybel_0(X0,X1,X2) <=> ~r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)))))),
% 2.17/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/0.99  
% 2.17/0.99  fof(f13,plain,(
% 2.17/0.99    ! [X0] : (! [X1] : (! [X2] : (r1_waybel_0(X0,X1,X2) <=> ~r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.17/0.99    inference(ennf_transformation,[],[f3])).
% 2.17/0.99  
% 2.17/0.99  fof(f14,plain,(
% 2.17/0.99    ! [X0] : (! [X1] : (! [X2] : (r1_waybel_0(X0,X1,X2) <=> ~r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.17/0.99    inference(flattening,[],[f13])).
% 2.17/0.99  
% 2.17/0.99  fof(f27,plain,(
% 2.17/0.99    ! [X0] : (! [X1] : (! [X2] : ((r1_waybel_0(X0,X1,X2) | r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) & (~r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) | ~r1_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.17/0.99    inference(nnf_transformation,[],[f14])).
% 2.17/0.99  
% 2.17/0.99  fof(f43,plain,(
% 2.17/0.99    ( ! [X2,X0,X1] : (~r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) | ~r1_waybel_0(X0,X1,X2) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.17/0.99    inference(cnf_transformation,[],[f27])).
% 2.17/0.99  
% 2.17/0.99  fof(f7,axiom,(
% 2.17/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m2_yellow_6(X2,X0,X1) => ! [X3] : (r2_waybel_0(X0,X2,X3) => r2_waybel_0(X0,X1,X3)))))),
% 2.17/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/0.99  
% 2.17/0.99  fof(f21,plain,(
% 2.17/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_waybel_0(X0,X1,X3) | ~r2_waybel_0(X0,X2,X3)) | ~m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.17/0.99    inference(ennf_transformation,[],[f7])).
% 2.17/0.99  
% 2.17/0.99  fof(f22,plain,(
% 2.17/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_waybel_0(X0,X1,X3) | ~r2_waybel_0(X0,X2,X3)) | ~m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.17/0.99    inference(flattening,[],[f21])).
% 2.17/0.99  
% 2.17/0.99  fof(f57,plain,(
% 2.17/0.99    ( ! [X2,X0,X3,X1] : (r2_waybel_0(X0,X1,X3) | ~r2_waybel_0(X0,X2,X3) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.17/0.99    inference(cnf_transformation,[],[f22])).
% 2.17/0.99  
% 2.17/0.99  fof(f44,plain,(
% 2.17/0.99    ( ! [X2,X0,X1] : (r1_waybel_0(X0,X1,X2) | r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.17/0.99    inference(cnf_transformation,[],[f27])).
% 2.17/0.99  
% 2.17/0.99  fof(f47,plain,(
% 2.17/0.99    ( ! [X6,X2,X0,X1] : (r2_hidden(X6,X2) | ~r1_waybel_0(X0,X1,sK3(X0,X1,X6)) | ~m1_subset_1(X6,u1_struct_0(X0)) | k10_yellow_6(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.17/0.99    inference(cnf_transformation,[],[f34])).
% 2.17/0.99  
% 2.17/0.99  fof(f67,plain,(
% 2.17/0.99    ( ! [X6,X0,X1] : (r2_hidden(X6,k10_yellow_6(X0,X1)) | ~r1_waybel_0(X0,X1,sK3(X0,X1,X6)) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.17/0.99    inference(equality_resolution,[],[f47])).
% 2.17/0.99  
% 2.17/0.99  fof(f41,plain,(
% 2.17/0.99    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r2_hidden(sK0(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.17/0.99    inference(cnf_transformation,[],[f26])).
% 2.17/0.99  
% 2.17/0.99  cnf(c_13,plain,
% 2.17/0.99      ( ~ l1_waybel_0(X0,X1)
% 2.17/0.99      | m1_subset_1(k10_yellow_6(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.17/0.99      | ~ v2_pre_topc(X1)
% 2.17/0.99      | ~ v4_orders_2(X0)
% 2.17/0.99      | ~ v7_waybel_0(X0)
% 2.17/0.99      | v2_struct_0(X1)
% 2.17/0.99      | v2_struct_0(X0)
% 2.17/0.99      | ~ l1_pre_topc(X1) ),
% 2.17/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_26,negated_conjecture,
% 2.17/0.99      ( v2_pre_topc(sK4) ),
% 2.17/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_634,plain,
% 2.17/0.99      ( ~ l1_waybel_0(X0,X1)
% 2.17/0.99      | m1_subset_1(k10_yellow_6(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.17/0.99      | ~ v4_orders_2(X0)
% 2.17/0.99      | ~ v7_waybel_0(X0)
% 2.17/0.99      | v2_struct_0(X0)
% 2.17/0.99      | v2_struct_0(X1)
% 2.17/0.99      | ~ l1_pre_topc(X1)
% 2.17/0.99      | sK4 != X1 ),
% 2.17/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_26]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_635,plain,
% 2.17/0.99      ( ~ l1_waybel_0(X0,sK4)
% 2.17/0.99      | m1_subset_1(k10_yellow_6(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
% 2.17/0.99      | ~ v4_orders_2(X0)
% 2.17/0.99      | ~ v7_waybel_0(X0)
% 2.17/0.99      | v2_struct_0(X0)
% 2.17/0.99      | v2_struct_0(sK4)
% 2.17/0.99      | ~ l1_pre_topc(sK4) ),
% 2.17/0.99      inference(unflattening,[status(thm)],[c_634]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_27,negated_conjecture,
% 2.17/0.99      ( ~ v2_struct_0(sK4) ),
% 2.17/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_25,negated_conjecture,
% 2.17/0.99      ( l1_pre_topc(sK4) ),
% 2.17/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_639,plain,
% 2.17/0.99      ( ~ l1_waybel_0(X0,sK4)
% 2.17/0.99      | m1_subset_1(k10_yellow_6(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
% 2.17/0.99      | ~ v4_orders_2(X0)
% 2.17/0.99      | ~ v7_waybel_0(X0)
% 2.17/0.99      | v2_struct_0(X0) ),
% 2.17/0.99      inference(global_propositional_subsumption,
% 2.17/0.99                [status(thm)],
% 2.17/0.99                [c_635,c_27,c_25]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_11,plain,
% 2.17/0.99      ( m1_connsp_2(sK3(X0,X1,X2),X0,X2)
% 2.17/0.99      | ~ l1_waybel_0(X1,X0)
% 2.17/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.17/0.99      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 2.17/0.99      | r2_hidden(X2,k10_yellow_6(X0,X1))
% 2.17/0.99      | ~ v2_pre_topc(X0)
% 2.17/0.99      | ~ v4_orders_2(X1)
% 2.17/0.99      | ~ v7_waybel_0(X1)
% 2.17/0.99      | v2_struct_0(X0)
% 2.17/0.99      | v2_struct_0(X1)
% 2.17/0.99      | ~ l1_pre_topc(X0) ),
% 2.17/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_490,plain,
% 2.17/0.99      ( m1_connsp_2(sK3(X0,X1,X2),X0,X2)
% 2.17/0.99      | ~ l1_waybel_0(X1,X0)
% 2.17/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.17/0.99      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 2.17/0.99      | r2_hidden(X2,k10_yellow_6(X0,X1))
% 2.17/0.99      | ~ v4_orders_2(X1)
% 2.17/0.99      | ~ v7_waybel_0(X1)
% 2.17/0.99      | v2_struct_0(X0)
% 2.17/0.99      | v2_struct_0(X1)
% 2.17/0.99      | ~ l1_pre_topc(X0)
% 2.17/0.99      | sK4 != X0 ),
% 2.17/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_26]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_491,plain,
% 2.17/0.99      ( m1_connsp_2(sK3(sK4,X0,X1),sK4,X1)
% 2.17/0.99      | ~ l1_waybel_0(X0,sK4)
% 2.17/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.17/0.99      | ~ m1_subset_1(k10_yellow_6(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
% 2.17/0.99      | r2_hidden(X1,k10_yellow_6(sK4,X0))
% 2.17/0.99      | ~ v4_orders_2(X0)
% 2.17/0.99      | ~ v7_waybel_0(X0)
% 2.17/0.99      | v2_struct_0(X0)
% 2.17/0.99      | v2_struct_0(sK4)
% 2.17/0.99      | ~ l1_pre_topc(sK4) ),
% 2.17/0.99      inference(unflattening,[status(thm)],[c_490]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_495,plain,
% 2.17/0.99      ( m1_connsp_2(sK3(sK4,X0,X1),sK4,X1)
% 2.17/0.99      | ~ l1_waybel_0(X0,sK4)
% 2.17/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.17/0.99      | ~ m1_subset_1(k10_yellow_6(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
% 2.17/0.99      | r2_hidden(X1,k10_yellow_6(sK4,X0))
% 2.17/0.99      | ~ v4_orders_2(X0)
% 2.17/0.99      | ~ v7_waybel_0(X0)
% 2.17/0.99      | v2_struct_0(X0) ),
% 2.17/0.99      inference(global_propositional_subsumption,
% 2.17/0.99                [status(thm)],
% 2.17/0.99                [c_491,c_27,c_25]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_657,plain,
% 2.17/0.99      ( m1_connsp_2(sK3(sK4,X0,X1),sK4,X1)
% 2.17/0.99      | ~ l1_waybel_0(X0,sK4)
% 2.17/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.17/0.99      | r2_hidden(X1,k10_yellow_6(sK4,X0))
% 2.17/0.99      | ~ v4_orders_2(X0)
% 2.17/0.99      | ~ v7_waybel_0(X0)
% 2.17/0.99      | v2_struct_0(X0) ),
% 2.17/0.99      inference(backward_subsumption_resolution,
% 2.17/0.99                [status(thm)],
% 2.17/0.99                [c_639,c_495]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_15,plain,
% 2.17/0.99      ( ~ m2_yellow_6(X0,X1,X2)
% 2.17/0.99      | ~ l1_waybel_0(X2,X1)
% 2.17/0.99      | ~ v4_orders_2(X2)
% 2.17/0.99      | ~ v7_waybel_0(X2)
% 2.17/0.99      | v7_waybel_0(X0)
% 2.17/0.99      | v2_struct_0(X1)
% 2.17/0.99      | v2_struct_0(X2)
% 2.17/0.99      | ~ l1_struct_0(X1) ),
% 2.17/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_20,negated_conjecture,
% 2.17/0.99      ( m2_yellow_6(sK6,sK4,sK5) ),
% 2.17/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_397,plain,
% 2.17/0.99      ( ~ l1_waybel_0(X0,X1)
% 2.17/0.99      | ~ v4_orders_2(X0)
% 2.17/0.99      | ~ v7_waybel_0(X0)
% 2.17/0.99      | v7_waybel_0(X2)
% 2.17/0.99      | v2_struct_0(X0)
% 2.17/0.99      | v2_struct_0(X1)
% 2.17/0.99      | ~ l1_struct_0(X1)
% 2.17/0.99      | sK6 != X2
% 2.17/0.99      | sK5 != X0
% 2.17/0.99      | sK4 != X1 ),
% 2.17/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_20]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_398,plain,
% 2.17/0.99      ( ~ l1_waybel_0(sK5,sK4)
% 2.17/0.99      | ~ v4_orders_2(sK5)
% 2.17/0.99      | v7_waybel_0(sK6)
% 2.17/0.99      | ~ v7_waybel_0(sK5)
% 2.17/0.99      | v2_struct_0(sK5)
% 2.17/0.99      | v2_struct_0(sK4)
% 2.17/0.99      | ~ l1_struct_0(sK4) ),
% 2.17/0.99      inference(unflattening,[status(thm)],[c_397]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_24,negated_conjecture,
% 2.17/0.99      ( ~ v2_struct_0(sK5) ),
% 2.17/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_23,negated_conjecture,
% 2.17/0.99      ( v4_orders_2(sK5) ),
% 2.17/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_22,negated_conjecture,
% 2.17/0.99      ( v7_waybel_0(sK5) ),
% 2.17/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_21,negated_conjecture,
% 2.17/0.99      ( l1_waybel_0(sK5,sK4) ),
% 2.17/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_3,plain,
% 2.17/0.99      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.17/0.99      inference(cnf_transformation,[],[f42]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_73,plain,
% 2.17/0.99      ( ~ l1_pre_topc(sK4) | l1_struct_0(sK4) ),
% 2.17/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_400,plain,
% 2.17/0.99      ( v7_waybel_0(sK6) ),
% 2.17/0.99      inference(global_propositional_subsumption,
% 2.17/0.99                [status(thm)],
% 2.17/0.99                [c_398,c_27,c_25,c_24,c_23,c_22,c_21,c_73]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_1580,plain,
% 2.17/0.99      ( m1_connsp_2(sK3(sK4,X0,X1),sK4,X1)
% 2.17/0.99      | ~ l1_waybel_0(X0,sK4)
% 2.17/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.17/0.99      | r2_hidden(X1,k10_yellow_6(sK4,X0))
% 2.17/0.99      | ~ v4_orders_2(X0)
% 2.17/0.99      | v2_struct_0(X0)
% 2.17/0.99      | sK6 != X0 ),
% 2.17/0.99      inference(resolution_lifted,[status(thm)],[c_657,c_400]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_1581,plain,
% 2.17/0.99      ( m1_connsp_2(sK3(sK4,sK6,X0),sK4,X0)
% 2.17/0.99      | ~ l1_waybel_0(sK6,sK4)
% 2.17/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.17/0.99      | r2_hidden(X0,k10_yellow_6(sK4,sK6))
% 2.17/0.99      | ~ v4_orders_2(sK6)
% 2.17/0.99      | v2_struct_0(sK6) ),
% 2.17/0.99      inference(unflattening,[status(thm)],[c_1580]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_17,plain,
% 2.17/0.99      ( ~ m2_yellow_6(X0,X1,X2)
% 2.17/0.99      | ~ l1_waybel_0(X2,X1)
% 2.17/0.99      | ~ v4_orders_2(X2)
% 2.17/0.99      | ~ v7_waybel_0(X2)
% 2.17/0.99      | ~ v2_struct_0(X0)
% 2.17/0.99      | v2_struct_0(X1)
% 2.17/0.99      | v2_struct_0(X2)
% 2.17/0.99      | ~ l1_struct_0(X1) ),
% 2.17/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_375,plain,
% 2.17/0.99      ( ~ l1_waybel_0(X0,X1)
% 2.17/0.99      | ~ v4_orders_2(X0)
% 2.17/0.99      | ~ v7_waybel_0(X0)
% 2.17/0.99      | ~ v2_struct_0(X2)
% 2.17/0.99      | v2_struct_0(X0)
% 2.17/0.99      | v2_struct_0(X1)
% 2.17/0.99      | ~ l1_struct_0(X1)
% 2.17/0.99      | sK6 != X2
% 2.17/0.99      | sK5 != X0
% 2.17/0.99      | sK4 != X1 ),
% 2.17/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_20]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_376,plain,
% 2.17/0.99      ( ~ l1_waybel_0(sK5,sK4)
% 2.17/0.99      | ~ v4_orders_2(sK5)
% 2.17/0.99      | ~ v7_waybel_0(sK5)
% 2.17/0.99      | ~ v2_struct_0(sK6)
% 2.17/0.99      | v2_struct_0(sK5)
% 2.17/0.99      | v2_struct_0(sK4)
% 2.17/0.99      | ~ l1_struct_0(sK4) ),
% 2.17/0.99      inference(unflattening,[status(thm)],[c_375]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_16,plain,
% 2.17/0.99      ( ~ m2_yellow_6(X0,X1,X2)
% 2.17/0.99      | ~ l1_waybel_0(X2,X1)
% 2.17/0.99      | ~ v4_orders_2(X2)
% 2.17/0.99      | v4_orders_2(X0)
% 2.17/0.99      | ~ v7_waybel_0(X2)
% 2.17/0.99      | v2_struct_0(X1)
% 2.17/0.99      | v2_struct_0(X2)
% 2.17/0.99      | ~ l1_struct_0(X1) ),
% 2.17/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_386,plain,
% 2.17/0.99      ( ~ l1_waybel_0(X0,X1)
% 2.17/0.99      | ~ v4_orders_2(X0)
% 2.17/0.99      | v4_orders_2(X2)
% 2.17/0.99      | ~ v7_waybel_0(X0)
% 2.17/0.99      | v2_struct_0(X0)
% 2.17/0.99      | v2_struct_0(X1)
% 2.17/0.99      | ~ l1_struct_0(X1)
% 2.17/0.99      | sK6 != X2
% 2.17/0.99      | sK5 != X0
% 2.17/0.99      | sK4 != X1 ),
% 2.17/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_20]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_387,plain,
% 2.17/0.99      ( ~ l1_waybel_0(sK5,sK4)
% 2.17/0.99      | v4_orders_2(sK6)
% 2.17/0.99      | ~ v4_orders_2(sK5)
% 2.17/0.99      | ~ v7_waybel_0(sK5)
% 2.17/0.99      | v2_struct_0(sK5)
% 2.17/0.99      | v2_struct_0(sK4)
% 2.17/0.99      | ~ l1_struct_0(sK4) ),
% 2.17/0.99      inference(unflattening,[status(thm)],[c_386]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_14,plain,
% 2.17/0.99      ( ~ m2_yellow_6(X0,X1,X2)
% 2.17/0.99      | ~ l1_waybel_0(X2,X1)
% 2.17/0.99      | l1_waybel_0(X0,X1)
% 2.17/0.99      | ~ v4_orders_2(X2)
% 2.17/0.99      | ~ v7_waybel_0(X2)
% 2.17/0.99      | v2_struct_0(X1)
% 2.17/0.99      | v2_struct_0(X2)
% 2.17/0.99      | ~ l1_struct_0(X1) ),
% 2.17/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_408,plain,
% 2.17/0.99      ( ~ l1_waybel_0(X0,X1)
% 2.17/0.99      | l1_waybel_0(X2,X1)
% 2.17/0.99      | ~ v4_orders_2(X0)
% 2.17/0.99      | ~ v7_waybel_0(X0)
% 2.17/0.99      | v2_struct_0(X0)
% 2.17/0.99      | v2_struct_0(X1)
% 2.17/0.99      | ~ l1_struct_0(X1)
% 2.17/0.99      | sK6 != X2
% 2.17/0.99      | sK5 != X0
% 2.17/0.99      | sK4 != X1 ),
% 2.17/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_20]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_409,plain,
% 2.17/0.99      ( l1_waybel_0(sK6,sK4)
% 2.17/0.99      | ~ l1_waybel_0(sK5,sK4)
% 2.17/0.99      | ~ v4_orders_2(sK5)
% 2.17/0.99      | ~ v7_waybel_0(sK5)
% 2.17/0.99      | v2_struct_0(sK5)
% 2.17/0.99      | v2_struct_0(sK4)
% 2.17/0.99      | ~ l1_struct_0(sK4) ),
% 2.17/0.99      inference(unflattening,[status(thm)],[c_408]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_1585,plain,
% 2.17/0.99      ( m1_connsp_2(sK3(sK4,sK6,X0),sK4,X0)
% 2.17/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.17/0.99      | r2_hidden(X0,k10_yellow_6(sK4,sK6)) ),
% 2.17/0.99      inference(global_propositional_subsumption,
% 2.17/0.99                [status(thm)],
% 2.17/0.99                [c_1581,c_27,c_25,c_24,c_23,c_22,c_21,c_73,c_376,c_387,
% 2.17/0.99                 c_409]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_6696,plain,
% 2.17/0.99      ( m1_connsp_2(sK3(sK4,sK6,X0_58),sK4,X0_58)
% 2.17/0.99      | ~ m1_subset_1(X0_58,u1_struct_0(sK4))
% 2.17/0.99      | r2_hidden(X0_58,k10_yellow_6(sK4,sK6)) ),
% 2.17/0.99      inference(subtyping,[status(esa)],[c_1585]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_7352,plain,
% 2.17/0.99      ( m1_connsp_2(sK3(sK4,sK6,X0_58),sK4,X0_58) = iProver_top
% 2.17/0.99      | m1_subset_1(X0_58,u1_struct_0(sK4)) != iProver_top
% 2.17/0.99      | r2_hidden(X0_58,k10_yellow_6(sK4,sK6)) = iProver_top ),
% 2.17/0.99      inference(predicate_to_equality,[status(thm)],[c_6696]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_2,plain,
% 2.17/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.17/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.17/0.99      | m1_subset_1(sK0(X1,X2,X0),X1)
% 2.17/0.99      | r1_tarski(X2,X0) ),
% 2.17/0.99      inference(cnf_transformation,[],[f39]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_19,negated_conjecture,
% 2.17/0.99      ( ~ r1_tarski(k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6)) ),
% 2.17/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_300,plain,
% 2.17/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.17/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.17/0.99      | m1_subset_1(sK0(X1,X2,X0),X1)
% 2.17/0.99      | k10_yellow_6(sK4,sK6) != X0
% 2.17/0.99      | k10_yellow_6(sK4,sK5) != X2 ),
% 2.17/0.99      inference(resolution_lifted,[status(thm)],[c_2,c_19]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_301,plain,
% 2.17/0.99      ( m1_subset_1(sK0(X0,k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6)),X0)
% 2.17/0.99      | ~ m1_subset_1(k10_yellow_6(sK4,sK6),k1_zfmisc_1(X0))
% 2.17/0.99      | ~ m1_subset_1(k10_yellow_6(sK4,sK5),k1_zfmisc_1(X0)) ),
% 2.17/0.99      inference(unflattening,[status(thm)],[c_300]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_6708,plain,
% 2.17/0.99      ( m1_subset_1(sK0(X0_56,k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6)),X0_56)
% 2.17/0.99      | ~ m1_subset_1(k10_yellow_6(sK4,sK6),k1_zfmisc_1(X0_56))
% 2.17/0.99      | ~ m1_subset_1(k10_yellow_6(sK4,sK5),k1_zfmisc_1(X0_56)) ),
% 2.17/0.99      inference(subtyping,[status(esa)],[c_301]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_7340,plain,
% 2.17/0.99      ( m1_subset_1(sK0(X0_56,k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6)),X0_56) = iProver_top
% 2.17/0.99      | m1_subset_1(k10_yellow_6(sK4,sK6),k1_zfmisc_1(X0_56)) != iProver_top
% 2.17/0.99      | m1_subset_1(k10_yellow_6(sK4,sK5),k1_zfmisc_1(X0_56)) != iProver_top ),
% 2.17/0.99      inference(predicate_to_equality,[status(thm)],[c_6708]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_1,plain,
% 2.17/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.17/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.17/0.99      | r2_hidden(sK0(X1,X2,X0),X2)
% 2.17/0.99      | r1_tarski(X2,X0) ),
% 2.17/0.99      inference(cnf_transformation,[],[f40]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_315,plain,
% 2.17/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.17/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.17/0.99      | r2_hidden(sK0(X1,X2,X0),X2)
% 2.17/0.99      | k10_yellow_6(sK4,sK6) != X0
% 2.17/0.99      | k10_yellow_6(sK4,sK5) != X2 ),
% 2.17/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_19]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_316,plain,
% 2.17/0.99      ( ~ m1_subset_1(k10_yellow_6(sK4,sK6),k1_zfmisc_1(X0))
% 2.17/0.99      | ~ m1_subset_1(k10_yellow_6(sK4,sK5),k1_zfmisc_1(X0))
% 2.17/0.99      | r2_hidden(sK0(X0,k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6)),k10_yellow_6(sK4,sK5)) ),
% 2.17/0.99      inference(unflattening,[status(thm)],[c_315]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_6707,plain,
% 2.17/0.99      ( ~ m1_subset_1(k10_yellow_6(sK4,sK6),k1_zfmisc_1(X0_56))
% 2.17/0.99      | ~ m1_subset_1(k10_yellow_6(sK4,sK5),k1_zfmisc_1(X0_56))
% 2.17/0.99      | r2_hidden(sK0(X0_56,k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6)),k10_yellow_6(sK4,sK5)) ),
% 2.17/0.99      inference(subtyping,[status(esa)],[c_316]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_7341,plain,
% 2.17/0.99      ( m1_subset_1(k10_yellow_6(sK4,sK6),k1_zfmisc_1(X0_56)) != iProver_top
% 2.17/0.99      | m1_subset_1(k10_yellow_6(sK4,sK5),k1_zfmisc_1(X0_56)) != iProver_top
% 2.17/0.99      | r2_hidden(sK0(X0_56,k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6)),k10_yellow_6(sK4,sK5)) = iProver_top ),
% 2.17/0.99      inference(predicate_to_equality,[status(thm)],[c_6707]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_12,plain,
% 2.17/0.99      ( ~ m1_connsp_2(X0,X1,X2)
% 2.17/0.99      | r1_waybel_0(X1,X3,X0)
% 2.17/0.99      | ~ l1_waybel_0(X3,X1)
% 2.17/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.17/0.99      | ~ m1_subset_1(k10_yellow_6(X1,X3),k1_zfmisc_1(u1_struct_0(X1)))
% 2.17/0.99      | ~ r2_hidden(X2,k10_yellow_6(X1,X3))
% 2.17/0.99      | ~ v2_pre_topc(X1)
% 2.17/0.99      | ~ v4_orders_2(X3)
% 2.17/0.99      | ~ v7_waybel_0(X3)
% 2.17/0.99      | v2_struct_0(X1)
% 2.17/0.99      | v2_struct_0(X3)
% 2.17/0.99      | ~ l1_pre_topc(X1) ),
% 2.17/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_669,plain,
% 2.17/0.99      ( ~ m1_connsp_2(X0,X1,X2)
% 2.17/0.99      | r1_waybel_0(X1,X3,X0)
% 2.17/0.99      | ~ l1_waybel_0(X3,X1)
% 2.17/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.17/0.99      | ~ m1_subset_1(k10_yellow_6(X1,X3),k1_zfmisc_1(u1_struct_0(X1)))
% 2.17/0.99      | ~ r2_hidden(X2,k10_yellow_6(X1,X3))
% 2.17/0.99      | ~ v4_orders_2(X3)
% 2.17/0.99      | ~ v7_waybel_0(X3)
% 2.17/0.99      | v2_struct_0(X1)
% 2.17/0.99      | v2_struct_0(X3)
% 2.17/0.99      | ~ l1_pre_topc(X1)
% 2.17/0.99      | sK4 != X1 ),
% 2.17/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_26]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_670,plain,
% 2.17/0.99      ( ~ m1_connsp_2(X0,sK4,X1)
% 2.17/0.99      | r1_waybel_0(sK4,X2,X0)
% 2.17/0.99      | ~ l1_waybel_0(X2,sK4)
% 2.17/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.17/0.99      | ~ m1_subset_1(k10_yellow_6(sK4,X2),k1_zfmisc_1(u1_struct_0(sK4)))
% 2.17/0.99      | ~ r2_hidden(X1,k10_yellow_6(sK4,X2))
% 2.17/0.99      | ~ v4_orders_2(X2)
% 2.17/0.99      | ~ v7_waybel_0(X2)
% 2.17/0.99      | v2_struct_0(X2)
% 2.17/0.99      | v2_struct_0(sK4)
% 2.17/0.99      | ~ l1_pre_topc(sK4) ),
% 2.17/0.99      inference(unflattening,[status(thm)],[c_669]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_674,plain,
% 2.17/0.99      ( ~ m1_connsp_2(X0,sK4,X1)
% 2.17/0.99      | r1_waybel_0(sK4,X2,X0)
% 2.17/0.99      | ~ l1_waybel_0(X2,sK4)
% 2.17/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.17/0.99      | ~ m1_subset_1(k10_yellow_6(sK4,X2),k1_zfmisc_1(u1_struct_0(sK4)))
% 2.17/0.99      | ~ r2_hidden(X1,k10_yellow_6(sK4,X2))
% 2.17/0.99      | ~ v4_orders_2(X2)
% 2.17/0.99      | ~ v7_waybel_0(X2)
% 2.17/0.99      | v2_struct_0(X2) ),
% 2.17/0.99      inference(global_propositional_subsumption,
% 2.17/0.99                [status(thm)],
% 2.17/0.99                [c_670,c_27,c_25]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_689,plain,
% 2.17/0.99      ( ~ m1_connsp_2(X0,sK4,X1)
% 2.17/0.99      | r1_waybel_0(sK4,X2,X0)
% 2.17/0.99      | ~ l1_waybel_0(X2,sK4)
% 2.17/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.17/0.99      | ~ r2_hidden(X1,k10_yellow_6(sK4,X2))
% 2.17/0.99      | ~ v4_orders_2(X2)
% 2.17/0.99      | ~ v7_waybel_0(X2)
% 2.17/0.99      | v2_struct_0(X2) ),
% 2.17/0.99      inference(forward_subsumption_resolution,
% 2.17/0.99                [status(thm)],
% 2.17/0.99                [c_674,c_639]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_1714,plain,
% 2.17/0.99      ( ~ m1_connsp_2(X0,sK4,X1)
% 2.17/0.99      | r1_waybel_0(sK4,X2,X0)
% 2.17/0.99      | ~ l1_waybel_0(X2,sK4)
% 2.17/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.17/0.99      | ~ r2_hidden(X1,k10_yellow_6(sK4,X2))
% 2.17/0.99      | ~ v4_orders_2(X2)
% 2.17/0.99      | v2_struct_0(X2)
% 2.17/0.99      | sK5 != X2 ),
% 2.17/0.99      inference(resolution_lifted,[status(thm)],[c_689,c_22]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_1715,plain,
% 2.17/0.99      ( ~ m1_connsp_2(X0,sK4,X1)
% 2.17/0.99      | r1_waybel_0(sK4,sK5,X0)
% 2.17/0.99      | ~ l1_waybel_0(sK5,sK4)
% 2.17/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.17/0.99      | ~ r2_hidden(X1,k10_yellow_6(sK4,sK5))
% 2.17/0.99      | ~ v4_orders_2(sK5)
% 2.17/0.99      | v2_struct_0(sK5) ),
% 2.17/0.99      inference(unflattening,[status(thm)],[c_1714]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_1719,plain,
% 2.17/0.99      ( r1_waybel_0(sK4,sK5,X0)
% 2.17/0.99      | ~ m1_connsp_2(X0,sK4,X1)
% 2.17/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.17/0.99      | ~ r2_hidden(X1,k10_yellow_6(sK4,sK5)) ),
% 2.17/0.99      inference(global_propositional_subsumption,
% 2.17/0.99                [status(thm)],
% 2.17/0.99                [c_1715,c_24,c_23,c_21]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_1720,plain,
% 2.17/0.99      ( ~ m1_connsp_2(X0,sK4,X1)
% 2.17/0.99      | r1_waybel_0(sK4,sK5,X0)
% 2.17/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.17/0.99      | ~ r2_hidden(X1,k10_yellow_6(sK4,sK5)) ),
% 2.17/0.99      inference(renaming,[status(thm)],[c_1719]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_6690,plain,
% 2.17/0.99      ( ~ m1_connsp_2(X0_57,sK4,X0_58)
% 2.17/0.99      | r1_waybel_0(sK4,sK5,X0_57)
% 2.17/0.99      | ~ m1_subset_1(X0_58,u1_struct_0(sK4))
% 2.17/0.99      | ~ r2_hidden(X0_58,k10_yellow_6(sK4,sK5)) ),
% 2.17/0.99      inference(subtyping,[status(esa)],[c_1720]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_7358,plain,
% 2.17/0.99      ( m1_connsp_2(X0_57,sK4,X0_58) != iProver_top
% 2.17/0.99      | r1_waybel_0(sK4,sK5,X0_57) = iProver_top
% 2.17/0.99      | m1_subset_1(X0_58,u1_struct_0(sK4)) != iProver_top
% 2.17/0.99      | r2_hidden(X0_58,k10_yellow_6(sK4,sK5)) != iProver_top ),
% 2.17/0.99      inference(predicate_to_equality,[status(thm)],[c_6690]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_7640,plain,
% 2.17/0.99      ( m1_connsp_2(X0_57,sK4,sK0(X0_56,k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6))) != iProver_top
% 2.17/0.99      | r1_waybel_0(sK4,sK5,X0_57) = iProver_top
% 2.17/0.99      | m1_subset_1(sK0(X0_56,k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6)),u1_struct_0(sK4)) != iProver_top
% 2.17/0.99      | m1_subset_1(k10_yellow_6(sK4,sK6),k1_zfmisc_1(X0_56)) != iProver_top
% 2.17/0.99      | m1_subset_1(k10_yellow_6(sK4,sK5),k1_zfmisc_1(X0_56)) != iProver_top ),
% 2.17/0.99      inference(superposition,[status(thm)],[c_7341,c_7358]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_8041,plain,
% 2.17/0.99      ( m1_connsp_2(X0_57,sK4,sK0(u1_struct_0(sK4),k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6))) != iProver_top
% 2.17/0.99      | r1_waybel_0(sK4,sK5,X0_57) = iProver_top
% 2.17/0.99      | m1_subset_1(k10_yellow_6(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.17/0.99      | m1_subset_1(k10_yellow_6(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 2.17/0.99      inference(superposition,[status(thm)],[c_7340,c_7640]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_28,plain,
% 2.17/0.99      ( v2_struct_0(sK4) != iProver_top ),
% 2.17/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_30,plain,
% 2.17/0.99      ( l1_pre_topc(sK4) = iProver_top ),
% 2.17/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_31,plain,
% 2.17/0.99      ( v2_struct_0(sK5) != iProver_top ),
% 2.17/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_32,plain,
% 2.17/0.99      ( v4_orders_2(sK5) = iProver_top ),
% 2.17/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_33,plain,
% 2.17/0.99      ( v7_waybel_0(sK5) = iProver_top ),
% 2.17/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_34,plain,
% 2.17/0.99      ( l1_waybel_0(sK5,sK4) = iProver_top ),
% 2.17/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_72,plain,
% 2.17/0.99      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 2.17/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_74,plain,
% 2.17/0.99      ( l1_pre_topc(sK4) != iProver_top
% 2.17/0.99      | l1_struct_0(sK4) = iProver_top ),
% 2.17/0.99      inference(instantiation,[status(thm)],[c_72]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_377,plain,
% 2.17/0.99      ( l1_waybel_0(sK5,sK4) != iProver_top
% 2.17/0.99      | v4_orders_2(sK5) != iProver_top
% 2.17/0.99      | v7_waybel_0(sK5) != iProver_top
% 2.17/0.99      | v2_struct_0(sK6) != iProver_top
% 2.17/0.99      | v2_struct_0(sK5) = iProver_top
% 2.17/0.99      | v2_struct_0(sK4) = iProver_top
% 2.17/0.99      | l1_struct_0(sK4) != iProver_top ),
% 2.17/0.99      inference(predicate_to_equality,[status(thm)],[c_376]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_388,plain,
% 2.17/0.99      ( l1_waybel_0(sK5,sK4) != iProver_top
% 2.17/0.99      | v4_orders_2(sK6) = iProver_top
% 2.17/0.99      | v4_orders_2(sK5) != iProver_top
% 2.17/0.99      | v7_waybel_0(sK5) != iProver_top
% 2.17/0.99      | v2_struct_0(sK5) = iProver_top
% 2.17/0.99      | v2_struct_0(sK4) = iProver_top
% 2.17/0.99      | l1_struct_0(sK4) != iProver_top ),
% 2.17/0.99      inference(predicate_to_equality,[status(thm)],[c_387]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_410,plain,
% 2.17/0.99      ( l1_waybel_0(sK6,sK4) = iProver_top
% 2.17/0.99      | l1_waybel_0(sK5,sK4) != iProver_top
% 2.17/0.99      | v4_orders_2(sK5) != iProver_top
% 2.17/0.99      | v7_waybel_0(sK5) != iProver_top
% 2.17/0.99      | v2_struct_0(sK5) = iProver_top
% 2.17/0.99      | v2_struct_0(sK4) = iProver_top
% 2.17/0.99      | l1_struct_0(sK4) != iProver_top ),
% 2.17/0.99      inference(predicate_to_equality,[status(thm)],[c_409]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_1479,plain,
% 2.17/0.99      ( ~ l1_waybel_0(X0,sK4)
% 2.17/0.99      | m1_subset_1(k10_yellow_6(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
% 2.17/0.99      | ~ v4_orders_2(X0)
% 2.17/0.99      | v2_struct_0(X0)
% 2.17/0.99      | sK5 != X0 ),
% 2.17/0.99      inference(resolution_lifted,[status(thm)],[c_639,c_22]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_1480,plain,
% 2.17/0.99      ( ~ l1_waybel_0(sK5,sK4)
% 2.17/0.99      | m1_subset_1(k10_yellow_6(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
% 2.17/0.99      | ~ v4_orders_2(sK5)
% 2.17/0.99      | v2_struct_0(sK5) ),
% 2.17/0.99      inference(unflattening,[status(thm)],[c_1479]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_1481,plain,
% 2.17/0.99      ( l1_waybel_0(sK5,sK4) != iProver_top
% 2.17/0.99      | m1_subset_1(k10_yellow_6(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 2.17/0.99      | v4_orders_2(sK5) != iProver_top
% 2.17/0.99      | v2_struct_0(sK5) = iProver_top ),
% 2.17/0.99      inference(predicate_to_equality,[status(thm)],[c_1480]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_1601,plain,
% 2.17/0.99      ( ~ l1_waybel_0(X0,sK4)
% 2.17/0.99      | m1_subset_1(k10_yellow_6(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
% 2.17/0.99      | ~ v4_orders_2(X0)
% 2.17/0.99      | v2_struct_0(X0)
% 2.17/0.99      | sK6 != X0 ),
% 2.17/0.99      inference(resolution_lifted,[status(thm)],[c_639,c_400]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_1602,plain,
% 2.17/0.99      ( ~ l1_waybel_0(sK6,sK4)
% 2.17/0.99      | m1_subset_1(k10_yellow_6(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4)))
% 2.17/0.99      | ~ v4_orders_2(sK6)
% 2.17/0.99      | v2_struct_0(sK6) ),
% 2.17/0.99      inference(unflattening,[status(thm)],[c_1601]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_1603,plain,
% 2.17/0.99      ( l1_waybel_0(sK6,sK4) != iProver_top
% 2.17/0.99      | m1_subset_1(k10_yellow_6(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 2.17/0.99      | v4_orders_2(sK6) != iProver_top
% 2.17/0.99      | v2_struct_0(sK6) = iProver_top ),
% 2.17/0.99      inference(predicate_to_equality,[status(thm)],[c_1602]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_8133,plain,
% 2.17/0.99      ( m1_connsp_2(X0_57,sK4,sK0(u1_struct_0(sK4),k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6))) != iProver_top
% 2.17/0.99      | r1_waybel_0(sK4,sK5,X0_57) = iProver_top ),
% 2.17/0.99      inference(global_propositional_subsumption,
% 2.17/0.99                [status(thm)],
% 2.17/0.99                [c_8041,c_28,c_30,c_31,c_32,c_33,c_34,c_74,c_377,c_388,
% 2.17/0.99                 c_410,c_1481,c_1603]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_8148,plain,
% 2.17/0.99      ( r1_waybel_0(sK4,sK5,sK3(sK4,sK6,sK0(u1_struct_0(sK4),k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6)))) = iProver_top
% 2.17/0.99      | m1_subset_1(sK0(u1_struct_0(sK4),k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6)),u1_struct_0(sK4)) != iProver_top
% 2.17/0.99      | r2_hidden(sK0(u1_struct_0(sK4),k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6)),k10_yellow_6(sK4,sK6)) = iProver_top ),
% 2.17/0.99      inference(superposition,[status(thm)],[c_7352,c_8133]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_5,plain,
% 2.17/0.99      ( ~ r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
% 2.17/0.99      | ~ r1_waybel_0(X0,X1,X2)
% 2.17/0.99      | ~ l1_waybel_0(X1,X0)
% 2.17/0.99      | v2_struct_0(X0)
% 2.17/0.99      | v2_struct_0(X1)
% 2.17/0.99      | ~ l1_struct_0(X0) ),
% 2.17/0.99      inference(cnf_transformation,[],[f43]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_430,plain,
% 2.17/0.99      ( ~ r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
% 2.17/0.99      | ~ r1_waybel_0(X0,X1,X2)
% 2.17/0.99      | ~ l1_waybel_0(X1,X0)
% 2.17/0.99      | v2_struct_0(X0)
% 2.17/0.99      | v2_struct_0(X1)
% 2.17/0.99      | ~ l1_pre_topc(X0) ),
% 2.17/0.99      inference(resolution,[status(thm)],[c_3,c_5]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_870,plain,
% 2.17/0.99      ( ~ r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
% 2.17/0.99      | ~ r1_waybel_0(X0,X1,X2)
% 2.17/0.99      | ~ l1_waybel_0(X1,X0)
% 2.17/0.99      | v2_struct_0(X0)
% 2.17/0.99      | v2_struct_0(X1)
% 2.17/0.99      | sK4 != X0 ),
% 2.17/0.99      inference(resolution_lifted,[status(thm)],[c_430,c_25]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_871,plain,
% 2.17/0.99      ( ~ r2_waybel_0(sK4,X0,k6_subset_1(u1_struct_0(sK4),X1))
% 2.17/0.99      | ~ r1_waybel_0(sK4,X0,X1)
% 2.17/0.99      | ~ l1_waybel_0(X0,sK4)
% 2.17/0.99      | v2_struct_0(X0)
% 2.17/0.99      | v2_struct_0(sK4) ),
% 2.17/0.99      inference(unflattening,[status(thm)],[c_870]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_875,plain,
% 2.17/0.99      ( v2_struct_0(X0)
% 2.17/0.99      | ~ l1_waybel_0(X0,sK4)
% 2.17/0.99      | ~ r1_waybel_0(sK4,X0,X1)
% 2.17/0.99      | ~ r2_waybel_0(sK4,X0,k6_subset_1(u1_struct_0(sK4),X1)) ),
% 2.17/0.99      inference(global_propositional_subsumption,
% 2.17/0.99                [status(thm)],
% 2.17/0.99                [c_871,c_27]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_876,plain,
% 2.17/0.99      ( ~ r2_waybel_0(sK4,X0,k6_subset_1(u1_struct_0(sK4),X1))
% 2.17/0.99      | ~ r1_waybel_0(sK4,X0,X1)
% 2.17/0.99      | ~ l1_waybel_0(X0,sK4)
% 2.17/0.99      | v2_struct_0(X0) ),
% 2.17/0.99      inference(renaming,[status(thm)],[c_875]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_1832,plain,
% 2.17/0.99      ( ~ r2_waybel_0(sK4,X0,k6_subset_1(u1_struct_0(sK4),X1))
% 2.17/0.99      | ~ r1_waybel_0(sK4,X0,X1)
% 2.17/0.99      | v2_struct_0(X0)
% 2.17/0.99      | sK5 != X0
% 2.17/0.99      | sK4 != sK4 ),
% 2.17/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_876]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_1833,plain,
% 2.17/0.99      ( ~ r2_waybel_0(sK4,sK5,k6_subset_1(u1_struct_0(sK4),X0))
% 2.17/0.99      | ~ r1_waybel_0(sK4,sK5,X0)
% 2.17/0.99      | v2_struct_0(sK5) ),
% 2.17/0.99      inference(unflattening,[status(thm)],[c_1832]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_4349,plain,
% 2.17/0.99      ( ~ r1_waybel_0(sK4,sK5,X0)
% 2.17/0.99      | ~ r2_waybel_0(sK4,sK5,k6_subset_1(u1_struct_0(sK4),X0)) ),
% 2.17/0.99      inference(prop_impl,[status(thm)],[c_24,c_1833]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_4350,plain,
% 2.17/0.99      ( ~ r2_waybel_0(sK4,sK5,k6_subset_1(u1_struct_0(sK4),X0))
% 2.17/0.99      | ~ r1_waybel_0(sK4,sK5,X0) ),
% 2.17/0.99      inference(renaming,[status(thm)],[c_4349]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_6688,plain,
% 2.17/0.99      ( ~ r2_waybel_0(sK4,sK5,k6_subset_1(u1_struct_0(sK4),X0_57))
% 2.17/0.99      | ~ r1_waybel_0(sK4,sK5,X0_57) ),
% 2.17/0.99      inference(subtyping,[status(esa)],[c_4350]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_7966,plain,
% 2.17/0.99      ( ~ r2_waybel_0(sK4,sK5,k6_subset_1(u1_struct_0(sK4),sK3(sK4,sK6,sK0(u1_struct_0(sK4),k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6)))))
% 2.17/0.99      | ~ r1_waybel_0(sK4,sK5,sK3(sK4,sK6,sK0(u1_struct_0(sK4),k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6)))) ),
% 2.17/0.99      inference(instantiation,[status(thm)],[c_6688]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_7967,plain,
% 2.17/0.99      ( r2_waybel_0(sK4,sK5,k6_subset_1(u1_struct_0(sK4),sK3(sK4,sK6,sK0(u1_struct_0(sK4),k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6))))) != iProver_top
% 2.17/0.99      | r1_waybel_0(sK4,sK5,sK3(sK4,sK6,sK0(u1_struct_0(sK4),k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6)))) != iProver_top ),
% 2.17/0.99      inference(predicate_to_equality,[status(thm)],[c_7966]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_18,plain,
% 2.17/0.99      ( ~ m2_yellow_6(X0,X1,X2)
% 2.17/0.99      | ~ r2_waybel_0(X1,X0,X3)
% 2.17/0.99      | r2_waybel_0(X1,X2,X3)
% 2.17/0.99      | ~ l1_waybel_0(X2,X1)
% 2.17/0.99      | ~ v4_orders_2(X2)
% 2.17/0.99      | ~ v7_waybel_0(X2)
% 2.17/0.99      | v2_struct_0(X1)
% 2.17/0.99      | v2_struct_0(X2)
% 2.17/0.99      | ~ l1_struct_0(X1) ),
% 2.17/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_357,plain,
% 2.17/0.99      ( ~ r2_waybel_0(X0,X1,X2)
% 2.17/0.99      | r2_waybel_0(X0,X3,X2)
% 2.17/0.99      | ~ l1_waybel_0(X3,X0)
% 2.17/0.99      | ~ v4_orders_2(X3)
% 2.17/0.99      | ~ v7_waybel_0(X3)
% 2.17/0.99      | v2_struct_0(X3)
% 2.17/0.99      | v2_struct_0(X0)
% 2.17/0.99      | ~ l1_struct_0(X0)
% 2.17/0.99      | sK6 != X1
% 2.17/0.99      | sK5 != X3
% 2.17/0.99      | sK4 != X0 ),
% 2.17/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_20]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_358,plain,
% 2.17/0.99      ( ~ r2_waybel_0(sK4,sK6,X0)
% 2.17/0.99      | r2_waybel_0(sK4,sK5,X0)
% 2.17/0.99      | ~ l1_waybel_0(sK5,sK4)
% 2.17/0.99      | ~ v4_orders_2(sK5)
% 2.17/0.99      | ~ v7_waybel_0(sK5)
% 2.17/0.99      | v2_struct_0(sK5)
% 2.17/0.99      | v2_struct_0(sK4)
% 2.17/0.99      | ~ l1_struct_0(sK4) ),
% 2.17/0.99      inference(unflattening,[status(thm)],[c_357]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_362,plain,
% 2.17/0.99      ( ~ r2_waybel_0(sK4,sK6,X0) | r2_waybel_0(sK4,sK5,X0) ),
% 2.17/0.99      inference(global_propositional_subsumption,
% 2.17/0.99                [status(thm)],
% 2.17/0.99                [c_358,c_27,c_25,c_24,c_23,c_22,c_21,c_73]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_6705,plain,
% 2.17/0.99      ( ~ r2_waybel_0(sK4,sK6,X0_55) | r2_waybel_0(sK4,sK5,X0_55) ),
% 2.17/0.99      inference(subtyping,[status(esa)],[c_362]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_7904,plain,
% 2.17/0.99      ( ~ r2_waybel_0(sK4,sK6,k6_subset_1(u1_struct_0(sK4),sK3(sK4,sK6,sK0(u1_struct_0(sK4),k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6)))))
% 2.17/0.99      | r2_waybel_0(sK4,sK5,k6_subset_1(u1_struct_0(sK4),sK3(sK4,sK6,sK0(u1_struct_0(sK4),k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6))))) ),
% 2.17/0.99      inference(instantiation,[status(thm)],[c_6705]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_7905,plain,
% 2.17/0.99      ( r2_waybel_0(sK4,sK6,k6_subset_1(u1_struct_0(sK4),sK3(sK4,sK6,sK0(u1_struct_0(sK4),k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6))))) != iProver_top
% 2.17/0.99      | r2_waybel_0(sK4,sK5,k6_subset_1(u1_struct_0(sK4),sK3(sK4,sK6,sK0(u1_struct_0(sK4),k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6))))) = iProver_top ),
% 2.17/0.99      inference(predicate_to_equality,[status(thm)],[c_7904]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_411,plain,
% 2.17/0.99      ( l1_waybel_0(sK6,sK4) ),
% 2.17/0.99      inference(global_propositional_subsumption,
% 2.17/0.99                [status(thm)],
% 2.17/0.99                [c_409,c_27,c_25,c_24,c_23,c_22,c_21,c_73]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_4,plain,
% 2.17/0.99      ( r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
% 2.17/0.99      | r1_waybel_0(X0,X1,X2)
% 2.17/0.99      | ~ l1_waybel_0(X1,X0)
% 2.17/0.99      | v2_struct_0(X0)
% 2.17/0.99      | v2_struct_0(X1)
% 2.17/0.99      | ~ l1_struct_0(X0) ),
% 2.17/0.99      inference(cnf_transformation,[],[f44]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_453,plain,
% 2.17/0.99      ( r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
% 2.17/0.99      | r1_waybel_0(X0,X1,X2)
% 2.17/0.99      | ~ l1_waybel_0(X1,X0)
% 2.17/0.99      | v2_struct_0(X0)
% 2.17/0.99      | v2_struct_0(X1)
% 2.17/0.99      | ~ l1_pre_topc(X0) ),
% 2.17/0.99      inference(resolution,[status(thm)],[c_3,c_4]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_848,plain,
% 2.17/0.99      ( r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
% 2.17/0.99      | r1_waybel_0(X0,X1,X2)
% 2.17/0.99      | ~ l1_waybel_0(X1,X0)
% 2.17/0.99      | v2_struct_0(X0)
% 2.17/0.99      | v2_struct_0(X1)
% 2.17/0.99      | sK4 != X0 ),
% 2.17/0.99      inference(resolution_lifted,[status(thm)],[c_453,c_25]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_849,plain,
% 2.17/0.99      ( r2_waybel_0(sK4,X0,k6_subset_1(u1_struct_0(sK4),X1))
% 2.17/0.99      | r1_waybel_0(sK4,X0,X1)
% 2.17/0.99      | ~ l1_waybel_0(X0,sK4)
% 2.17/0.99      | v2_struct_0(X0)
% 2.17/0.99      | v2_struct_0(sK4) ),
% 2.17/0.99      inference(unflattening,[status(thm)],[c_848]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_853,plain,
% 2.17/0.99      ( v2_struct_0(X0)
% 2.17/0.99      | ~ l1_waybel_0(X0,sK4)
% 2.17/0.99      | r1_waybel_0(sK4,X0,X1)
% 2.17/0.99      | r2_waybel_0(sK4,X0,k6_subset_1(u1_struct_0(sK4),X1)) ),
% 2.17/0.99      inference(global_propositional_subsumption,
% 2.17/0.99                [status(thm)],
% 2.17/0.99                [c_849,c_27]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_854,plain,
% 2.17/0.99      ( r2_waybel_0(sK4,X0,k6_subset_1(u1_struct_0(sK4),X1))
% 2.17/0.99      | r1_waybel_0(sK4,X0,X1)
% 2.17/0.99      | ~ l1_waybel_0(X0,sK4)
% 2.17/0.99      | v2_struct_0(X0) ),
% 2.17/0.99      inference(renaming,[status(thm)],[c_853]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_1886,plain,
% 2.17/0.99      ( r2_waybel_0(sK4,X0,k6_subset_1(u1_struct_0(sK4),X1))
% 2.17/0.99      | r1_waybel_0(sK4,X0,X1)
% 2.17/0.99      | v2_struct_0(X0)
% 2.17/0.99      | sK6 != X0
% 2.17/0.99      | sK4 != sK4 ),
% 2.17/0.99      inference(resolution_lifted,[status(thm)],[c_411,c_854]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_1887,plain,
% 2.17/0.99      ( r2_waybel_0(sK4,sK6,k6_subset_1(u1_struct_0(sK4),X0))
% 2.17/0.99      | r1_waybel_0(sK4,sK6,X0)
% 2.17/0.99      | v2_struct_0(sK6) ),
% 2.17/0.99      inference(unflattening,[status(thm)],[c_1886]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_4355,plain,
% 2.17/0.99      ( r1_waybel_0(sK4,sK6,X0)
% 2.17/0.99      | r2_waybel_0(sK4,sK6,k6_subset_1(u1_struct_0(sK4),X0)) ),
% 2.17/0.99      inference(prop_impl,
% 2.17/0.99                [status(thm)],
% 2.17/0.99                [c_27,c_25,c_24,c_23,c_22,c_21,c_73,c_376,c_1887]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_4356,plain,
% 2.17/0.99      ( r2_waybel_0(sK4,sK6,k6_subset_1(u1_struct_0(sK4),X0))
% 2.17/0.99      | r1_waybel_0(sK4,sK6,X0) ),
% 2.17/0.99      inference(renaming,[status(thm)],[c_4355]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_6685,plain,
% 2.17/0.99      ( r2_waybel_0(sK4,sK6,k6_subset_1(u1_struct_0(sK4),X0_57))
% 2.17/0.99      | r1_waybel_0(sK4,sK6,X0_57) ),
% 2.17/0.99      inference(subtyping,[status(esa)],[c_4356]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_7791,plain,
% 2.17/0.99      ( r2_waybel_0(sK4,sK6,k6_subset_1(u1_struct_0(sK4),sK3(sK4,sK6,sK0(u1_struct_0(sK4),k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6)))))
% 2.17/0.99      | r1_waybel_0(sK4,sK6,sK3(sK4,sK6,sK0(u1_struct_0(sK4),k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6)))) ),
% 2.17/0.99      inference(instantiation,[status(thm)],[c_6685]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_7792,plain,
% 2.17/0.99      ( r2_waybel_0(sK4,sK6,k6_subset_1(u1_struct_0(sK4),sK3(sK4,sK6,sK0(u1_struct_0(sK4),k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6))))) = iProver_top
% 2.17/0.99      | r1_waybel_0(sK4,sK6,sK3(sK4,sK6,sK0(u1_struct_0(sK4),k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6)))) = iProver_top ),
% 2.17/0.99      inference(predicate_to_equality,[status(thm)],[c_7791]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_10,plain,
% 2.17/0.99      ( ~ r1_waybel_0(X0,X1,sK3(X0,X1,X2))
% 2.17/0.99      | ~ l1_waybel_0(X1,X0)
% 2.17/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.17/0.99      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 2.17/0.99      | r2_hidden(X2,k10_yellow_6(X0,X1))
% 2.17/0.99      | ~ v2_pre_topc(X0)
% 2.17/0.99      | ~ v4_orders_2(X1)
% 2.17/0.99      | ~ v7_waybel_0(X1)
% 2.17/0.99      | v2_struct_0(X0)
% 2.17/0.99      | v2_struct_0(X1)
% 2.17/0.99      | ~ l1_pre_topc(X0) ),
% 2.17/0.99      inference(cnf_transformation,[],[f67]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_526,plain,
% 2.17/0.99      ( ~ r1_waybel_0(X0,X1,sK3(X0,X1,X2))
% 2.17/0.99      | ~ l1_waybel_0(X1,X0)
% 2.17/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.17/0.99      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 2.17/0.99      | r2_hidden(X2,k10_yellow_6(X0,X1))
% 2.17/0.99      | ~ v4_orders_2(X1)
% 2.17/0.99      | ~ v7_waybel_0(X1)
% 2.17/0.99      | v2_struct_0(X0)
% 2.17/0.99      | v2_struct_0(X1)
% 2.17/0.99      | ~ l1_pre_topc(X0)
% 2.17/0.99      | sK4 != X0 ),
% 2.17/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_26]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_527,plain,
% 2.17/0.99      ( ~ r1_waybel_0(sK4,X0,sK3(sK4,X0,X1))
% 2.17/0.99      | ~ l1_waybel_0(X0,sK4)
% 2.17/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.17/0.99      | ~ m1_subset_1(k10_yellow_6(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
% 2.17/0.99      | r2_hidden(X1,k10_yellow_6(sK4,X0))
% 2.17/0.99      | ~ v4_orders_2(X0)
% 2.17/0.99      | ~ v7_waybel_0(X0)
% 2.17/0.99      | v2_struct_0(X0)
% 2.17/0.99      | v2_struct_0(sK4)
% 2.17/0.99      | ~ l1_pre_topc(sK4) ),
% 2.17/0.99      inference(unflattening,[status(thm)],[c_526]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_531,plain,
% 2.17/0.99      ( ~ r1_waybel_0(sK4,X0,sK3(sK4,X0,X1))
% 2.17/0.99      | ~ l1_waybel_0(X0,sK4)
% 2.17/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.17/0.99      | ~ m1_subset_1(k10_yellow_6(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
% 2.17/0.99      | r2_hidden(X1,k10_yellow_6(sK4,X0))
% 2.17/0.99      | ~ v4_orders_2(X0)
% 2.17/0.99      | ~ v7_waybel_0(X0)
% 2.17/0.99      | v2_struct_0(X0) ),
% 2.17/0.99      inference(global_propositional_subsumption,
% 2.17/0.99                [status(thm)],
% 2.17/0.99                [c_527,c_27,c_25]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_658,plain,
% 2.17/0.99      ( ~ r1_waybel_0(sK4,X0,sK3(sK4,X0,X1))
% 2.17/0.99      | ~ l1_waybel_0(X0,sK4)
% 2.17/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.17/0.99      | r2_hidden(X1,k10_yellow_6(sK4,X0))
% 2.17/0.99      | ~ v4_orders_2(X0)
% 2.17/0.99      | ~ v7_waybel_0(X0)
% 2.17/0.99      | v2_struct_0(X0) ),
% 2.17/0.99      inference(backward_subsumption_resolution,
% 2.17/0.99                [status(thm)],
% 2.17/0.99                [c_639,c_531]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_1559,plain,
% 2.17/0.99      ( ~ r1_waybel_0(sK4,X0,sK3(sK4,X0,X1))
% 2.17/0.99      | ~ l1_waybel_0(X0,sK4)
% 2.17/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.17/0.99      | r2_hidden(X1,k10_yellow_6(sK4,X0))
% 2.17/0.99      | ~ v4_orders_2(X0)
% 2.17/0.99      | v2_struct_0(X0)
% 2.17/0.99      | sK6 != X0 ),
% 2.17/0.99      inference(resolution_lifted,[status(thm)],[c_658,c_400]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_1560,plain,
% 2.17/0.99      ( ~ r1_waybel_0(sK4,sK6,sK3(sK4,sK6,X0))
% 2.17/0.99      | ~ l1_waybel_0(sK6,sK4)
% 2.17/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.17/0.99      | r2_hidden(X0,k10_yellow_6(sK4,sK6))
% 2.17/0.99      | ~ v4_orders_2(sK6)
% 2.17/0.99      | v2_struct_0(sK6) ),
% 2.17/0.99      inference(unflattening,[status(thm)],[c_1559]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_1564,plain,
% 2.17/0.99      ( ~ r1_waybel_0(sK4,sK6,sK3(sK4,sK6,X0))
% 2.17/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.17/0.99      | r2_hidden(X0,k10_yellow_6(sK4,sK6)) ),
% 2.17/0.99      inference(global_propositional_subsumption,
% 2.17/0.99                [status(thm)],
% 2.17/0.99                [c_1560,c_27,c_25,c_24,c_23,c_22,c_21,c_73,c_376,c_387,
% 2.17/0.99                 c_409]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_6697,plain,
% 2.17/0.99      ( ~ r1_waybel_0(sK4,sK6,sK3(sK4,sK6,X0_58))
% 2.17/0.99      | ~ m1_subset_1(X0_58,u1_struct_0(sK4))
% 2.17/0.99      | r2_hidden(X0_58,k10_yellow_6(sK4,sK6)) ),
% 2.17/0.99      inference(subtyping,[status(esa)],[c_1564]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_7661,plain,
% 2.17/0.99      ( ~ r1_waybel_0(sK4,sK6,sK3(sK4,sK6,sK0(u1_struct_0(sK4),k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6))))
% 2.17/0.99      | ~ m1_subset_1(sK0(u1_struct_0(sK4),k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6)),u1_struct_0(sK4))
% 2.17/0.99      | r2_hidden(sK0(u1_struct_0(sK4),k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6)),k10_yellow_6(sK4,sK6)) ),
% 2.17/0.99      inference(instantiation,[status(thm)],[c_6697]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_7662,plain,
% 2.17/0.99      ( r1_waybel_0(sK4,sK6,sK3(sK4,sK6,sK0(u1_struct_0(sK4),k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6)))) != iProver_top
% 2.17/0.99      | m1_subset_1(sK0(u1_struct_0(sK4),k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6)),u1_struct_0(sK4)) != iProver_top
% 2.17/0.99      | r2_hidden(sK0(u1_struct_0(sK4),k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6)),k10_yellow_6(sK4,sK6)) = iProver_top ),
% 2.17/0.99      inference(predicate_to_equality,[status(thm)],[c_7661]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_7586,plain,
% 2.17/0.99      ( m1_subset_1(sK0(u1_struct_0(sK4),k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6)),u1_struct_0(sK4))
% 2.17/0.99      | ~ m1_subset_1(k10_yellow_6(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4)))
% 2.17/0.99      | ~ m1_subset_1(k10_yellow_6(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4))) ),
% 2.17/0.99      inference(instantiation,[status(thm)],[c_6708]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_7587,plain,
% 2.17/0.99      ( m1_subset_1(sK0(u1_struct_0(sK4),k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6)),u1_struct_0(sK4)) = iProver_top
% 2.17/0.99      | m1_subset_1(k10_yellow_6(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.17/0.99      | m1_subset_1(k10_yellow_6(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 2.17/0.99      inference(predicate_to_equality,[status(thm)],[c_7586]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_0,plain,
% 2.17/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.17/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.17/0.99      | ~ r2_hidden(sK0(X1,X2,X0),X0)
% 2.17/0.99      | r1_tarski(X2,X0) ),
% 2.17/0.99      inference(cnf_transformation,[],[f41]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_330,plain,
% 2.17/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.17/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.17/0.99      | ~ r2_hidden(sK0(X1,X2,X0),X0)
% 2.17/0.99      | k10_yellow_6(sK4,sK6) != X0
% 2.17/0.99      | k10_yellow_6(sK4,sK5) != X2 ),
% 2.17/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_19]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_331,plain,
% 2.17/0.99      ( ~ m1_subset_1(k10_yellow_6(sK4,sK6),k1_zfmisc_1(X0))
% 2.17/0.99      | ~ m1_subset_1(k10_yellow_6(sK4,sK5),k1_zfmisc_1(X0))
% 2.17/0.99      | ~ r2_hidden(sK0(X0,k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6)),k10_yellow_6(sK4,sK6)) ),
% 2.17/0.99      inference(unflattening,[status(thm)],[c_330]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_6706,plain,
% 2.17/0.99      ( ~ m1_subset_1(k10_yellow_6(sK4,sK6),k1_zfmisc_1(X0_56))
% 2.17/0.99      | ~ m1_subset_1(k10_yellow_6(sK4,sK5),k1_zfmisc_1(X0_56))
% 2.17/0.99      | ~ r2_hidden(sK0(X0_56,k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6)),k10_yellow_6(sK4,sK6)) ),
% 2.17/0.99      inference(subtyping,[status(esa)],[c_331]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_7580,plain,
% 2.17/0.99      ( ~ m1_subset_1(k10_yellow_6(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4)))
% 2.17/0.99      | ~ m1_subset_1(k10_yellow_6(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
% 2.17/0.99      | ~ r2_hidden(sK0(u1_struct_0(sK4),k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6)),k10_yellow_6(sK4,sK6)) ),
% 2.17/0.99      inference(instantiation,[status(thm)],[c_6706]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_7581,plain,
% 2.17/0.99      ( m1_subset_1(k10_yellow_6(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.17/0.99      | m1_subset_1(k10_yellow_6(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.17/0.99      | r2_hidden(sK0(u1_struct_0(sK4),k10_yellow_6(sK4,sK5),k10_yellow_6(sK4,sK6)),k10_yellow_6(sK4,sK6)) != iProver_top ),
% 2.17/0.99      inference(predicate_to_equality,[status(thm)],[c_7580]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(contradiction,plain,
% 2.17/0.99      ( $false ),
% 2.17/0.99      inference(minisat,
% 2.17/0.99                [status(thm)],
% 2.17/0.99                [c_8148,c_7967,c_7905,c_7792,c_7662,c_7587,c_7581,c_1603,
% 2.17/0.99                 c_1481,c_410,c_388,c_377,c_74,c_34,c_33,c_32,c_31,c_30,
% 2.17/0.99                 c_28]) ).
% 2.17/0.99  
% 2.17/0.99  
% 2.17/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.17/0.99  
% 2.17/0.99  ------                               Statistics
% 2.17/0.99  
% 2.17/0.99  ------ General
% 2.17/0.99  
% 2.17/0.99  abstr_ref_over_cycles:                  0
% 2.17/0.99  abstr_ref_under_cycles:                 0
% 2.17/0.99  gc_basic_clause_elim:                   0
% 2.17/0.99  forced_gc_time:                         0
% 2.17/0.99  parsing_time:                           0.011
% 2.17/0.99  unif_index_cands_time:                  0.
% 2.17/0.99  unif_index_add_time:                    0.
% 2.17/0.99  orderings_time:                         0.
% 2.17/0.99  out_proof_time:                         0.012
% 2.17/0.99  total_time:                             0.205
% 2.17/0.99  num_of_symbols:                         59
% 2.17/0.99  num_of_terms:                           3675
% 2.17/0.99  
% 2.17/0.99  ------ Preprocessing
% 2.17/0.99  
% 2.17/0.99  num_of_splits:                          0
% 2.17/0.99  num_of_split_atoms:                     0
% 2.17/0.99  num_of_reused_defs:                     0
% 2.17/0.99  num_eq_ax_congr_red:                    47
% 2.17/0.99  num_of_sem_filtered_clauses:            1
% 2.17/0.99  num_of_subtypes:                        6
% 2.17/0.99  monotx_restored_types:                  0
% 2.17/0.99  sat_num_of_epr_types:                   0
% 2.17/0.99  sat_num_of_non_cyclic_types:            0
% 2.17/0.99  sat_guarded_non_collapsed_types:        1
% 2.17/0.99  num_pure_diseq_elim:                    0
% 2.17/0.99  simp_replaced_by:                       0
% 2.17/0.99  res_preprocessed:                       121
% 2.17/0.99  prep_upred:                             0
% 2.17/0.99  prep_unflattend:                        326
% 2.17/0.99  smt_new_axioms:                         0
% 2.17/0.99  pred_elim_cands:                        5
% 2.17/0.99  pred_elim:                              9
% 2.17/0.99  pred_elim_cl:                           4
% 2.17/0.99  pred_elim_cycles:                       17
% 2.17/0.99  merged_defs:                            12
% 2.17/0.99  merged_defs_ncl:                        0
% 2.17/0.99  bin_hyper_res:                          12
% 2.17/0.99  prep_cycles:                            4
% 2.17/0.99  pred_elim_time:                         0.11
% 2.17/0.99  splitting_time:                         0.
% 2.17/0.99  sem_filter_time:                        0.
% 2.17/0.99  monotx_time:                            0.
% 2.17/0.99  subtype_inf_time:                       0.
% 2.17/0.99  
% 2.17/0.99  ------ Problem properties
% 2.17/0.99  
% 2.17/0.99  clauses:                                24
% 2.17/0.99  conjectures:                            0
% 2.17/0.99  epr:                                    1
% 2.17/0.99  horn:                                   14
% 2.17/0.99  ground:                                 2
% 2.17/0.99  unary:                                  2
% 2.17/0.99  binary:                                 5
% 2.17/0.99  lits:                                   73
% 2.17/0.99  lits_eq:                                8
% 2.17/0.99  fd_pure:                                0
% 2.17/0.99  fd_pseudo:                              0
% 2.17/0.99  fd_cond:                                8
% 2.17/0.99  fd_pseudo_cond:                         0
% 2.17/0.99  ac_symbols:                             0
% 2.17/0.99  
% 2.17/0.99  ------ Propositional Solver
% 2.17/0.99  
% 2.17/0.99  prop_solver_calls:                      27
% 2.17/0.99  prop_fast_solver_calls:                 2620
% 2.17/0.99  smt_solver_calls:                       0
% 2.17/0.99  smt_fast_solver_calls:                  0
% 2.17/0.99  prop_num_of_clauses:                    1183
% 2.17/0.99  prop_preprocess_simplified:             5201
% 2.17/0.99  prop_fo_subsumed:                       152
% 2.17/0.99  prop_solver_time:                       0.
% 2.17/0.99  smt_solver_time:                        0.
% 2.17/0.99  smt_fast_solver_time:                   0.
% 2.17/0.99  prop_fast_solver_time:                  0.
% 2.17/0.99  prop_unsat_core_time:                   0.
% 2.17/0.99  
% 2.17/0.99  ------ QBF
% 2.17/0.99  
% 2.17/0.99  qbf_q_res:                              0
% 2.17/0.99  qbf_num_tautologies:                    0
% 2.17/0.99  qbf_prep_cycles:                        0
% 2.17/0.99  
% 2.17/0.99  ------ BMC1
% 2.17/0.99  
% 2.17/0.99  bmc1_current_bound:                     -1
% 2.17/0.99  bmc1_last_solved_bound:                 -1
% 2.17/0.99  bmc1_unsat_core_size:                   -1
% 2.17/0.99  bmc1_unsat_core_parents_size:           -1
% 2.17/0.99  bmc1_merge_next_fun:                    0
% 2.17/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.17/0.99  
% 2.17/0.99  ------ Instantiation
% 2.17/0.99  
% 2.17/0.99  inst_num_of_clauses:                    130
% 2.17/0.99  inst_num_in_passive:                    13
% 2.17/0.99  inst_num_in_active:                     111
% 2.17/0.99  inst_num_in_unprocessed:                6
% 2.17/0.99  inst_num_of_loops:                      130
% 2.17/0.99  inst_num_of_learning_restarts:          0
% 2.17/0.99  inst_num_moves_active_passive:          15
% 2.17/0.99  inst_lit_activity:                      0
% 2.17/0.99  inst_lit_activity_moves:                0
% 2.17/0.99  inst_num_tautologies:                   0
% 2.17/0.99  inst_num_prop_implied:                  0
% 2.17/0.99  inst_num_existing_simplified:           0
% 2.17/0.99  inst_num_eq_res_simplified:             0
% 2.17/0.99  inst_num_child_elim:                    0
% 2.17/0.99  inst_num_of_dismatching_blockings:      5
% 2.17/0.99  inst_num_of_non_proper_insts:           104
% 2.17/0.99  inst_num_of_duplicates:                 0
% 2.17/0.99  inst_inst_num_from_inst_to_res:         0
% 2.17/0.99  inst_dismatching_checking_time:         0.
% 2.17/0.99  
% 2.17/0.99  ------ Resolution
% 2.17/0.99  
% 2.17/0.99  res_num_of_clauses:                     0
% 2.17/0.99  res_num_in_passive:                     0
% 2.17/0.99  res_num_in_active:                      0
% 2.17/0.99  res_num_of_loops:                       125
% 2.17/0.99  res_forward_subset_subsumed:            16
% 2.17/0.99  res_backward_subset_subsumed:           0
% 2.17/0.99  res_forward_subsumed:                   2
% 2.17/0.99  res_backward_subsumed:                  0
% 2.17/0.99  res_forward_subsumption_resolution:     3
% 2.17/0.99  res_backward_subsumption_resolution:    2
% 2.17/0.99  res_clause_to_clause_subsumption:       276
% 2.17/0.99  res_orphan_elimination:                 0
% 2.17/0.99  res_tautology_del:                      80
% 2.17/0.99  res_num_eq_res_simplified:              0
% 2.17/0.99  res_num_sel_changes:                    0
% 2.17/0.99  res_moves_from_active_to_pass:          0
% 2.17/0.99  
% 2.17/0.99  ------ Superposition
% 2.17/0.99  
% 2.17/0.99  sup_time_total:                         0.
% 2.17/0.99  sup_time_generating:                    0.
% 2.17/0.99  sup_time_sim_full:                      0.
% 2.17/0.99  sup_time_sim_immed:                     0.
% 2.17/0.99  
% 2.17/0.99  sup_num_of_clauses:                     34
% 2.17/0.99  sup_num_in_active:                      26
% 2.17/0.99  sup_num_in_passive:                     8
% 2.17/0.99  sup_num_of_loops:                       25
% 2.17/0.99  sup_fw_superposition:                   6
% 2.17/0.99  sup_bw_superposition:                   5
% 2.17/0.99  sup_immediate_simplified:               0
% 2.17/0.99  sup_given_eliminated:                   0
% 2.17/0.99  comparisons_done:                       0
% 2.17/0.99  comparisons_avoided:                    0
% 2.17/0.99  
% 2.17/0.99  ------ Simplifications
% 2.17/0.99  
% 2.17/0.99  
% 2.17/0.99  sim_fw_subset_subsumed:                 0
% 2.17/0.99  sim_bw_subset_subsumed:                 0
% 2.17/0.99  sim_fw_subsumed:                        0
% 2.17/0.99  sim_bw_subsumed:                        0
% 2.17/0.99  sim_fw_subsumption_res:                 0
% 2.17/0.99  sim_bw_subsumption_res:                 0
% 2.17/0.99  sim_tautology_del:                      3
% 2.17/0.99  sim_eq_tautology_del:                   0
% 2.17/0.99  sim_eq_res_simp:                        0
% 2.17/0.99  sim_fw_demodulated:                     0
% 2.17/0.99  sim_bw_demodulated:                     0
% 2.17/0.99  sim_light_normalised:                   0
% 2.17/0.99  sim_joinable_taut:                      0
% 2.17/0.99  sim_joinable_simp:                      0
% 2.17/0.99  sim_ac_normalised:                      0
% 2.17/0.99  sim_smt_subsumption:                    0
% 2.17/0.99  
%------------------------------------------------------------------------------
