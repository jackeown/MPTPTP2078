%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1944+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:54 EST 2020

% Result     : Theorem 2.34s
% Output     : CNFRefutation 2.34s
% Verified   : 
% Statistics : Number of formulae       :  163 ( 742 expanded)
%              Number of clauses        :   96 ( 177 expanded)
%              Number of leaves         :   18 ( 206 expanded)
%              Depth                    :   24
%              Number of atoms          :  947 (5945 expanded)
%              Number of equality atoms :   81 ( 116 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal clause size      :   24 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] : m1_subset_1(sK5(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f7,f41])).

fof(f62,plain,(
    ! [X0] : m1_subset_1(sK5(X0),X0) ),
    inference(cnf_transformation,[],[f42])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f60,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
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

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
              | ~ r1_orders_2(X1,X5,X6)
              | ~ m1_subset_1(X6,u1_struct_0(X1)) )
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ! [X6] :
            ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
            | ~ r1_orders_2(X1,sK1(X0,X1,X2),X6)
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
          & r1_orders_2(X1,X3,X4)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_hidden(k2_waybel_0(X0,X1,sK0(X0,X1,X2,X3)),X2)
        & r1_orders_2(X1,X3,sK0(X0,X1,X2,X3))
        & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_waybel_0(X0,X1,X2)
                | ! [X3] :
                    ( ( ~ r2_hidden(k2_waybel_0(X0,X1,sK0(X0,X1,X2,X3)),X2)
                      & r1_orders_2(X1,X3,sK0(X0,X1,X2,X3))
                      & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ( ! [X6] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
                      | ~ r1_orders_2(X1,sK1(X0,X1,X2),X6)
                      | ~ m1_subset_1(X6,u1_struct_0(X1)) )
                  & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1)) )
                | ~ r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f32,f31])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_waybel_0(X0,X1,X2)
      | m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

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

fof(f72,plain,(
    l1_waybel_0(sK7,sK6) ),
    inference(cnf_transformation,[],[f45])).

fof(f65,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f45])).

fof(f67,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f45])).

fof(f68,plain,(
    ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f45])).

fof(f8,axiom,(
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

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f63,plain,(
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
    inference(cnf_transformation,[],[f24])).

fof(f71,plain,(
    v1_yellow_6(sK7,sK6) ),
    inference(cnf_transformation,[],[f45])).

fof(f69,plain,(
    v4_orders_2(sK7) ),
    inference(cnf_transformation,[],[f45])).

fof(f70,plain,(
    v7_waybel_0(sK7) ),
    inference(cnf_transformation,[],[f45])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
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
    inference(flattening,[],[f16])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
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

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f2])).

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
    inference(flattening,[],[f14])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

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
    inference(rectify,[],[f35])).

fof(f39,plain,(
    ! [X6,X1,X0] :
      ( ? [X7] :
          ( ~ r1_waybel_0(X0,X1,X7)
          & m1_connsp_2(X7,X0,X6) )
     => ( ~ r1_waybel_0(X0,X1,sK4(X0,X1,X6))
        & m1_connsp_2(sK4(X0,X1,X6),X0,X6) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_waybel_0(X0,X1,X4)
          & m1_connsp_2(X4,X0,X3) )
     => ( ~ r1_waybel_0(X0,X1,sK3(X0,X1,X2))
        & m1_connsp_2(sK3(X0,X1,X2),X0,X3) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
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
              & m1_connsp_2(X4,X0,sK2(X0,X1,X2)) )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ! [X5] :
              ( r1_waybel_0(X0,X1,X5)
              | ~ m1_connsp_2(X5,X0,sK2(X0,X1,X2)) )
          | r2_hidden(sK2(X0,X1,X2),X2) )
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k10_yellow_6(X0,X1) = X2
                  | ( ( ( ~ r1_waybel_0(X0,X1,sK3(X0,X1,X2))
                        & m1_connsp_2(sK3(X0,X1,X2),X0,sK2(X0,X1,X2)) )
                      | ~ r2_hidden(sK2(X0,X1,X2),X2) )
                    & ( ! [X5] :
                          ( r1_waybel_0(X0,X1,X5)
                          | ~ m1_connsp_2(X5,X0,sK2(X0,X1,X2)) )
                      | r2_hidden(sK2(X0,X1,X2),X2) )
                    & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) )
                & ( ! [X6] :
                      ( ( ( r2_hidden(X6,X2)
                          | ( ~ r1_waybel_0(X0,X1,sK4(X0,X1,X6))
                            & m1_connsp_2(sK4(X0,X1,X6),X0,X6) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f36,f39,f38,f37])).

fof(f53,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,X2)
      | ~ r1_waybel_0(X0,X1,sK4(X0,X1,X6))
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
    inference(cnf_transformation,[],[f40])).

fof(f74,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(X6,k10_yellow_6(X0,X1))
      | ~ r1_waybel_0(X0,X1,sK4(X0,X1,X6))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f66,plain,(
    v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f45])).

fof(f73,plain,(
    ~ r2_hidden(k4_yellow_6(sK6,sK7),k10_yellow_6(sK6,sK7)) ),
    inference(cnf_transformation,[],[f45])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_waybel_0(X0,X1,X2)
      | ~ r2_hidden(k2_waybel_0(X0,X1,sK0(X0,X1,X2,X3)),X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f9,axiom,(
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

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ m1_connsp_2(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f52,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,X2)
      | m1_connsp_2(sK4(X0,X1,X6),X0,X6)
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
    inference(cnf_transformation,[],[f40])).

fof(f75,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(X6,k10_yellow_6(X0,X1))
      | m1_connsp_2(sK4(X0,X1,X6),X0,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f52])).

cnf(c_16,plain,
    ( m1_subset_1(sK5(X0),X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2696,plain,
    ( m1_subset_1(sK5(X0_56),X0_56) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_3050,plain,
    ( m1_subset_1(sK5(X0_56),X0_56) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2696])).

cnf(c_14,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2,plain,
    ( r1_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X1))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_401,plain,
    ( r1_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X1))
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(resolution,[status(thm)],[c_14,c_2])).

cnf(c_20,negated_conjecture,
    ( l1_waybel_0(sK7,sK6) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1251,plain,
    ( r1_waybel_0(X0,X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X1))
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK7 != X1
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_401,c_20])).

cnf(c_1252,plain,
    ( r1_waybel_0(sK6,sK7,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | m1_subset_1(sK0(sK6,sK7,X0,X1),u1_struct_0(sK7))
    | ~ l1_pre_topc(sK6)
    | v2_struct_0(sK7)
    | v2_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_1251])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_25,negated_conjecture,
    ( l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1256,plain,
    ( m1_subset_1(sK0(sK6,sK7,X0,X1),u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | r1_waybel_0(sK6,sK7,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1252,c_27,c_25,c_24])).

cnf(c_1257,plain,
    ( r1_waybel_0(sK6,sK7,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | m1_subset_1(sK0(sK6,sK7,X0,X1),u1_struct_0(sK7)) ),
    inference(renaming,[status(thm)],[c_1256])).

cnf(c_2682,plain,
    ( r1_waybel_0(sK6,sK7,X0_55)
    | ~ m1_subset_1(X1_55,u1_struct_0(sK7))
    | m1_subset_1(sK0(sK6,sK7,X0_55,X1_55),u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_1257])).

cnf(c_3064,plain,
    ( r1_waybel_0(sK6,sK7,X0_55) = iProver_top
    | m1_subset_1(X1_55,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK0(sK6,sK7,X0_55,X1_55),u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2682])).

cnf(c_17,plain,
    ( ~ v1_yellow_6(X0,X1)
    | ~ l1_waybel_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_struct_0(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | k2_waybel_0(X1,X0,X2) = k4_yellow_6(X1,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_21,negated_conjecture,
    ( v1_yellow_6(sK7,sK6) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_316,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | k2_waybel_0(X1,X0,X2) = k4_yellow_6(X1,X0)
    | sK7 != X0
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_21])).

cnf(c_317,plain,
    ( ~ l1_waybel_0(sK7,sK6)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ v4_orders_2(sK7)
    | ~ v7_waybel_0(sK7)
    | ~ l1_struct_0(sK6)
    | v2_struct_0(sK7)
    | v2_struct_0(sK6)
    | k2_waybel_0(sK6,sK7,X0) = k4_yellow_6(sK6,sK7) ),
    inference(unflattening,[status(thm)],[c_316])).

cnf(c_23,negated_conjecture,
    ( v4_orders_2(sK7) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_22,negated_conjecture,
    ( v7_waybel_0(sK7) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_50,plain,
    ( ~ l1_pre_topc(sK6)
    | l1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_321,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | k2_waybel_0(sK6,sK7,X0) = k4_yellow_6(sK6,sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_317,c_27,c_25,c_24,c_23,c_22,c_20,c_50])).

cnf(c_2694,plain,
    ( ~ m1_subset_1(X0_55,u1_struct_0(sK7))
    | k2_waybel_0(sK6,sK7,X0_55) = k4_yellow_6(sK6,sK7) ),
    inference(subtyping,[status(esa)],[c_321])).

cnf(c_3052,plain,
    ( k2_waybel_0(sK6,sK7,X0_55) = k4_yellow_6(sK6,sK7)
    | m1_subset_1(X0_55,u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2694])).

cnf(c_3655,plain,
    ( k2_waybel_0(sK6,sK7,sK0(sK6,sK7,X0_55,X1_55)) = k4_yellow_6(sK6,sK7)
    | r1_waybel_0(sK6,sK7,X0_55) = iProver_top
    | m1_subset_1(X1_55,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3064,c_3052])).

cnf(c_3945,plain,
    ( k2_waybel_0(sK6,sK7,sK0(sK6,sK7,X0_55,sK5(u1_struct_0(sK7)))) = k4_yellow_6(sK6,sK7)
    | r1_waybel_0(sK6,sK7,X0_55) = iProver_top ),
    inference(superposition,[status(thm)],[c_3050,c_3655])).

cnf(c_12,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(k10_yellow_6(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_797,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(k10_yellow_6(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_22])).

cnf(c_798,plain,
    ( ~ l1_waybel_0(sK7,X0)
    | m1_subset_1(k10_yellow_6(X0,sK7),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ v4_orders_2(sK7)
    | v2_struct_0(X0)
    | v2_struct_0(sK7) ),
    inference(unflattening,[status(thm)],[c_797])).

cnf(c_802,plain,
    ( v2_struct_0(X0)
    | ~ l1_waybel_0(sK7,X0)
    | m1_subset_1(k10_yellow_6(X0,sK7),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_798,c_24,c_23])).

cnf(c_803,plain,
    ( ~ l1_waybel_0(sK7,X0)
    | m1_subset_1(k10_yellow_6(X0,sK7),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_802])).

cnf(c_9,plain,
    ( ~ r1_waybel_0(X0,X1,sK4(X0,X1,X2))
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | r2_hidden(X2,k10_yellow_6(X0,X1))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_650,plain,
    ( ~ r1_waybel_0(X0,X1,sK4(X0,X1,X2))
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | r2_hidden(X2,k10_yellow_6(X0,X1))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ v4_orders_2(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_22])).

cnf(c_651,plain,
    ( ~ r1_waybel_0(X0,sK7,sK4(X0,sK7,X1))
    | ~ l1_waybel_0(sK7,X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k10_yellow_6(X0,sK7),k1_zfmisc_1(u1_struct_0(X0)))
    | r2_hidden(X1,k10_yellow_6(X0,sK7))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ v4_orders_2(sK7)
    | v2_struct_0(X0)
    | v2_struct_0(sK7) ),
    inference(unflattening,[status(thm)],[c_650])).

cnf(c_655,plain,
    ( v2_struct_0(X0)
    | ~ r1_waybel_0(X0,sK7,sK4(X0,sK7,X1))
    | ~ l1_waybel_0(sK7,X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k10_yellow_6(X0,sK7),k1_zfmisc_1(u1_struct_0(X0)))
    | r2_hidden(X1,k10_yellow_6(X0,sK7))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_651,c_24,c_23])).

cnf(c_656,plain,
    ( ~ r1_waybel_0(X0,sK7,sK4(X0,sK7,X1))
    | ~ l1_waybel_0(sK7,X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k10_yellow_6(X0,sK7),k1_zfmisc_1(u1_struct_0(X0)))
    | r2_hidden(X1,k10_yellow_6(X0,sK7))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_655])).

cnf(c_821,plain,
    ( ~ r1_waybel_0(X0,sK7,sK4(X0,sK7,X1))
    | ~ l1_waybel_0(sK7,X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r2_hidden(X1,k10_yellow_6(X0,sK7))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_803,c_656])).

cnf(c_26,negated_conjecture,
    ( v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_993,plain,
    ( ~ r1_waybel_0(X0,sK7,sK4(X0,sK7,X1))
    | ~ l1_waybel_0(sK7,X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r2_hidden(X1,k10_yellow_6(X0,sK7))
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_821,c_26])).

cnf(c_994,plain,
    ( ~ r1_waybel_0(sK6,sK7,sK4(sK6,sK7,X0))
    | ~ l1_waybel_0(sK7,sK6)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | r2_hidden(X0,k10_yellow_6(sK6,sK7))
    | ~ l1_pre_topc(sK6)
    | v2_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_993])).

cnf(c_998,plain,
    ( ~ r1_waybel_0(sK6,sK7,sK4(sK6,sK7,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | r2_hidden(X0,k10_yellow_6(sK6,sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_994,c_27,c_25,c_20])).

cnf(c_2692,plain,
    ( ~ r1_waybel_0(sK6,sK7,sK4(sK6,sK7,X0_55))
    | ~ m1_subset_1(X0_55,u1_struct_0(sK6))
    | r2_hidden(X0_55,k10_yellow_6(sK6,sK7)) ),
    inference(subtyping,[status(esa)],[c_998])).

cnf(c_3054,plain,
    ( r1_waybel_0(sK6,sK7,sK4(sK6,sK7,X0_55)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X0_55,k10_yellow_6(sK6,sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2692])).

cnf(c_3976,plain,
    ( k2_waybel_0(sK6,sK7,sK0(sK6,sK7,sK4(sK6,sK7,X0_55),sK5(u1_struct_0(sK7)))) = k4_yellow_6(sK6,sK7)
    | m1_subset_1(X0_55,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X0_55,k10_yellow_6(sK6,sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3945,c_3054])).

cnf(c_19,negated_conjecture,
    ( ~ r2_hidden(k4_yellow_6(sK6,sK7),k10_yellow_6(sK6,sK7)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2695,negated_conjecture,
    ( ~ r2_hidden(k4_yellow_6(sK6,sK7),k10_yellow_6(sK6,sK7)) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_3051,plain,
    ( r2_hidden(k4_yellow_6(sK6,sK7),k10_yellow_6(sK6,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2695])).

cnf(c_4068,plain,
    ( k2_waybel_0(sK6,sK7,sK0(sK6,sK7,sK4(sK6,sK7,k4_yellow_6(sK6,sK7)),sK5(u1_struct_0(sK7)))) = k4_yellow_6(sK6,sK7)
    | m1_subset_1(k4_yellow_6(sK6,sK7),u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3976,c_3051])).

cnf(c_28,plain,
    ( v2_struct_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_30,plain,
    ( l1_pre_topc(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_13,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(k4_yellow_6(X1,X0),u1_struct_0(X1))
    | ~ l1_struct_0(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_480,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(k4_yellow_6(X1,X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X2)
    | v2_struct_0(X1)
    | X1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_13])).

cnf(c_481,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(k4_yellow_6(X1,X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1) ),
    inference(unflattening,[status(thm)],[c_480])).

cnf(c_1335,plain,
    ( m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0))
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | sK7 != X1
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_481,c_20])).

cnf(c_1336,plain,
    ( m1_subset_1(k4_yellow_6(sK6,sK7),u1_struct_0(sK6))
    | ~ l1_pre_topc(sK6)
    | v2_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_1335])).

cnf(c_1337,plain,
    ( m1_subset_1(k4_yellow_6(sK6,sK7),u1_struct_0(sK6)) = iProver_top
    | l1_pre_topc(sK6) != iProver_top
    | v2_struct_0(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1336])).

cnf(c_4164,plain,
    ( k2_waybel_0(sK6,sK7,sK0(sK6,sK7,sK4(sK6,sK7,k4_yellow_6(sK6,sK7)),sK5(u1_struct_0(sK7)))) = k4_yellow_6(sK6,sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4068,c_28,c_30,c_1337])).

cnf(c_0,plain,
    ( r1_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(k2_waybel_0(X0,X1,sK0(X0,X1,X2,X3)),X2)
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_427,plain,
    ( r1_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(k2_waybel_0(X0,X1,sK0(X0,X1,X2,X3)),X2)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(resolution,[status(thm)],[c_14,c_0])).

cnf(c_1230,plain,
    ( r1_waybel_0(X0,X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(k2_waybel_0(X0,X1,sK0(X0,X1,X2,X3)),X2)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK7 != X1
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_427,c_20])).

cnf(c_1231,plain,
    ( r1_waybel_0(sK6,sK7,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ r2_hidden(k2_waybel_0(sK6,sK7,sK0(sK6,sK7,X0,X1)),X0)
    | ~ l1_pre_topc(sK6)
    | v2_struct_0(sK7)
    | v2_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_1230])).

cnf(c_1235,plain,
    ( ~ r2_hidden(k2_waybel_0(sK6,sK7,sK0(sK6,sK7,X0,X1)),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | r1_waybel_0(sK6,sK7,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1231,c_27,c_25,c_24])).

cnf(c_1236,plain,
    ( r1_waybel_0(sK6,sK7,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ r2_hidden(k2_waybel_0(sK6,sK7,sK0(sK6,sK7,X0,X1)),X0) ),
    inference(renaming,[status(thm)],[c_1235])).

cnf(c_2683,plain,
    ( r1_waybel_0(sK6,sK7,X0_55)
    | ~ m1_subset_1(X1_55,u1_struct_0(sK7))
    | ~ r2_hidden(k2_waybel_0(sK6,sK7,sK0(sK6,sK7,X0_55,X1_55)),X0_55) ),
    inference(subtyping,[status(esa)],[c_1236])).

cnf(c_3063,plain,
    ( r1_waybel_0(sK6,sK7,X0_55) = iProver_top
    | m1_subset_1(X1_55,u1_struct_0(sK7)) != iProver_top
    | r2_hidden(k2_waybel_0(sK6,sK7,sK0(sK6,sK7,X0_55,X1_55)),X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2683])).

cnf(c_4167,plain,
    ( r1_waybel_0(sK6,sK7,sK4(sK6,sK7,k4_yellow_6(sK6,sK7))) = iProver_top
    | m1_subset_1(sK5(u1_struct_0(sK7)),u1_struct_0(sK7)) != iProver_top
    | r2_hidden(k4_yellow_6(sK6,sK7),sK4(sK6,sK7,k4_yellow_6(sK6,sK7))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4164,c_3063])).

cnf(c_18,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_15,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_160,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_18,c_15])).

cnf(c_1145,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,X0)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_160,c_26])).

cnf(c_1146,plain,
    ( ~ m1_connsp_2(X0,sK6,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | r2_hidden(X1,X0)
    | ~ l1_pre_topc(sK6)
    | v2_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_1145])).

cnf(c_1150,plain,
    ( ~ m1_connsp_2(X0,sK6,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | r2_hidden(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1146,c_27,c_25])).

cnf(c_2685,plain,
    ( ~ m1_connsp_2(X0_55,sK6,X1_55)
    | ~ m1_subset_1(X1_55,u1_struct_0(sK6))
    | r2_hidden(X1_55,X0_55) ),
    inference(subtyping,[status(esa)],[c_1150])).

cnf(c_3226,plain,
    ( ~ m1_connsp_2(X0_55,sK6,k4_yellow_6(sK6,sK7))
    | ~ m1_subset_1(k4_yellow_6(sK6,sK7),u1_struct_0(sK6))
    | r2_hidden(k4_yellow_6(sK6,sK7),X0_55) ),
    inference(instantiation,[status(thm)],[c_2685])).

cnf(c_3378,plain,
    ( ~ m1_connsp_2(sK4(sK6,sK7,k4_yellow_6(sK6,sK7)),sK6,k4_yellow_6(sK6,sK7))
    | ~ m1_subset_1(k4_yellow_6(sK6,sK7),u1_struct_0(sK6))
    | r2_hidden(k4_yellow_6(sK6,sK7),sK4(sK6,sK7,k4_yellow_6(sK6,sK7))) ),
    inference(instantiation,[status(thm)],[c_3226])).

cnf(c_3379,plain,
    ( m1_connsp_2(sK4(sK6,sK7,k4_yellow_6(sK6,sK7)),sK6,k4_yellow_6(sK6,sK7)) != iProver_top
    | m1_subset_1(k4_yellow_6(sK6,sK7),u1_struct_0(sK6)) != iProver_top
    | r2_hidden(k4_yellow_6(sK6,sK7),sK4(sK6,sK7,k4_yellow_6(sK6,sK7))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3378])).

cnf(c_3243,plain,
    ( m1_subset_1(sK5(u1_struct_0(sK7)),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_2696])).

cnf(c_3246,plain,
    ( m1_subset_1(sK5(u1_struct_0(sK7)),u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3243])).

cnf(c_1594,plain,
    ( ~ r1_waybel_0(sK6,sK7,sK4(sK6,sK7,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | k4_yellow_6(sK6,sK7) != X0
    | k10_yellow_6(sK6,sK7) != k10_yellow_6(sK6,sK7) ),
    inference(resolution_lifted,[status(thm)],[c_19,c_998])).

cnf(c_1595,plain,
    ( ~ r1_waybel_0(sK6,sK7,sK4(sK6,sK7,k4_yellow_6(sK6,sK7)))
    | ~ m1_subset_1(k4_yellow_6(sK6,sK7),u1_struct_0(sK6)) ),
    inference(unflattening,[status(thm)],[c_1594])).

cnf(c_1596,plain,
    ( r1_waybel_0(sK6,sK7,sK4(sK6,sK7,k4_yellow_6(sK6,sK7))) != iProver_top
    | m1_subset_1(k4_yellow_6(sK6,sK7),u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1595])).

cnf(c_10,plain,
    ( m1_connsp_2(sK4(X0,X1,X2),X0,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | r2_hidden(X2,k10_yellow_6(X0,X1))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_614,plain,
    ( m1_connsp_2(sK4(X0,X1,X2),X0,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | r2_hidden(X2,k10_yellow_6(X0,X1))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ v4_orders_2(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_22])).

cnf(c_615,plain,
    ( m1_connsp_2(sK4(X0,sK7,X1),X0,X1)
    | ~ l1_waybel_0(sK7,X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k10_yellow_6(X0,sK7),k1_zfmisc_1(u1_struct_0(X0)))
    | r2_hidden(X1,k10_yellow_6(X0,sK7))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ v4_orders_2(sK7)
    | v2_struct_0(X0)
    | v2_struct_0(sK7) ),
    inference(unflattening,[status(thm)],[c_614])).

cnf(c_619,plain,
    ( v2_struct_0(X0)
    | m1_connsp_2(sK4(X0,sK7,X1),X0,X1)
    | ~ l1_waybel_0(sK7,X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k10_yellow_6(X0,sK7),k1_zfmisc_1(u1_struct_0(X0)))
    | r2_hidden(X1,k10_yellow_6(X0,sK7))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_615,c_24,c_23])).

cnf(c_620,plain,
    ( m1_connsp_2(sK4(X0,sK7,X1),X0,X1)
    | ~ l1_waybel_0(sK7,X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k10_yellow_6(X0,sK7),k1_zfmisc_1(u1_struct_0(X0)))
    | r2_hidden(X1,k10_yellow_6(X0,sK7))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_619])).

cnf(c_820,plain,
    ( m1_connsp_2(sK4(X0,sK7,X1),X0,X1)
    | ~ l1_waybel_0(sK7,X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r2_hidden(X1,k10_yellow_6(X0,sK7))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_803,c_620])).

cnf(c_1014,plain,
    ( m1_connsp_2(sK4(X0,sK7,X1),X0,X1)
    | ~ l1_waybel_0(sK7,X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r2_hidden(X1,k10_yellow_6(X0,sK7))
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_820,c_26])).

cnf(c_1015,plain,
    ( m1_connsp_2(sK4(sK6,sK7,X0),sK6,X0)
    | ~ l1_waybel_0(sK7,sK6)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | r2_hidden(X0,k10_yellow_6(sK6,sK7))
    | ~ l1_pre_topc(sK6)
    | v2_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_1014])).

cnf(c_1019,plain,
    ( m1_connsp_2(sK4(sK6,sK7,X0),sK6,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | r2_hidden(X0,k10_yellow_6(sK6,sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1015,c_27,c_25,c_20])).

cnf(c_1583,plain,
    ( m1_connsp_2(sK4(sK6,sK7,X0),sK6,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | k4_yellow_6(sK6,sK7) != X0
    | k10_yellow_6(sK6,sK7) != k10_yellow_6(sK6,sK7) ),
    inference(resolution_lifted,[status(thm)],[c_19,c_1019])).

cnf(c_1584,plain,
    ( m1_connsp_2(sK4(sK6,sK7,k4_yellow_6(sK6,sK7)),sK6,k4_yellow_6(sK6,sK7))
    | ~ m1_subset_1(k4_yellow_6(sK6,sK7),u1_struct_0(sK6)) ),
    inference(unflattening,[status(thm)],[c_1583])).

cnf(c_1585,plain,
    ( m1_connsp_2(sK4(sK6,sK7,k4_yellow_6(sK6,sK7)),sK6,k4_yellow_6(sK6,sK7)) = iProver_top
    | m1_subset_1(k4_yellow_6(sK6,sK7),u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1584])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4167,c_3379,c_3246,c_1596,c_1585,c_1337,c_30,c_28])).


%------------------------------------------------------------------------------
