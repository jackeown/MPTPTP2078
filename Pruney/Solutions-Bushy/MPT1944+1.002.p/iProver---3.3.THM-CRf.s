%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1944+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:54 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :  174 (1202 expanded)
%              Number of clauses        :  107 ( 262 expanded)
%              Number of leaves         :   17 ( 342 expanded)
%              Depth                    :   24
%              Number of atoms          : 1026 (9906 expanded)
%              Number of equality atoms :   97 ( 161 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal clause size      :   24 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & v1_yellow_6(X1,X0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(o_2_6_yellow_6(X0,X1),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(o_2_6_yellow_6(X0,X1),u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v1_yellow_6(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(o_2_6_yellow_6(X0,X1),u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v1_yellow_6(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(o_2_6_yellow_6(X0,X1),u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v1_yellow_6(X1,X0)
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

fof(f29,plain,(
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

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1))
          & l1_waybel_0(X1,X0)
          & v1_yellow_6(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
     => ( ~ r2_hidden(k4_yellow_6(X0,sK6),k10_yellow_6(X0,sK6))
        & l1_waybel_0(sK6,X0)
        & v1_yellow_6(sK6,X0)
        & v7_waybel_0(sK6)
        & v4_orders_2(sK6)
        & ~ v2_struct_0(sK6) ) ) ),
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
          ( ~ r2_hidden(k4_yellow_6(sK5,X1),k10_yellow_6(sK5,X1))
          & l1_waybel_0(X1,sK5)
          & v1_yellow_6(X1,sK5)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK5)
      & v2_pre_topc(sK5)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ~ r2_hidden(k4_yellow_6(sK5,sK6),k10_yellow_6(sK5,sK6))
    & l1_waybel_0(sK6,sK5)
    & v1_yellow_6(sK6,sK5)
    & v7_waybel_0(sK6)
    & v4_orders_2(sK6)
    & ~ v2_struct_0(sK6)
    & l1_pre_topc(sK5)
    & v2_pre_topc(sK5)
    & ~ v2_struct_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f30,f44,f43])).

fof(f71,plain,(
    v1_yellow_6(sK6,sK5) ),
    inference(cnf_transformation,[],[f45])).

fof(f65,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f45])).

fof(f66,plain,(
    v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f45])).

fof(f67,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f45])).

fof(f68,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f45])).

fof(f69,plain,(
    v4_orders_2(sK6) ),
    inference(cnf_transformation,[],[f45])).

fof(f70,plain,(
    v7_waybel_0(sK6) ),
    inference(cnf_transformation,[],[f45])).

fof(f72,plain,(
    l1_waybel_0(sK6,sK5) ),
    inference(cnf_transformation,[],[f45])).

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
    inference(nnf_transformation,[],[f13])).

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
            | ~ r1_orders_2(X1,sK1(X0,X1,X2),X6)
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
          & r1_orders_2(X1,X3,X4)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_hidden(k2_waybel_0(X0,X1,sK0(X0,X1,X2,X3)),X2)
        & r1_orders_2(X1,X3,sK0(X0,X1,X2,X3))
        & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f34,f33])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_waybel_0(X0,X1,X2)
      | m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

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
    inference(ennf_transformation,[],[f8])).

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
    inference(cnf_transformation,[],[f26])).

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
    inference(nnf_transformation,[],[f15])).

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
     => ( ~ r1_waybel_0(X0,X1,sK4(X0,X1,X6))
        & m1_connsp_2(sK4(X0,X1,X6),X0,X6) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_waybel_0(X0,X1,X4)
          & m1_connsp_2(X4,X0,X3) )
     => ( ~ r1_waybel_0(X0,X1,sK3(X0,X1,X2))
        & m1_connsp_2(sK3(X0,X1,X2),X0,X3) ) ) ),
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
              & m1_connsp_2(X4,X0,sK2(X0,X1,X2)) )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ! [X5] :
              ( r1_waybel_0(X0,X1,X5)
              | ~ m1_connsp_2(X5,X0,sK2(X0,X1,X2)) )
          | r2_hidden(sK2(X0,X1,X2),X2) )
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f38,f41,f40,f39])).

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
    inference(cnf_transformation,[],[f42])).

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

fof(f73,plain,(
    ~ r2_hidden(k4_yellow_6(sK5,sK6),k10_yellow_6(sK5,sK6)) ),
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
    inference(cnf_transformation,[],[f35])).

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

fof(f27,plain,(
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

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ m1_connsp_2(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

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
    inference(cnf_transformation,[],[f42])).

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
    ( ~ v1_yellow_6(X0,X1)
    | ~ l1_waybel_0(X0,X1)
    | m1_subset_1(o_2_6_yellow_6(X1,X0),u1_struct_0(X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_21,negated_conjecture,
    ( v1_yellow_6(sK6,sK5) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_375,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(o_2_6_yellow_6(X1,X0),u1_struct_0(X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK6 != X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_21])).

cnf(c_376,plain,
    ( ~ l1_waybel_0(sK6,sK5)
    | m1_subset_1(o_2_6_yellow_6(sK5,sK6),u1_struct_0(sK6))
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK5)
    | ~ v4_orders_2(sK6)
    | ~ v7_waybel_0(sK6)
    | v2_struct_0(sK6)
    | v2_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_375])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_26,negated_conjecture,
    ( v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_25,negated_conjecture,
    ( l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_23,negated_conjecture,
    ( v4_orders_2(sK6) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_22,negated_conjecture,
    ( v7_waybel_0(sK6) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_20,negated_conjecture,
    ( l1_waybel_0(sK6,sK5) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_378,plain,
    ( m1_subset_1(o_2_6_yellow_6(sK5,sK6),u1_struct_0(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_376,c_27,c_26,c_25,c_24,c_23,c_22,c_20])).

cnf(c_2708,plain,
    ( m1_subset_1(o_2_6_yellow_6(sK5,sK6),u1_struct_0(sK6)) ),
    inference(subtyping,[status(esa)],[c_378])).

cnf(c_3064,plain,
    ( m1_subset_1(o_2_6_yellow_6(sK5,sK6),u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2708])).

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

cnf(c_414,plain,
    ( r1_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X1))
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(resolution,[status(thm)],[c_14,c_2])).

cnf(c_1264,plain,
    ( r1_waybel_0(X0,X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X1))
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK6 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_414,c_20])).

cnf(c_1265,plain,
    ( r1_waybel_0(sK5,sK6,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | m1_subset_1(sK0(sK5,sK6,X0,X1),u1_struct_0(sK6))
    | ~ l1_pre_topc(sK5)
    | v2_struct_0(sK6)
    | v2_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_1264])).

cnf(c_1269,plain,
    ( m1_subset_1(sK0(sK5,sK6,X0,X1),u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | r1_waybel_0(sK5,sK6,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1265,c_27,c_25,c_24])).

cnf(c_1270,plain,
    ( r1_waybel_0(sK5,sK6,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | m1_subset_1(sK0(sK5,sK6,X0,X1),u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_1269])).

cnf(c_2696,plain,
    ( r1_waybel_0(sK5,sK6,X0_55)
    | ~ m1_subset_1(X1_55,u1_struct_0(sK6))
    | m1_subset_1(sK0(sK5,sK6,X0_55,X1_55),u1_struct_0(sK6)) ),
    inference(subtyping,[status(esa)],[c_1270])).

cnf(c_3076,plain,
    ( r1_waybel_0(sK5,sK6,X0_55) = iProver_top
    | m1_subset_1(X1_55,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK0(sK5,sK6,X0_55,X1_55),u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2696])).

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

cnf(c_357,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | k2_waybel_0(X1,X0,X2) = k4_yellow_6(X1,X0)
    | sK6 != X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_21])).

cnf(c_358,plain,
    ( ~ l1_waybel_0(sK6,sK5)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ v4_orders_2(sK6)
    | ~ v7_waybel_0(sK6)
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK6)
    | v2_struct_0(sK5)
    | k2_waybel_0(sK5,sK6,X0) = k4_yellow_6(sK5,sK6) ),
    inference(unflattening,[status(thm)],[c_357])).

cnf(c_50,plain,
    ( ~ l1_pre_topc(sK5)
    | l1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_362,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | k2_waybel_0(sK5,sK6,X0) = k4_yellow_6(sK5,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_358,c_27,c_25,c_24,c_23,c_22,c_20,c_50])).

cnf(c_2709,plain,
    ( ~ m1_subset_1(X0_55,u1_struct_0(sK6))
    | k2_waybel_0(sK5,sK6,X0_55) = k4_yellow_6(sK5,sK6) ),
    inference(subtyping,[status(esa)],[c_362])).

cnf(c_3063,plain,
    ( k2_waybel_0(sK5,sK6,X0_55) = k4_yellow_6(sK5,sK6)
    | m1_subset_1(X0_55,u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2709])).

cnf(c_3654,plain,
    ( k2_waybel_0(sK5,sK6,sK0(sK5,sK6,X0_55,X1_55)) = k4_yellow_6(sK5,sK6)
    | r1_waybel_0(sK5,sK6,X0_55) = iProver_top
    | m1_subset_1(X1_55,u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3076,c_3063])).

cnf(c_3948,plain,
    ( k2_waybel_0(sK5,sK6,sK0(sK5,sK6,X0_55,o_2_6_yellow_6(sK5,sK6))) = k4_yellow_6(sK5,sK6)
    | r1_waybel_0(sK5,sK6,X0_55) = iProver_top ),
    inference(superposition,[status(thm)],[c_3064,c_3654])).

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

cnf(c_810,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(k10_yellow_6(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_22])).

cnf(c_811,plain,
    ( ~ l1_waybel_0(sK6,X0)
    | m1_subset_1(k10_yellow_6(X0,sK6),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ v4_orders_2(sK6)
    | v2_struct_0(X0)
    | v2_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_810])).

cnf(c_815,plain,
    ( v2_struct_0(X0)
    | ~ l1_waybel_0(sK6,X0)
    | m1_subset_1(k10_yellow_6(X0,sK6),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_811,c_24,c_23])).

cnf(c_816,plain,
    ( ~ l1_waybel_0(sK6,X0)
    | m1_subset_1(k10_yellow_6(X0,sK6),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_815])).

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

cnf(c_663,plain,
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
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_22])).

cnf(c_664,plain,
    ( ~ r1_waybel_0(X0,sK6,sK4(X0,sK6,X1))
    | ~ l1_waybel_0(sK6,X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k10_yellow_6(X0,sK6),k1_zfmisc_1(u1_struct_0(X0)))
    | r2_hidden(X1,k10_yellow_6(X0,sK6))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ v4_orders_2(sK6)
    | v2_struct_0(X0)
    | v2_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_663])).

cnf(c_668,plain,
    ( v2_struct_0(X0)
    | ~ r1_waybel_0(X0,sK6,sK4(X0,sK6,X1))
    | ~ l1_waybel_0(sK6,X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k10_yellow_6(X0,sK6),k1_zfmisc_1(u1_struct_0(X0)))
    | r2_hidden(X1,k10_yellow_6(X0,sK6))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_664,c_24,c_23])).

cnf(c_669,plain,
    ( ~ r1_waybel_0(X0,sK6,sK4(X0,sK6,X1))
    | ~ l1_waybel_0(sK6,X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k10_yellow_6(X0,sK6),k1_zfmisc_1(u1_struct_0(X0)))
    | r2_hidden(X1,k10_yellow_6(X0,sK6))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_668])).

cnf(c_834,plain,
    ( ~ r1_waybel_0(X0,sK6,sK4(X0,sK6,X1))
    | ~ l1_waybel_0(sK6,X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r2_hidden(X1,k10_yellow_6(X0,sK6))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_816,c_669])).

cnf(c_1006,plain,
    ( ~ r1_waybel_0(X0,sK6,sK4(X0,sK6,X1))
    | ~ l1_waybel_0(sK6,X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r2_hidden(X1,k10_yellow_6(X0,sK6))
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_834,c_26])).

cnf(c_1007,plain,
    ( ~ r1_waybel_0(sK5,sK6,sK4(sK5,sK6,X0))
    | ~ l1_waybel_0(sK6,sK5)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | r2_hidden(X0,k10_yellow_6(sK5,sK6))
    | ~ l1_pre_topc(sK5)
    | v2_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_1006])).

cnf(c_1011,plain,
    ( ~ r1_waybel_0(sK5,sK6,sK4(sK5,sK6,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | r2_hidden(X0,k10_yellow_6(sK5,sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1007,c_27,c_25,c_20])).

cnf(c_2706,plain,
    ( ~ r1_waybel_0(sK5,sK6,sK4(sK5,sK6,X0_55))
    | ~ m1_subset_1(X0_55,u1_struct_0(sK5))
    | r2_hidden(X0_55,k10_yellow_6(sK5,sK6)) ),
    inference(subtyping,[status(esa)],[c_1011])).

cnf(c_3066,plain,
    ( r1_waybel_0(sK5,sK6,sK4(sK5,sK6,X0_55)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X0_55,k10_yellow_6(sK5,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2706])).

cnf(c_3981,plain,
    ( k2_waybel_0(sK5,sK6,sK0(sK5,sK6,sK4(sK5,sK6,X0_55),o_2_6_yellow_6(sK5,sK6))) = k4_yellow_6(sK5,sK6)
    | m1_subset_1(X0_55,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X0_55,k10_yellow_6(sK5,sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3948,c_3066])).

cnf(c_19,negated_conjecture,
    ( ~ r2_hidden(k4_yellow_6(sK5,sK6),k10_yellow_6(sK5,sK6)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2710,negated_conjecture,
    ( ~ r2_hidden(k4_yellow_6(sK5,sK6),k10_yellow_6(sK5,sK6)) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_3062,plain,
    ( r2_hidden(k4_yellow_6(sK5,sK6),k10_yellow_6(sK5,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2710])).

cnf(c_4105,plain,
    ( k2_waybel_0(sK5,sK6,sK0(sK5,sK6,sK4(sK5,sK6,k4_yellow_6(sK5,sK6)),o_2_6_yellow_6(sK5,sK6))) = k4_yellow_6(sK5,sK6)
    | m1_subset_1(k4_yellow_6(sK5,sK6),u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3981,c_3062])).

cnf(c_13,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(k4_yellow_6(X1,X0),u1_struct_0(X1))
    | ~ l1_struct_0(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_493,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(k4_yellow_6(X1,X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X2)
    | v2_struct_0(X1)
    | X1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_13])).

cnf(c_494,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(k4_yellow_6(X1,X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1) ),
    inference(unflattening,[status(thm)],[c_493])).

cnf(c_1348,plain,
    ( m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0))
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | sK6 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_494,c_20])).

cnf(c_1349,plain,
    ( m1_subset_1(k4_yellow_6(sK5,sK6),u1_struct_0(sK5))
    | ~ l1_pre_topc(sK5)
    | v2_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_1348])).

cnf(c_1607,plain,
    ( ~ r1_waybel_0(sK5,sK6,sK4(sK5,sK6,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | k4_yellow_6(sK5,sK6) != X0
    | k10_yellow_6(sK5,sK6) != k10_yellow_6(sK5,sK6) ),
    inference(resolution_lifted,[status(thm)],[c_19,c_1011])).

cnf(c_1608,plain,
    ( ~ r1_waybel_0(sK5,sK6,sK4(sK5,sK6,k4_yellow_6(sK5,sK6)))
    | ~ m1_subset_1(k4_yellow_6(sK5,sK6),u1_struct_0(sK5)) ),
    inference(unflattening,[status(thm)],[c_1607])).

cnf(c_3229,plain,
    ( r1_waybel_0(sK5,sK6,X0_55)
    | m1_subset_1(sK0(sK5,sK6,X0_55,o_2_6_yellow_6(sK5,sK6)),u1_struct_0(sK6))
    | ~ m1_subset_1(o_2_6_yellow_6(sK5,sK6),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_2696])).

cnf(c_3390,plain,
    ( r1_waybel_0(sK5,sK6,sK4(sK5,sK6,k4_yellow_6(sK5,sK6)))
    | m1_subset_1(sK0(sK5,sK6,sK4(sK5,sK6,k4_yellow_6(sK5,sK6)),o_2_6_yellow_6(sK5,sK6)),u1_struct_0(sK6))
    | ~ m1_subset_1(o_2_6_yellow_6(sK5,sK6),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_3229])).

cnf(c_3313,plain,
    ( ~ m1_subset_1(sK0(sK5,sK6,X0_55,o_2_6_yellow_6(sK5,sK6)),u1_struct_0(sK6))
    | k2_waybel_0(sK5,sK6,sK0(sK5,sK6,X0_55,o_2_6_yellow_6(sK5,sK6))) = k4_yellow_6(sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_2709])).

cnf(c_4098,plain,
    ( ~ m1_subset_1(sK0(sK5,sK6,sK4(sK5,sK6,k4_yellow_6(sK5,sK6)),o_2_6_yellow_6(sK5,sK6)),u1_struct_0(sK6))
    | k2_waybel_0(sK5,sK6,sK0(sK5,sK6,sK4(sK5,sK6,k4_yellow_6(sK5,sK6)),o_2_6_yellow_6(sK5,sK6))) = k4_yellow_6(sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_3313])).

cnf(c_4136,plain,
    ( k2_waybel_0(sK5,sK6,sK0(sK5,sK6,sK4(sK5,sK6,k4_yellow_6(sK5,sK6)),o_2_6_yellow_6(sK5,sK6))) = k4_yellow_6(sK5,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4105,c_27,c_26,c_25,c_24,c_23,c_22,c_20,c_376,c_1349,c_1608,c_3390,c_4098])).

cnf(c_0,plain,
    ( r1_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(k2_waybel_0(X0,X1,sK0(X0,X1,X2,X3)),X2)
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_440,plain,
    ( r1_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(k2_waybel_0(X0,X1,sK0(X0,X1,X2,X3)),X2)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(resolution,[status(thm)],[c_14,c_0])).

cnf(c_1243,plain,
    ( r1_waybel_0(X0,X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(k2_waybel_0(X0,X1,sK0(X0,X1,X2,X3)),X2)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK6 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_440,c_20])).

cnf(c_1244,plain,
    ( r1_waybel_0(sK5,sK6,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ r2_hidden(k2_waybel_0(sK5,sK6,sK0(sK5,sK6,X0,X1)),X0)
    | ~ l1_pre_topc(sK5)
    | v2_struct_0(sK6)
    | v2_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_1243])).

cnf(c_1248,plain,
    ( ~ r2_hidden(k2_waybel_0(sK5,sK6,sK0(sK5,sK6,X0,X1)),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | r1_waybel_0(sK5,sK6,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1244,c_27,c_25,c_24])).

cnf(c_1249,plain,
    ( r1_waybel_0(sK5,sK6,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ r2_hidden(k2_waybel_0(sK5,sK6,sK0(sK5,sK6,X0,X1)),X0) ),
    inference(renaming,[status(thm)],[c_1248])).

cnf(c_2697,plain,
    ( r1_waybel_0(sK5,sK6,X0_55)
    | ~ m1_subset_1(X1_55,u1_struct_0(sK6))
    | ~ r2_hidden(k2_waybel_0(sK5,sK6,sK0(sK5,sK6,X0_55,X1_55)),X0_55) ),
    inference(subtyping,[status(esa)],[c_1249])).

cnf(c_3075,plain,
    ( r1_waybel_0(sK5,sK6,X0_55) = iProver_top
    | m1_subset_1(X1_55,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(k2_waybel_0(sK5,sK6,sK0(sK5,sK6,X0_55,X1_55)),X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2697])).

cnf(c_4139,plain,
    ( r1_waybel_0(sK5,sK6,sK4(sK5,sK6,k4_yellow_6(sK5,sK6))) = iProver_top
    | m1_subset_1(o_2_6_yellow_6(sK5,sK6),u1_struct_0(sK6)) != iProver_top
    | r2_hidden(k4_yellow_6(sK5,sK6),sK4(sK5,sK6,k4_yellow_6(sK5,sK6))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4136,c_3075])).

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

cnf(c_1158,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,X0)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_160,c_26])).

cnf(c_1159,plain,
    ( ~ m1_connsp_2(X0,sK5,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | r2_hidden(X1,X0)
    | ~ l1_pre_topc(sK5)
    | v2_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_1158])).

cnf(c_1163,plain,
    ( ~ m1_connsp_2(X0,sK5,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | r2_hidden(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1159,c_27,c_25])).

cnf(c_2699,plain,
    ( ~ m1_connsp_2(X0_55,sK5,X1_55)
    | ~ m1_subset_1(X1_55,u1_struct_0(sK5))
    | r2_hidden(X1_55,X0_55) ),
    inference(subtyping,[status(esa)],[c_1163])).

cnf(c_3251,plain,
    ( ~ m1_connsp_2(X0_55,sK5,k4_yellow_6(sK5,sK6))
    | ~ m1_subset_1(k4_yellow_6(sK5,sK6),u1_struct_0(sK5))
    | r2_hidden(k4_yellow_6(sK5,sK6),X0_55) ),
    inference(instantiation,[status(thm)],[c_2699])).

cnf(c_3326,plain,
    ( ~ m1_connsp_2(sK4(sK5,sK6,k4_yellow_6(sK5,sK6)),sK5,k4_yellow_6(sK5,sK6))
    | ~ m1_subset_1(k4_yellow_6(sK5,sK6),u1_struct_0(sK5))
    | r2_hidden(k4_yellow_6(sK5,sK6),sK4(sK5,sK6,k4_yellow_6(sK5,sK6))) ),
    inference(instantiation,[status(thm)],[c_3251])).

cnf(c_3327,plain,
    ( m1_connsp_2(sK4(sK5,sK6,k4_yellow_6(sK5,sK6)),sK5,k4_yellow_6(sK5,sK6)) != iProver_top
    | m1_subset_1(k4_yellow_6(sK5,sK6),u1_struct_0(sK5)) != iProver_top
    | r2_hidden(k4_yellow_6(sK5,sK6),sK4(sK5,sK6,k4_yellow_6(sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3326])).

cnf(c_1609,plain,
    ( r1_waybel_0(sK5,sK6,sK4(sK5,sK6,k4_yellow_6(sK5,sK6))) != iProver_top
    | m1_subset_1(k4_yellow_6(sK5,sK6),u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1608])).

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

cnf(c_627,plain,
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
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_22])).

cnf(c_628,plain,
    ( m1_connsp_2(sK4(X0,sK6,X1),X0,X1)
    | ~ l1_waybel_0(sK6,X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k10_yellow_6(X0,sK6),k1_zfmisc_1(u1_struct_0(X0)))
    | r2_hidden(X1,k10_yellow_6(X0,sK6))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ v4_orders_2(sK6)
    | v2_struct_0(X0)
    | v2_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_627])).

cnf(c_632,plain,
    ( v2_struct_0(X0)
    | m1_connsp_2(sK4(X0,sK6,X1),X0,X1)
    | ~ l1_waybel_0(sK6,X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k10_yellow_6(X0,sK6),k1_zfmisc_1(u1_struct_0(X0)))
    | r2_hidden(X1,k10_yellow_6(X0,sK6))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_628,c_24,c_23])).

cnf(c_633,plain,
    ( m1_connsp_2(sK4(X0,sK6,X1),X0,X1)
    | ~ l1_waybel_0(sK6,X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k10_yellow_6(X0,sK6),k1_zfmisc_1(u1_struct_0(X0)))
    | r2_hidden(X1,k10_yellow_6(X0,sK6))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_632])).

cnf(c_833,plain,
    ( m1_connsp_2(sK4(X0,sK6,X1),X0,X1)
    | ~ l1_waybel_0(sK6,X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r2_hidden(X1,k10_yellow_6(X0,sK6))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_816,c_633])).

cnf(c_1027,plain,
    ( m1_connsp_2(sK4(X0,sK6,X1),X0,X1)
    | ~ l1_waybel_0(sK6,X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r2_hidden(X1,k10_yellow_6(X0,sK6))
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_833,c_26])).

cnf(c_1028,plain,
    ( m1_connsp_2(sK4(sK5,sK6,X0),sK5,X0)
    | ~ l1_waybel_0(sK6,sK5)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | r2_hidden(X0,k10_yellow_6(sK5,sK6))
    | ~ l1_pre_topc(sK5)
    | v2_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_1027])).

cnf(c_1032,plain,
    ( m1_connsp_2(sK4(sK5,sK6,X0),sK5,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | r2_hidden(X0,k10_yellow_6(sK5,sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1028,c_27,c_25,c_20])).

cnf(c_1596,plain,
    ( m1_connsp_2(sK4(sK5,sK6,X0),sK5,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | k4_yellow_6(sK5,sK6) != X0
    | k10_yellow_6(sK5,sK6) != k10_yellow_6(sK5,sK6) ),
    inference(resolution_lifted,[status(thm)],[c_19,c_1032])).

cnf(c_1597,plain,
    ( m1_connsp_2(sK4(sK5,sK6,k4_yellow_6(sK5,sK6)),sK5,k4_yellow_6(sK5,sK6))
    | ~ m1_subset_1(k4_yellow_6(sK5,sK6),u1_struct_0(sK5)) ),
    inference(unflattening,[status(thm)],[c_1596])).

cnf(c_1598,plain,
    ( m1_connsp_2(sK4(sK5,sK6,k4_yellow_6(sK5,sK6)),sK5,k4_yellow_6(sK5,sK6)) = iProver_top
    | m1_subset_1(k4_yellow_6(sK5,sK6),u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1597])).

cnf(c_1350,plain,
    ( m1_subset_1(k4_yellow_6(sK5,sK6),u1_struct_0(sK5)) = iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v2_struct_0(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1349])).

cnf(c_377,plain,
    ( l1_waybel_0(sK6,sK5) != iProver_top
    | m1_subset_1(o_2_6_yellow_6(sK5,sK6),u1_struct_0(sK6)) = iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v4_orders_2(sK6) != iProver_top
    | v7_waybel_0(sK6) != iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v2_struct_0(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_376])).

cnf(c_35,plain,
    ( l1_waybel_0(sK6,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_33,plain,
    ( v7_waybel_0(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_32,plain,
    ( v4_orders_2(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_31,plain,
    ( v2_struct_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_30,plain,
    ( l1_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_29,plain,
    ( v2_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_28,plain,
    ( v2_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4139,c_3327,c_1609,c_1598,c_1350,c_377,c_35,c_33,c_32,c_31,c_30,c_29,c_28])).


%------------------------------------------------------------------------------
