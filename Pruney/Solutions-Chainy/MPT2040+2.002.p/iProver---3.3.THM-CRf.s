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
% DateTime   : Thu Dec  3 12:29:00 EST 2020

% Result     : Theorem 2.82s
% Output     : CNFRefutation 2.82s
% Verified   : 
% Statistics : Number of formulae       :  349 (20920 expanded)
%              Number of clauses        :  256 (3445 expanded)
%              Number of leaves         :   21 (5252 expanded)
%              Depth                    :   33
%              Number of atoms          : 2779 (316629 expanded)
%              Number of equality atoms :  395 (3054 expanded)
%              Maximal formula depth    :   27 (   8 average)
%              Maximal clause size      :   36 (   7 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_waybel_9(X0)
        & v1_compts_1(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => v5_pre_topc(k4_waybel_1(X0,X1),X0,X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ( v11_waybel_0(X1,X0)
             => ( r2_hidden(k1_waybel_9(X0,X1),k10_yellow_6(X0,X1))
                & r2_waybel_9(X0,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_waybel_9(X0)
          & v1_compts_1(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & v8_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ( ! [X1] :
              ( m1_subset_1(X1,u1_struct_0(X0))
             => v5_pre_topc(k4_waybel_1(X0,X1),X0,X0) )
         => ! [X1] :
              ( ( l1_waybel_0(X1,X0)
                & v7_waybel_0(X1)
                & v4_orders_2(X1)
                & ~ v2_struct_0(X1) )
             => ( v11_waybel_0(X1,X0)
               => ( r2_hidden(k1_waybel_9(X0,X1),k10_yellow_6(X0,X1))
                  & r2_waybel_9(X0,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f15,plain,(
    ~ ! [X0] :
        ( ( l1_waybel_9(X0)
          & v1_compts_1(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & v8_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ( ! [X1] :
              ( m1_subset_1(X1,u1_struct_0(X0))
             => v5_pre_topc(k4_waybel_1(X0,X1),X0,X0) )
         => ! [X2] :
              ( ( l1_waybel_0(X2,X0)
                & v7_waybel_0(X2)
                & v4_orders_2(X2)
                & ~ v2_struct_0(X2) )
             => ( v11_waybel_0(X2,X0)
               => ( r2_hidden(k1_waybel_9(X0,X2),k10_yellow_6(X0,X2))
                  & r2_waybel_9(X0,X2) ) ) ) ) ) ),
    inference(rectify,[],[f11])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(k1_waybel_9(X0,X2),k10_yellow_6(X0,X2))
            | ~ r2_waybel_9(X0,X2) )
          & v11_waybel_0(X2,X0)
          & l1_waybel_0(X2,X0)
          & v7_waybel_0(X2)
          & v4_orders_2(X2)
          & ~ v2_struct_0(X2) )
      & ! [X1] :
          ( v5_pre_topc(k4_waybel_1(X0,X1),X0,X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_waybel_9(X0)
      & v1_compts_1(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & v8_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(k1_waybel_9(X0,X2),k10_yellow_6(X0,X2))
            | ~ r2_waybel_9(X0,X2) )
          & v11_waybel_0(X2,X0)
          & l1_waybel_0(X2,X0)
          & v7_waybel_0(X2)
          & v4_orders_2(X2)
          & ~ v2_struct_0(X2) )
      & ! [X1] :
          ( v5_pre_topc(k4_waybel_1(X0,X1),X0,X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_waybel_9(X0)
      & v1_compts_1(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & v8_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f50,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r2_hidden(k1_waybel_9(X0,X1),k10_yellow_6(X0,X1))
            | ~ r2_waybel_9(X0,X1) )
          & v11_waybel_0(X1,X0)
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & ! [X2] :
          ( v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      & l1_waybel_9(X0)
      & v1_compts_1(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & v8_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(rectify,[],[f33])).

fof(f52,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ r2_hidden(k1_waybel_9(X0,X1),k10_yellow_6(X0,X1))
            | ~ r2_waybel_9(X0,X1) )
          & v11_waybel_0(X1,X0)
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
     => ( ( ~ r2_hidden(k1_waybel_9(X0,sK8),k10_yellow_6(X0,sK8))
          | ~ r2_waybel_9(X0,sK8) )
        & v11_waybel_0(sK8,X0)
        & l1_waybel_0(sK8,X0)
        & v7_waybel_0(sK8)
        & v4_orders_2(sK8)
        & ~ v2_struct_0(sK8) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r2_hidden(k1_waybel_9(X0,X1),k10_yellow_6(X0,X1))
              | ~ r2_waybel_9(X0,X1) )
            & v11_waybel_0(X1,X0)
            & l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        & ! [X2] :
            ( v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        & l1_waybel_9(X0)
        & v1_compts_1(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ r2_hidden(k1_waybel_9(sK7,X1),k10_yellow_6(sK7,X1))
            | ~ r2_waybel_9(sK7,X1) )
          & v11_waybel_0(X1,sK7)
          & l1_waybel_0(X1,sK7)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & ! [X2] :
          ( v5_pre_topc(k4_waybel_1(sK7,X2),sK7,sK7)
          | ~ m1_subset_1(X2,u1_struct_0(sK7)) )
      & l1_waybel_9(sK7)
      & v1_compts_1(sK7)
      & v2_lattice3(sK7)
      & v1_lattice3(sK7)
      & v5_orders_2(sK7)
      & v4_orders_2(sK7)
      & v3_orders_2(sK7)
      & v8_pre_topc(sK7)
      & v2_pre_topc(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ( ~ r2_hidden(k1_waybel_9(sK7,sK8),k10_yellow_6(sK7,sK8))
      | ~ r2_waybel_9(sK7,sK8) )
    & v11_waybel_0(sK8,sK7)
    & l1_waybel_0(sK8,sK7)
    & v7_waybel_0(sK8)
    & v4_orders_2(sK8)
    & ~ v2_struct_0(sK8)
    & ! [X2] :
        ( v5_pre_topc(k4_waybel_1(sK7,X2),sK7,sK7)
        | ~ m1_subset_1(X2,u1_struct_0(sK7)) )
    & l1_waybel_9(sK7)
    & v1_compts_1(sK7)
    & v2_lattice3(sK7)
    & v1_lattice3(sK7)
    & v5_orders_2(sK7)
    & v4_orders_2(sK7)
    & v3_orders_2(sK7)
    & v8_pre_topc(sK7)
    & v2_pre_topc(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f50,f52,f51])).

fof(f93,plain,(
    l1_waybel_0(sK8,sK7) ),
    inference(cnf_transformation,[],[f53])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_compts_1(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ? [X2] :
              ( r3_waybel_9(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( r3_waybel_9(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( r3_waybel_9(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( r3_waybel_9(X0,X1,X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( r3_waybel_9(X0,X1,sK3(X0,X1))
        & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r3_waybel_9(X0,X1,sK3(X0,X1))
            & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f42])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r3_waybel_9(X0,X1,sK3(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_waybel_9(X0)
     => ( l1_orders_2(X0)
        & l1_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & l1_pre_topc(X0) )
      | ~ l1_waybel_9(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f65,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
      | ~ l1_waybel_9(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f88,plain,(
    l1_waybel_9(sK7) ),
    inference(cnf_transformation,[],[f53])).

fof(f80,plain,(
    v2_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f53])).

fof(f81,plain,(
    v8_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f53])).

fof(f85,plain,(
    v1_lattice3(sK7) ),
    inference(cnf_transformation,[],[f53])).

fof(f87,plain,(
    v1_compts_1(sK7) ),
    inference(cnf_transformation,[],[f53])).

fof(f66,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
      | ~ l1_waybel_9(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f16])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f90,plain,(
    ~ v2_struct_0(sK8) ),
    inference(cnf_transformation,[],[f53])).

fof(f91,plain,(
    v4_orders_2(sK8) ),
    inference(cnf_transformation,[],[f53])).

fof(f92,plain,(
    v7_waybel_0(sK8) ),
    inference(cnf_transformation,[],[f53])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r1_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X3,X1) ) )
                  & r1_lattice3(X0,X2,X1) )
               => ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 ) )
              & ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
               => ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r1_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X3,X1) ) )
                  & r1_lattice3(X0,X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r1_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X3,X1) ) )
                  & r1_lattice3(X0,X2,X1) )
               => ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 ) )
              & ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
               => ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X0))
                     => ( r1_lattice3(X0,X2,X4)
                       => r1_orders_2(X0,X4,X1) ) )
                  & r1_lattice3(X0,X2,X1) ) ) ) ) ) ),
    inference(rectify,[],[f2])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X3,X1)
                    & r1_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X4,X1)
                      | ~ r1_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r1_lattice3(X0,X2,X1) )
                | ~ r2_yellow_0(X0,X2)
                | k2_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X3,X1)
                    & r1_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X4,X1)
                      | ~ r1_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r1_lattice3(X0,X2,X1) )
                | ~ r2_yellow_0(X0,X2)
                | k2_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f18])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X1)
          & r1_lattice3(X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK0(X0,X1,X2),X1)
        & r1_lattice3(X0,X2,sK0(X0,X1,X2))
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
                | ( ~ r1_orders_2(X0,sK0(X0,X1,X2),X1)
                  & r1_lattice3(X0,X2,sK0(X0,X1,X2))
                  & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X4,X1)
                      | ~ r1_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r1_lattice3(X0,X2,X1) )
                | ~ r2_yellow_0(X0,X2)
                | k2_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f34])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r2_yellow_0(X0,X2)
      | r1_lattice3(X0,X2,sK0(X0,X1,X2))
      | ~ r1_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f84,plain,(
    v5_orders_2(sK7) ),
    inference(cnf_transformation,[],[f53])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_waybel_9(X0)
        & v1_compts_1(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( r3_waybel_9(X0,X1,X2)
                      & ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) )
                      & X2 = X3 )
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ( r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
                         => r1_orders_2(X0,X4,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ( l1_waybel_9(X0)
        & v1_compts_1(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( r3_waybel_9(X0,X1,X2)
                      & ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) )
                      & X2 = X3 )
                   => ! [X5] :
                        ( m1_subset_1(X5,u1_struct_0(X0))
                       => ( r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5)
                         => r1_orders_2(X0,X5,X3) ) ) ) ) ) ) ) ),
    inference(rectify,[],[f6])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X5] :
                      ( r1_orders_2(X0,X5,X3)
                      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ? [X4] :
                      ( ~ v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X5] :
                      ( r1_orders_2(X0,X5,X3)
                      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ? [X4] :
                      ( ~ v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r1_orders_2(X0,X4,X3)
                      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ? [X5] :
                      ( ~ v5_pre_topc(k4_waybel_1(X0,X5),X0,X0)
                      & m1_subset_1(X5,u1_struct_0(X0)) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f25])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X5] :
          ( ~ v5_pre_topc(k4_waybel_1(X0,X5),X0,X0)
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( ~ v5_pre_topc(k4_waybel_1(X0,sK2(X0)),X0,X0)
        & m1_subset_1(sK2(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r1_orders_2(X0,X4,X3)
                      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ( ~ v5_pre_topc(k4_waybel_1(X0,sK2(X0)),X0,X0)
                    & m1_subset_1(sK2(X0),u1_struct_0(X0)) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f39,f40])).

fof(f70,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r1_orders_2(X0,X4,X3)
      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK2(X0)),X0,X0)
      | X2 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f100,plain,(
    ! [X4,X0,X3,X1] :
      ( r1_orders_2(X0,X4,X3)
      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X3)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK2(X0)),X0,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f70])).

fof(f89,plain,(
    ! [X2] :
      ( v5_pre_topc(k4_waybel_1(sK7,X2),sK7,sK7)
      | ~ m1_subset_1(X2,u1_struct_0(sK7)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f82,plain,(
    v3_orders_2(sK7) ),
    inference(cnf_transformation,[],[f53])).

fof(f83,plain,(
    v4_orders_2(sK7) ),
    inference(cnf_transformation,[],[f53])).

fof(f86,plain,(
    v2_lattice3(sK7) ),
    inference(cnf_transformation,[],[f53])).

fof(f69,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r1_orders_2(X0,X4,X3)
      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X2)
      | m1_subset_1(sK2(X0),u1_struct_0(X0))
      | X2 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f101,plain,(
    ! [X4,X0,X3,X1] :
      ( r1_orders_2(X0,X4,X3)
      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X3)
      | m1_subset_1(sK2(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f69])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r2_yellow_0(X0,X2)
      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
      | ~ r1_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r2_yellow_0(X0,X2)
      | ~ r1_orders_2(X0,sK0(X0,X1,X2),X1)
      | ~ r1_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f94,plain,(
    v11_waybel_0(sK8,sK7) ),
    inference(cnf_transformation,[],[f53])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_waybel_9(X0)
        & v1_compts_1(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( r3_waybel_9(X0,X1,X2)
                      & v11_waybel_0(X1,X0)
                      & ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) )
                      & X2 = X3 )
                   => r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ~ v11_waybel_0(X1,X0)
                  | ? [X4] :
                      ( ~ v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ~ v11_waybel_0(X1,X0)
                  | ? [X4] :
                      ( ~ v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X4] :
          ( ~ v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ v5_pre_topc(k4_waybel_1(X0,sK1(X0)),X0,X0)
        & m1_subset_1(sK1(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ~ v11_waybel_0(X1,X0)
                  | ( ~ v5_pre_topc(k4_waybel_1(X0,sK1(X0)),X0,X0)
                    & m1_subset_1(sK1(X0),u1_struct_0(X0)) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f23,f37])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ v11_waybel_0(X1,X0)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK1(X0)),X0,X0)
      | X2 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f98,plain,(
    ! [X0,X3,X1] :
      ( r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
      | ~ r3_waybel_9(X0,X1,X3)
      | ~ v11_waybel_0(X1,X0)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK1(X0)),X0,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f68])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ v11_waybel_0(X1,X0)
      | m1_subset_1(sK1(X0),u1_struct_0(X0))
      | X2 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f99,plain,(
    ! [X0,X3,X1] :
      ( r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
      | ~ r3_waybel_9(X0,X1,X3)
      | ~ v11_waybel_0(X1,X0)
      | m1_subset_1(sK1(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f67])).

fof(f71,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_compts_1(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ( ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r3_waybel_9(X0,X1,X3)
                        & r3_waybel_9(X0,X1,X2) )
                     => X2 = X3 ) ) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r3_waybel_9(X0,X1,X2)
                 => r2_hidden(X2,k10_yellow_6(X0,X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_compts_1(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ( ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r3_waybel_9(X0,X1,X3)
                        & r3_waybel_9(X0,X1,X2) )
                     => X2 = X3 ) ) )
           => ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X0))
               => ( r3_waybel_9(X0,X1,X4)
                 => r2_hidden(X4,k10_yellow_6(X0,X1)) ) ) ) ) ) ),
    inference(rectify,[],[f8])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X4] :
              ( r2_hidden(X4,k10_yellow_6(X0,X1))
              | ~ r3_waybel_9(X0,X1,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ? [X2] :
              ( ? [X3] :
                  ( X2 != X3
                  & r3_waybel_9(X0,X1,X3)
                  & r3_waybel_9(X0,X1,X2)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X4] :
              ( r2_hidden(X4,k10_yellow_6(X0,X1))
              | ~ r3_waybel_9(X0,X1,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ? [X2] :
              ( ? [X3] :
                  ( X2 != X3
                  & r3_waybel_9(X0,X1,X3)
                  & r3_waybel_9(X0,X1,X2)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k10_yellow_6(X0,X1))
              | ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ? [X3] :
              ( ? [X4] :
                  ( X3 != X4
                  & r3_waybel_9(X0,X1,X4)
                  & r3_waybel_9(X0,X1,X3)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f29])).

fof(f46,plain,(
    ! [X3,X1,X0] :
      ( ? [X4] :
          ( X3 != X4
          & r3_waybel_9(X0,X1,X4)
          & r3_waybel_9(X0,X1,X3)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( sK5(X0,X1) != X3
        & r3_waybel_9(X0,X1,sK5(X0,X1))
        & r3_waybel_9(X0,X1,X3)
        & m1_subset_1(sK5(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ? [X4] :
              ( X3 != X4
              & r3_waybel_9(X0,X1,X4)
              & r3_waybel_9(X0,X1,X3)
              & m1_subset_1(X4,u1_struct_0(X0)) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ? [X4] :
            ( sK4(X0,X1) != X4
            & r3_waybel_9(X0,X1,X4)
            & r3_waybel_9(X0,X1,sK4(X0,X1))
            & m1_subset_1(X4,u1_struct_0(X0)) )
        & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k10_yellow_6(X0,X1))
              | ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ( sK4(X0,X1) != sK5(X0,X1)
            & r3_waybel_9(X0,X1,sK5(X0,X1))
            & r3_waybel_9(X0,X1,sK4(X0,X1))
            & m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
            & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f44,f46,f45])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k10_yellow_6(X0,X1))
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r3_waybel_9(X0,X1,sK4(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => ( r2_waybel_9(X0,X1)
          <=> r2_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_waybel_9(X0,X1)
          <=> r2_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) )
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_waybel_9(X0,X1)
              | ~ r2_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) )
            & ( r2_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
              | ~ r2_waybel_9(X0,X1) ) )
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r2_waybel_9(X0,X1)
      | ~ r2_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f95,plain,
    ( ~ r2_hidden(k1_waybel_9(sK7,sK8),k10_yellow_6(sK7,sK8))
    | ~ r2_waybel_9(sK7,sK8) ),
    inference(cnf_transformation,[],[f53])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_waybel_9(X0)
        & v1_compts_1(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( l1_waybel_0(X2,X0)
                & v7_waybel_0(X2)
                & v4_orders_2(X2)
                & ~ v2_struct_0(X2) )
             => ( ( r3_waybel_9(X0,X2,X1)
                  & v11_waybel_0(X2,X0)
                  & ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) ) )
               => k1_waybel_9(X0,X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_waybel_9(X0,X2) = X1
              | ~ r3_waybel_9(X0,X2,X1)
              | ~ v11_waybel_0(X2,X0)
              | ? [X3] :
                  ( ~ v5_pre_topc(k4_waybel_1(X0,X3),X0,X0)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ l1_waybel_0(X2,X0)
              | ~ v7_waybel_0(X2)
              | ~ v4_orders_2(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_waybel_9(X0,X2) = X1
              | ~ r3_waybel_9(X0,X2,X1)
              | ~ v11_waybel_0(X2,X0)
              | ? [X3] :
                  ( ~ v5_pre_topc(k4_waybel_1(X0,X3),X0,X0)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ l1_waybel_0(X2,X0)
              | ~ v7_waybel_0(X2)
              | ~ v4_orders_2(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X3] :
          ( ~ v5_pre_topc(k4_waybel_1(X0,X3),X0,X0)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ v5_pre_topc(k4_waybel_1(X0,sK6(X0)),X0,X0)
        & m1_subset_1(sK6(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_waybel_9(X0,X2) = X1
              | ~ r3_waybel_9(X0,X2,X1)
              | ~ v11_waybel_0(X2,X0)
              | ( ~ v5_pre_topc(k4_waybel_1(X0,sK6(X0)),X0,X0)
                & m1_subset_1(sK6(X0),u1_struct_0(X0)) )
              | ~ l1_waybel_0(X2,X0)
              | ~ v7_waybel_0(X2)
              | ~ v4_orders_2(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f31,f48])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k1_waybel_9(X0,X2) = X1
      | ~ r3_waybel_9(X0,X2,X1)
      | ~ v11_waybel_0(X2,X0)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK6(X0)),X0,X0)
      | ~ l1_waybel_0(X2,X0)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k1_waybel_9(X0,X2) = X1
      | ~ r3_waybel_9(X0,X2,X1)
      | ~ v11_waybel_0(X2,X0)
      | m1_subset_1(sK6(X0),u1_struct_0(X0))
      | ~ l1_waybel_0(X2,X0)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k10_yellow_6(X0,X1))
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k10_yellow_6(X0,X1))
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | sK4(X0,X1) != sK5(X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k10_yellow_6(X0,X1))
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r3_waybel_9(X0,X1,sK5(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k10_yellow_6(X0,X1))
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_28,negated_conjecture,
    ( l1_waybel_0(sK8,sK7) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_17,plain,
    ( r3_waybel_9(X0,X1,sK3(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_12,plain,
    ( l1_pre_topc(X0)
    | ~ l1_waybel_9(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_33,negated_conjecture,
    ( l1_waybel_9(sK7) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1315,plain,
    ( l1_pre_topc(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_33])).

cnf(c_1316,plain,
    ( l1_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_1315])).

cnf(c_2252,plain,
    ( r3_waybel_9(X0,X1,sK3(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_1316])).

cnf(c_2253,plain,
    ( r3_waybel_9(sK7,X0,sK3(sK7,X0))
    | ~ l1_waybel_0(X0,sK7)
    | ~ v2_pre_topc(sK7)
    | ~ v8_pre_topc(sK7)
    | ~ v1_compts_1(sK7)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK7) ),
    inference(unflattening,[status(thm)],[c_2252])).

cnf(c_41,negated_conjecture,
    ( v2_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_40,negated_conjecture,
    ( v8_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_36,negated_conjecture,
    ( v1_lattice3(sK7) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_34,negated_conjecture,
    ( v1_compts_1(sK7) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_11,plain,
    ( ~ l1_waybel_9(X0)
    | l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_103,plain,
    ( ~ l1_waybel_9(sK7)
    | l1_orders_2(sK7) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_0,plain,
    ( ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | ~ v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_136,plain,
    ( ~ l1_orders_2(sK7)
    | ~ v1_lattice3(sK7)
    | ~ v2_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2257,plain,
    ( v2_struct_0(X0)
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | r3_waybel_9(sK7,X0,sK3(sK7,X0))
    | ~ l1_waybel_0(X0,sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2253,c_41,c_40,c_36,c_34,c_33,c_103,c_136])).

cnf(c_2258,plain,
    ( r3_waybel_9(sK7,X0,sK3(sK7,X0))
    | ~ l1_waybel_0(X0,sK7)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_2257])).

cnf(c_2379,plain,
    ( r3_waybel_9(sK7,X0,sK3(sK7,X0))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | sK8 != X0
    | sK7 != sK7 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_2258])).

cnf(c_2380,plain,
    ( r3_waybel_9(sK7,sK8,sK3(sK7,sK8))
    | ~ v4_orders_2(sK8)
    | ~ v7_waybel_0(sK8)
    | v2_struct_0(sK8) ),
    inference(unflattening,[status(thm)],[c_2379])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK8) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_30,negated_conjecture,
    ( v4_orders_2(sK8) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_29,negated_conjecture,
    ( v7_waybel_0(sK8) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_2382,plain,
    ( r3_waybel_9(sK7,sK8,sK3(sK7,sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2380,c_31,c_30,c_29])).

cnf(c_4366,plain,
    ( r3_waybel_9(sK7,sK8,sK3(sK7,sK8)) ),
    inference(subtyping,[status(esa)],[c_2382])).

cnf(c_4894,plain,
    ( r3_waybel_9(sK7,sK8,sK3(sK7,sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4366])).

cnf(c_2,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_lattice3(X0,X1,sK0(X0,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_yellow_0(X0,X1)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_621,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_lattice3(X0,X1,sK0(X0,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_yellow_0(X0,X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0) ),
    inference(resolution,[status(thm)],[c_11,c_2])).

cnf(c_37,negated_conjecture,
    ( v5_orders_2(sK7) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1107,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_lattice3(X0,X1,sK0(X0,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_yellow_0(X0,X1)
    | ~ l1_waybel_9(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_621,c_37])).

cnf(c_1108,plain,
    ( ~ r1_lattice3(sK7,X0,X1)
    | r1_lattice3(sK7,X0,sK0(sK7,X1,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | r2_yellow_0(sK7,X0)
    | ~ l1_waybel_9(sK7) ),
    inference(unflattening,[status(thm)],[c_1107])).

cnf(c_1112,plain,
    ( r2_yellow_0(sK7,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | r1_lattice3(sK7,X0,sK0(sK7,X1,X0))
    | ~ r1_lattice3(sK7,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1108,c_33])).

cnf(c_1113,plain,
    ( ~ r1_lattice3(sK7,X0,X1)
    | r1_lattice3(sK7,X0,sK0(sK7,X1,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | r2_yellow_0(sK7,X0) ),
    inference(renaming,[status(thm)],[c_1112])).

cnf(c_4374,plain,
    ( ~ r1_lattice3(sK7,X0_70,X0_68)
    | r1_lattice3(sK7,X0_70,sK0(sK7,X0_68,X0_70))
    | ~ m1_subset_1(X0_68,u1_struct_0(sK7))
    | r2_yellow_0(sK7,X0_70) ),
    inference(subtyping,[status(esa)],[c_1113])).

cnf(c_4886,plain,
    ( r1_lattice3(sK7,X0_70,X0_68) != iProver_top
    | r1_lattice3(sK7,X0_70,sK0(sK7,X0_68,X0_70)) = iProver_top
    | m1_subset_1(X0_68,u1_struct_0(sK7)) != iProver_top
    | r2_yellow_0(sK7,X0_70) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4374])).

cnf(c_15,plain,
    ( ~ v5_pre_topc(k4_waybel_1(X0,sK2(X0)),X0,X0)
    | ~ r3_waybel_9(X0,X1,X2)
    | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
    | r1_orders_2(X0,X3,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v3_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_32,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(sK7,X0),sK7,sK7)
    | ~ m1_subset_1(X0,u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_783,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
    | r1_orders_2(X0,X3,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(sK7))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v3_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X1)
    | k4_waybel_1(X0,sK2(X0)) != k4_waybel_1(sK7,X4)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_32])).

cnf(c_784,plain,
    ( ~ r3_waybel_9(sK7,X0,X1)
    | ~ r1_lattice3(sK7,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK7),u1_waybel_0(sK7,X0)),X2)
    | r1_orders_2(sK7,X2,X1)
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X3,u1_struct_0(sK7))
    | ~ v2_pre_topc(sK7)
    | ~ v8_pre_topc(sK7)
    | ~ v3_orders_2(sK7)
    | ~ v2_lattice3(sK7)
    | ~ v1_compts_1(sK7)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(sK7)
    | ~ v7_waybel_0(X0)
    | ~ l1_waybel_9(sK7)
    | ~ v5_orders_2(sK7)
    | ~ v1_lattice3(sK7)
    | v2_struct_0(X0)
    | k4_waybel_1(sK7,sK2(sK7)) != k4_waybel_1(sK7,X3) ),
    inference(unflattening,[status(thm)],[c_783])).

cnf(c_39,negated_conjecture,
    ( v3_orders_2(sK7) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_38,negated_conjecture,
    ( v4_orders_2(sK7) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_35,negated_conjecture,
    ( v2_lattice3(sK7) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_788,plain,
    ( ~ v7_waybel_0(X0)
    | ~ m1_subset_1(X3,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ l1_waybel_0(X0,sK7)
    | r1_orders_2(sK7,X2,X1)
    | ~ r1_lattice3(sK7,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK7),u1_waybel_0(sK7,X0)),X2)
    | ~ r3_waybel_9(sK7,X0,X1)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | k4_waybel_1(sK7,sK2(sK7)) != k4_waybel_1(sK7,X3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_784,c_41,c_40,c_39,c_38,c_37,c_36,c_35,c_34,c_33])).

cnf(c_789,plain,
    ( ~ r3_waybel_9(sK7,X0,X1)
    | ~ r1_lattice3(sK7,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK7),u1_waybel_0(sK7,X0)),X2)
    | r1_orders_2(sK7,X2,X1)
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X3,u1_struct_0(sK7))
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | k4_waybel_1(sK7,sK2(sK7)) != k4_waybel_1(sK7,X3) ),
    inference(renaming,[status(thm)],[c_788])).

cnf(c_2535,plain,
    ( ~ r3_waybel_9(sK7,X0,X1)
    | ~ r1_lattice3(sK7,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK7),u1_waybel_0(sK7,X0)),X2)
    | r1_orders_2(sK7,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X3,u1_struct_0(sK7))
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | k4_waybel_1(sK7,sK2(sK7)) != k4_waybel_1(sK7,X3)
    | sK8 != X0
    | sK7 != sK7 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_789])).

cnf(c_2536,plain,
    ( ~ r3_waybel_9(sK7,sK8,X0)
    | ~ r1_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X1)
    | r1_orders_2(sK7,X1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ v4_orders_2(sK8)
    | ~ v7_waybel_0(sK8)
    | v2_struct_0(sK8)
    | k4_waybel_1(sK7,sK2(sK7)) != k4_waybel_1(sK7,X2) ),
    inference(unflattening,[status(thm)],[c_2535])).

cnf(c_2540,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | r1_orders_2(sK7,X1,X0)
    | ~ r1_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X1)
    | ~ r3_waybel_9(sK7,sK8,X0)
    | k4_waybel_1(sK7,sK2(sK7)) != k4_waybel_1(sK7,X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2536,c_31,c_30,c_29])).

cnf(c_2541,plain,
    ( ~ r3_waybel_9(sK7,sK8,X0)
    | ~ r1_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X1)
    | r1_orders_2(sK7,X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | k4_waybel_1(sK7,sK2(sK7)) != k4_waybel_1(sK7,X2) ),
    inference(renaming,[status(thm)],[c_2540])).

cnf(c_4364,plain,
    ( ~ r3_waybel_9(sK7,sK8,X0_68)
    | ~ r1_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X1_68)
    | r1_orders_2(sK7,X1_68,X0_68)
    | ~ m1_subset_1(X1_68,u1_struct_0(sK7))
    | ~ m1_subset_1(X0_68,u1_struct_0(sK7))
    | ~ m1_subset_1(X2_68,u1_struct_0(sK7))
    | k4_waybel_1(sK7,sK2(sK7)) != k4_waybel_1(sK7,X2_68) ),
    inference(subtyping,[status(esa)],[c_2541])).

cnf(c_4387,plain,
    ( ~ r3_waybel_9(sK7,sK8,X0_68)
    | ~ r1_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X1_68)
    | r1_orders_2(sK7,X1_68,X0_68)
    | ~ m1_subset_1(X1_68,u1_struct_0(sK7))
    | ~ m1_subset_1(X0_68,u1_struct_0(sK7))
    | ~ sP5_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP5_iProver_split])],[c_4364])).

cnf(c_4897,plain,
    ( r3_waybel_9(sK7,sK8,X0_68) != iProver_top
    | r1_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X1_68) != iProver_top
    | r1_orders_2(sK7,X1_68,X0_68) = iProver_top
    | m1_subset_1(X0_68,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_68,u1_struct_0(sK7)) != iProver_top
    | sP5_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4387])).

cnf(c_16,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
    | r1_orders_2(X0,X3,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK2(X0),u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v3_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1017,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
    | r1_orders_2(X0,X3,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | m1_subset_1(sK2(X0),u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v3_orders_2(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X1)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_35])).

cnf(c_1018,plain,
    ( ~ r3_waybel_9(sK7,X0,X1)
    | ~ r1_lattice3(sK7,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK7),u1_waybel_0(sK7,X0)),X2)
    | r1_orders_2(sK7,X2,X1)
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | m1_subset_1(sK2(sK7),u1_struct_0(sK7))
    | ~ v2_pre_topc(sK7)
    | ~ v8_pre_topc(sK7)
    | ~ v3_orders_2(sK7)
    | ~ v1_compts_1(sK7)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(sK7)
    | ~ v7_waybel_0(X0)
    | ~ l1_waybel_9(sK7)
    | ~ v5_orders_2(sK7)
    | ~ v1_lattice3(sK7)
    | v2_struct_0(X0) ),
    inference(unflattening,[status(thm)],[c_1017])).

cnf(c_1022,plain,
    ( ~ v7_waybel_0(X0)
    | ~ r3_waybel_9(sK7,X0,X1)
    | ~ r1_lattice3(sK7,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK7),u1_waybel_0(sK7,X0)),X2)
    | r1_orders_2(sK7,X2,X1)
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | m1_subset_1(sK2(sK7),u1_struct_0(sK7))
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1018,c_41,c_40,c_39,c_38,c_37,c_36,c_34,c_33])).

cnf(c_1023,plain,
    ( ~ r3_waybel_9(sK7,X0,X1)
    | ~ r1_lattice3(sK7,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK7),u1_waybel_0(sK7,X0)),X2)
    | r1_orders_2(sK7,X2,X1)
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | m1_subset_1(sK2(sK7),u1_struct_0(sK7))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_1022])).

cnf(c_2505,plain,
    ( ~ r3_waybel_9(sK7,X0,X1)
    | ~ r1_lattice3(sK7,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK7),u1_waybel_0(sK7,X0)),X2)
    | r1_orders_2(sK7,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | m1_subset_1(sK2(sK7),u1_struct_0(sK7))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | sK8 != X0
    | sK7 != sK7 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_1023])).

cnf(c_2506,plain,
    ( ~ r3_waybel_9(sK7,sK8,X0)
    | ~ r1_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X1)
    | r1_orders_2(sK7,X1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | m1_subset_1(sK2(sK7),u1_struct_0(sK7))
    | ~ v4_orders_2(sK8)
    | ~ v7_waybel_0(sK8)
    | v2_struct_0(sK8) ),
    inference(unflattening,[status(thm)],[c_2505])).

cnf(c_2510,plain,
    ( m1_subset_1(sK2(sK7),u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | r1_orders_2(sK7,X1,X0)
    | ~ r1_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X1)
    | ~ r3_waybel_9(sK7,sK8,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2506,c_31,c_30,c_29])).

cnf(c_2511,plain,
    ( ~ r3_waybel_9(sK7,sK8,X0)
    | ~ r1_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X1)
    | r1_orders_2(sK7,X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | m1_subset_1(sK2(sK7),u1_struct_0(sK7)) ),
    inference(renaming,[status(thm)],[c_2510])).

cnf(c_4365,plain,
    ( ~ r3_waybel_9(sK7,sK8,X0_68)
    | ~ r1_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X1_68)
    | r1_orders_2(sK7,X1_68,X0_68)
    | ~ m1_subset_1(X1_68,u1_struct_0(sK7))
    | ~ m1_subset_1(X0_68,u1_struct_0(sK7))
    | m1_subset_1(sK2(sK7),u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_2511])).

cnf(c_4453,plain,
    ( r3_waybel_9(sK7,sK8,X0_68) != iProver_top
    | r1_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X1_68) != iProver_top
    | r1_orders_2(sK7,X1_68,X0_68) = iProver_top
    | m1_subset_1(X0_68,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_68,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK2(sK7),u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4365])).

cnf(c_4388,plain,
    ( sP5_iProver_split
    | sP4_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_4364])).

cnf(c_4456,plain,
    ( sP5_iProver_split = iProver_top
    | sP4_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4388])).

cnf(c_4457,plain,
    ( r3_waybel_9(sK7,sK8,X0_68) != iProver_top
    | r1_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X1_68) != iProver_top
    | r1_orders_2(sK7,X1_68,X0_68) = iProver_top
    | m1_subset_1(X0_68,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_68,u1_struct_0(sK7)) != iProver_top
    | sP5_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4387])).

cnf(c_4386,plain,
    ( ~ m1_subset_1(X0_68,u1_struct_0(sK7))
    | k4_waybel_1(sK7,sK2(sK7)) != k4_waybel_1(sK7,X0_68)
    | ~ sP4_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP4_iProver_split])],[c_4364])).

cnf(c_4898,plain,
    ( k4_waybel_1(sK7,sK2(sK7)) != k4_waybel_1(sK7,X0_68)
    | m1_subset_1(X0_68,u1_struct_0(sK7)) != iProver_top
    | sP4_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4386])).

cnf(c_5218,plain,
    ( m1_subset_1(sK2(sK7),u1_struct_0(sK7)) != iProver_top
    | sP4_iProver_split != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4898])).

cnf(c_5616,plain,
    ( m1_subset_1(X1_68,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X0_68,u1_struct_0(sK7)) != iProver_top
    | r1_orders_2(sK7,X1_68,X0_68) = iProver_top
    | r1_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X1_68) != iProver_top
    | r3_waybel_9(sK7,sK8,X0_68) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4897,c_4453,c_4456,c_4457,c_5218])).

cnf(c_5617,plain,
    ( r3_waybel_9(sK7,sK8,X0_68) != iProver_top
    | r1_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X1_68) != iProver_top
    | r1_orders_2(sK7,X1_68,X0_68) = iProver_top
    | m1_subset_1(X0_68,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_68,u1_struct_0(sK7)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5616])).

cnf(c_5628,plain,
    ( r3_waybel_9(sK7,sK8,X0_68) != iProver_top
    | r1_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X1_68) != iProver_top
    | r1_orders_2(sK7,sK0(sK7,X1_68,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))),X0_68) = iProver_top
    | m1_subset_1(X1_68,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X0_68,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK0(sK7,X1_68,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))),u1_struct_0(sK7)) != iProver_top
    | r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4886,c_5617])).

cnf(c_3,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X2,X1),u1_struct_0(X0))
    | r2_yellow_0(X0,X1)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_598,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X2,X1),u1_struct_0(X0))
    | r2_yellow_0(X0,X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0) ),
    inference(resolution,[status(thm)],[c_11,c_3])).

cnf(c_1131,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X2,X1),u1_struct_0(X0))
    | r2_yellow_0(X0,X1)
    | ~ l1_waybel_9(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_598,c_37])).

cnf(c_1132,plain,
    ( ~ r1_lattice3(sK7,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | m1_subset_1(sK0(sK7,X1,X0),u1_struct_0(sK7))
    | r2_yellow_0(sK7,X0)
    | ~ l1_waybel_9(sK7) ),
    inference(unflattening,[status(thm)],[c_1131])).

cnf(c_1136,plain,
    ( r2_yellow_0(sK7,X0)
    | m1_subset_1(sK0(sK7,X1,X0),u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ r1_lattice3(sK7,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1132,c_33])).

cnf(c_1137,plain,
    ( ~ r1_lattice3(sK7,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | m1_subset_1(sK0(sK7,X1,X0),u1_struct_0(sK7))
    | r2_yellow_0(sK7,X0) ),
    inference(renaming,[status(thm)],[c_1136])).

cnf(c_4373,plain,
    ( ~ r1_lattice3(sK7,X0_70,X0_68)
    | ~ m1_subset_1(X0_68,u1_struct_0(sK7))
    | m1_subset_1(sK0(sK7,X0_68,X0_70),u1_struct_0(sK7))
    | r2_yellow_0(sK7,X0_70) ),
    inference(subtyping,[status(esa)],[c_1137])).

cnf(c_4887,plain,
    ( r1_lattice3(sK7,X0_70,X0_68) != iProver_top
    | m1_subset_1(X0_68,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK0(sK7,X0_68,X0_70),u1_struct_0(sK7)) = iProver_top
    | r2_yellow_0(sK7,X0_70) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4373])).

cnf(c_6615,plain,
    ( r3_waybel_9(sK7,sK8,X0_68) != iProver_top
    | r1_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X1_68) != iProver_top
    | r1_orders_2(sK7,sK0(sK7,X1_68,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))),X0_68) = iProver_top
    | m1_subset_1(X0_68,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_68,u1_struct_0(sK7)) != iProver_top
    | r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5628,c_4887])).

cnf(c_1,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK0(X0,X2,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_yellow_0(X0,X1)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_644,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK0(X0,X2,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_yellow_0(X0,X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0) ),
    inference(resolution,[status(thm)],[c_11,c_1])).

cnf(c_1083,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK0(X0,X2,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_yellow_0(X0,X1)
    | ~ l1_waybel_9(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_644,c_37])).

cnf(c_1084,plain,
    ( ~ r1_lattice3(sK7,X0,X1)
    | ~ r1_orders_2(sK7,sK0(sK7,X1,X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | r2_yellow_0(sK7,X0)
    | ~ l1_waybel_9(sK7) ),
    inference(unflattening,[status(thm)],[c_1083])).

cnf(c_1088,plain,
    ( r2_yellow_0(sK7,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ r1_orders_2(sK7,sK0(sK7,X1,X0),X1)
    | ~ r1_lattice3(sK7,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1084,c_33])).

cnf(c_1089,plain,
    ( ~ r1_lattice3(sK7,X0,X1)
    | ~ r1_orders_2(sK7,sK0(sK7,X1,X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | r2_yellow_0(sK7,X0) ),
    inference(renaming,[status(thm)],[c_1088])).

cnf(c_4375,plain,
    ( ~ r1_lattice3(sK7,X0_70,X0_68)
    | ~ r1_orders_2(sK7,sK0(sK7,X0_68,X0_70),X0_68)
    | ~ m1_subset_1(X0_68,u1_struct_0(sK7))
    | r2_yellow_0(sK7,X0_70) ),
    inference(subtyping,[status(esa)],[c_1089])).

cnf(c_4885,plain,
    ( r1_lattice3(sK7,X0_70,X0_68) != iProver_top
    | r1_orders_2(sK7,sK0(sK7,X0_68,X0_70),X0_68) != iProver_top
    | m1_subset_1(X0_68,u1_struct_0(sK7)) != iProver_top
    | r2_yellow_0(sK7,X0_70) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4375])).

cnf(c_6620,plain,
    ( r3_waybel_9(sK7,sK8,X0_68) != iProver_top
    | r1_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X0_68) != iProver_top
    | m1_subset_1(X0_68,u1_struct_0(sK7)) != iProver_top
    | r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) = iProver_top ),
    inference(superposition,[status(thm)],[c_6615,c_4885])).

cnf(c_27,negated_conjecture,
    ( v11_waybel_0(sK8,sK7) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_13,plain,
    ( ~ v5_pre_topc(k4_waybel_1(X0,sK1(X0)),X0,X0)
    | ~ r3_waybel_9(X0,X1,X2)
    | r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
    | ~ v11_waybel_0(X1,X0)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v3_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_741,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
    | ~ v11_waybel_0(X1,X0)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(sK7))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v3_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X1)
    | k4_waybel_1(X0,sK1(X0)) != k4_waybel_1(sK7,X3)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_32])).

cnf(c_742,plain,
    ( ~ r3_waybel_9(sK7,X0,X1)
    | r1_lattice3(sK7,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK7),u1_waybel_0(sK7,X0)),X1)
    | ~ v11_waybel_0(X0,sK7)
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ v2_pre_topc(sK7)
    | ~ v8_pre_topc(sK7)
    | ~ v3_orders_2(sK7)
    | ~ v2_lattice3(sK7)
    | ~ v1_compts_1(sK7)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(sK7)
    | ~ v7_waybel_0(X0)
    | ~ l1_waybel_9(sK7)
    | ~ v5_orders_2(sK7)
    | ~ v1_lattice3(sK7)
    | v2_struct_0(X0)
    | k4_waybel_1(sK7,sK1(sK7)) != k4_waybel_1(sK7,X2) ),
    inference(unflattening,[status(thm)],[c_741])).

cnf(c_746,plain,
    ( ~ v7_waybel_0(X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ l1_waybel_0(X0,sK7)
    | ~ v11_waybel_0(X0,sK7)
    | r1_lattice3(sK7,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK7),u1_waybel_0(sK7,X0)),X1)
    | ~ r3_waybel_9(sK7,X0,X1)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | k4_waybel_1(sK7,sK1(sK7)) != k4_waybel_1(sK7,X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_742,c_41,c_40,c_39,c_38,c_37,c_36,c_35,c_34,c_33])).

cnf(c_747,plain,
    ( ~ r3_waybel_9(sK7,X0,X1)
    | r1_lattice3(sK7,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK7),u1_waybel_0(sK7,X0)),X1)
    | ~ v11_waybel_0(X0,sK7)
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | k4_waybel_1(sK7,sK1(sK7)) != k4_waybel_1(sK7,X2) ),
    inference(renaming,[status(thm)],[c_746])).

cnf(c_968,plain,
    ( ~ r3_waybel_9(sK7,X0,X1)
    | r1_lattice3(sK7,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK7),u1_waybel_0(sK7,X0)),X1)
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | k4_waybel_1(sK7,sK1(sK7)) != k4_waybel_1(sK7,X2)
    | sK8 != X0
    | sK7 != sK7 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_747])).

cnf(c_969,plain,
    ( ~ r3_waybel_9(sK7,sK8,X0)
    | r1_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X0)
    | ~ l1_waybel_0(sK8,sK7)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ v4_orders_2(sK8)
    | ~ v7_waybel_0(sK8)
    | v2_struct_0(sK8)
    | k4_waybel_1(sK7,sK1(sK7)) != k4_waybel_1(sK7,X1) ),
    inference(unflattening,[status(thm)],[c_968])).

cnf(c_973,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ r3_waybel_9(sK7,sK8,X0)
    | r1_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X0)
    | k4_waybel_1(sK7,sK1(sK7)) != k4_waybel_1(sK7,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_969,c_31,c_30,c_29,c_28])).

cnf(c_974,plain,
    ( ~ r3_waybel_9(sK7,sK8,X0)
    | r1_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | k4_waybel_1(sK7,sK1(sK7)) != k4_waybel_1(sK7,X1) ),
    inference(renaming,[status(thm)],[c_973])).

cnf(c_4376,plain,
    ( ~ r3_waybel_9(sK7,sK8,X0_68)
    | r1_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X0_68)
    | ~ m1_subset_1(X1_68,u1_struct_0(sK7))
    | ~ m1_subset_1(X0_68,u1_struct_0(sK7))
    | k4_waybel_1(sK7,sK1(sK7)) != k4_waybel_1(sK7,X1_68) ),
    inference(subtyping,[status(esa)],[c_974])).

cnf(c_4384,plain,
    ( ~ r3_waybel_9(sK7,sK8,X0_68)
    | r1_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X0_68)
    | ~ m1_subset_1(X0_68,u1_struct_0(sK7))
    | ~ sP3_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP3_iProver_split])],[c_4376])).

cnf(c_4883,plain,
    ( r3_waybel_9(sK7,sK8,X0_68) != iProver_top
    | r1_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X0_68) = iProver_top
    | m1_subset_1(X0_68,u1_struct_0(sK7)) != iProver_top
    | sP3_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4384])).

cnf(c_14,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
    | ~ v11_waybel_0(X1,X0)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK1(X0),u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v3_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_917,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK1(X0),u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v3_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X1)
    | sK8 != X1
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_27])).

cnf(c_918,plain,
    ( ~ r3_waybel_9(sK7,sK8,X0)
    | r1_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X0)
    | ~ l1_waybel_0(sK8,sK7)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | m1_subset_1(sK1(sK7),u1_struct_0(sK7))
    | ~ v2_pre_topc(sK7)
    | ~ v8_pre_topc(sK7)
    | ~ v3_orders_2(sK7)
    | ~ v2_lattice3(sK7)
    | ~ v1_compts_1(sK7)
    | ~ v4_orders_2(sK8)
    | ~ v4_orders_2(sK7)
    | ~ v7_waybel_0(sK8)
    | ~ l1_waybel_9(sK7)
    | ~ v5_orders_2(sK7)
    | ~ v1_lattice3(sK7)
    | v2_struct_0(sK8) ),
    inference(unflattening,[status(thm)],[c_917])).

cnf(c_922,plain,
    ( r1_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X0)
    | ~ r3_waybel_9(sK7,sK8,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | m1_subset_1(sK1(sK7),u1_struct_0(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_918,c_41,c_40,c_39,c_38,c_37,c_36,c_35,c_34,c_33,c_31,c_30,c_29,c_28])).

cnf(c_923,plain,
    ( ~ r3_waybel_9(sK7,sK8,X0)
    | r1_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | m1_subset_1(sK1(sK7),u1_struct_0(sK7)) ),
    inference(renaming,[status(thm)],[c_922])).

cnf(c_4378,plain,
    ( ~ r3_waybel_9(sK7,sK8,X0_68)
    | r1_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X0_68)
    | ~ m1_subset_1(X0_68,u1_struct_0(sK7))
    | m1_subset_1(sK1(sK7),u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_923])).

cnf(c_4410,plain,
    ( r3_waybel_9(sK7,sK8,X0_68) != iProver_top
    | r1_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X0_68) = iProver_top
    | m1_subset_1(X0_68,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK1(sK7),u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4378])).

cnf(c_4385,plain,
    ( sP3_iProver_split
    | sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_4376])).

cnf(c_4420,plain,
    ( sP3_iProver_split = iProver_top
    | sP2_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4385])).

cnf(c_4421,plain,
    ( r3_waybel_9(sK7,sK8,X0_68) != iProver_top
    | r1_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X0_68) = iProver_top
    | m1_subset_1(X0_68,u1_struct_0(sK7)) != iProver_top
    | sP3_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4384])).

cnf(c_4383,plain,
    ( ~ m1_subset_1(X0_68,u1_struct_0(sK7))
    | k4_waybel_1(sK7,sK1(sK7)) != k4_waybel_1(sK7,X0_68)
    | ~ sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP2_iProver_split])],[c_4376])).

cnf(c_4884,plain,
    ( k4_waybel_1(sK7,sK1(sK7)) != k4_waybel_1(sK7,X0_68)
    | m1_subset_1(X0_68,u1_struct_0(sK7)) != iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4383])).

cnf(c_5182,plain,
    ( m1_subset_1(sK1(sK7),u1_struct_0(sK7)) != iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4884])).

cnf(c_5533,plain,
    ( m1_subset_1(X0_68,u1_struct_0(sK7)) != iProver_top
    | r1_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X0_68) = iProver_top
    | r3_waybel_9(sK7,sK8,X0_68) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4883,c_4410,c_4420,c_4421,c_5182])).

cnf(c_5534,plain,
    ( r3_waybel_9(sK7,sK8,X0_68) != iProver_top
    | r1_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X0_68) = iProver_top
    | m1_subset_1(X0_68,u1_struct_0(sK7)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5533])).

cnf(c_6633,plain,
    ( r3_waybel_9(sK7,sK8,X0_68) != iProver_top
    | m1_subset_1(X0_68,u1_struct_0(sK7)) != iProver_top
    | r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6620,c_4410,c_4420,c_4421,c_5182])).

cnf(c_6642,plain,
    ( m1_subset_1(sK3(sK7,sK8),u1_struct_0(sK7)) != iProver_top
    | r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4894,c_6633])).

cnf(c_54,plain,
    ( v2_struct_0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_55,plain,
    ( v4_orders_2(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_56,plain,
    ( v7_waybel_0(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_18,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(sK3(X1,X0),u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ v8_pre_topc(X1)
    | ~ v1_compts_1(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2279,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(sK3(X1,X0),u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ v8_pre_topc(X1)
    | ~ v1_compts_1(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_1316])).

cnf(c_2280,plain,
    ( ~ l1_waybel_0(X0,sK7)
    | m1_subset_1(sK3(sK7,X0),u1_struct_0(sK7))
    | ~ v2_pre_topc(sK7)
    | ~ v8_pre_topc(sK7)
    | ~ v1_compts_1(sK7)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK7) ),
    inference(unflattening,[status(thm)],[c_2279])).

cnf(c_2284,plain,
    ( v2_struct_0(X0)
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ l1_waybel_0(X0,sK7)
    | m1_subset_1(sK3(sK7,X0),u1_struct_0(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2280,c_41,c_40,c_36,c_34,c_33,c_103,c_136])).

cnf(c_2285,plain,
    ( ~ l1_waybel_0(X0,sK7)
    | m1_subset_1(sK3(sK7,X0),u1_struct_0(sK7))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_2284])).

cnf(c_2368,plain,
    ( m1_subset_1(sK3(sK7,X0),u1_struct_0(sK7))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | sK8 != X0
    | sK7 != sK7 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_2285])).

cnf(c_2369,plain,
    ( m1_subset_1(sK3(sK7,sK8),u1_struct_0(sK7))
    | ~ v4_orders_2(sK8)
    | ~ v7_waybel_0(sK8)
    | v2_struct_0(sK8) ),
    inference(unflattening,[status(thm)],[c_2368])).

cnf(c_2370,plain,
    ( m1_subset_1(sK3(sK7,sK8),u1_struct_0(sK7)) = iProver_top
    | v4_orders_2(sK8) != iProver_top
    | v7_waybel_0(sK8) != iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2369])).

cnf(c_6718,plain,
    ( r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6642,c_54,c_55,c_56,c_2370])).

cnf(c_21,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | r3_waybel_9(X0,X1,sK4(X0,X1))
    | r2_hidden(X2,k10_yellow_6(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_9,plain,
    ( ~ l1_waybel_0(X0,X1)
    | r2_waybel_9(X1,X0)
    | ~ r2_yellow_0(X1,k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0)))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_26,negated_conjecture,
    ( ~ r2_hidden(k1_waybel_9(sK7,sK8),k10_yellow_6(sK7,sK8))
    | ~ r2_waybel_9(sK7,sK8) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_466,plain,
    ( ~ r2_hidden(k1_waybel_9(sK7,sK8),k10_yellow_6(sK7,sK8))
    | ~ l1_waybel_0(X0,X1)
    | ~ r2_yellow_0(X1,k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0)))
    | ~ l1_orders_2(X1)
    | sK8 != X0
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_26])).

cnf(c_467,plain,
    ( ~ r2_hidden(k1_waybel_9(sK7,sK8),k10_yellow_6(sK7,sK8))
    | ~ l1_waybel_0(sK8,sK7)
    | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ l1_orders_2(sK7) ),
    inference(unflattening,[status(thm)],[c_466])).

cnf(c_469,plain,
    ( ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ r2_hidden(k1_waybel_9(sK7,sK8),k10_yellow_6(sK7,sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_467,c_33,c_28,c_103])).

cnf(c_470,plain,
    ( ~ r2_hidden(k1_waybel_9(sK7,sK8),k10_yellow_6(sK7,sK8))
    | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) ),
    inference(renaming,[status(thm)],[c_469])).

cnf(c_1908,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | r3_waybel_9(X0,X1,sK4(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | k1_waybel_9(sK7,sK8) != X2
    | k10_yellow_6(X0,X1) != k10_yellow_6(sK7,sK8) ),
    inference(resolution_lifted,[status(thm)],[c_21,c_470])).

cnf(c_1909,plain,
    ( ~ r3_waybel_9(X0,X1,k1_waybel_9(sK7,sK8))
    | r3_waybel_9(X0,X1,sK4(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(X0))
    | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | k10_yellow_6(X0,X1) != k10_yellow_6(sK7,sK8) ),
    inference(unflattening,[status(thm)],[c_1908])).

cnf(c_2135,plain,
    ( ~ r3_waybel_9(X0,X1,k1_waybel_9(sK7,sK8))
    | r3_waybel_9(X0,X1,sK4(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(X0))
    | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | k10_yellow_6(X0,X1) != k10_yellow_6(sK7,sK8)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1909,c_1316])).

cnf(c_2136,plain,
    ( ~ r3_waybel_9(sK7,X0,k1_waybel_9(sK7,sK8))
    | r3_waybel_9(sK7,X0,sK4(sK7,X0))
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
    | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ v2_pre_topc(sK7)
    | ~ v8_pre_topc(sK7)
    | ~ v1_compts_1(sK7)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK7)
    | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8) ),
    inference(unflattening,[status(thm)],[c_2135])).

cnf(c_2140,plain,
    ( v2_struct_0(X0)
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ r3_waybel_9(sK7,X0,k1_waybel_9(sK7,sK8))
    | r3_waybel_9(sK7,X0,sK4(sK7,X0))
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
    | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2136,c_41,c_40,c_36,c_34,c_33,c_103,c_136])).

cnf(c_2141,plain,
    ( ~ r3_waybel_9(sK7,X0,k1_waybel_9(sK7,sK8))
    | r3_waybel_9(sK7,X0,sK4(sK7,X0))
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
    | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8) ),
    inference(renaming,[status(thm)],[c_2140])).

cnf(c_2436,plain,
    ( ~ r3_waybel_9(sK7,X0,k1_waybel_9(sK7,sK8))
    | r3_waybel_9(sK7,X0,sK4(sK7,X0))
    | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
    | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8)
    | sK8 != X0
    | sK7 != sK7 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_2141])).

cnf(c_2437,plain,
    ( ~ r3_waybel_9(sK7,sK8,k1_waybel_9(sK7,sK8))
    | r3_waybel_9(sK7,sK8,sK4(sK7,sK8))
    | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
    | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ v4_orders_2(sK8)
    | ~ v7_waybel_0(sK8)
    | v2_struct_0(sK8)
    | k10_yellow_6(sK7,sK8) != k10_yellow_6(sK7,sK8) ),
    inference(unflattening,[status(thm)],[c_2436])).

cnf(c_2439,plain,
    ( ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
    | r3_waybel_9(sK7,sK8,sK4(sK7,sK8))
    | ~ r3_waybel_9(sK7,sK8,k1_waybel_9(sK7,sK8))
    | k10_yellow_6(sK7,sK8) != k10_yellow_6(sK7,sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2437,c_31,c_30,c_29])).

cnf(c_2440,plain,
    ( ~ r3_waybel_9(sK7,sK8,k1_waybel_9(sK7,sK8))
    | r3_waybel_9(sK7,sK8,sK4(sK7,sK8))
    | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
    | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | k10_yellow_6(sK7,sK8) != k10_yellow_6(sK7,sK8) ),
    inference(renaming,[status(thm)],[c_2439])).

cnf(c_3460,plain,
    ( ~ r3_waybel_9(sK7,sK8,k1_waybel_9(sK7,sK8))
    | r3_waybel_9(sK7,sK8,sK4(sK7,sK8))
    | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
    | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) ),
    inference(equality_resolution_simp,[status(thm)],[c_2440])).

cnf(c_4361,plain,
    ( ~ r3_waybel_9(sK7,sK8,k1_waybel_9(sK7,sK8))
    | r3_waybel_9(sK7,sK8,sK4(sK7,sK8))
    | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
    | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) ),
    inference(subtyping,[status(esa)],[c_3460])).

cnf(c_4901,plain,
    ( r3_waybel_9(sK7,sK8,k1_waybel_9(sK7,sK8)) != iProver_top
    | r3_waybel_9(sK7,sK8,sK4(sK7,sK8)) = iProver_top
    | m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7)) != iProver_top
    | r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4361])).

cnf(c_2381,plain,
    ( r3_waybel_9(sK7,sK8,sK3(sK7,sK8)) = iProver_top
    | v4_orders_2(sK8) != iProver_top
    | v7_waybel_0(sK8) != iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2380])).

cnf(c_3461,plain,
    ( r3_waybel_9(sK7,sK8,k1_waybel_9(sK7,sK8)) != iProver_top
    | r3_waybel_9(sK7,sK8,sK4(sK7,sK8)) = iProver_top
    | m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7)) != iProver_top
    | r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3460])).

cnf(c_24,plain,
    ( ~ v5_pre_topc(k4_waybel_1(X0,sK6(X0)),X0,X0)
    | ~ r3_waybel_9(X0,X1,X2)
    | ~ v11_waybel_0(X1,X0)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v3_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X1)
    | k1_waybel_9(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_828,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | ~ v11_waybel_0(X1,X0)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(sK7))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v3_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X1)
    | k1_waybel_9(X0,X1) = X2
    | k4_waybel_1(X0,sK6(X0)) != k4_waybel_1(sK7,X3)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_32])).

cnf(c_829,plain,
    ( ~ r3_waybel_9(sK7,X0,X1)
    | ~ v11_waybel_0(X0,sK7)
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ v2_pre_topc(sK7)
    | ~ v8_pre_topc(sK7)
    | ~ v3_orders_2(sK7)
    | ~ v2_lattice3(sK7)
    | ~ v1_compts_1(sK7)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(sK7)
    | ~ v7_waybel_0(X0)
    | ~ l1_waybel_9(sK7)
    | ~ v5_orders_2(sK7)
    | ~ v1_lattice3(sK7)
    | v2_struct_0(X0)
    | k1_waybel_9(sK7,X0) = X1
    | k4_waybel_1(sK7,sK6(sK7)) != k4_waybel_1(sK7,X2) ),
    inference(unflattening,[status(thm)],[c_828])).

cnf(c_833,plain,
    ( ~ v7_waybel_0(X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ l1_waybel_0(X0,sK7)
    | ~ v11_waybel_0(X0,sK7)
    | ~ r3_waybel_9(sK7,X0,X1)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | k1_waybel_9(sK7,X0) = X1
    | k4_waybel_1(sK7,sK6(sK7)) != k4_waybel_1(sK7,X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_829,c_41,c_40,c_39,c_38,c_37,c_36,c_35,c_34,c_33])).

cnf(c_834,plain,
    ( ~ r3_waybel_9(sK7,X0,X1)
    | ~ v11_waybel_0(X0,sK7)
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | k1_waybel_9(sK7,X0) = X1
    | k4_waybel_1(sK7,sK6(sK7)) != k4_waybel_1(sK7,X2) ),
    inference(renaming,[status(thm)],[c_833])).

cnf(c_941,plain,
    ( ~ r3_waybel_9(sK7,X0,X1)
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | k1_waybel_9(sK7,X0) = X1
    | k4_waybel_1(sK7,sK6(sK7)) != k4_waybel_1(sK7,X2)
    | sK8 != X0
    | sK7 != sK7 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_834])).

cnf(c_942,plain,
    ( ~ r3_waybel_9(sK7,sK8,X0)
    | ~ l1_waybel_0(sK8,sK7)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ v4_orders_2(sK8)
    | ~ v7_waybel_0(sK8)
    | v2_struct_0(sK8)
    | k1_waybel_9(sK7,sK8) = X0
    | k4_waybel_1(sK7,sK6(sK7)) != k4_waybel_1(sK7,X1) ),
    inference(unflattening,[status(thm)],[c_941])).

cnf(c_946,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ r3_waybel_9(sK7,sK8,X0)
    | k1_waybel_9(sK7,sK8) = X0
    | k4_waybel_1(sK7,sK6(sK7)) != k4_waybel_1(sK7,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_942,c_31,c_30,c_29,c_28])).

cnf(c_947,plain,
    ( ~ r3_waybel_9(sK7,sK8,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | k1_waybel_9(sK7,sK8) = X0
    | k4_waybel_1(sK7,sK6(sK7)) != k4_waybel_1(sK7,X1) ),
    inference(renaming,[status(thm)],[c_946])).

cnf(c_4377,plain,
    ( ~ r3_waybel_9(sK7,sK8,X0_68)
    | ~ m1_subset_1(X1_68,u1_struct_0(sK7))
    | ~ m1_subset_1(X0_68,u1_struct_0(sK7))
    | k4_waybel_1(sK7,sK6(sK7)) != k4_waybel_1(sK7,X1_68)
    | k1_waybel_9(sK7,sK8) = X0_68 ),
    inference(subtyping,[status(esa)],[c_947])).

cnf(c_4381,plain,
    ( ~ r3_waybel_9(sK7,sK8,X0_68)
    | ~ m1_subset_1(X0_68,u1_struct_0(sK7))
    | k1_waybel_9(sK7,sK8) = X0_68
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_4377])).

cnf(c_4880,plain,
    ( k1_waybel_9(sK7,sK8) = X0_68
    | r3_waybel_9(sK7,sK8,X0_68) != iProver_top
    | m1_subset_1(X0_68,u1_struct_0(sK7)) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4381])).

cnf(c_25,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | ~ v11_waybel_0(X1,X0)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK6(X0),u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v3_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X1)
    | k1_waybel_9(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_893,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK6(X0),u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v3_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X1)
    | k1_waybel_9(X0,X1) = X2
    | sK8 != X1
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_27])).

cnf(c_894,plain,
    ( ~ r3_waybel_9(sK7,sK8,X0)
    | ~ l1_waybel_0(sK8,sK7)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | m1_subset_1(sK6(sK7),u1_struct_0(sK7))
    | ~ v2_pre_topc(sK7)
    | ~ v8_pre_topc(sK7)
    | ~ v3_orders_2(sK7)
    | ~ v2_lattice3(sK7)
    | ~ v1_compts_1(sK7)
    | ~ v4_orders_2(sK8)
    | ~ v4_orders_2(sK7)
    | ~ v7_waybel_0(sK8)
    | ~ l1_waybel_9(sK7)
    | ~ v5_orders_2(sK7)
    | ~ v1_lattice3(sK7)
    | v2_struct_0(sK8)
    | k1_waybel_9(sK7,sK8) = X0 ),
    inference(unflattening,[status(thm)],[c_893])).

cnf(c_898,plain,
    ( ~ r3_waybel_9(sK7,sK8,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | m1_subset_1(sK6(sK7),u1_struct_0(sK7))
    | k1_waybel_9(sK7,sK8) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_894,c_41,c_40,c_39,c_38,c_37,c_36,c_35,c_34,c_33,c_31,c_30,c_29,c_28])).

cnf(c_4379,plain,
    ( ~ r3_waybel_9(sK7,sK8,X0_68)
    | ~ m1_subset_1(X0_68,u1_struct_0(sK7))
    | m1_subset_1(sK6(sK7),u1_struct_0(sK7))
    | k1_waybel_9(sK7,sK8) = X0_68 ),
    inference(subtyping,[status(esa)],[c_898])).

cnf(c_4407,plain,
    ( k1_waybel_9(sK7,sK8) = X0_68
    | r3_waybel_9(sK7,sK8,X0_68) != iProver_top
    | m1_subset_1(X0_68,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK6(sK7),u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4379])).

cnf(c_4382,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_4377])).

cnf(c_4413,plain,
    ( sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4382])).

cnf(c_4414,plain,
    ( k1_waybel_9(sK7,sK8) = X0_68
    | r3_waybel_9(sK7,sK8,X0_68) != iProver_top
    | m1_subset_1(X0_68,u1_struct_0(sK7)) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4381])).

cnf(c_4380,plain,
    ( ~ m1_subset_1(X0_68,u1_struct_0(sK7))
    | k4_waybel_1(sK7,sK6(sK7)) != k4_waybel_1(sK7,X0_68)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_4377])).

cnf(c_4881,plain,
    ( k4_waybel_1(sK7,sK6(sK7)) != k4_waybel_1(sK7,X0_68)
    | m1_subset_1(X0_68,u1_struct_0(sK7)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4380])).

cnf(c_5176,plain,
    ( m1_subset_1(sK6(sK7),u1_struct_0(sK7)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4881])).

cnf(c_5250,plain,
    ( m1_subset_1(X0_68,u1_struct_0(sK7)) != iProver_top
    | r3_waybel_9(sK7,sK8,X0_68) != iProver_top
    | k1_waybel_9(sK7,sK8) = X0_68 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4880,c_4407,c_4413,c_4414,c_5176])).

cnf(c_5251,plain,
    ( k1_waybel_9(sK7,sK8) = X0_68
    | r3_waybel_9(sK7,sK8,X0_68) != iProver_top
    | m1_subset_1(X0_68,u1_struct_0(sK7)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5250])).

cnf(c_5259,plain,
    ( k1_waybel_9(sK7,sK8) = sK3(sK7,sK8)
    | m1_subset_1(sK3(sK7,sK8),u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4894,c_5251])).

cnf(c_4396,plain,
    ( ~ m1_subset_1(X0_68,X0_69)
    | m1_subset_1(X1_68,X0_69)
    | X1_68 != X0_68 ),
    theory(equality)).

cnf(c_5199,plain,
    ( m1_subset_1(X0_68,u1_struct_0(sK7))
    | ~ m1_subset_1(sK3(sK7,sK8),u1_struct_0(sK7))
    | X0_68 != sK3(sK7,sK8) ),
    inference(instantiation,[status(thm)],[c_4396])).

cnf(c_5270,plain,
    ( m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
    | ~ m1_subset_1(sK3(sK7,sK8),u1_struct_0(sK7))
    | k1_waybel_9(sK7,sK8) != sK3(sK7,sK8) ),
    inference(instantiation,[status(thm)],[c_5199])).

cnf(c_5271,plain,
    ( k1_waybel_9(sK7,sK8) != sK3(sK7,sK8)
    | m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7)) = iProver_top
    | m1_subset_1(sK3(sK7,sK8),u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5270])).

cnf(c_4397,plain,
    ( ~ r3_waybel_9(X0_67,X1_67,X0_68)
    | r3_waybel_9(X0_67,X1_67,X1_68)
    | X1_68 != X0_68 ),
    theory(equality)).

cnf(c_5239,plain,
    ( r3_waybel_9(sK7,sK8,X0_68)
    | ~ r3_waybel_9(sK7,sK8,sK3(sK7,sK8))
    | X0_68 != sK3(sK7,sK8) ),
    inference(instantiation,[status(thm)],[c_4397])).

cnf(c_5275,plain,
    ( r3_waybel_9(sK7,sK8,k1_waybel_9(sK7,sK8))
    | ~ r3_waybel_9(sK7,sK8,sK3(sK7,sK8))
    | k1_waybel_9(sK7,sK8) != sK3(sK7,sK8) ),
    inference(instantiation,[status(thm)],[c_5239])).

cnf(c_5276,plain,
    ( k1_waybel_9(sK7,sK8) != sK3(sK7,sK8)
    | r3_waybel_9(sK7,sK8,k1_waybel_9(sK7,sK8)) = iProver_top
    | r3_waybel_9(sK7,sK8,sK3(sK7,sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5275])).

cnf(c_6049,plain,
    ( r3_waybel_9(sK7,sK8,sK4(sK7,sK8)) = iProver_top
    | r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4901,c_54,c_55,c_56,c_2370,c_2381,c_3461,c_5259,c_5271,c_5276])).

cnf(c_6725,plain,
    ( r3_waybel_9(sK7,sK8,sK4(sK7,sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6718,c_6049])).

cnf(c_5300,plain,
    ( k1_waybel_9(sK7,sK8) = sK3(sK7,sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5259,c_54,c_55,c_56,c_2370])).

cnf(c_5303,plain,
    ( sK3(sK7,sK8) = X0_68
    | r3_waybel_9(sK7,sK8,X0_68) != iProver_top
    | m1_subset_1(X0_68,u1_struct_0(sK7)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5300,c_5251])).

cnf(c_6776,plain,
    ( sK4(sK7,sK8) = sK3(sK7,sK8)
    | m1_subset_1(sK4(sK7,sK8),u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6725,c_5303])).

cnf(c_23,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | r2_hidden(X2,k10_yellow_6(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1812,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
    | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | k1_waybel_9(sK7,sK8) != X2
    | k10_yellow_6(X0,X1) != k10_yellow_6(sK7,sK8) ),
    inference(resolution_lifted,[status(thm)],[c_23,c_470])).

cnf(c_1813,plain,
    ( ~ r3_waybel_9(X0,X1,k1_waybel_9(sK7,sK8))
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(X0))
    | m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
    | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | k10_yellow_6(X0,X1) != k10_yellow_6(sK7,sK8) ),
    inference(unflattening,[status(thm)],[c_1812])).

cnf(c_2213,plain,
    ( ~ r3_waybel_9(X0,X1,k1_waybel_9(sK7,sK8))
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(X0))
    | m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
    | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | k10_yellow_6(X0,X1) != k10_yellow_6(sK7,sK8)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1813,c_1316])).

cnf(c_2214,plain,
    ( ~ r3_waybel_9(sK7,X0,k1_waybel_9(sK7,sK8))
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
    | m1_subset_1(sK4(sK7,X0),u1_struct_0(sK7))
    | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ v2_pre_topc(sK7)
    | ~ v8_pre_topc(sK7)
    | ~ v1_compts_1(sK7)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK7)
    | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8) ),
    inference(unflattening,[status(thm)],[c_2213])).

cnf(c_2218,plain,
    ( v2_struct_0(X0)
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ r3_waybel_9(sK7,X0,k1_waybel_9(sK7,sK8))
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
    | m1_subset_1(sK4(sK7,X0),u1_struct_0(sK7))
    | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2214,c_41,c_40,c_36,c_34,c_33,c_103,c_136])).

cnf(c_2219,plain,
    ( ~ r3_waybel_9(sK7,X0,k1_waybel_9(sK7,sK8))
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
    | m1_subset_1(sK4(sK7,X0),u1_struct_0(sK7))
    | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8) ),
    inference(renaming,[status(thm)],[c_2218])).

cnf(c_2390,plain,
    ( ~ r3_waybel_9(sK7,X0,k1_waybel_9(sK7,sK8))
    | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
    | m1_subset_1(sK4(sK7,X0),u1_struct_0(sK7))
    | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8)
    | sK8 != X0
    | sK7 != sK7 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_2219])).

cnf(c_2391,plain,
    ( ~ r3_waybel_9(sK7,sK8,k1_waybel_9(sK7,sK8))
    | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
    | m1_subset_1(sK4(sK7,sK8),u1_struct_0(sK7))
    | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ v4_orders_2(sK8)
    | ~ v7_waybel_0(sK8)
    | v2_struct_0(sK8)
    | k10_yellow_6(sK7,sK8) != k10_yellow_6(sK7,sK8) ),
    inference(unflattening,[status(thm)],[c_2390])).

cnf(c_2393,plain,
    ( ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | m1_subset_1(sK4(sK7,sK8),u1_struct_0(sK7))
    | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
    | ~ r3_waybel_9(sK7,sK8,k1_waybel_9(sK7,sK8))
    | k10_yellow_6(sK7,sK8) != k10_yellow_6(sK7,sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2391,c_31,c_30,c_29])).

cnf(c_2394,plain,
    ( ~ r3_waybel_9(sK7,sK8,k1_waybel_9(sK7,sK8))
    | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
    | m1_subset_1(sK4(sK7,sK8),u1_struct_0(sK7))
    | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | k10_yellow_6(sK7,sK8) != k10_yellow_6(sK7,sK8) ),
    inference(renaming,[status(thm)],[c_2393])).

cnf(c_3464,plain,
    ( ~ r3_waybel_9(sK7,sK8,k1_waybel_9(sK7,sK8))
    | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
    | m1_subset_1(sK4(sK7,sK8),u1_struct_0(sK7))
    | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) ),
    inference(equality_resolution_simp,[status(thm)],[c_2394])).

cnf(c_3465,plain,
    ( r3_waybel_9(sK7,sK8,k1_waybel_9(sK7,sK8)) != iProver_top
    | m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK4(sK7,sK8),u1_struct_0(sK7)) = iProver_top
    | r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3464])).

cnf(c_7091,plain,
    ( sK4(sK7,sK8) = sK3(sK7,sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6776,c_54,c_55,c_56,c_2370,c_2381,c_3465,c_5259,c_5271,c_5276,c_6642])).

cnf(c_19,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | r2_hidden(X2,k10_yellow_6(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK5(X0,X1) != sK4(X0,X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2004,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | k1_waybel_9(sK7,sK8) != X2
    | sK5(X0,X1) != sK4(X0,X1)
    | k10_yellow_6(X0,X1) != k10_yellow_6(sK7,sK8) ),
    inference(resolution_lifted,[status(thm)],[c_19,c_470])).

cnf(c_2005,plain,
    ( ~ r3_waybel_9(X0,X1,k1_waybel_9(sK7,sK8))
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(X0))
    | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK5(X0,X1) != sK4(X0,X1)
    | k10_yellow_6(X0,X1) != k10_yellow_6(sK7,sK8) ),
    inference(unflattening,[status(thm)],[c_2004])).

cnf(c_2057,plain,
    ( ~ r3_waybel_9(X0,X1,k1_waybel_9(sK7,sK8))
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(X0))
    | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK5(X0,X1) != sK4(X0,X1)
    | k10_yellow_6(X0,X1) != k10_yellow_6(sK7,sK8)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2005,c_1316])).

cnf(c_2058,plain,
    ( ~ r3_waybel_9(sK7,X0,k1_waybel_9(sK7,sK8))
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
    | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ v2_pre_topc(sK7)
    | ~ v8_pre_topc(sK7)
    | ~ v1_compts_1(sK7)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK7)
    | sK5(sK7,X0) != sK4(sK7,X0)
    | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8) ),
    inference(unflattening,[status(thm)],[c_2057])).

cnf(c_2062,plain,
    ( v2_struct_0(X0)
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ r3_waybel_9(sK7,X0,k1_waybel_9(sK7,sK8))
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
    | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | sK5(sK7,X0) != sK4(sK7,X0)
    | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2058,c_41,c_40,c_36,c_34,c_33,c_103,c_136])).

cnf(c_2063,plain,
    ( ~ r3_waybel_9(sK7,X0,k1_waybel_9(sK7,sK8))
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
    | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | sK5(sK7,X0) != sK4(sK7,X0)
    | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8) ),
    inference(renaming,[status(thm)],[c_2062])).

cnf(c_2482,plain,
    ( ~ r3_waybel_9(sK7,X0,k1_waybel_9(sK7,sK8))
    | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
    | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | sK5(sK7,X0) != sK4(sK7,X0)
    | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8)
    | sK8 != X0
    | sK7 != sK7 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_2063])).

cnf(c_2483,plain,
    ( ~ r3_waybel_9(sK7,sK8,k1_waybel_9(sK7,sK8))
    | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
    | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ v4_orders_2(sK8)
    | ~ v7_waybel_0(sK8)
    | v2_struct_0(sK8)
    | sK5(sK7,sK8) != sK4(sK7,sK8)
    | k10_yellow_6(sK7,sK8) != k10_yellow_6(sK7,sK8) ),
    inference(unflattening,[status(thm)],[c_2482])).

cnf(c_2485,plain,
    ( ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
    | ~ r3_waybel_9(sK7,sK8,k1_waybel_9(sK7,sK8))
    | sK5(sK7,sK8) != sK4(sK7,sK8)
    | k10_yellow_6(sK7,sK8) != k10_yellow_6(sK7,sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2483,c_31,c_30,c_29])).

cnf(c_2486,plain,
    ( ~ r3_waybel_9(sK7,sK8,k1_waybel_9(sK7,sK8))
    | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
    | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | sK5(sK7,sK8) != sK4(sK7,sK8)
    | k10_yellow_6(sK7,sK8) != k10_yellow_6(sK7,sK8) ),
    inference(renaming,[status(thm)],[c_2485])).

cnf(c_3456,plain,
    ( ~ r3_waybel_9(sK7,sK8,k1_waybel_9(sK7,sK8))
    | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
    | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | sK5(sK7,sK8) != sK4(sK7,sK8) ),
    inference(equality_resolution_simp,[status(thm)],[c_2486])).

cnf(c_4363,plain,
    ( ~ r3_waybel_9(sK7,sK8,k1_waybel_9(sK7,sK8))
    | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
    | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | sK5(sK7,sK8) != sK4(sK7,sK8) ),
    inference(subtyping,[status(esa)],[c_3456])).

cnf(c_4899,plain,
    ( sK5(sK7,sK8) != sK4(sK7,sK8)
    | r3_waybel_9(sK7,sK8,k1_waybel_9(sK7,sK8)) != iProver_top
    | m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7)) != iProver_top
    | r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4363])).

cnf(c_4463,plain,
    ( sK5(sK7,sK8) != sK4(sK7,sK8)
    | r3_waybel_9(sK7,sK8,k1_waybel_9(sK7,sK8)) != iProver_top
    | m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7)) != iProver_top
    | r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4363])).

cnf(c_5984,plain,
    ( sK5(sK7,sK8) != sK4(sK7,sK8)
    | r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4899,c_54,c_55,c_56,c_2370,c_2381,c_4463,c_5259,c_5271,c_5276])).

cnf(c_7096,plain,
    ( sK5(sK7,sK8) != sK3(sK7,sK8)
    | r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7091,c_5984])).

cnf(c_20,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | r3_waybel_9(X0,X1,sK5(X0,X1))
    | r2_hidden(X2,k10_yellow_6(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1956,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | r3_waybel_9(X0,X1,sK5(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | k1_waybel_9(sK7,sK8) != X2
    | k10_yellow_6(X0,X1) != k10_yellow_6(sK7,sK8) ),
    inference(resolution_lifted,[status(thm)],[c_20,c_470])).

cnf(c_1957,plain,
    ( ~ r3_waybel_9(X0,X1,k1_waybel_9(sK7,sK8))
    | r3_waybel_9(X0,X1,sK5(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(X0))
    | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | k10_yellow_6(X0,X1) != k10_yellow_6(sK7,sK8) ),
    inference(unflattening,[status(thm)],[c_1956])).

cnf(c_2096,plain,
    ( ~ r3_waybel_9(X0,X1,k1_waybel_9(sK7,sK8))
    | r3_waybel_9(X0,X1,sK5(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(X0))
    | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | k10_yellow_6(X0,X1) != k10_yellow_6(sK7,sK8)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1957,c_1316])).

cnf(c_2097,plain,
    ( ~ r3_waybel_9(sK7,X0,k1_waybel_9(sK7,sK8))
    | r3_waybel_9(sK7,X0,sK5(sK7,X0))
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
    | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ v2_pre_topc(sK7)
    | ~ v8_pre_topc(sK7)
    | ~ v1_compts_1(sK7)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK7)
    | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8) ),
    inference(unflattening,[status(thm)],[c_2096])).

cnf(c_2101,plain,
    ( v2_struct_0(X0)
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ r3_waybel_9(sK7,X0,k1_waybel_9(sK7,sK8))
    | r3_waybel_9(sK7,X0,sK5(sK7,X0))
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
    | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2097,c_41,c_40,c_36,c_34,c_33,c_103,c_136])).

cnf(c_2102,plain,
    ( ~ r3_waybel_9(sK7,X0,k1_waybel_9(sK7,sK8))
    | r3_waybel_9(sK7,X0,sK5(sK7,X0))
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
    | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8) ),
    inference(renaming,[status(thm)],[c_2101])).

cnf(c_2459,plain,
    ( ~ r3_waybel_9(sK7,X0,k1_waybel_9(sK7,sK8))
    | r3_waybel_9(sK7,X0,sK5(sK7,X0))
    | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
    | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8)
    | sK8 != X0
    | sK7 != sK7 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_2102])).

cnf(c_2460,plain,
    ( ~ r3_waybel_9(sK7,sK8,k1_waybel_9(sK7,sK8))
    | r3_waybel_9(sK7,sK8,sK5(sK7,sK8))
    | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
    | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ v4_orders_2(sK8)
    | ~ v7_waybel_0(sK8)
    | v2_struct_0(sK8)
    | k10_yellow_6(sK7,sK8) != k10_yellow_6(sK7,sK8) ),
    inference(unflattening,[status(thm)],[c_2459])).

cnf(c_2462,plain,
    ( ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
    | r3_waybel_9(sK7,sK8,sK5(sK7,sK8))
    | ~ r3_waybel_9(sK7,sK8,k1_waybel_9(sK7,sK8))
    | k10_yellow_6(sK7,sK8) != k10_yellow_6(sK7,sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2460,c_31,c_30,c_29])).

cnf(c_2463,plain,
    ( ~ r3_waybel_9(sK7,sK8,k1_waybel_9(sK7,sK8))
    | r3_waybel_9(sK7,sK8,sK5(sK7,sK8))
    | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
    | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | k10_yellow_6(sK7,sK8) != k10_yellow_6(sK7,sK8) ),
    inference(renaming,[status(thm)],[c_2462])).

cnf(c_3458,plain,
    ( ~ r3_waybel_9(sK7,sK8,k1_waybel_9(sK7,sK8))
    | r3_waybel_9(sK7,sK8,sK5(sK7,sK8))
    | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
    | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) ),
    inference(equality_resolution_simp,[status(thm)],[c_2463])).

cnf(c_4362,plain,
    ( ~ r3_waybel_9(sK7,sK8,k1_waybel_9(sK7,sK8))
    | r3_waybel_9(sK7,sK8,sK5(sK7,sK8))
    | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
    | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) ),
    inference(subtyping,[status(esa)],[c_3458])).

cnf(c_4900,plain,
    ( r3_waybel_9(sK7,sK8,k1_waybel_9(sK7,sK8)) != iProver_top
    | r3_waybel_9(sK7,sK8,sK5(sK7,sK8)) = iProver_top
    | m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7)) != iProver_top
    | r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4362])).

cnf(c_3459,plain,
    ( r3_waybel_9(sK7,sK8,k1_waybel_9(sK7,sK8)) != iProver_top
    | r3_waybel_9(sK7,sK8,sK5(sK7,sK8)) = iProver_top
    | m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7)) != iProver_top
    | r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3458])).

cnf(c_5991,plain,
    ( r3_waybel_9(sK7,sK8,sK5(sK7,sK8)) = iProver_top
    | r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4900,c_54,c_55,c_56,c_2370,c_2381,c_3459,c_5259,c_5271,c_5276])).

cnf(c_6726,plain,
    ( r3_waybel_9(sK7,sK8,sK5(sK7,sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6718,c_5991])).

cnf(c_6825,plain,
    ( sK5(sK7,sK8) = sK3(sK7,sK8)
    | m1_subset_1(sK5(sK7,sK8),u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6726,c_5303])).

cnf(c_22,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | r2_hidden(X2,k10_yellow_6(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1860,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
    | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | k1_waybel_9(sK7,sK8) != X2
    | k10_yellow_6(X0,X1) != k10_yellow_6(sK7,sK8) ),
    inference(resolution_lifted,[status(thm)],[c_22,c_470])).

cnf(c_1861,plain,
    ( ~ r3_waybel_9(X0,X1,k1_waybel_9(sK7,sK8))
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(X0))
    | m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
    | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | k10_yellow_6(X0,X1) != k10_yellow_6(sK7,sK8) ),
    inference(unflattening,[status(thm)],[c_1860])).

cnf(c_2174,plain,
    ( ~ r3_waybel_9(X0,X1,k1_waybel_9(sK7,sK8))
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(X0))
    | m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
    | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | k10_yellow_6(X0,X1) != k10_yellow_6(sK7,sK8)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1861,c_1316])).

cnf(c_2175,plain,
    ( ~ r3_waybel_9(sK7,X0,k1_waybel_9(sK7,sK8))
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
    | m1_subset_1(sK5(sK7,X0),u1_struct_0(sK7))
    | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ v2_pre_topc(sK7)
    | ~ v8_pre_topc(sK7)
    | ~ v1_compts_1(sK7)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK7)
    | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8) ),
    inference(unflattening,[status(thm)],[c_2174])).

cnf(c_2179,plain,
    ( v2_struct_0(X0)
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ r3_waybel_9(sK7,X0,k1_waybel_9(sK7,sK8))
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
    | m1_subset_1(sK5(sK7,X0),u1_struct_0(sK7))
    | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2175,c_41,c_40,c_36,c_34,c_33,c_103,c_136])).

cnf(c_2180,plain,
    ( ~ r3_waybel_9(sK7,X0,k1_waybel_9(sK7,sK8))
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
    | m1_subset_1(sK5(sK7,X0),u1_struct_0(sK7))
    | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8) ),
    inference(renaming,[status(thm)],[c_2179])).

cnf(c_2413,plain,
    ( ~ r3_waybel_9(sK7,X0,k1_waybel_9(sK7,sK8))
    | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
    | m1_subset_1(sK5(sK7,X0),u1_struct_0(sK7))
    | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8)
    | sK8 != X0
    | sK7 != sK7 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_2180])).

cnf(c_2414,plain,
    ( ~ r3_waybel_9(sK7,sK8,k1_waybel_9(sK7,sK8))
    | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
    | m1_subset_1(sK5(sK7,sK8),u1_struct_0(sK7))
    | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ v4_orders_2(sK8)
    | ~ v7_waybel_0(sK8)
    | v2_struct_0(sK8)
    | k10_yellow_6(sK7,sK8) != k10_yellow_6(sK7,sK8) ),
    inference(unflattening,[status(thm)],[c_2413])).

cnf(c_2416,plain,
    ( ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | m1_subset_1(sK5(sK7,sK8),u1_struct_0(sK7))
    | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
    | ~ r3_waybel_9(sK7,sK8,k1_waybel_9(sK7,sK8))
    | k10_yellow_6(sK7,sK8) != k10_yellow_6(sK7,sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2414,c_31,c_30,c_29])).

cnf(c_2417,plain,
    ( ~ r3_waybel_9(sK7,sK8,k1_waybel_9(sK7,sK8))
    | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
    | m1_subset_1(sK5(sK7,sK8),u1_struct_0(sK7))
    | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | k10_yellow_6(sK7,sK8) != k10_yellow_6(sK7,sK8) ),
    inference(renaming,[status(thm)],[c_2416])).

cnf(c_3462,plain,
    ( ~ r3_waybel_9(sK7,sK8,k1_waybel_9(sK7,sK8))
    | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
    | m1_subset_1(sK5(sK7,sK8),u1_struct_0(sK7))
    | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) ),
    inference(equality_resolution_simp,[status(thm)],[c_2417])).

cnf(c_3463,plain,
    ( r3_waybel_9(sK7,sK8,k1_waybel_9(sK7,sK8)) != iProver_top
    | m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK5(sK7,sK8),u1_struct_0(sK7)) = iProver_top
    | r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3462])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7096,c_6825,c_6642,c_5276,c_5271,c_5259,c_3463,c_2381,c_2370,c_56,c_55,c_54])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:44:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.82/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.82/0.98  
% 2.82/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.82/0.98  
% 2.82/0.98  ------  iProver source info
% 2.82/0.98  
% 2.82/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.82/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.82/0.98  git: non_committed_changes: false
% 2.82/0.98  git: last_make_outside_of_git: false
% 2.82/0.98  
% 2.82/0.98  ------ 
% 2.82/0.98  
% 2.82/0.98  ------ Input Options
% 2.82/0.98  
% 2.82/0.98  --out_options                           all
% 2.82/0.98  --tptp_safe_out                         true
% 2.82/0.98  --problem_path                          ""
% 2.82/0.98  --include_path                          ""
% 2.82/0.98  --clausifier                            res/vclausify_rel
% 2.82/0.98  --clausifier_options                    --mode clausify
% 2.82/0.98  --stdin                                 false
% 2.82/0.98  --stats_out                             all
% 2.82/0.98  
% 2.82/0.98  ------ General Options
% 2.82/0.98  
% 2.82/0.98  --fof                                   false
% 2.82/0.98  --time_out_real                         305.
% 2.82/0.98  --time_out_virtual                      -1.
% 2.82/0.98  --symbol_type_check                     false
% 2.82/0.98  --clausify_out                          false
% 2.82/0.98  --sig_cnt_out                           false
% 2.82/0.99  --trig_cnt_out                          false
% 2.82/0.99  --trig_cnt_out_tolerance                1.
% 2.82/0.99  --trig_cnt_out_sk_spl                   false
% 2.82/0.99  --abstr_cl_out                          false
% 2.82/0.99  
% 2.82/0.99  ------ Global Options
% 2.82/0.99  
% 2.82/0.99  --schedule                              default
% 2.82/0.99  --add_important_lit                     false
% 2.82/0.99  --prop_solver_per_cl                    1000
% 2.82/0.99  --min_unsat_core                        false
% 2.82/0.99  --soft_assumptions                      false
% 2.82/0.99  --soft_lemma_size                       3
% 2.82/0.99  --prop_impl_unit_size                   0
% 2.82/0.99  --prop_impl_unit                        []
% 2.82/0.99  --share_sel_clauses                     true
% 2.82/0.99  --reset_solvers                         false
% 2.82/0.99  --bc_imp_inh                            [conj_cone]
% 2.82/0.99  --conj_cone_tolerance                   3.
% 2.82/0.99  --extra_neg_conj                        none
% 2.82/0.99  --large_theory_mode                     true
% 2.82/0.99  --prolific_symb_bound                   200
% 2.82/0.99  --lt_threshold                          2000
% 2.82/0.99  --clause_weak_htbl                      true
% 2.82/0.99  --gc_record_bc_elim                     false
% 2.82/0.99  
% 2.82/0.99  ------ Preprocessing Options
% 2.82/0.99  
% 2.82/0.99  --preprocessing_flag                    true
% 2.82/0.99  --time_out_prep_mult                    0.1
% 2.82/0.99  --splitting_mode                        input
% 2.82/0.99  --splitting_grd                         true
% 2.82/0.99  --splitting_cvd                         false
% 2.82/0.99  --splitting_cvd_svl                     false
% 2.82/0.99  --splitting_nvd                         32
% 2.82/0.99  --sub_typing                            true
% 2.82/0.99  --prep_gs_sim                           true
% 2.82/0.99  --prep_unflatten                        true
% 2.82/0.99  --prep_res_sim                          true
% 2.82/0.99  --prep_upred                            true
% 2.82/0.99  --prep_sem_filter                       exhaustive
% 2.82/0.99  --prep_sem_filter_out                   false
% 2.82/0.99  --pred_elim                             true
% 2.82/0.99  --res_sim_input                         true
% 2.82/0.99  --eq_ax_congr_red                       true
% 2.82/0.99  --pure_diseq_elim                       true
% 2.82/0.99  --brand_transform                       false
% 2.82/0.99  --non_eq_to_eq                          false
% 2.82/0.99  --prep_def_merge                        true
% 2.82/0.99  --prep_def_merge_prop_impl              false
% 2.82/0.99  --prep_def_merge_mbd                    true
% 2.82/0.99  --prep_def_merge_tr_red                 false
% 2.82/0.99  --prep_def_merge_tr_cl                  false
% 2.82/0.99  --smt_preprocessing                     true
% 2.82/0.99  --smt_ac_axioms                         fast
% 2.82/0.99  --preprocessed_out                      false
% 2.82/0.99  --preprocessed_stats                    false
% 2.82/0.99  
% 2.82/0.99  ------ Abstraction refinement Options
% 2.82/0.99  
% 2.82/0.99  --abstr_ref                             []
% 2.82/0.99  --abstr_ref_prep                        false
% 2.82/0.99  --abstr_ref_until_sat                   false
% 2.82/0.99  --abstr_ref_sig_restrict                funpre
% 2.82/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.82/0.99  --abstr_ref_under                       []
% 2.82/0.99  
% 2.82/0.99  ------ SAT Options
% 2.82/0.99  
% 2.82/0.99  --sat_mode                              false
% 2.82/0.99  --sat_fm_restart_options                ""
% 2.82/0.99  --sat_gr_def                            false
% 2.82/0.99  --sat_epr_types                         true
% 2.82/0.99  --sat_non_cyclic_types                  false
% 2.82/0.99  --sat_finite_models                     false
% 2.82/0.99  --sat_fm_lemmas                         false
% 2.82/0.99  --sat_fm_prep                           false
% 2.82/0.99  --sat_fm_uc_incr                        true
% 2.82/0.99  --sat_out_model                         small
% 2.82/0.99  --sat_out_clauses                       false
% 2.82/0.99  
% 2.82/0.99  ------ QBF Options
% 2.82/0.99  
% 2.82/0.99  --qbf_mode                              false
% 2.82/0.99  --qbf_elim_univ                         false
% 2.82/0.99  --qbf_dom_inst                          none
% 2.82/0.99  --qbf_dom_pre_inst                      false
% 2.82/0.99  --qbf_sk_in                             false
% 2.82/0.99  --qbf_pred_elim                         true
% 2.82/0.99  --qbf_split                             512
% 2.82/0.99  
% 2.82/0.99  ------ BMC1 Options
% 2.82/0.99  
% 2.82/0.99  --bmc1_incremental                      false
% 2.82/0.99  --bmc1_axioms                           reachable_all
% 2.82/0.99  --bmc1_min_bound                        0
% 2.82/0.99  --bmc1_max_bound                        -1
% 2.82/0.99  --bmc1_max_bound_default                -1
% 2.82/0.99  --bmc1_symbol_reachability              true
% 2.82/0.99  --bmc1_property_lemmas                  false
% 2.82/0.99  --bmc1_k_induction                      false
% 2.82/0.99  --bmc1_non_equiv_states                 false
% 2.82/0.99  --bmc1_deadlock                         false
% 2.82/0.99  --bmc1_ucm                              false
% 2.82/0.99  --bmc1_add_unsat_core                   none
% 2.82/0.99  --bmc1_unsat_core_children              false
% 2.82/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.82/0.99  --bmc1_out_stat                         full
% 2.82/0.99  --bmc1_ground_init                      false
% 2.82/0.99  --bmc1_pre_inst_next_state              false
% 2.82/0.99  --bmc1_pre_inst_state                   false
% 2.82/0.99  --bmc1_pre_inst_reach_state             false
% 2.82/0.99  --bmc1_out_unsat_core                   false
% 2.82/0.99  --bmc1_aig_witness_out                  false
% 2.82/0.99  --bmc1_verbose                          false
% 2.82/0.99  --bmc1_dump_clauses_tptp                false
% 2.82/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.82/0.99  --bmc1_dump_file                        -
% 2.82/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.82/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.82/0.99  --bmc1_ucm_extend_mode                  1
% 2.82/0.99  --bmc1_ucm_init_mode                    2
% 2.82/0.99  --bmc1_ucm_cone_mode                    none
% 2.82/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.82/0.99  --bmc1_ucm_relax_model                  4
% 2.82/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.82/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.82/0.99  --bmc1_ucm_layered_model                none
% 2.82/0.99  --bmc1_ucm_max_lemma_size               10
% 2.82/0.99  
% 2.82/0.99  ------ AIG Options
% 2.82/0.99  
% 2.82/0.99  --aig_mode                              false
% 2.82/0.99  
% 2.82/0.99  ------ Instantiation Options
% 2.82/0.99  
% 2.82/0.99  --instantiation_flag                    true
% 2.82/0.99  --inst_sos_flag                         false
% 2.82/0.99  --inst_sos_phase                        true
% 2.82/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.82/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.82/0.99  --inst_lit_sel_side                     num_symb
% 2.82/0.99  --inst_solver_per_active                1400
% 2.82/0.99  --inst_solver_calls_frac                1.
% 2.82/0.99  --inst_passive_queue_type               priority_queues
% 2.82/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.82/0.99  --inst_passive_queues_freq              [25;2]
% 2.82/0.99  --inst_dismatching                      true
% 2.82/0.99  --inst_eager_unprocessed_to_passive     true
% 2.82/0.99  --inst_prop_sim_given                   true
% 2.82/0.99  --inst_prop_sim_new                     false
% 2.82/0.99  --inst_subs_new                         false
% 2.82/0.99  --inst_eq_res_simp                      false
% 2.82/0.99  --inst_subs_given                       false
% 2.82/0.99  --inst_orphan_elimination               true
% 2.82/0.99  --inst_learning_loop_flag               true
% 2.82/0.99  --inst_learning_start                   3000
% 2.82/0.99  --inst_learning_factor                  2
% 2.82/0.99  --inst_start_prop_sim_after_learn       3
% 2.82/0.99  --inst_sel_renew                        solver
% 2.82/0.99  --inst_lit_activity_flag                true
% 2.82/0.99  --inst_restr_to_given                   false
% 2.82/0.99  --inst_activity_threshold               500
% 2.82/0.99  --inst_out_proof                        true
% 2.82/0.99  
% 2.82/0.99  ------ Resolution Options
% 2.82/0.99  
% 2.82/0.99  --resolution_flag                       true
% 2.82/0.99  --res_lit_sel                           adaptive
% 2.82/0.99  --res_lit_sel_side                      none
% 2.82/0.99  --res_ordering                          kbo
% 2.82/0.99  --res_to_prop_solver                    active
% 2.82/0.99  --res_prop_simpl_new                    false
% 2.82/0.99  --res_prop_simpl_given                  true
% 2.82/0.99  --res_passive_queue_type                priority_queues
% 2.82/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.82/0.99  --res_passive_queues_freq               [15;5]
% 2.82/0.99  --res_forward_subs                      full
% 2.82/0.99  --res_backward_subs                     full
% 2.82/0.99  --res_forward_subs_resolution           true
% 2.82/0.99  --res_backward_subs_resolution          true
% 2.82/0.99  --res_orphan_elimination                true
% 2.82/0.99  --res_time_limit                        2.
% 2.82/0.99  --res_out_proof                         true
% 2.82/0.99  
% 2.82/0.99  ------ Superposition Options
% 2.82/0.99  
% 2.82/0.99  --superposition_flag                    true
% 2.82/0.99  --sup_passive_queue_type                priority_queues
% 2.82/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.82/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.82/0.99  --demod_completeness_check              fast
% 2.82/0.99  --demod_use_ground                      true
% 2.82/0.99  --sup_to_prop_solver                    passive
% 2.82/0.99  --sup_prop_simpl_new                    true
% 2.82/0.99  --sup_prop_simpl_given                  true
% 2.82/0.99  --sup_fun_splitting                     false
% 2.82/0.99  --sup_smt_interval                      50000
% 2.82/0.99  
% 2.82/0.99  ------ Superposition Simplification Setup
% 2.82/0.99  
% 2.82/0.99  --sup_indices_passive                   []
% 2.82/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.82/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.82/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.82/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.82/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.82/0.99  --sup_full_bw                           [BwDemod]
% 2.82/0.99  --sup_immed_triv                        [TrivRules]
% 2.82/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.82/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.82/0.99  --sup_immed_bw_main                     []
% 2.82/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.82/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.82/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.82/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.82/0.99  
% 2.82/0.99  ------ Combination Options
% 2.82/0.99  
% 2.82/0.99  --comb_res_mult                         3
% 2.82/0.99  --comb_sup_mult                         2
% 2.82/0.99  --comb_inst_mult                        10
% 2.82/0.99  
% 2.82/0.99  ------ Debug Options
% 2.82/0.99  
% 2.82/0.99  --dbg_backtrace                         false
% 2.82/0.99  --dbg_dump_prop_clauses                 false
% 2.82/0.99  --dbg_dump_prop_clauses_file            -
% 2.82/0.99  --dbg_out_stat                          false
% 2.82/0.99  ------ Parsing...
% 2.82/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.82/0.99  
% 2.82/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe:16:0s pe_e  sf_s  rm: 17 0s  sf_e  pe_s  pe_e 
% 2.82/0.99  
% 2.82/0.99  ------ Preprocessing... gs_s  sp: 6 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.82/0.99  
% 2.82/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.82/0.99  ------ Proving...
% 2.82/0.99  ------ Problem Properties 
% 2.82/0.99  
% 2.82/0.99  
% 2.82/0.99  clauses                                 27
% 2.82/0.99  conjectures                             0
% 2.82/0.99  EPR                                     3
% 2.82/0.99  Horn                                    17
% 2.82/0.99  unary                                   2
% 2.82/0.99  binary                                  3
% 2.82/0.99  lits                                    97
% 2.82/0.99  lits eq                                 9
% 2.82/0.99  fd_pure                                 0
% 2.82/0.99  fd_pseudo                               0
% 2.82/0.99  fd_cond                                 2
% 2.82/0.99  fd_pseudo_cond                          3
% 2.82/0.99  AC symbols                              0
% 2.82/0.99  
% 2.82/0.99  ------ Schedule dynamic 5 is on 
% 2.82/0.99  
% 2.82/0.99  ------ no conjectures: strip conj schedule 
% 2.82/0.99  
% 2.82/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" stripped conjectures Time Limit: 10.
% 2.82/0.99  
% 2.82/0.99  
% 2.82/0.99  ------ 
% 2.82/0.99  Current options:
% 2.82/0.99  ------ 
% 2.82/0.99  
% 2.82/0.99  ------ Input Options
% 2.82/0.99  
% 2.82/0.99  --out_options                           all
% 2.82/0.99  --tptp_safe_out                         true
% 2.82/0.99  --problem_path                          ""
% 2.82/0.99  --include_path                          ""
% 2.82/0.99  --clausifier                            res/vclausify_rel
% 2.82/0.99  --clausifier_options                    --mode clausify
% 2.82/0.99  --stdin                                 false
% 2.82/0.99  --stats_out                             all
% 2.82/0.99  
% 2.82/0.99  ------ General Options
% 2.82/0.99  
% 2.82/0.99  --fof                                   false
% 2.82/0.99  --time_out_real                         305.
% 2.82/0.99  --time_out_virtual                      -1.
% 2.82/0.99  --symbol_type_check                     false
% 2.82/0.99  --clausify_out                          false
% 2.82/0.99  --sig_cnt_out                           false
% 2.82/0.99  --trig_cnt_out                          false
% 2.82/0.99  --trig_cnt_out_tolerance                1.
% 2.82/0.99  --trig_cnt_out_sk_spl                   false
% 2.82/0.99  --abstr_cl_out                          false
% 2.82/0.99  
% 2.82/0.99  ------ Global Options
% 2.82/0.99  
% 2.82/0.99  --schedule                              default
% 2.82/0.99  --add_important_lit                     false
% 2.82/0.99  --prop_solver_per_cl                    1000
% 2.82/0.99  --min_unsat_core                        false
% 2.82/0.99  --soft_assumptions                      false
% 2.82/0.99  --soft_lemma_size                       3
% 2.82/0.99  --prop_impl_unit_size                   0
% 2.82/0.99  --prop_impl_unit                        []
% 2.82/0.99  --share_sel_clauses                     true
% 2.82/0.99  --reset_solvers                         false
% 2.82/0.99  --bc_imp_inh                            [conj_cone]
% 2.82/0.99  --conj_cone_tolerance                   3.
% 2.82/0.99  --extra_neg_conj                        none
% 2.82/0.99  --large_theory_mode                     true
% 2.82/0.99  --prolific_symb_bound                   200
% 2.82/0.99  --lt_threshold                          2000
% 2.82/0.99  --clause_weak_htbl                      true
% 2.82/0.99  --gc_record_bc_elim                     false
% 2.82/0.99  
% 2.82/0.99  ------ Preprocessing Options
% 2.82/0.99  
% 2.82/0.99  --preprocessing_flag                    true
% 2.82/0.99  --time_out_prep_mult                    0.1
% 2.82/0.99  --splitting_mode                        input
% 2.82/0.99  --splitting_grd                         true
% 2.82/0.99  --splitting_cvd                         false
% 2.82/0.99  --splitting_cvd_svl                     false
% 2.82/0.99  --splitting_nvd                         32
% 2.82/0.99  --sub_typing                            true
% 2.82/0.99  --prep_gs_sim                           true
% 2.82/0.99  --prep_unflatten                        true
% 2.82/0.99  --prep_res_sim                          true
% 2.82/0.99  --prep_upred                            true
% 2.82/0.99  --prep_sem_filter                       exhaustive
% 2.82/0.99  --prep_sem_filter_out                   false
% 2.82/0.99  --pred_elim                             true
% 2.82/0.99  --res_sim_input                         true
% 2.82/0.99  --eq_ax_congr_red                       true
% 2.82/0.99  --pure_diseq_elim                       true
% 2.82/0.99  --brand_transform                       false
% 2.82/0.99  --non_eq_to_eq                          false
% 2.82/0.99  --prep_def_merge                        true
% 2.82/0.99  --prep_def_merge_prop_impl              false
% 2.82/0.99  --prep_def_merge_mbd                    true
% 2.82/0.99  --prep_def_merge_tr_red                 false
% 2.82/0.99  --prep_def_merge_tr_cl                  false
% 2.82/0.99  --smt_preprocessing                     true
% 2.82/0.99  --smt_ac_axioms                         fast
% 2.82/0.99  --preprocessed_out                      false
% 2.82/0.99  --preprocessed_stats                    false
% 2.82/0.99  
% 2.82/0.99  ------ Abstraction refinement Options
% 2.82/0.99  
% 2.82/0.99  --abstr_ref                             []
% 2.82/0.99  --abstr_ref_prep                        false
% 2.82/0.99  --abstr_ref_until_sat                   false
% 2.82/0.99  --abstr_ref_sig_restrict                funpre
% 2.82/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.82/0.99  --abstr_ref_under                       []
% 2.82/0.99  
% 2.82/0.99  ------ SAT Options
% 2.82/0.99  
% 2.82/0.99  --sat_mode                              false
% 2.82/0.99  --sat_fm_restart_options                ""
% 2.82/0.99  --sat_gr_def                            false
% 2.82/0.99  --sat_epr_types                         true
% 2.82/0.99  --sat_non_cyclic_types                  false
% 2.82/0.99  --sat_finite_models                     false
% 2.82/0.99  --sat_fm_lemmas                         false
% 2.82/0.99  --sat_fm_prep                           false
% 2.82/0.99  --sat_fm_uc_incr                        true
% 2.82/0.99  --sat_out_model                         small
% 2.82/0.99  --sat_out_clauses                       false
% 2.82/0.99  
% 2.82/0.99  ------ QBF Options
% 2.82/0.99  
% 2.82/0.99  --qbf_mode                              false
% 2.82/0.99  --qbf_elim_univ                         false
% 2.82/0.99  --qbf_dom_inst                          none
% 2.82/0.99  --qbf_dom_pre_inst                      false
% 2.82/0.99  --qbf_sk_in                             false
% 2.82/0.99  --qbf_pred_elim                         true
% 2.82/0.99  --qbf_split                             512
% 2.82/0.99  
% 2.82/0.99  ------ BMC1 Options
% 2.82/0.99  
% 2.82/0.99  --bmc1_incremental                      false
% 2.82/0.99  --bmc1_axioms                           reachable_all
% 2.82/0.99  --bmc1_min_bound                        0
% 2.82/0.99  --bmc1_max_bound                        -1
% 2.82/0.99  --bmc1_max_bound_default                -1
% 2.82/0.99  --bmc1_symbol_reachability              true
% 2.82/0.99  --bmc1_property_lemmas                  false
% 2.82/0.99  --bmc1_k_induction                      false
% 2.82/0.99  --bmc1_non_equiv_states                 false
% 2.82/0.99  --bmc1_deadlock                         false
% 2.82/0.99  --bmc1_ucm                              false
% 2.82/0.99  --bmc1_add_unsat_core                   none
% 2.82/0.99  --bmc1_unsat_core_children              false
% 2.82/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.82/0.99  --bmc1_out_stat                         full
% 2.82/0.99  --bmc1_ground_init                      false
% 2.82/0.99  --bmc1_pre_inst_next_state              false
% 2.82/0.99  --bmc1_pre_inst_state                   false
% 2.82/0.99  --bmc1_pre_inst_reach_state             false
% 2.82/0.99  --bmc1_out_unsat_core                   false
% 2.82/0.99  --bmc1_aig_witness_out                  false
% 2.82/0.99  --bmc1_verbose                          false
% 2.82/0.99  --bmc1_dump_clauses_tptp                false
% 2.82/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.82/0.99  --bmc1_dump_file                        -
% 2.82/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.82/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.82/0.99  --bmc1_ucm_extend_mode                  1
% 2.82/0.99  --bmc1_ucm_init_mode                    2
% 2.82/0.99  --bmc1_ucm_cone_mode                    none
% 2.82/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.82/0.99  --bmc1_ucm_relax_model                  4
% 2.82/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.82/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.82/0.99  --bmc1_ucm_layered_model                none
% 2.82/0.99  --bmc1_ucm_max_lemma_size               10
% 2.82/0.99  
% 2.82/0.99  ------ AIG Options
% 2.82/0.99  
% 2.82/0.99  --aig_mode                              false
% 2.82/0.99  
% 2.82/0.99  ------ Instantiation Options
% 2.82/0.99  
% 2.82/0.99  --instantiation_flag                    true
% 2.82/0.99  --inst_sos_flag                         false
% 2.82/0.99  --inst_sos_phase                        true
% 2.82/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.82/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.82/0.99  --inst_lit_sel_side                     none
% 2.82/0.99  --inst_solver_per_active                1400
% 2.82/0.99  --inst_solver_calls_frac                1.
% 2.82/0.99  --inst_passive_queue_type               priority_queues
% 2.82/0.99  --inst_passive_queues                   [[-num_var];[+age;-num_symb]]
% 2.82/0.99  --inst_passive_queues_freq              [25;2]
% 2.82/0.99  --inst_dismatching                      true
% 2.82/0.99  --inst_eager_unprocessed_to_passive     true
% 2.82/0.99  --inst_prop_sim_given                   true
% 2.82/0.99  --inst_prop_sim_new                     false
% 2.82/0.99  --inst_subs_new                         false
% 2.82/0.99  --inst_eq_res_simp                      false
% 2.82/0.99  --inst_subs_given                       false
% 2.82/0.99  --inst_orphan_elimination               true
% 2.82/0.99  --inst_learning_loop_flag               true
% 2.82/0.99  --inst_learning_start                   3000
% 2.82/0.99  --inst_learning_factor                  2
% 2.82/0.99  --inst_start_prop_sim_after_learn       3
% 2.82/0.99  --inst_sel_renew                        solver
% 2.82/0.99  --inst_lit_activity_flag                true
% 2.82/0.99  --inst_restr_to_given                   false
% 2.82/0.99  --inst_activity_threshold               500
% 2.82/0.99  --inst_out_proof                        true
% 2.82/0.99  
% 2.82/0.99  ------ Resolution Options
% 2.82/0.99  
% 2.82/0.99  --resolution_flag                       false
% 2.82/0.99  --res_lit_sel                           adaptive
% 2.82/0.99  --res_lit_sel_side                      none
% 2.82/0.99  --res_ordering                          kbo
% 2.82/0.99  --res_to_prop_solver                    active
% 2.82/0.99  --res_prop_simpl_new                    false
% 2.82/0.99  --res_prop_simpl_given                  true
% 2.82/0.99  --res_passive_queue_type                priority_queues
% 2.82/0.99  --res_passive_queues                    [[-num_symb];[+age;-num_symb]]
% 2.82/0.99  --res_passive_queues_freq               [15;5]
% 2.82/0.99  --res_forward_subs                      full
% 2.82/0.99  --res_backward_subs                     full
% 2.82/0.99  --res_forward_subs_resolution           true
% 2.82/0.99  --res_backward_subs_resolution          true
% 2.82/0.99  --res_orphan_elimination                true
% 2.82/0.99  --res_time_limit                        2.
% 2.82/0.99  --res_out_proof                         true
% 2.82/0.99  
% 2.82/0.99  ------ Superposition Options
% 2.82/0.99  
% 2.82/0.99  --superposition_flag                    true
% 2.82/0.99  --sup_passive_queue_type                priority_queues
% 2.82/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.82/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.82/0.99  --demod_completeness_check              fast
% 2.82/0.99  --demod_use_ground                      true
% 2.82/0.99  --sup_to_prop_solver                    passive
% 2.82/0.99  --sup_prop_simpl_new                    true
% 2.82/0.99  --sup_prop_simpl_given                  true
% 2.82/0.99  --sup_fun_splitting                     false
% 2.82/0.99  --sup_smt_interval                      50000
% 2.82/0.99  
% 2.82/0.99  ------ Superposition Simplification Setup
% 2.82/0.99  
% 2.82/0.99  --sup_indices_passive                   []
% 2.82/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.82/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.82/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.82/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.82/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.82/0.99  --sup_full_bw                           [BwDemod]
% 2.82/0.99  --sup_immed_triv                        [TrivRules]
% 2.82/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.82/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.82/0.99  --sup_immed_bw_main                     []
% 2.82/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.82/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.82/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.82/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.82/0.99  
% 2.82/0.99  ------ Combination Options
% 2.82/0.99  
% 2.82/0.99  --comb_res_mult                         3
% 2.82/0.99  --comb_sup_mult                         2
% 2.82/0.99  --comb_inst_mult                        10
% 2.82/0.99  
% 2.82/0.99  ------ Debug Options
% 2.82/0.99  
% 2.82/0.99  --dbg_backtrace                         false
% 2.82/0.99  --dbg_dump_prop_clauses                 false
% 2.82/0.99  --dbg_dump_prop_clauses_file            -
% 2.82/0.99  --dbg_out_stat                          false
% 2.82/0.99  
% 2.82/0.99  
% 2.82/0.99  
% 2.82/0.99  
% 2.82/0.99  ------ Proving...
% 2.82/0.99  
% 2.82/0.99  
% 2.82/0.99  % SZS status Theorem for theBenchmark.p
% 2.82/0.99  
% 2.82/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.82/0.99  
% 2.82/0.99  fof(f10,conjecture,(
% 2.82/0.99    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => (! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X1),X0,X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (v11_waybel_0(X1,X0) => (r2_hidden(k1_waybel_9(X0,X1),k10_yellow_6(X0,X1)) & r2_waybel_9(X0,X1))))))),
% 2.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.82/0.99  
% 2.82/0.99  fof(f11,negated_conjecture,(
% 2.82/0.99    ~! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => (! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X1),X0,X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (v11_waybel_0(X1,X0) => (r2_hidden(k1_waybel_9(X0,X1),k10_yellow_6(X0,X1)) & r2_waybel_9(X0,X1))))))),
% 2.82/0.99    inference(negated_conjecture,[],[f10])).
% 2.82/0.99  
% 2.82/0.99  fof(f15,plain,(
% 2.82/0.99    ~! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => (! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X1),X0,X0)) => ! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => (v11_waybel_0(X2,X0) => (r2_hidden(k1_waybel_9(X0,X2),k10_yellow_6(X0,X2)) & r2_waybel_9(X0,X2))))))),
% 2.82/0.99    inference(rectify,[],[f11])).
% 2.82/0.99  
% 2.82/0.99  fof(f32,plain,(
% 2.82/0.99    ? [X0] : ((? [X2] : (((~r2_hidden(k1_waybel_9(X0,X2),k10_yellow_6(X0,X2)) | ~r2_waybel_9(X0,X2)) & v11_waybel_0(X2,X0)) & (l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2))) & ! [X1] : (v5_pre_topc(k4_waybel_1(X0,X1),X0,X0) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.82/0.99    inference(ennf_transformation,[],[f15])).
% 2.82/0.99  
% 2.82/0.99  fof(f33,plain,(
% 2.82/0.99    ? [X0] : (? [X2] : ((~r2_hidden(k1_waybel_9(X0,X2),k10_yellow_6(X0,X2)) | ~r2_waybel_9(X0,X2)) & v11_waybel_0(X2,X0) & l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & ! [X1] : (v5_pre_topc(k4_waybel_1(X0,X1),X0,X0) | ~m1_subset_1(X1,u1_struct_0(X0))) & l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0))),
% 2.82/0.99    inference(flattening,[],[f32])).
% 2.82/0.99  
% 2.82/0.99  fof(f50,plain,(
% 2.82/0.99    ? [X0] : (? [X1] : ((~r2_hidden(k1_waybel_9(X0,X1),k10_yellow_6(X0,X1)) | ~r2_waybel_9(X0,X1)) & v11_waybel_0(X1,X0) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & ! [X2] : (v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0))),
% 2.82/0.99    inference(rectify,[],[f33])).
% 2.82/0.99  
% 2.82/0.99  fof(f52,plain,(
% 2.82/0.99    ( ! [X0] : (? [X1] : ((~r2_hidden(k1_waybel_9(X0,X1),k10_yellow_6(X0,X1)) | ~r2_waybel_9(X0,X1)) & v11_waybel_0(X1,X0) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ((~r2_hidden(k1_waybel_9(X0,sK8),k10_yellow_6(X0,sK8)) | ~r2_waybel_9(X0,sK8)) & v11_waybel_0(sK8,X0) & l1_waybel_0(sK8,X0) & v7_waybel_0(sK8) & v4_orders_2(sK8) & ~v2_struct_0(sK8))) )),
% 2.82/0.99    introduced(choice_axiom,[])).
% 2.82/0.99  
% 2.82/0.99  fof(f51,plain,(
% 2.82/0.99    ? [X0] : (? [X1] : ((~r2_hidden(k1_waybel_9(X0,X1),k10_yellow_6(X0,X1)) | ~r2_waybel_9(X0,X1)) & v11_waybel_0(X1,X0) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & ! [X2] : (v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((~r2_hidden(k1_waybel_9(sK7,X1),k10_yellow_6(sK7,X1)) | ~r2_waybel_9(sK7,X1)) & v11_waybel_0(X1,sK7) & l1_waybel_0(X1,sK7) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & ! [X2] : (v5_pre_topc(k4_waybel_1(sK7,X2),sK7,sK7) | ~m1_subset_1(X2,u1_struct_0(sK7))) & l1_waybel_9(sK7) & v1_compts_1(sK7) & v2_lattice3(sK7) & v1_lattice3(sK7) & v5_orders_2(sK7) & v4_orders_2(sK7) & v3_orders_2(sK7) & v8_pre_topc(sK7) & v2_pre_topc(sK7))),
% 2.82/0.99    introduced(choice_axiom,[])).
% 2.82/0.99  
% 2.82/0.99  fof(f53,plain,(
% 2.82/0.99    ((~r2_hidden(k1_waybel_9(sK7,sK8),k10_yellow_6(sK7,sK8)) | ~r2_waybel_9(sK7,sK8)) & v11_waybel_0(sK8,sK7) & l1_waybel_0(sK8,sK7) & v7_waybel_0(sK8) & v4_orders_2(sK8) & ~v2_struct_0(sK8)) & ! [X2] : (v5_pre_topc(k4_waybel_1(sK7,X2),sK7,sK7) | ~m1_subset_1(X2,u1_struct_0(sK7))) & l1_waybel_9(sK7) & v1_compts_1(sK7) & v2_lattice3(sK7) & v1_lattice3(sK7) & v5_orders_2(sK7) & v4_orders_2(sK7) & v3_orders_2(sK7) & v8_pre_topc(sK7) & v2_pre_topc(sK7)),
% 2.82/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f50,f52,f51])).
% 2.82/0.99  
% 2.82/0.99  fof(f93,plain,(
% 2.82/0.99    l1_waybel_0(sK8,sK7)),
% 2.82/0.99    inference(cnf_transformation,[],[f53])).
% 2.82/0.99  
% 2.82/0.99  fof(f7,axiom,(
% 2.82/0.99    ! [X0] : ((l1_pre_topc(X0) & v1_compts_1(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0)))))),
% 2.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.82/0.99  
% 2.82/0.99  fof(f26,plain,(
% 2.82/0.99    ! [X0] : (! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.82/0.99    inference(ennf_transformation,[],[f7])).
% 2.82/0.99  
% 2.82/0.99  fof(f27,plain,(
% 2.82/0.99    ! [X0] : (! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.82/0.99    inference(flattening,[],[f26])).
% 2.82/0.99  
% 2.82/0.99  fof(f42,plain,(
% 2.82/0.99    ! [X1,X0] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) => (r3_waybel_9(X0,X1,sK3(X0,X1)) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))))),
% 2.82/0.99    introduced(choice_axiom,[])).
% 2.82/0.99  
% 2.82/0.99  fof(f43,plain,(
% 2.82/0.99    ! [X0] : (! [X1] : ((r3_waybel_9(X0,X1,sK3(X0,X1)) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.82/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f42])).
% 2.82/0.99  
% 2.82/0.99  fof(f72,plain,(
% 2.82/0.99    ( ! [X0,X1] : (r3_waybel_9(X0,X1,sK3(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.82/0.99    inference(cnf_transformation,[],[f43])).
% 2.82/0.99  
% 2.82/0.99  fof(f4,axiom,(
% 2.82/0.99    ! [X0] : (l1_waybel_9(X0) => (l1_orders_2(X0) & l1_pre_topc(X0)))),
% 2.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.82/0.99  
% 2.82/0.99  fof(f21,plain,(
% 2.82/0.99    ! [X0] : ((l1_orders_2(X0) & l1_pre_topc(X0)) | ~l1_waybel_9(X0))),
% 2.82/0.99    inference(ennf_transformation,[],[f4])).
% 2.82/0.99  
% 2.82/0.99  fof(f65,plain,(
% 2.82/0.99    ( ! [X0] : (l1_pre_topc(X0) | ~l1_waybel_9(X0)) )),
% 2.82/0.99    inference(cnf_transformation,[],[f21])).
% 2.82/0.99  
% 2.82/0.99  fof(f88,plain,(
% 2.82/0.99    l1_waybel_9(sK7)),
% 2.82/0.99    inference(cnf_transformation,[],[f53])).
% 2.82/0.99  
% 2.82/0.99  fof(f80,plain,(
% 2.82/0.99    v2_pre_topc(sK7)),
% 2.82/0.99    inference(cnf_transformation,[],[f53])).
% 2.82/0.99  
% 2.82/0.99  fof(f81,plain,(
% 2.82/0.99    v8_pre_topc(sK7)),
% 2.82/0.99    inference(cnf_transformation,[],[f53])).
% 2.82/0.99  
% 2.82/0.99  fof(f85,plain,(
% 2.82/0.99    v1_lattice3(sK7)),
% 2.82/0.99    inference(cnf_transformation,[],[f53])).
% 2.82/0.99  
% 2.82/0.99  fof(f87,plain,(
% 2.82/0.99    v1_compts_1(sK7)),
% 2.82/0.99    inference(cnf_transformation,[],[f53])).
% 2.82/0.99  
% 2.82/0.99  fof(f66,plain,(
% 2.82/0.99    ( ! [X0] : (l1_orders_2(X0) | ~l1_waybel_9(X0)) )),
% 2.82/0.99    inference(cnf_transformation,[],[f21])).
% 2.82/0.99  
% 2.82/0.99  fof(f1,axiom,(
% 2.82/0.99    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 2.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.82/0.99  
% 2.82/0.99  fof(f16,plain,(
% 2.82/0.99    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 2.82/0.99    inference(ennf_transformation,[],[f1])).
% 2.82/0.99  
% 2.82/0.99  fof(f17,plain,(
% 2.82/0.99    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 2.82/0.99    inference(flattening,[],[f16])).
% 2.82/0.99  
% 2.82/0.99  fof(f54,plain,(
% 2.82/0.99    ( ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0)) )),
% 2.82/0.99    inference(cnf_transformation,[],[f17])).
% 2.82/0.99  
% 2.82/0.99  fof(f90,plain,(
% 2.82/0.99    ~v2_struct_0(sK8)),
% 2.82/0.99    inference(cnf_transformation,[],[f53])).
% 2.82/0.99  
% 2.82/0.99  fof(f91,plain,(
% 2.82/0.99    v4_orders_2(sK8)),
% 2.82/0.99    inference(cnf_transformation,[],[f53])).
% 2.82/0.99  
% 2.82/0.99  fof(f92,plain,(
% 2.82/0.99    v7_waybel_0(sK8)),
% 2.82/0.99    inference(cnf_transformation,[],[f53])).
% 2.82/0.99  
% 2.82/0.99  fof(f2,axiom,(
% 2.82/0.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X2,X3) => r1_orders_2(X0,X3,X1))) & r1_lattice3(X0,X2,X1)) => (r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1)) & ((r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X2,X3) => r1_orders_2(X0,X3,X1))) & r1_lattice3(X0,X2,X1))))))),
% 2.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.82/0.99  
% 2.82/0.99  fof(f12,plain,(
% 2.82/0.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X2,X3) => r1_orders_2(X0,X3,X1))) & r1_lattice3(X0,X2,X1)) => (r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1)) & ((r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1) => (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r1_lattice3(X0,X2,X4) => r1_orders_2(X0,X4,X1))) & r1_lattice3(X0,X2,X1))))))),
% 2.82/0.99    inference(rectify,[],[f2])).
% 2.82/0.99  
% 2.82/0.99  fof(f18,plain,(
% 2.82/0.99    ! [X0] : (! [X1] : (! [X2] : (((r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1) | (? [X3] : ((~r1_orders_2(X0,X3,X1) & r1_lattice3(X0,X2,X3)) & m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X2,X1))) & ((! [X4] : ((r1_orders_2(X0,X4,X1) | ~r1_lattice3(X0,X2,X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_lattice3(X0,X2,X1)) | (~r2_yellow_0(X0,X2) | k2_yellow_0(X0,X2) != X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0)))),
% 2.82/0.99    inference(ennf_transformation,[],[f12])).
% 2.82/0.99  
% 2.82/0.99  fof(f19,plain,(
% 2.82/0.99    ! [X0] : (! [X1] : (! [X2] : (((r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1) | ? [X3] : (~r1_orders_2(X0,X3,X1) & r1_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X4,X1) | ~r1_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_lattice3(X0,X2,X1)) | ~r2_yellow_0(X0,X2) | k2_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 2.82/0.99    inference(flattening,[],[f18])).
% 2.82/0.99  
% 2.82/0.99  fof(f34,plain,(
% 2.82/0.99    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X1) & r1_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK0(X0,X1,X2),X1) & r1_lattice3(X0,X2,sK0(X0,X1,X2)) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 2.82/0.99    introduced(choice_axiom,[])).
% 2.82/0.99  
% 2.82/0.99  fof(f35,plain,(
% 2.82/0.99    ! [X0] : (! [X1] : (! [X2] : (((r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1) | (~r1_orders_2(X0,sK0(X0,X1,X2),X1) & r1_lattice3(X0,X2,sK0(X0,X1,X2)) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))) | ~r1_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X4,X1) | ~r1_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_lattice3(X0,X2,X1)) | ~r2_yellow_0(X0,X2) | k2_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 2.82/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f34])).
% 2.82/0.99  
% 2.82/0.99  fof(f61,plain,(
% 2.82/0.99    ( ! [X2,X0,X1] : (r2_yellow_0(X0,X2) | r1_lattice3(X0,X2,sK0(X0,X1,X2)) | ~r1_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 2.82/0.99    inference(cnf_transformation,[],[f35])).
% 2.82/0.99  
% 2.82/0.99  fof(f84,plain,(
% 2.82/0.99    v5_orders_2(sK7)),
% 2.82/0.99    inference(cnf_transformation,[],[f53])).
% 2.82/0.99  
% 2.82/0.99  fof(f6,axiom,(
% 2.82/0.99    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X2) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)) & X2 = X3) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) => r1_orders_2(X0,X4,X3))))))))),
% 2.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.82/0.99  
% 2.82/0.99  fof(f13,plain,(
% 2.82/0.99    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X2) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)) & X2 = X3) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X0)) => (r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5) => r1_orders_2(X0,X5,X3))))))))),
% 2.82/0.99    inference(rectify,[],[f6])).
% 2.82/0.99  
% 2.82/0.99  fof(f24,plain,(
% 2.82/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((! [X5] : ((r1_orders_2(X0,X5,X3) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5)) | ~m1_subset_1(X5,u1_struct_0(X0))) | (~r3_waybel_9(X0,X1,X2) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.82/0.99    inference(ennf_transformation,[],[f13])).
% 2.82/0.99  
% 2.82/0.99  fof(f25,plain,(
% 2.82/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~r3_waybel_9(X0,X1,X2) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.82/0.99    inference(flattening,[],[f24])).
% 2.82/0.99  
% 2.82/0.99  fof(f39,plain,(
% 2.82/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_waybel_9(X0,X1,X2) | ? [X5] : (~v5_pre_topc(k4_waybel_1(X0,X5),X0,X0) & m1_subset_1(X5,u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.82/0.99    inference(rectify,[],[f25])).
% 2.82/0.99  
% 2.82/0.99  fof(f40,plain,(
% 2.82/0.99    ! [X0] : (? [X5] : (~v5_pre_topc(k4_waybel_1(X0,X5),X0,X0) & m1_subset_1(X5,u1_struct_0(X0))) => (~v5_pre_topc(k4_waybel_1(X0,sK2(X0)),X0,X0) & m1_subset_1(sK2(X0),u1_struct_0(X0))))),
% 2.82/0.99    introduced(choice_axiom,[])).
% 2.82/0.99  
% 2.82/0.99  fof(f41,plain,(
% 2.82/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_waybel_9(X0,X1,X2) | (~v5_pre_topc(k4_waybel_1(X0,sK2(X0)),X0,X0) & m1_subset_1(sK2(X0),u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.82/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f39,f40])).
% 2.82/0.99  
% 2.82/0.99  fof(f70,plain,(
% 2.82/0.99    ( ! [X4,X2,X0,X3,X1] : (r1_orders_2(X0,X4,X3) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X2) | ~v5_pre_topc(k4_waybel_1(X0,sK2(X0)),X0,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.82/0.99    inference(cnf_transformation,[],[f41])).
% 2.82/0.99  
% 2.82/0.99  fof(f100,plain,(
% 2.82/0.99    ( ! [X4,X0,X3,X1] : (r1_orders_2(X0,X4,X3) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X3) | ~v5_pre_topc(k4_waybel_1(X0,sK2(X0)),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.82/0.99    inference(equality_resolution,[],[f70])).
% 2.82/0.99  
% 2.82/0.99  fof(f89,plain,(
% 2.82/0.99    ( ! [X2] : (v5_pre_topc(k4_waybel_1(sK7,X2),sK7,sK7) | ~m1_subset_1(X2,u1_struct_0(sK7))) )),
% 2.82/0.99    inference(cnf_transformation,[],[f53])).
% 2.82/0.99  
% 2.82/0.99  fof(f82,plain,(
% 2.82/0.99    v3_orders_2(sK7)),
% 2.82/0.99    inference(cnf_transformation,[],[f53])).
% 2.82/0.99  
% 2.82/0.99  fof(f83,plain,(
% 2.82/0.99    v4_orders_2(sK7)),
% 2.82/0.99    inference(cnf_transformation,[],[f53])).
% 2.82/0.99  
% 2.82/0.99  fof(f86,plain,(
% 2.82/0.99    v2_lattice3(sK7)),
% 2.82/0.99    inference(cnf_transformation,[],[f53])).
% 2.82/0.99  
% 2.82/0.99  fof(f69,plain,(
% 2.82/0.99    ( ! [X4,X2,X0,X3,X1] : (r1_orders_2(X0,X4,X3) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X2) | m1_subset_1(sK2(X0),u1_struct_0(X0)) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.82/0.99    inference(cnf_transformation,[],[f41])).
% 2.82/0.99  
% 2.82/0.99  fof(f101,plain,(
% 2.82/0.99    ( ! [X4,X0,X3,X1] : (r1_orders_2(X0,X4,X3) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X3) | m1_subset_1(sK2(X0),u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.82/0.99    inference(equality_resolution,[],[f69])).
% 2.82/0.99  
% 2.82/0.99  fof(f60,plain,(
% 2.82/0.99    ( ! [X2,X0,X1] : (r2_yellow_0(X0,X2) | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) | ~r1_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 2.82/0.99    inference(cnf_transformation,[],[f35])).
% 2.82/0.99  
% 2.82/0.99  fof(f62,plain,(
% 2.82/0.99    ( ! [X2,X0,X1] : (r2_yellow_0(X0,X2) | ~r1_orders_2(X0,sK0(X0,X1,X2),X1) | ~r1_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 2.82/0.99    inference(cnf_transformation,[],[f35])).
% 2.82/0.99  
% 2.82/0.99  fof(f94,plain,(
% 2.82/0.99    v11_waybel_0(sK8,sK7)),
% 2.82/0.99    inference(cnf_transformation,[],[f53])).
% 2.82/0.99  
% 2.82/0.99  fof(f5,axiom,(
% 2.82/0.99    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X2) & v11_waybel_0(X1,X0) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)) & X2 = X3) => r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3))))))),
% 2.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.82/0.99  
% 2.82/0.99  fof(f22,plain,(
% 2.82/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | (~r3_waybel_9(X0,X1,X2) | ~v11_waybel_0(X1,X0) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.82/0.99    inference(ennf_transformation,[],[f5])).
% 2.82/0.99  
% 2.82/0.99  fof(f23,plain,(
% 2.82/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X2) | ~v11_waybel_0(X1,X0) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.82/0.99    inference(flattening,[],[f22])).
% 2.82/0.99  
% 2.82/0.99  fof(f37,plain,(
% 2.82/0.99    ! [X0] : (? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) => (~v5_pre_topc(k4_waybel_1(X0,sK1(X0)),X0,X0) & m1_subset_1(sK1(X0),u1_struct_0(X0))))),
% 2.82/0.99    introduced(choice_axiom,[])).
% 2.82/0.99  
% 2.82/0.99  fof(f38,plain,(
% 2.82/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X2) | ~v11_waybel_0(X1,X0) | (~v5_pre_topc(k4_waybel_1(X0,sK1(X0)),X0,X0) & m1_subset_1(sK1(X0),u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.82/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f23,f37])).
% 2.82/0.99  
% 2.82/0.99  fof(f68,plain,(
% 2.82/0.99    ( ! [X2,X0,X3,X1] : (r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X2) | ~v11_waybel_0(X1,X0) | ~v5_pre_topc(k4_waybel_1(X0,sK1(X0)),X0,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.82/0.99    inference(cnf_transformation,[],[f38])).
% 2.82/0.99  
% 2.82/0.99  fof(f98,plain,(
% 2.82/0.99    ( ! [X0,X3,X1] : (r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X3) | ~v11_waybel_0(X1,X0) | ~v5_pre_topc(k4_waybel_1(X0,sK1(X0)),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.82/0.99    inference(equality_resolution,[],[f68])).
% 2.82/0.99  
% 2.82/0.99  fof(f67,plain,(
% 2.82/0.99    ( ! [X2,X0,X3,X1] : (r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X2) | ~v11_waybel_0(X1,X0) | m1_subset_1(sK1(X0),u1_struct_0(X0)) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.82/0.99    inference(cnf_transformation,[],[f38])).
% 2.82/0.99  
% 2.82/0.99  fof(f99,plain,(
% 2.82/0.99    ( ! [X0,X3,X1] : (r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X3) | ~v11_waybel_0(X1,X0) | m1_subset_1(sK1(X0),u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.82/0.99    inference(equality_resolution,[],[f67])).
% 2.82/0.99  
% 2.82/0.99  fof(f71,plain,(
% 2.82/0.99    ( ! [X0,X1] : (m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.82/0.99    inference(cnf_transformation,[],[f43])).
% 2.82/0.99  
% 2.82/0.99  fof(f8,axiom,(
% 2.82/0.99    ! [X0] : ((l1_pre_topc(X0) & v1_compts_1(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X3) & r3_waybel_9(X0,X1,X2)) => X2 = X3))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,X1,X2) => r2_hidden(X2,k10_yellow_6(X0,X1)))))))),
% 2.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.82/0.99  
% 2.82/0.99  fof(f14,plain,(
% 2.82/0.99    ! [X0] : ((l1_pre_topc(X0) & v1_compts_1(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X3) & r3_waybel_9(X0,X1,X2)) => X2 = X3))) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r3_waybel_9(X0,X1,X4) => r2_hidden(X4,k10_yellow_6(X0,X1)))))))),
% 2.82/0.99    inference(rectify,[],[f8])).
% 2.82/0.99  
% 2.82/0.99  fof(f28,plain,(
% 2.82/0.99    ! [X0] : (! [X1] : ((! [X4] : ((r2_hidden(X4,k10_yellow_6(X0,X1)) | ~r3_waybel_9(X0,X1,X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) | ? [X2] : (? [X3] : ((X2 != X3 & (r3_waybel_9(X0,X1,X3) & r3_waybel_9(X0,X1,X2))) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.82/0.99    inference(ennf_transformation,[],[f14])).
% 2.82/0.99  
% 2.82/0.99  fof(f29,plain,(
% 2.82/0.99    ! [X0] : (! [X1] : (! [X4] : (r2_hidden(X4,k10_yellow_6(X0,X1)) | ~r3_waybel_9(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ? [X2] : (? [X3] : (X2 != X3 & r3_waybel_9(X0,X1,X3) & r3_waybel_9(X0,X1,X2) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.82/0.99    inference(flattening,[],[f28])).
% 2.82/0.99  
% 2.82/0.99  fof(f44,plain,(
% 2.82/0.99    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,k10_yellow_6(X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ? [X3] : (? [X4] : (X3 != X4 & r3_waybel_9(X0,X1,X4) & r3_waybel_9(X0,X1,X3) & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.82/0.99    inference(rectify,[],[f29])).
% 2.82/0.99  
% 2.82/0.99  fof(f46,plain,(
% 2.82/0.99    ( ! [X3] : (! [X1,X0] : (? [X4] : (X3 != X4 & r3_waybel_9(X0,X1,X4) & r3_waybel_9(X0,X1,X3) & m1_subset_1(X4,u1_struct_0(X0))) => (sK5(X0,X1) != X3 & r3_waybel_9(X0,X1,sK5(X0,X1)) & r3_waybel_9(X0,X1,X3) & m1_subset_1(sK5(X0,X1),u1_struct_0(X0))))) )),
% 2.82/0.99    introduced(choice_axiom,[])).
% 2.82/0.99  
% 2.82/0.99  fof(f45,plain,(
% 2.82/0.99    ! [X1,X0] : (? [X3] : (? [X4] : (X3 != X4 & r3_waybel_9(X0,X1,X4) & r3_waybel_9(X0,X1,X3) & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0))) => (? [X4] : (sK4(X0,X1) != X4 & r3_waybel_9(X0,X1,X4) & r3_waybel_9(X0,X1,sK4(X0,X1)) & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(sK4(X0,X1),u1_struct_0(X0))))),
% 2.82/0.99    introduced(choice_axiom,[])).
% 2.82/0.99  
% 2.82/0.99  fof(f47,plain,(
% 2.82/0.99    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,k10_yellow_6(X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ((sK4(X0,X1) != sK5(X0,X1) & r3_waybel_9(X0,X1,sK5(X0,X1)) & r3_waybel_9(X0,X1,sK4(X0,X1)) & m1_subset_1(sK5(X0,X1),u1_struct_0(X0))) & m1_subset_1(sK4(X0,X1),u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.82/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f44,f46,f45])).
% 2.82/0.99  
% 2.82/0.99  fof(f75,plain,(
% 2.82/0.99    ( ! [X2,X0,X1] : (r2_hidden(X2,k10_yellow_6(X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | r3_waybel_9(X0,X1,sK4(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.82/0.99    inference(cnf_transformation,[],[f47])).
% 2.82/0.99  
% 2.82/0.99  fof(f3,axiom,(
% 2.82/0.99    ! [X0] : (l1_orders_2(X0) => ! [X1] : (l1_waybel_0(X1,X0) => (r2_waybel_9(X0,X1) <=> r2_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))))))),
% 2.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.82/0.99  
% 2.82/0.99  fof(f20,plain,(
% 2.82/0.99    ! [X0] : (! [X1] : ((r2_waybel_9(X0,X1) <=> r2_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))) | ~l1_waybel_0(X1,X0)) | ~l1_orders_2(X0))),
% 2.82/0.99    inference(ennf_transformation,[],[f3])).
% 2.82/0.99  
% 2.82/0.99  fof(f36,plain,(
% 2.82/0.99    ! [X0] : (! [X1] : (((r2_waybel_9(X0,X1) | ~r2_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))) & (r2_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) | ~r2_waybel_9(X0,X1))) | ~l1_waybel_0(X1,X0)) | ~l1_orders_2(X0))),
% 2.82/0.99    inference(nnf_transformation,[],[f20])).
% 2.82/0.99  
% 2.82/0.99  fof(f64,plain,(
% 2.82/0.99    ( ! [X0,X1] : (r2_waybel_9(X0,X1) | ~r2_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) | ~l1_waybel_0(X1,X0) | ~l1_orders_2(X0)) )),
% 2.82/0.99    inference(cnf_transformation,[],[f36])).
% 2.82/0.99  
% 2.82/0.99  fof(f95,plain,(
% 2.82/0.99    ~r2_hidden(k1_waybel_9(sK7,sK8),k10_yellow_6(sK7,sK8)) | ~r2_waybel_9(sK7,sK8)),
% 2.82/0.99    inference(cnf_transformation,[],[f53])).
% 2.82/0.99  
% 2.82/0.99  fof(f9,axiom,(
% 2.82/0.99    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => ((r3_waybel_9(X0,X2,X1) & v11_waybel_0(X2,X0) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X3),X0,X0))) => k1_waybel_9(X0,X2) = X1))))),
% 2.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.82/0.99  
% 2.82/0.99  fof(f30,plain,(
% 2.82/0.99    ! [X0] : (! [X1] : (! [X2] : ((k1_waybel_9(X0,X2) = X1 | (~r3_waybel_9(X0,X2,X1) | ~v11_waybel_0(X2,X0) | ? [X3] : (~v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) & m1_subset_1(X3,u1_struct_0(X0))))) | (~l1_waybel_0(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.82/0.99    inference(ennf_transformation,[],[f9])).
% 2.82/0.99  
% 2.82/0.99  fof(f31,plain,(
% 2.82/0.99    ! [X0] : (! [X1] : (! [X2] : (k1_waybel_9(X0,X2) = X1 | ~r3_waybel_9(X0,X2,X1) | ~v11_waybel_0(X2,X0) | ? [X3] : (~v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) & m1_subset_1(X3,u1_struct_0(X0))) | ~l1_waybel_0(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.82/0.99    inference(flattening,[],[f30])).
% 2.82/0.99  
% 2.82/0.99  fof(f48,plain,(
% 2.82/0.99    ! [X0] : (? [X3] : (~v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) & m1_subset_1(X3,u1_struct_0(X0))) => (~v5_pre_topc(k4_waybel_1(X0,sK6(X0)),X0,X0) & m1_subset_1(sK6(X0),u1_struct_0(X0))))),
% 2.82/0.99    introduced(choice_axiom,[])).
% 2.82/0.99  
% 2.82/0.99  fof(f49,plain,(
% 2.82/0.99    ! [X0] : (! [X1] : (! [X2] : (k1_waybel_9(X0,X2) = X1 | ~r3_waybel_9(X0,X2,X1) | ~v11_waybel_0(X2,X0) | (~v5_pre_topc(k4_waybel_1(X0,sK6(X0)),X0,X0) & m1_subset_1(sK6(X0),u1_struct_0(X0))) | ~l1_waybel_0(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.82/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f31,f48])).
% 2.82/0.99  
% 2.82/0.99  fof(f79,plain,(
% 2.82/0.99    ( ! [X2,X0,X1] : (k1_waybel_9(X0,X2) = X1 | ~r3_waybel_9(X0,X2,X1) | ~v11_waybel_0(X2,X0) | ~v5_pre_topc(k4_waybel_1(X0,sK6(X0)),X0,X0) | ~l1_waybel_0(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.82/0.99    inference(cnf_transformation,[],[f49])).
% 2.82/0.99  
% 2.82/0.99  fof(f78,plain,(
% 2.82/0.99    ( ! [X2,X0,X1] : (k1_waybel_9(X0,X2) = X1 | ~r3_waybel_9(X0,X2,X1) | ~v11_waybel_0(X2,X0) | m1_subset_1(sK6(X0),u1_struct_0(X0)) | ~l1_waybel_0(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.82/0.99    inference(cnf_transformation,[],[f49])).
% 2.82/0.99  
% 2.82/0.99  fof(f73,plain,(
% 2.82/0.99    ( ! [X2,X0,X1] : (r2_hidden(X2,k10_yellow_6(X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.82/0.99    inference(cnf_transformation,[],[f47])).
% 2.82/0.99  
% 2.82/0.99  fof(f77,plain,(
% 2.82/0.99    ( ! [X2,X0,X1] : (r2_hidden(X2,k10_yellow_6(X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | sK4(X0,X1) != sK5(X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.82/0.99    inference(cnf_transformation,[],[f47])).
% 2.82/0.99  
% 2.82/0.99  fof(f76,plain,(
% 2.82/0.99    ( ! [X2,X0,X1] : (r2_hidden(X2,k10_yellow_6(X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | r3_waybel_9(X0,X1,sK5(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.82/0.99    inference(cnf_transformation,[],[f47])).
% 2.82/0.99  
% 2.82/0.99  fof(f74,plain,(
% 2.82/0.99    ( ! [X2,X0,X1] : (r2_hidden(X2,k10_yellow_6(X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | m1_subset_1(sK5(X0,X1),u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.82/0.99    inference(cnf_transformation,[],[f47])).
% 2.82/0.99  
% 2.82/0.99  cnf(c_28,negated_conjecture,
% 2.82/0.99      ( l1_waybel_0(sK8,sK7) ),
% 2.82/0.99      inference(cnf_transformation,[],[f93]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_17,plain,
% 2.82/0.99      ( r3_waybel_9(X0,X1,sK3(X0,X1))
% 2.82/0.99      | ~ l1_waybel_0(X1,X0)
% 2.82/0.99      | ~ v2_pre_topc(X0)
% 2.82/0.99      | ~ v8_pre_topc(X0)
% 2.82/0.99      | ~ v1_compts_1(X0)
% 2.82/0.99      | ~ v4_orders_2(X1)
% 2.82/0.99      | ~ v7_waybel_0(X1)
% 2.82/0.99      | ~ l1_pre_topc(X0)
% 2.82/0.99      | v2_struct_0(X0)
% 2.82/0.99      | v2_struct_0(X1) ),
% 2.82/0.99      inference(cnf_transformation,[],[f72]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_12,plain,
% 2.82/0.99      ( l1_pre_topc(X0) | ~ l1_waybel_9(X0) ),
% 2.82/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_33,negated_conjecture,
% 2.82/0.99      ( l1_waybel_9(sK7) ),
% 2.82/0.99      inference(cnf_transformation,[],[f88]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_1315,plain,
% 2.82/0.99      ( l1_pre_topc(X0) | sK7 != X0 ),
% 2.82/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_33]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_1316,plain,
% 2.82/0.99      ( l1_pre_topc(sK7) ),
% 2.82/0.99      inference(unflattening,[status(thm)],[c_1315]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_2252,plain,
% 2.82/0.99      ( r3_waybel_9(X0,X1,sK3(X0,X1))
% 2.82/0.99      | ~ l1_waybel_0(X1,X0)
% 2.82/0.99      | ~ v2_pre_topc(X0)
% 2.82/0.99      | ~ v8_pre_topc(X0)
% 2.82/0.99      | ~ v1_compts_1(X0)
% 2.82/0.99      | ~ v4_orders_2(X1)
% 2.82/0.99      | ~ v7_waybel_0(X1)
% 2.82/0.99      | v2_struct_0(X0)
% 2.82/0.99      | v2_struct_0(X1)
% 2.82/0.99      | sK7 != X0 ),
% 2.82/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_1316]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_2253,plain,
% 2.82/0.99      ( r3_waybel_9(sK7,X0,sK3(sK7,X0))
% 2.82/0.99      | ~ l1_waybel_0(X0,sK7)
% 2.82/0.99      | ~ v2_pre_topc(sK7)
% 2.82/0.99      | ~ v8_pre_topc(sK7)
% 2.82/0.99      | ~ v1_compts_1(sK7)
% 2.82/0.99      | ~ v4_orders_2(X0)
% 2.82/0.99      | ~ v7_waybel_0(X0)
% 2.82/0.99      | v2_struct_0(X0)
% 2.82/0.99      | v2_struct_0(sK7) ),
% 2.82/0.99      inference(unflattening,[status(thm)],[c_2252]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_41,negated_conjecture,
% 2.82/0.99      ( v2_pre_topc(sK7) ),
% 2.82/0.99      inference(cnf_transformation,[],[f80]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_40,negated_conjecture,
% 2.82/0.99      ( v8_pre_topc(sK7) ),
% 2.82/0.99      inference(cnf_transformation,[],[f81]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_36,negated_conjecture,
% 2.82/0.99      ( v1_lattice3(sK7) ),
% 2.82/0.99      inference(cnf_transformation,[],[f85]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_34,negated_conjecture,
% 2.82/0.99      ( v1_compts_1(sK7) ),
% 2.82/0.99      inference(cnf_transformation,[],[f87]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_11,plain,
% 2.82/0.99      ( ~ l1_waybel_9(X0) | l1_orders_2(X0) ),
% 2.82/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_103,plain,
% 2.82/0.99      ( ~ l1_waybel_9(sK7) | l1_orders_2(sK7) ),
% 2.82/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_0,plain,
% 2.82/0.99      ( ~ l1_orders_2(X0) | ~ v1_lattice3(X0) | ~ v2_struct_0(X0) ),
% 2.82/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_136,plain,
% 2.82/0.99      ( ~ l1_orders_2(sK7) | ~ v1_lattice3(sK7) | ~ v2_struct_0(sK7) ),
% 2.82/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_2257,plain,
% 2.82/0.99      ( v2_struct_0(X0)
% 2.82/0.99      | ~ v7_waybel_0(X0)
% 2.82/0.99      | ~ v4_orders_2(X0)
% 2.82/0.99      | r3_waybel_9(sK7,X0,sK3(sK7,X0))
% 2.82/0.99      | ~ l1_waybel_0(X0,sK7) ),
% 2.82/0.99      inference(global_propositional_subsumption,
% 2.82/0.99                [status(thm)],
% 2.82/0.99                [c_2253,c_41,c_40,c_36,c_34,c_33,c_103,c_136]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_2258,plain,
% 2.82/0.99      ( r3_waybel_9(sK7,X0,sK3(sK7,X0))
% 2.82/0.99      | ~ l1_waybel_0(X0,sK7)
% 2.82/0.99      | ~ v4_orders_2(X0)
% 2.82/0.99      | ~ v7_waybel_0(X0)
% 2.82/0.99      | v2_struct_0(X0) ),
% 2.82/0.99      inference(renaming,[status(thm)],[c_2257]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_2379,plain,
% 2.82/0.99      ( r3_waybel_9(sK7,X0,sK3(sK7,X0))
% 2.82/0.99      | ~ v4_orders_2(X0)
% 2.82/0.99      | ~ v7_waybel_0(X0)
% 2.82/0.99      | v2_struct_0(X0)
% 2.82/0.99      | sK8 != X0
% 2.82/0.99      | sK7 != sK7 ),
% 2.82/0.99      inference(resolution_lifted,[status(thm)],[c_28,c_2258]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_2380,plain,
% 2.82/0.99      ( r3_waybel_9(sK7,sK8,sK3(sK7,sK8))
% 2.82/0.99      | ~ v4_orders_2(sK8)
% 2.82/0.99      | ~ v7_waybel_0(sK8)
% 2.82/0.99      | v2_struct_0(sK8) ),
% 2.82/0.99      inference(unflattening,[status(thm)],[c_2379]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_31,negated_conjecture,
% 2.82/0.99      ( ~ v2_struct_0(sK8) ),
% 2.82/0.99      inference(cnf_transformation,[],[f90]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_30,negated_conjecture,
% 2.82/0.99      ( v4_orders_2(sK8) ),
% 2.82/0.99      inference(cnf_transformation,[],[f91]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_29,negated_conjecture,
% 2.82/0.99      ( v7_waybel_0(sK8) ),
% 2.82/0.99      inference(cnf_transformation,[],[f92]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_2382,plain,
% 2.82/0.99      ( r3_waybel_9(sK7,sK8,sK3(sK7,sK8)) ),
% 2.82/0.99      inference(global_propositional_subsumption,
% 2.82/0.99                [status(thm)],
% 2.82/0.99                [c_2380,c_31,c_30,c_29]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_4366,plain,
% 2.82/0.99      ( r3_waybel_9(sK7,sK8,sK3(sK7,sK8)) ),
% 2.82/0.99      inference(subtyping,[status(esa)],[c_2382]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_4894,plain,
% 2.82/0.99      ( r3_waybel_9(sK7,sK8,sK3(sK7,sK8)) = iProver_top ),
% 2.82/0.99      inference(predicate_to_equality,[status(thm)],[c_4366]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_2,plain,
% 2.82/0.99      ( ~ r1_lattice3(X0,X1,X2)
% 2.82/0.99      | r1_lattice3(X0,X1,sK0(X0,X2,X1))
% 2.82/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.82/0.99      | r2_yellow_0(X0,X1)
% 2.82/0.99      | ~ v5_orders_2(X0)
% 2.82/0.99      | ~ l1_orders_2(X0) ),
% 2.82/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_621,plain,
% 2.82/0.99      ( ~ r1_lattice3(X0,X1,X2)
% 2.82/0.99      | r1_lattice3(X0,X1,sK0(X0,X2,X1))
% 2.82/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.82/0.99      | r2_yellow_0(X0,X1)
% 2.82/0.99      | ~ l1_waybel_9(X0)
% 2.82/0.99      | ~ v5_orders_2(X0) ),
% 2.82/0.99      inference(resolution,[status(thm)],[c_11,c_2]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_37,negated_conjecture,
% 2.82/0.99      ( v5_orders_2(sK7) ),
% 2.82/0.99      inference(cnf_transformation,[],[f84]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_1107,plain,
% 2.82/0.99      ( ~ r1_lattice3(X0,X1,X2)
% 2.82/0.99      | r1_lattice3(X0,X1,sK0(X0,X2,X1))
% 2.82/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.82/0.99      | r2_yellow_0(X0,X1)
% 2.82/0.99      | ~ l1_waybel_9(X0)
% 2.82/0.99      | sK7 != X0 ),
% 2.82/0.99      inference(resolution_lifted,[status(thm)],[c_621,c_37]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_1108,plain,
% 2.82/0.99      ( ~ r1_lattice3(sK7,X0,X1)
% 2.82/0.99      | r1_lattice3(sK7,X0,sK0(sK7,X1,X0))
% 2.82/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 2.82/0.99      | r2_yellow_0(sK7,X0)
% 2.82/0.99      | ~ l1_waybel_9(sK7) ),
% 2.82/0.99      inference(unflattening,[status(thm)],[c_1107]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_1112,plain,
% 2.82/0.99      ( r2_yellow_0(sK7,X0)
% 2.82/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 2.82/0.99      | r1_lattice3(sK7,X0,sK0(sK7,X1,X0))
% 2.82/0.99      | ~ r1_lattice3(sK7,X0,X1) ),
% 2.82/0.99      inference(global_propositional_subsumption,
% 2.82/0.99                [status(thm)],
% 2.82/0.99                [c_1108,c_33]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_1113,plain,
% 2.82/0.99      ( ~ r1_lattice3(sK7,X0,X1)
% 2.82/0.99      | r1_lattice3(sK7,X0,sK0(sK7,X1,X0))
% 2.82/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 2.82/0.99      | r2_yellow_0(sK7,X0) ),
% 2.82/0.99      inference(renaming,[status(thm)],[c_1112]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_4374,plain,
% 2.82/0.99      ( ~ r1_lattice3(sK7,X0_70,X0_68)
% 2.82/0.99      | r1_lattice3(sK7,X0_70,sK0(sK7,X0_68,X0_70))
% 2.82/0.99      | ~ m1_subset_1(X0_68,u1_struct_0(sK7))
% 2.82/0.99      | r2_yellow_0(sK7,X0_70) ),
% 2.82/0.99      inference(subtyping,[status(esa)],[c_1113]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_4886,plain,
% 2.82/0.99      ( r1_lattice3(sK7,X0_70,X0_68) != iProver_top
% 2.82/0.99      | r1_lattice3(sK7,X0_70,sK0(sK7,X0_68,X0_70)) = iProver_top
% 2.82/0.99      | m1_subset_1(X0_68,u1_struct_0(sK7)) != iProver_top
% 2.82/0.99      | r2_yellow_0(sK7,X0_70) = iProver_top ),
% 2.82/0.99      inference(predicate_to_equality,[status(thm)],[c_4374]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_15,plain,
% 2.82/0.99      ( ~ v5_pre_topc(k4_waybel_1(X0,sK2(X0)),X0,X0)
% 2.82/0.99      | ~ r3_waybel_9(X0,X1,X2)
% 2.82/0.99      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
% 2.82/0.99      | r1_orders_2(X0,X3,X2)
% 2.82/0.99      | ~ l1_waybel_0(X1,X0)
% 2.82/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.82/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.82/0.99      | ~ v2_pre_topc(X0)
% 2.82/0.99      | ~ v8_pre_topc(X0)
% 2.82/0.99      | ~ v3_orders_2(X0)
% 2.82/0.99      | ~ v2_lattice3(X0)
% 2.82/0.99      | ~ v1_compts_1(X0)
% 2.82/0.99      | ~ v4_orders_2(X1)
% 2.82/0.99      | ~ v4_orders_2(X0)
% 2.82/0.99      | ~ v7_waybel_0(X1)
% 2.82/0.99      | ~ l1_waybel_9(X0)
% 2.82/0.99      | ~ v5_orders_2(X0)
% 2.82/0.99      | ~ v1_lattice3(X0)
% 2.82/0.99      | v2_struct_0(X1) ),
% 2.82/0.99      inference(cnf_transformation,[],[f100]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_32,negated_conjecture,
% 2.82/0.99      ( v5_pre_topc(k4_waybel_1(sK7,X0),sK7,sK7)
% 2.82/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK7)) ),
% 2.82/0.99      inference(cnf_transformation,[],[f89]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_783,plain,
% 2.82/0.99      ( ~ r3_waybel_9(X0,X1,X2)
% 2.82/0.99      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
% 2.82/0.99      | r1_orders_2(X0,X3,X2)
% 2.82/0.99      | ~ l1_waybel_0(X1,X0)
% 2.82/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.82/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.82/0.99      | ~ m1_subset_1(X4,u1_struct_0(sK7))
% 2.82/0.99      | ~ v2_pre_topc(X0)
% 2.82/0.99      | ~ v8_pre_topc(X0)
% 2.82/0.99      | ~ v3_orders_2(X0)
% 2.82/0.99      | ~ v2_lattice3(X0)
% 2.82/0.99      | ~ v1_compts_1(X0)
% 2.82/0.99      | ~ v4_orders_2(X0)
% 2.82/0.99      | ~ v4_orders_2(X1)
% 2.82/0.99      | ~ v7_waybel_0(X1)
% 2.82/0.99      | ~ l1_waybel_9(X0)
% 2.82/0.99      | ~ v5_orders_2(X0)
% 2.82/0.99      | ~ v1_lattice3(X0)
% 2.82/0.99      | v2_struct_0(X1)
% 2.82/0.99      | k4_waybel_1(X0,sK2(X0)) != k4_waybel_1(sK7,X4)
% 2.82/0.99      | sK7 != X0 ),
% 2.82/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_32]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_784,plain,
% 2.82/0.99      ( ~ r3_waybel_9(sK7,X0,X1)
% 2.82/0.99      | ~ r1_lattice3(sK7,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK7),u1_waybel_0(sK7,X0)),X2)
% 2.82/0.99      | r1_orders_2(sK7,X2,X1)
% 2.82/0.99      | ~ l1_waybel_0(X0,sK7)
% 2.82/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 2.82/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 2.82/0.99      | ~ m1_subset_1(X3,u1_struct_0(sK7))
% 2.82/0.99      | ~ v2_pre_topc(sK7)
% 2.82/0.99      | ~ v8_pre_topc(sK7)
% 2.82/0.99      | ~ v3_orders_2(sK7)
% 2.82/0.99      | ~ v2_lattice3(sK7)
% 2.82/0.99      | ~ v1_compts_1(sK7)
% 2.82/0.99      | ~ v4_orders_2(X0)
% 2.82/0.99      | ~ v4_orders_2(sK7)
% 2.82/0.99      | ~ v7_waybel_0(X0)
% 2.82/0.99      | ~ l1_waybel_9(sK7)
% 2.82/0.99      | ~ v5_orders_2(sK7)
% 2.82/0.99      | ~ v1_lattice3(sK7)
% 2.82/0.99      | v2_struct_0(X0)
% 2.82/0.99      | k4_waybel_1(sK7,sK2(sK7)) != k4_waybel_1(sK7,X3) ),
% 2.82/0.99      inference(unflattening,[status(thm)],[c_783]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_39,negated_conjecture,
% 2.82/0.99      ( v3_orders_2(sK7) ),
% 2.82/0.99      inference(cnf_transformation,[],[f82]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_38,negated_conjecture,
% 2.82/0.99      ( v4_orders_2(sK7) ),
% 2.82/0.99      inference(cnf_transformation,[],[f83]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_35,negated_conjecture,
% 2.82/0.99      ( v2_lattice3(sK7) ),
% 2.82/0.99      inference(cnf_transformation,[],[f86]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_788,plain,
% 2.82/0.99      ( ~ v7_waybel_0(X0)
% 2.82/0.99      | ~ m1_subset_1(X3,u1_struct_0(sK7))
% 2.82/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 2.82/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 2.82/0.99      | ~ l1_waybel_0(X0,sK7)
% 2.82/0.99      | r1_orders_2(sK7,X2,X1)
% 2.82/0.99      | ~ r1_lattice3(sK7,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK7),u1_waybel_0(sK7,X0)),X2)
% 2.82/0.99      | ~ r3_waybel_9(sK7,X0,X1)
% 2.82/0.99      | ~ v4_orders_2(X0)
% 2.82/0.99      | v2_struct_0(X0)
% 2.82/0.99      | k4_waybel_1(sK7,sK2(sK7)) != k4_waybel_1(sK7,X3) ),
% 2.82/0.99      inference(global_propositional_subsumption,
% 2.82/0.99                [status(thm)],
% 2.82/0.99                [c_784,c_41,c_40,c_39,c_38,c_37,c_36,c_35,c_34,c_33]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_789,plain,
% 2.82/0.99      ( ~ r3_waybel_9(sK7,X0,X1)
% 2.82/0.99      | ~ r1_lattice3(sK7,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK7),u1_waybel_0(sK7,X0)),X2)
% 2.82/0.99      | r1_orders_2(sK7,X2,X1)
% 2.82/0.99      | ~ l1_waybel_0(X0,sK7)
% 2.82/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 2.82/0.99      | ~ m1_subset_1(X3,u1_struct_0(sK7))
% 2.82/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 2.82/0.99      | ~ v4_orders_2(X0)
% 2.82/0.99      | ~ v7_waybel_0(X0)
% 2.82/0.99      | v2_struct_0(X0)
% 2.82/0.99      | k4_waybel_1(sK7,sK2(sK7)) != k4_waybel_1(sK7,X3) ),
% 2.82/0.99      inference(renaming,[status(thm)],[c_788]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_2535,plain,
% 2.82/0.99      ( ~ r3_waybel_9(sK7,X0,X1)
% 2.82/0.99      | ~ r1_lattice3(sK7,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK7),u1_waybel_0(sK7,X0)),X2)
% 2.82/0.99      | r1_orders_2(sK7,X2,X1)
% 2.82/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 2.82/0.99      | ~ m1_subset_1(X3,u1_struct_0(sK7))
% 2.82/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 2.82/0.99      | ~ v4_orders_2(X0)
% 2.82/0.99      | ~ v7_waybel_0(X0)
% 2.82/0.99      | v2_struct_0(X0)
% 2.82/0.99      | k4_waybel_1(sK7,sK2(sK7)) != k4_waybel_1(sK7,X3)
% 2.82/0.99      | sK8 != X0
% 2.82/0.99      | sK7 != sK7 ),
% 2.82/0.99      inference(resolution_lifted,[status(thm)],[c_28,c_789]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_2536,plain,
% 2.82/0.99      ( ~ r3_waybel_9(sK7,sK8,X0)
% 2.82/0.99      | ~ r1_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X1)
% 2.82/0.99      | r1_orders_2(sK7,X1,X0)
% 2.82/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 2.82/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 2.82/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 2.82/0.99      | ~ v4_orders_2(sK8)
% 2.82/0.99      | ~ v7_waybel_0(sK8)
% 2.82/0.99      | v2_struct_0(sK8)
% 2.82/0.99      | k4_waybel_1(sK7,sK2(sK7)) != k4_waybel_1(sK7,X2) ),
% 2.82/0.99      inference(unflattening,[status(thm)],[c_2535]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_2540,plain,
% 2.82/0.99      ( ~ m1_subset_1(X1,u1_struct_0(sK7))
% 2.82/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 2.82/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 2.82/0.99      | r1_orders_2(sK7,X1,X0)
% 2.82/0.99      | ~ r1_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X1)
% 2.82/0.99      | ~ r3_waybel_9(sK7,sK8,X0)
% 2.82/0.99      | k4_waybel_1(sK7,sK2(sK7)) != k4_waybel_1(sK7,X2) ),
% 2.82/0.99      inference(global_propositional_subsumption,
% 2.82/0.99                [status(thm)],
% 2.82/0.99                [c_2536,c_31,c_30,c_29]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_2541,plain,
% 2.82/0.99      ( ~ r3_waybel_9(sK7,sK8,X0)
% 2.82/0.99      | ~ r1_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X1)
% 2.82/0.99      | r1_orders_2(sK7,X1,X0)
% 2.82/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 2.82/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 2.82/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 2.82/0.99      | k4_waybel_1(sK7,sK2(sK7)) != k4_waybel_1(sK7,X2) ),
% 2.82/0.99      inference(renaming,[status(thm)],[c_2540]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_4364,plain,
% 2.82/0.99      ( ~ r3_waybel_9(sK7,sK8,X0_68)
% 2.82/0.99      | ~ r1_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X1_68)
% 2.82/0.99      | r1_orders_2(sK7,X1_68,X0_68)
% 2.82/0.99      | ~ m1_subset_1(X1_68,u1_struct_0(sK7))
% 2.82/0.99      | ~ m1_subset_1(X0_68,u1_struct_0(sK7))
% 2.82/0.99      | ~ m1_subset_1(X2_68,u1_struct_0(sK7))
% 2.82/0.99      | k4_waybel_1(sK7,sK2(sK7)) != k4_waybel_1(sK7,X2_68) ),
% 2.82/0.99      inference(subtyping,[status(esa)],[c_2541]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_4387,plain,
% 2.82/0.99      ( ~ r3_waybel_9(sK7,sK8,X0_68)
% 2.82/0.99      | ~ r1_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X1_68)
% 2.82/0.99      | r1_orders_2(sK7,X1_68,X0_68)
% 2.82/0.99      | ~ m1_subset_1(X1_68,u1_struct_0(sK7))
% 2.82/0.99      | ~ m1_subset_1(X0_68,u1_struct_0(sK7))
% 2.82/0.99      | ~ sP5_iProver_split ),
% 2.82/0.99      inference(splitting,
% 2.82/0.99                [splitting(split),new_symbols(definition,[sP5_iProver_split])],
% 2.82/0.99                [c_4364]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_4897,plain,
% 2.82/0.99      ( r3_waybel_9(sK7,sK8,X0_68) != iProver_top
% 2.82/0.99      | r1_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X1_68) != iProver_top
% 2.82/0.99      | r1_orders_2(sK7,X1_68,X0_68) = iProver_top
% 2.82/0.99      | m1_subset_1(X0_68,u1_struct_0(sK7)) != iProver_top
% 2.82/0.99      | m1_subset_1(X1_68,u1_struct_0(sK7)) != iProver_top
% 2.82/0.99      | sP5_iProver_split != iProver_top ),
% 2.82/0.99      inference(predicate_to_equality,[status(thm)],[c_4387]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_16,plain,
% 2.82/0.99      ( ~ r3_waybel_9(X0,X1,X2)
% 2.82/0.99      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
% 2.82/0.99      | r1_orders_2(X0,X3,X2)
% 2.82/0.99      | ~ l1_waybel_0(X1,X0)
% 2.82/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.82/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.82/0.99      | m1_subset_1(sK2(X0),u1_struct_0(X0))
% 2.82/0.99      | ~ v2_pre_topc(X0)
% 2.82/0.99      | ~ v8_pre_topc(X0)
% 2.82/0.99      | ~ v3_orders_2(X0)
% 2.82/0.99      | ~ v2_lattice3(X0)
% 2.82/0.99      | ~ v1_compts_1(X0)
% 2.82/0.99      | ~ v4_orders_2(X1)
% 2.82/0.99      | ~ v4_orders_2(X0)
% 2.82/0.99      | ~ v7_waybel_0(X1)
% 2.82/0.99      | ~ l1_waybel_9(X0)
% 2.82/0.99      | ~ v5_orders_2(X0)
% 2.82/0.99      | ~ v1_lattice3(X0)
% 2.82/0.99      | v2_struct_0(X1) ),
% 2.82/0.99      inference(cnf_transformation,[],[f101]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_1017,plain,
% 2.82/0.99      ( ~ r3_waybel_9(X0,X1,X2)
% 2.82/0.99      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
% 2.82/0.99      | r1_orders_2(X0,X3,X2)
% 2.82/0.99      | ~ l1_waybel_0(X1,X0)
% 2.82/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.82/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.82/0.99      | m1_subset_1(sK2(X0),u1_struct_0(X0))
% 2.82/0.99      | ~ v2_pre_topc(X0)
% 2.82/0.99      | ~ v8_pre_topc(X0)
% 2.82/0.99      | ~ v3_orders_2(X0)
% 2.82/0.99      | ~ v1_compts_1(X0)
% 2.82/0.99      | ~ v4_orders_2(X0)
% 2.82/0.99      | ~ v4_orders_2(X1)
% 2.82/0.99      | ~ v7_waybel_0(X1)
% 2.82/0.99      | ~ l1_waybel_9(X0)
% 2.82/0.99      | ~ v5_orders_2(X0)
% 2.82/0.99      | ~ v1_lattice3(X0)
% 2.82/0.99      | v2_struct_0(X1)
% 2.82/0.99      | sK7 != X0 ),
% 2.82/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_35]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_1018,plain,
% 2.82/0.99      ( ~ r3_waybel_9(sK7,X0,X1)
% 2.82/0.99      | ~ r1_lattice3(sK7,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK7),u1_waybel_0(sK7,X0)),X2)
% 2.82/0.99      | r1_orders_2(sK7,X2,X1)
% 2.82/0.99      | ~ l1_waybel_0(X0,sK7)
% 2.82/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 2.82/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 2.82/0.99      | m1_subset_1(sK2(sK7),u1_struct_0(sK7))
% 2.82/0.99      | ~ v2_pre_topc(sK7)
% 2.82/0.99      | ~ v8_pre_topc(sK7)
% 2.82/0.99      | ~ v3_orders_2(sK7)
% 2.82/0.99      | ~ v1_compts_1(sK7)
% 2.82/0.99      | ~ v4_orders_2(X0)
% 2.82/0.99      | ~ v4_orders_2(sK7)
% 2.82/0.99      | ~ v7_waybel_0(X0)
% 2.82/0.99      | ~ l1_waybel_9(sK7)
% 2.82/0.99      | ~ v5_orders_2(sK7)
% 2.82/0.99      | ~ v1_lattice3(sK7)
% 2.82/0.99      | v2_struct_0(X0) ),
% 2.82/0.99      inference(unflattening,[status(thm)],[c_1017]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_1022,plain,
% 2.82/0.99      ( ~ v7_waybel_0(X0)
% 2.82/0.99      | ~ r3_waybel_9(sK7,X0,X1)
% 2.82/0.99      | ~ r1_lattice3(sK7,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK7),u1_waybel_0(sK7,X0)),X2)
% 2.82/0.99      | r1_orders_2(sK7,X2,X1)
% 2.82/0.99      | ~ l1_waybel_0(X0,sK7)
% 2.82/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 2.82/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 2.82/0.99      | m1_subset_1(sK2(sK7),u1_struct_0(sK7))
% 2.82/0.99      | ~ v4_orders_2(X0)
% 2.82/0.99      | v2_struct_0(X0) ),
% 2.82/0.99      inference(global_propositional_subsumption,
% 2.82/0.99                [status(thm)],
% 2.82/0.99                [c_1018,c_41,c_40,c_39,c_38,c_37,c_36,c_34,c_33]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_1023,plain,
% 2.82/0.99      ( ~ r3_waybel_9(sK7,X0,X1)
% 2.82/0.99      | ~ r1_lattice3(sK7,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK7),u1_waybel_0(sK7,X0)),X2)
% 2.82/0.99      | r1_orders_2(sK7,X2,X1)
% 2.82/0.99      | ~ l1_waybel_0(X0,sK7)
% 2.82/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 2.82/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 2.82/0.99      | m1_subset_1(sK2(sK7),u1_struct_0(sK7))
% 2.82/0.99      | ~ v4_orders_2(X0)
% 2.82/0.99      | ~ v7_waybel_0(X0)
% 2.82/0.99      | v2_struct_0(X0) ),
% 2.82/0.99      inference(renaming,[status(thm)],[c_1022]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_2505,plain,
% 2.82/0.99      ( ~ r3_waybel_9(sK7,X0,X1)
% 2.82/0.99      | ~ r1_lattice3(sK7,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK7),u1_waybel_0(sK7,X0)),X2)
% 2.82/0.99      | r1_orders_2(sK7,X2,X1)
% 2.82/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 2.82/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 2.82/0.99      | m1_subset_1(sK2(sK7),u1_struct_0(sK7))
% 2.82/0.99      | ~ v4_orders_2(X0)
% 2.82/0.99      | ~ v7_waybel_0(X0)
% 2.82/0.99      | v2_struct_0(X0)
% 2.82/0.99      | sK8 != X0
% 2.82/0.99      | sK7 != sK7 ),
% 2.82/0.99      inference(resolution_lifted,[status(thm)],[c_28,c_1023]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_2506,plain,
% 2.82/0.99      ( ~ r3_waybel_9(sK7,sK8,X0)
% 2.82/0.99      | ~ r1_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X1)
% 2.82/0.99      | r1_orders_2(sK7,X1,X0)
% 2.82/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 2.82/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 2.82/0.99      | m1_subset_1(sK2(sK7),u1_struct_0(sK7))
% 2.82/0.99      | ~ v4_orders_2(sK8)
% 2.82/0.99      | ~ v7_waybel_0(sK8)
% 2.82/0.99      | v2_struct_0(sK8) ),
% 2.82/0.99      inference(unflattening,[status(thm)],[c_2505]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_2510,plain,
% 2.82/0.99      ( m1_subset_1(sK2(sK7),u1_struct_0(sK7))
% 2.82/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 2.82/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 2.82/0.99      | r1_orders_2(sK7,X1,X0)
% 2.82/0.99      | ~ r1_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X1)
% 2.82/0.99      | ~ r3_waybel_9(sK7,sK8,X0) ),
% 2.82/0.99      inference(global_propositional_subsumption,
% 2.82/0.99                [status(thm)],
% 2.82/0.99                [c_2506,c_31,c_30,c_29]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_2511,plain,
% 2.82/0.99      ( ~ r3_waybel_9(sK7,sK8,X0)
% 2.82/0.99      | ~ r1_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X1)
% 2.82/0.99      | r1_orders_2(sK7,X1,X0)
% 2.82/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 2.82/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 2.82/0.99      | m1_subset_1(sK2(sK7),u1_struct_0(sK7)) ),
% 2.82/0.99      inference(renaming,[status(thm)],[c_2510]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_4365,plain,
% 2.82/0.99      ( ~ r3_waybel_9(sK7,sK8,X0_68)
% 2.82/0.99      | ~ r1_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X1_68)
% 2.82/0.99      | r1_orders_2(sK7,X1_68,X0_68)
% 2.82/0.99      | ~ m1_subset_1(X1_68,u1_struct_0(sK7))
% 2.82/0.99      | ~ m1_subset_1(X0_68,u1_struct_0(sK7))
% 2.82/0.99      | m1_subset_1(sK2(sK7),u1_struct_0(sK7)) ),
% 2.82/0.99      inference(subtyping,[status(esa)],[c_2511]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_4453,plain,
% 2.82/0.99      ( r3_waybel_9(sK7,sK8,X0_68) != iProver_top
% 2.82/0.99      | r1_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X1_68) != iProver_top
% 2.82/0.99      | r1_orders_2(sK7,X1_68,X0_68) = iProver_top
% 2.82/0.99      | m1_subset_1(X0_68,u1_struct_0(sK7)) != iProver_top
% 2.82/0.99      | m1_subset_1(X1_68,u1_struct_0(sK7)) != iProver_top
% 2.82/0.99      | m1_subset_1(sK2(sK7),u1_struct_0(sK7)) = iProver_top ),
% 2.82/0.99      inference(predicate_to_equality,[status(thm)],[c_4365]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_4388,plain,
% 2.82/0.99      ( sP5_iProver_split | sP4_iProver_split ),
% 2.82/0.99      inference(splitting,
% 2.82/0.99                [splitting(split),new_symbols(definition,[])],
% 2.82/0.99                [c_4364]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_4456,plain,
% 2.82/0.99      ( sP5_iProver_split = iProver_top
% 2.82/0.99      | sP4_iProver_split = iProver_top ),
% 2.82/0.99      inference(predicate_to_equality,[status(thm)],[c_4388]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_4457,plain,
% 2.82/0.99      ( r3_waybel_9(sK7,sK8,X0_68) != iProver_top
% 2.82/0.99      | r1_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X1_68) != iProver_top
% 2.82/0.99      | r1_orders_2(sK7,X1_68,X0_68) = iProver_top
% 2.82/0.99      | m1_subset_1(X0_68,u1_struct_0(sK7)) != iProver_top
% 2.82/0.99      | m1_subset_1(X1_68,u1_struct_0(sK7)) != iProver_top
% 2.82/0.99      | sP5_iProver_split != iProver_top ),
% 2.82/0.99      inference(predicate_to_equality,[status(thm)],[c_4387]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_4386,plain,
% 2.82/0.99      ( ~ m1_subset_1(X0_68,u1_struct_0(sK7))
% 2.82/0.99      | k4_waybel_1(sK7,sK2(sK7)) != k4_waybel_1(sK7,X0_68)
% 2.82/0.99      | ~ sP4_iProver_split ),
% 2.82/0.99      inference(splitting,
% 2.82/0.99                [splitting(split),new_symbols(definition,[sP4_iProver_split])],
% 2.82/0.99                [c_4364]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_4898,plain,
% 2.82/0.99      ( k4_waybel_1(sK7,sK2(sK7)) != k4_waybel_1(sK7,X0_68)
% 2.82/0.99      | m1_subset_1(X0_68,u1_struct_0(sK7)) != iProver_top
% 2.82/0.99      | sP4_iProver_split != iProver_top ),
% 2.82/0.99      inference(predicate_to_equality,[status(thm)],[c_4386]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_5218,plain,
% 2.82/0.99      ( m1_subset_1(sK2(sK7),u1_struct_0(sK7)) != iProver_top
% 2.82/0.99      | sP4_iProver_split != iProver_top ),
% 2.82/0.99      inference(equality_resolution,[status(thm)],[c_4898]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_5616,plain,
% 2.82/0.99      ( m1_subset_1(X1_68,u1_struct_0(sK7)) != iProver_top
% 2.82/0.99      | m1_subset_1(X0_68,u1_struct_0(sK7)) != iProver_top
% 2.82/0.99      | r1_orders_2(sK7,X1_68,X0_68) = iProver_top
% 2.82/0.99      | r1_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X1_68) != iProver_top
% 2.82/0.99      | r3_waybel_9(sK7,sK8,X0_68) != iProver_top ),
% 2.82/0.99      inference(global_propositional_subsumption,
% 2.82/0.99                [status(thm)],
% 2.82/0.99                [c_4897,c_4453,c_4456,c_4457,c_5218]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_5617,plain,
% 2.82/0.99      ( r3_waybel_9(sK7,sK8,X0_68) != iProver_top
% 2.82/0.99      | r1_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X1_68) != iProver_top
% 2.82/0.99      | r1_orders_2(sK7,X1_68,X0_68) = iProver_top
% 2.82/0.99      | m1_subset_1(X0_68,u1_struct_0(sK7)) != iProver_top
% 2.82/0.99      | m1_subset_1(X1_68,u1_struct_0(sK7)) != iProver_top ),
% 2.82/0.99      inference(renaming,[status(thm)],[c_5616]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_5628,plain,
% 2.82/0.99      ( r3_waybel_9(sK7,sK8,X0_68) != iProver_top
% 2.82/0.99      | r1_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X1_68) != iProver_top
% 2.82/0.99      | r1_orders_2(sK7,sK0(sK7,X1_68,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))),X0_68) = iProver_top
% 2.82/0.99      | m1_subset_1(X1_68,u1_struct_0(sK7)) != iProver_top
% 2.82/0.99      | m1_subset_1(X0_68,u1_struct_0(sK7)) != iProver_top
% 2.82/0.99      | m1_subset_1(sK0(sK7,X1_68,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))),u1_struct_0(sK7)) != iProver_top
% 2.82/0.99      | r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) = iProver_top ),
% 2.82/0.99      inference(superposition,[status(thm)],[c_4886,c_5617]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_3,plain,
% 2.82/0.99      ( ~ r1_lattice3(X0,X1,X2)
% 2.82/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.82/0.99      | m1_subset_1(sK0(X0,X2,X1),u1_struct_0(X0))
% 2.82/0.99      | r2_yellow_0(X0,X1)
% 2.82/0.99      | ~ v5_orders_2(X0)
% 2.82/0.99      | ~ l1_orders_2(X0) ),
% 2.82/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_598,plain,
% 2.82/0.99      ( ~ r1_lattice3(X0,X1,X2)
% 2.82/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.82/0.99      | m1_subset_1(sK0(X0,X2,X1),u1_struct_0(X0))
% 2.82/0.99      | r2_yellow_0(X0,X1)
% 2.82/0.99      | ~ l1_waybel_9(X0)
% 2.82/0.99      | ~ v5_orders_2(X0) ),
% 2.82/0.99      inference(resolution,[status(thm)],[c_11,c_3]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_1131,plain,
% 2.82/0.99      ( ~ r1_lattice3(X0,X1,X2)
% 2.82/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.82/0.99      | m1_subset_1(sK0(X0,X2,X1),u1_struct_0(X0))
% 2.82/0.99      | r2_yellow_0(X0,X1)
% 2.82/0.99      | ~ l1_waybel_9(X0)
% 2.82/0.99      | sK7 != X0 ),
% 2.82/0.99      inference(resolution_lifted,[status(thm)],[c_598,c_37]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_1132,plain,
% 2.82/0.99      ( ~ r1_lattice3(sK7,X0,X1)
% 2.82/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 2.82/0.99      | m1_subset_1(sK0(sK7,X1,X0),u1_struct_0(sK7))
% 2.82/0.99      | r2_yellow_0(sK7,X0)
% 2.82/0.99      | ~ l1_waybel_9(sK7) ),
% 2.82/0.99      inference(unflattening,[status(thm)],[c_1131]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_1136,plain,
% 2.82/0.99      ( r2_yellow_0(sK7,X0)
% 2.82/0.99      | m1_subset_1(sK0(sK7,X1,X0),u1_struct_0(sK7))
% 2.82/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 2.82/0.99      | ~ r1_lattice3(sK7,X0,X1) ),
% 2.82/0.99      inference(global_propositional_subsumption,
% 2.82/0.99                [status(thm)],
% 2.82/0.99                [c_1132,c_33]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_1137,plain,
% 2.82/0.99      ( ~ r1_lattice3(sK7,X0,X1)
% 2.82/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 2.82/0.99      | m1_subset_1(sK0(sK7,X1,X0),u1_struct_0(sK7))
% 2.82/0.99      | r2_yellow_0(sK7,X0) ),
% 2.82/0.99      inference(renaming,[status(thm)],[c_1136]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_4373,plain,
% 2.82/0.99      ( ~ r1_lattice3(sK7,X0_70,X0_68)
% 2.82/0.99      | ~ m1_subset_1(X0_68,u1_struct_0(sK7))
% 2.82/0.99      | m1_subset_1(sK0(sK7,X0_68,X0_70),u1_struct_0(sK7))
% 2.82/0.99      | r2_yellow_0(sK7,X0_70) ),
% 2.82/0.99      inference(subtyping,[status(esa)],[c_1137]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_4887,plain,
% 2.82/0.99      ( r1_lattice3(sK7,X0_70,X0_68) != iProver_top
% 2.82/0.99      | m1_subset_1(X0_68,u1_struct_0(sK7)) != iProver_top
% 2.82/0.99      | m1_subset_1(sK0(sK7,X0_68,X0_70),u1_struct_0(sK7)) = iProver_top
% 2.82/0.99      | r2_yellow_0(sK7,X0_70) = iProver_top ),
% 2.82/0.99      inference(predicate_to_equality,[status(thm)],[c_4373]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_6615,plain,
% 2.82/0.99      ( r3_waybel_9(sK7,sK8,X0_68) != iProver_top
% 2.82/0.99      | r1_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X1_68) != iProver_top
% 2.82/0.99      | r1_orders_2(sK7,sK0(sK7,X1_68,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))),X0_68) = iProver_top
% 2.82/0.99      | m1_subset_1(X0_68,u1_struct_0(sK7)) != iProver_top
% 2.82/0.99      | m1_subset_1(X1_68,u1_struct_0(sK7)) != iProver_top
% 2.82/0.99      | r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) = iProver_top ),
% 2.82/0.99      inference(forward_subsumption_resolution,
% 2.82/0.99                [status(thm)],
% 2.82/0.99                [c_5628,c_4887]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_1,plain,
% 2.82/0.99      ( ~ r1_lattice3(X0,X1,X2)
% 2.82/0.99      | ~ r1_orders_2(X0,sK0(X0,X2,X1),X2)
% 2.82/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.82/0.99      | r2_yellow_0(X0,X1)
% 2.82/0.99      | ~ v5_orders_2(X0)
% 2.82/0.99      | ~ l1_orders_2(X0) ),
% 2.82/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_644,plain,
% 2.82/0.99      ( ~ r1_lattice3(X0,X1,X2)
% 2.82/0.99      | ~ r1_orders_2(X0,sK0(X0,X2,X1),X2)
% 2.82/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.82/0.99      | r2_yellow_0(X0,X1)
% 2.82/0.99      | ~ l1_waybel_9(X0)
% 2.82/0.99      | ~ v5_orders_2(X0) ),
% 2.82/0.99      inference(resolution,[status(thm)],[c_11,c_1]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_1083,plain,
% 2.82/0.99      ( ~ r1_lattice3(X0,X1,X2)
% 2.82/0.99      | ~ r1_orders_2(X0,sK0(X0,X2,X1),X2)
% 2.82/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.82/0.99      | r2_yellow_0(X0,X1)
% 2.82/0.99      | ~ l1_waybel_9(X0)
% 2.82/0.99      | sK7 != X0 ),
% 2.82/0.99      inference(resolution_lifted,[status(thm)],[c_644,c_37]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_1084,plain,
% 2.82/0.99      ( ~ r1_lattice3(sK7,X0,X1)
% 2.82/0.99      | ~ r1_orders_2(sK7,sK0(sK7,X1,X0),X1)
% 2.82/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 2.82/0.99      | r2_yellow_0(sK7,X0)
% 2.82/0.99      | ~ l1_waybel_9(sK7) ),
% 2.82/0.99      inference(unflattening,[status(thm)],[c_1083]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_1088,plain,
% 2.82/0.99      ( r2_yellow_0(sK7,X0)
% 2.82/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 2.82/0.99      | ~ r1_orders_2(sK7,sK0(sK7,X1,X0),X1)
% 2.82/0.99      | ~ r1_lattice3(sK7,X0,X1) ),
% 2.82/0.99      inference(global_propositional_subsumption,
% 2.82/0.99                [status(thm)],
% 2.82/0.99                [c_1084,c_33]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_1089,plain,
% 2.82/0.99      ( ~ r1_lattice3(sK7,X0,X1)
% 2.82/0.99      | ~ r1_orders_2(sK7,sK0(sK7,X1,X0),X1)
% 2.82/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 2.82/0.99      | r2_yellow_0(sK7,X0) ),
% 2.82/0.99      inference(renaming,[status(thm)],[c_1088]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_4375,plain,
% 2.82/0.99      ( ~ r1_lattice3(sK7,X0_70,X0_68)
% 2.82/0.99      | ~ r1_orders_2(sK7,sK0(sK7,X0_68,X0_70),X0_68)
% 2.82/0.99      | ~ m1_subset_1(X0_68,u1_struct_0(sK7))
% 2.82/0.99      | r2_yellow_0(sK7,X0_70) ),
% 2.82/0.99      inference(subtyping,[status(esa)],[c_1089]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_4885,plain,
% 2.82/0.99      ( r1_lattice3(sK7,X0_70,X0_68) != iProver_top
% 2.82/0.99      | r1_orders_2(sK7,sK0(sK7,X0_68,X0_70),X0_68) != iProver_top
% 2.82/0.99      | m1_subset_1(X0_68,u1_struct_0(sK7)) != iProver_top
% 2.82/0.99      | r2_yellow_0(sK7,X0_70) = iProver_top ),
% 2.82/0.99      inference(predicate_to_equality,[status(thm)],[c_4375]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_6620,plain,
% 2.82/0.99      ( r3_waybel_9(sK7,sK8,X0_68) != iProver_top
% 2.82/0.99      | r1_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X0_68) != iProver_top
% 2.82/0.99      | m1_subset_1(X0_68,u1_struct_0(sK7)) != iProver_top
% 2.82/0.99      | r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) = iProver_top ),
% 2.82/0.99      inference(superposition,[status(thm)],[c_6615,c_4885]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_27,negated_conjecture,
% 2.82/0.99      ( v11_waybel_0(sK8,sK7) ),
% 2.82/0.99      inference(cnf_transformation,[],[f94]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_13,plain,
% 2.82/0.99      ( ~ v5_pre_topc(k4_waybel_1(X0,sK1(X0)),X0,X0)
% 2.82/0.99      | ~ r3_waybel_9(X0,X1,X2)
% 2.82/0.99      | r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
% 2.82/0.99      | ~ v11_waybel_0(X1,X0)
% 2.82/0.99      | ~ l1_waybel_0(X1,X0)
% 2.82/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.82/0.99      | ~ v2_pre_topc(X0)
% 2.82/0.99      | ~ v8_pre_topc(X0)
% 2.82/0.99      | ~ v3_orders_2(X0)
% 2.82/0.99      | ~ v2_lattice3(X0)
% 2.82/0.99      | ~ v1_compts_1(X0)
% 2.82/0.99      | ~ v4_orders_2(X1)
% 2.82/0.99      | ~ v4_orders_2(X0)
% 2.82/0.99      | ~ v7_waybel_0(X1)
% 2.82/0.99      | ~ l1_waybel_9(X0)
% 2.82/0.99      | ~ v5_orders_2(X0)
% 2.82/0.99      | ~ v1_lattice3(X0)
% 2.82/0.99      | v2_struct_0(X1) ),
% 2.82/0.99      inference(cnf_transformation,[],[f98]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_741,plain,
% 2.82/0.99      ( ~ r3_waybel_9(X0,X1,X2)
% 2.82/0.99      | r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
% 2.82/0.99      | ~ v11_waybel_0(X1,X0)
% 2.82/0.99      | ~ l1_waybel_0(X1,X0)
% 2.82/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.82/0.99      | ~ m1_subset_1(X3,u1_struct_0(sK7))
% 2.82/0.99      | ~ v2_pre_topc(X0)
% 2.82/0.99      | ~ v8_pre_topc(X0)
% 2.82/0.99      | ~ v3_orders_2(X0)
% 2.82/0.99      | ~ v2_lattice3(X0)
% 2.82/0.99      | ~ v1_compts_1(X0)
% 2.82/0.99      | ~ v4_orders_2(X0)
% 2.82/0.99      | ~ v4_orders_2(X1)
% 2.82/0.99      | ~ v7_waybel_0(X1)
% 2.82/0.99      | ~ l1_waybel_9(X0)
% 2.82/0.99      | ~ v5_orders_2(X0)
% 2.82/0.99      | ~ v1_lattice3(X0)
% 2.82/0.99      | v2_struct_0(X1)
% 2.82/0.99      | k4_waybel_1(X0,sK1(X0)) != k4_waybel_1(sK7,X3)
% 2.82/0.99      | sK7 != X0 ),
% 2.82/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_32]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_742,plain,
% 2.82/0.99      ( ~ r3_waybel_9(sK7,X0,X1)
% 2.82/0.99      | r1_lattice3(sK7,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK7),u1_waybel_0(sK7,X0)),X1)
% 2.82/0.99      | ~ v11_waybel_0(X0,sK7)
% 2.82/0.99      | ~ l1_waybel_0(X0,sK7)
% 2.82/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 2.82/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 2.82/0.99      | ~ v2_pre_topc(sK7)
% 2.82/0.99      | ~ v8_pre_topc(sK7)
% 2.82/0.99      | ~ v3_orders_2(sK7)
% 2.82/0.99      | ~ v2_lattice3(sK7)
% 2.82/0.99      | ~ v1_compts_1(sK7)
% 2.82/0.99      | ~ v4_orders_2(X0)
% 2.82/0.99      | ~ v4_orders_2(sK7)
% 2.82/0.99      | ~ v7_waybel_0(X0)
% 2.82/0.99      | ~ l1_waybel_9(sK7)
% 2.82/0.99      | ~ v5_orders_2(sK7)
% 2.82/0.99      | ~ v1_lattice3(sK7)
% 2.82/0.99      | v2_struct_0(X0)
% 2.82/0.99      | k4_waybel_1(sK7,sK1(sK7)) != k4_waybel_1(sK7,X2) ),
% 2.82/0.99      inference(unflattening,[status(thm)],[c_741]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_746,plain,
% 2.82/0.99      ( ~ v7_waybel_0(X0)
% 2.82/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 2.82/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 2.82/0.99      | ~ l1_waybel_0(X0,sK7)
% 2.82/0.99      | ~ v11_waybel_0(X0,sK7)
% 2.82/0.99      | r1_lattice3(sK7,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK7),u1_waybel_0(sK7,X0)),X1)
% 2.82/0.99      | ~ r3_waybel_9(sK7,X0,X1)
% 2.82/0.99      | ~ v4_orders_2(X0)
% 2.82/0.99      | v2_struct_0(X0)
% 2.82/0.99      | k4_waybel_1(sK7,sK1(sK7)) != k4_waybel_1(sK7,X2) ),
% 2.82/0.99      inference(global_propositional_subsumption,
% 2.82/0.99                [status(thm)],
% 2.82/0.99                [c_742,c_41,c_40,c_39,c_38,c_37,c_36,c_35,c_34,c_33]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_747,plain,
% 2.82/0.99      ( ~ r3_waybel_9(sK7,X0,X1)
% 2.82/0.99      | r1_lattice3(sK7,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK7),u1_waybel_0(sK7,X0)),X1)
% 2.82/0.99      | ~ v11_waybel_0(X0,sK7)
% 2.82/0.99      | ~ l1_waybel_0(X0,sK7)
% 2.82/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 2.82/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 2.82/0.99      | ~ v4_orders_2(X0)
% 2.82/0.99      | ~ v7_waybel_0(X0)
% 2.82/0.99      | v2_struct_0(X0)
% 2.82/0.99      | k4_waybel_1(sK7,sK1(sK7)) != k4_waybel_1(sK7,X2) ),
% 2.82/0.99      inference(renaming,[status(thm)],[c_746]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_968,plain,
% 2.82/0.99      ( ~ r3_waybel_9(sK7,X0,X1)
% 2.82/0.99      | r1_lattice3(sK7,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK7),u1_waybel_0(sK7,X0)),X1)
% 2.82/0.99      | ~ l1_waybel_0(X0,sK7)
% 2.82/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 2.82/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 2.82/0.99      | ~ v4_orders_2(X0)
% 2.82/0.99      | ~ v7_waybel_0(X0)
% 2.82/0.99      | v2_struct_0(X0)
% 2.82/0.99      | k4_waybel_1(sK7,sK1(sK7)) != k4_waybel_1(sK7,X2)
% 2.82/0.99      | sK8 != X0
% 2.82/0.99      | sK7 != sK7 ),
% 2.82/0.99      inference(resolution_lifted,[status(thm)],[c_27,c_747]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_969,plain,
% 2.82/0.99      ( ~ r3_waybel_9(sK7,sK8,X0)
% 2.82/0.99      | r1_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X0)
% 2.82/0.99      | ~ l1_waybel_0(sK8,sK7)
% 2.82/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 2.82/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 2.82/0.99      | ~ v4_orders_2(sK8)
% 2.82/0.99      | ~ v7_waybel_0(sK8)
% 2.82/0.99      | v2_struct_0(sK8)
% 2.82/0.99      | k4_waybel_1(sK7,sK1(sK7)) != k4_waybel_1(sK7,X1) ),
% 2.82/0.99      inference(unflattening,[status(thm)],[c_968]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_973,plain,
% 2.82/0.99      ( ~ m1_subset_1(X1,u1_struct_0(sK7))
% 2.82/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 2.82/0.99      | ~ r3_waybel_9(sK7,sK8,X0)
% 2.82/0.99      | r1_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X0)
% 2.82/0.99      | k4_waybel_1(sK7,sK1(sK7)) != k4_waybel_1(sK7,X1) ),
% 2.82/0.99      inference(global_propositional_subsumption,
% 2.82/0.99                [status(thm)],
% 2.82/0.99                [c_969,c_31,c_30,c_29,c_28]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_974,plain,
% 2.82/0.99      ( ~ r3_waybel_9(sK7,sK8,X0)
% 2.82/0.99      | r1_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X0)
% 2.82/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 2.82/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 2.82/0.99      | k4_waybel_1(sK7,sK1(sK7)) != k4_waybel_1(sK7,X1) ),
% 2.82/0.99      inference(renaming,[status(thm)],[c_973]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_4376,plain,
% 2.82/0.99      ( ~ r3_waybel_9(sK7,sK8,X0_68)
% 2.82/0.99      | r1_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X0_68)
% 2.82/0.99      | ~ m1_subset_1(X1_68,u1_struct_0(sK7))
% 2.82/0.99      | ~ m1_subset_1(X0_68,u1_struct_0(sK7))
% 2.82/0.99      | k4_waybel_1(sK7,sK1(sK7)) != k4_waybel_1(sK7,X1_68) ),
% 2.82/0.99      inference(subtyping,[status(esa)],[c_974]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_4384,plain,
% 2.82/0.99      ( ~ r3_waybel_9(sK7,sK8,X0_68)
% 2.82/0.99      | r1_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X0_68)
% 2.82/0.99      | ~ m1_subset_1(X0_68,u1_struct_0(sK7))
% 2.82/0.99      | ~ sP3_iProver_split ),
% 2.82/0.99      inference(splitting,
% 2.82/0.99                [splitting(split),new_symbols(definition,[sP3_iProver_split])],
% 2.82/0.99                [c_4376]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_4883,plain,
% 2.82/0.99      ( r3_waybel_9(sK7,sK8,X0_68) != iProver_top
% 2.82/0.99      | r1_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X0_68) = iProver_top
% 2.82/0.99      | m1_subset_1(X0_68,u1_struct_0(sK7)) != iProver_top
% 2.82/0.99      | sP3_iProver_split != iProver_top ),
% 2.82/0.99      inference(predicate_to_equality,[status(thm)],[c_4384]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_14,plain,
% 2.82/0.99      ( ~ r3_waybel_9(X0,X1,X2)
% 2.82/0.99      | r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
% 2.82/0.99      | ~ v11_waybel_0(X1,X0)
% 2.82/0.99      | ~ l1_waybel_0(X1,X0)
% 2.82/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.82/0.99      | m1_subset_1(sK1(X0),u1_struct_0(X0))
% 2.82/0.99      | ~ v2_pre_topc(X0)
% 2.82/0.99      | ~ v8_pre_topc(X0)
% 2.82/0.99      | ~ v3_orders_2(X0)
% 2.82/0.99      | ~ v2_lattice3(X0)
% 2.82/0.99      | ~ v1_compts_1(X0)
% 2.82/0.99      | ~ v4_orders_2(X1)
% 2.82/0.99      | ~ v4_orders_2(X0)
% 2.82/0.99      | ~ v7_waybel_0(X1)
% 2.82/0.99      | ~ l1_waybel_9(X0)
% 2.82/0.99      | ~ v5_orders_2(X0)
% 2.82/0.99      | ~ v1_lattice3(X0)
% 2.82/0.99      | v2_struct_0(X1) ),
% 2.82/0.99      inference(cnf_transformation,[],[f99]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_917,plain,
% 2.82/0.99      ( ~ r3_waybel_9(X0,X1,X2)
% 2.82/0.99      | r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
% 2.82/0.99      | ~ l1_waybel_0(X1,X0)
% 2.82/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.82/0.99      | m1_subset_1(sK1(X0),u1_struct_0(X0))
% 2.82/0.99      | ~ v2_pre_topc(X0)
% 2.82/0.99      | ~ v8_pre_topc(X0)
% 2.82/0.99      | ~ v3_orders_2(X0)
% 2.82/0.99      | ~ v2_lattice3(X0)
% 2.82/0.99      | ~ v1_compts_1(X0)
% 2.82/0.99      | ~ v4_orders_2(X0)
% 2.82/0.99      | ~ v4_orders_2(X1)
% 2.82/0.99      | ~ v7_waybel_0(X1)
% 2.82/0.99      | ~ l1_waybel_9(X0)
% 2.82/0.99      | ~ v5_orders_2(X0)
% 2.82/0.99      | ~ v1_lattice3(X0)
% 2.82/0.99      | v2_struct_0(X1)
% 2.82/0.99      | sK8 != X1
% 2.82/0.99      | sK7 != X0 ),
% 2.82/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_27]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_918,plain,
% 2.82/0.99      ( ~ r3_waybel_9(sK7,sK8,X0)
% 2.82/0.99      | r1_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X0)
% 2.82/0.99      | ~ l1_waybel_0(sK8,sK7)
% 2.82/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 2.82/0.99      | m1_subset_1(sK1(sK7),u1_struct_0(sK7))
% 2.82/0.99      | ~ v2_pre_topc(sK7)
% 2.82/0.99      | ~ v8_pre_topc(sK7)
% 2.82/0.99      | ~ v3_orders_2(sK7)
% 2.82/0.99      | ~ v2_lattice3(sK7)
% 2.82/0.99      | ~ v1_compts_1(sK7)
% 2.82/0.99      | ~ v4_orders_2(sK8)
% 2.82/0.99      | ~ v4_orders_2(sK7)
% 2.82/0.99      | ~ v7_waybel_0(sK8)
% 2.82/0.99      | ~ l1_waybel_9(sK7)
% 2.82/0.99      | ~ v5_orders_2(sK7)
% 2.82/0.99      | ~ v1_lattice3(sK7)
% 2.82/0.99      | v2_struct_0(sK8) ),
% 2.82/0.99      inference(unflattening,[status(thm)],[c_917]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_922,plain,
% 2.82/0.99      ( r1_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X0)
% 2.82/0.99      | ~ r3_waybel_9(sK7,sK8,X0)
% 2.82/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 2.82/0.99      | m1_subset_1(sK1(sK7),u1_struct_0(sK7)) ),
% 2.82/0.99      inference(global_propositional_subsumption,
% 2.82/0.99                [status(thm)],
% 2.82/0.99                [c_918,c_41,c_40,c_39,c_38,c_37,c_36,c_35,c_34,c_33,c_31,
% 2.82/0.99                 c_30,c_29,c_28]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_923,plain,
% 2.82/0.99      ( ~ r3_waybel_9(sK7,sK8,X0)
% 2.82/0.99      | r1_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X0)
% 2.82/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 2.82/0.99      | m1_subset_1(sK1(sK7),u1_struct_0(sK7)) ),
% 2.82/0.99      inference(renaming,[status(thm)],[c_922]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_4378,plain,
% 2.82/0.99      ( ~ r3_waybel_9(sK7,sK8,X0_68)
% 2.82/0.99      | r1_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X0_68)
% 2.82/0.99      | ~ m1_subset_1(X0_68,u1_struct_0(sK7))
% 2.82/0.99      | m1_subset_1(sK1(sK7),u1_struct_0(sK7)) ),
% 2.82/0.99      inference(subtyping,[status(esa)],[c_923]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_4410,plain,
% 2.82/0.99      ( r3_waybel_9(sK7,sK8,X0_68) != iProver_top
% 2.82/0.99      | r1_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X0_68) = iProver_top
% 2.82/0.99      | m1_subset_1(X0_68,u1_struct_0(sK7)) != iProver_top
% 2.82/0.99      | m1_subset_1(sK1(sK7),u1_struct_0(sK7)) = iProver_top ),
% 2.82/0.99      inference(predicate_to_equality,[status(thm)],[c_4378]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_4385,plain,
% 2.82/0.99      ( sP3_iProver_split | sP2_iProver_split ),
% 2.82/0.99      inference(splitting,
% 2.82/0.99                [splitting(split),new_symbols(definition,[])],
% 2.82/0.99                [c_4376]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_4420,plain,
% 2.82/0.99      ( sP3_iProver_split = iProver_top
% 2.82/0.99      | sP2_iProver_split = iProver_top ),
% 2.82/0.99      inference(predicate_to_equality,[status(thm)],[c_4385]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_4421,plain,
% 2.82/0.99      ( r3_waybel_9(sK7,sK8,X0_68) != iProver_top
% 2.82/0.99      | r1_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X0_68) = iProver_top
% 2.82/0.99      | m1_subset_1(X0_68,u1_struct_0(sK7)) != iProver_top
% 2.82/0.99      | sP3_iProver_split != iProver_top ),
% 2.82/0.99      inference(predicate_to_equality,[status(thm)],[c_4384]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_4383,plain,
% 2.82/0.99      ( ~ m1_subset_1(X0_68,u1_struct_0(sK7))
% 2.82/0.99      | k4_waybel_1(sK7,sK1(sK7)) != k4_waybel_1(sK7,X0_68)
% 2.82/0.99      | ~ sP2_iProver_split ),
% 2.82/0.99      inference(splitting,
% 2.82/0.99                [splitting(split),new_symbols(definition,[sP2_iProver_split])],
% 2.82/0.99                [c_4376]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_4884,plain,
% 2.82/0.99      ( k4_waybel_1(sK7,sK1(sK7)) != k4_waybel_1(sK7,X0_68)
% 2.82/0.99      | m1_subset_1(X0_68,u1_struct_0(sK7)) != iProver_top
% 2.82/0.99      | sP2_iProver_split != iProver_top ),
% 2.82/0.99      inference(predicate_to_equality,[status(thm)],[c_4383]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_5182,plain,
% 2.82/0.99      ( m1_subset_1(sK1(sK7),u1_struct_0(sK7)) != iProver_top
% 2.82/0.99      | sP2_iProver_split != iProver_top ),
% 2.82/0.99      inference(equality_resolution,[status(thm)],[c_4884]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_5533,plain,
% 2.82/0.99      ( m1_subset_1(X0_68,u1_struct_0(sK7)) != iProver_top
% 2.82/0.99      | r1_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X0_68) = iProver_top
% 2.82/0.99      | r3_waybel_9(sK7,sK8,X0_68) != iProver_top ),
% 2.82/0.99      inference(global_propositional_subsumption,
% 2.82/0.99                [status(thm)],
% 2.82/0.99                [c_4883,c_4410,c_4420,c_4421,c_5182]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_5534,plain,
% 2.82/0.99      ( r3_waybel_9(sK7,sK8,X0_68) != iProver_top
% 2.82/0.99      | r1_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X0_68) = iProver_top
% 2.82/0.99      | m1_subset_1(X0_68,u1_struct_0(sK7)) != iProver_top ),
% 2.82/0.99      inference(renaming,[status(thm)],[c_5533]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_6633,plain,
% 2.82/0.99      ( r3_waybel_9(sK7,sK8,X0_68) != iProver_top
% 2.82/0.99      | m1_subset_1(X0_68,u1_struct_0(sK7)) != iProver_top
% 2.82/0.99      | r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) = iProver_top ),
% 2.82/0.99      inference(global_propositional_subsumption,
% 2.82/0.99                [status(thm)],
% 2.82/0.99                [c_6620,c_4410,c_4420,c_4421,c_5182]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_6642,plain,
% 2.82/0.99      ( m1_subset_1(sK3(sK7,sK8),u1_struct_0(sK7)) != iProver_top
% 2.82/0.99      | r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) = iProver_top ),
% 2.82/0.99      inference(superposition,[status(thm)],[c_4894,c_6633]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_54,plain,
% 2.82/0.99      ( v2_struct_0(sK8) != iProver_top ),
% 2.82/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_55,plain,
% 2.82/0.99      ( v4_orders_2(sK8) = iProver_top ),
% 2.82/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_56,plain,
% 2.82/0.99      ( v7_waybel_0(sK8) = iProver_top ),
% 2.82/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_18,plain,
% 2.82/0.99      ( ~ l1_waybel_0(X0,X1)
% 2.82/0.99      | m1_subset_1(sK3(X1,X0),u1_struct_0(X1))
% 2.82/0.99      | ~ v2_pre_topc(X1)
% 2.82/0.99      | ~ v8_pre_topc(X1)
% 2.82/0.99      | ~ v1_compts_1(X1)
% 2.82/0.99      | ~ v4_orders_2(X0)
% 2.82/0.99      | ~ v7_waybel_0(X0)
% 2.82/0.99      | ~ l1_pre_topc(X1)
% 2.82/0.99      | v2_struct_0(X1)
% 2.82/0.99      | v2_struct_0(X0) ),
% 2.82/0.99      inference(cnf_transformation,[],[f71]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_2279,plain,
% 2.82/0.99      ( ~ l1_waybel_0(X0,X1)
% 2.82/0.99      | m1_subset_1(sK3(X1,X0),u1_struct_0(X1))
% 2.82/0.99      | ~ v2_pre_topc(X1)
% 2.82/0.99      | ~ v8_pre_topc(X1)
% 2.82/0.99      | ~ v1_compts_1(X1)
% 2.82/0.99      | ~ v4_orders_2(X0)
% 2.82/0.99      | ~ v7_waybel_0(X0)
% 2.82/0.99      | v2_struct_0(X0)
% 2.82/0.99      | v2_struct_0(X1)
% 2.82/0.99      | sK7 != X1 ),
% 2.82/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_1316]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_2280,plain,
% 2.82/0.99      ( ~ l1_waybel_0(X0,sK7)
% 2.82/0.99      | m1_subset_1(sK3(sK7,X0),u1_struct_0(sK7))
% 2.82/0.99      | ~ v2_pre_topc(sK7)
% 2.82/0.99      | ~ v8_pre_topc(sK7)
% 2.82/0.99      | ~ v1_compts_1(sK7)
% 2.82/0.99      | ~ v4_orders_2(X0)
% 2.82/0.99      | ~ v7_waybel_0(X0)
% 2.82/0.99      | v2_struct_0(X0)
% 2.82/0.99      | v2_struct_0(sK7) ),
% 2.82/0.99      inference(unflattening,[status(thm)],[c_2279]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_2284,plain,
% 2.82/0.99      ( v2_struct_0(X0)
% 2.82/0.99      | ~ v7_waybel_0(X0)
% 2.82/0.99      | ~ v4_orders_2(X0)
% 2.82/0.99      | ~ l1_waybel_0(X0,sK7)
% 2.82/0.99      | m1_subset_1(sK3(sK7,X0),u1_struct_0(sK7)) ),
% 2.82/0.99      inference(global_propositional_subsumption,
% 2.82/0.99                [status(thm)],
% 2.82/0.99                [c_2280,c_41,c_40,c_36,c_34,c_33,c_103,c_136]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_2285,plain,
% 2.82/0.99      ( ~ l1_waybel_0(X0,sK7)
% 2.82/0.99      | m1_subset_1(sK3(sK7,X0),u1_struct_0(sK7))
% 2.82/0.99      | ~ v4_orders_2(X0)
% 2.82/0.99      | ~ v7_waybel_0(X0)
% 2.82/0.99      | v2_struct_0(X0) ),
% 2.82/0.99      inference(renaming,[status(thm)],[c_2284]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_2368,plain,
% 2.82/0.99      ( m1_subset_1(sK3(sK7,X0),u1_struct_0(sK7))
% 2.82/0.99      | ~ v4_orders_2(X0)
% 2.82/0.99      | ~ v7_waybel_0(X0)
% 2.82/0.99      | v2_struct_0(X0)
% 2.82/0.99      | sK8 != X0
% 2.82/0.99      | sK7 != sK7 ),
% 2.82/0.99      inference(resolution_lifted,[status(thm)],[c_28,c_2285]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_2369,plain,
% 2.82/0.99      ( m1_subset_1(sK3(sK7,sK8),u1_struct_0(sK7))
% 2.82/0.99      | ~ v4_orders_2(sK8)
% 2.82/0.99      | ~ v7_waybel_0(sK8)
% 2.82/0.99      | v2_struct_0(sK8) ),
% 2.82/0.99      inference(unflattening,[status(thm)],[c_2368]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_2370,plain,
% 2.82/0.99      ( m1_subset_1(sK3(sK7,sK8),u1_struct_0(sK7)) = iProver_top
% 2.82/0.99      | v4_orders_2(sK8) != iProver_top
% 2.82/0.99      | v7_waybel_0(sK8) != iProver_top
% 2.82/0.99      | v2_struct_0(sK8) = iProver_top ),
% 2.82/0.99      inference(predicate_to_equality,[status(thm)],[c_2369]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_6718,plain,
% 2.82/0.99      ( r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) = iProver_top ),
% 2.82/0.99      inference(global_propositional_subsumption,
% 2.82/0.99                [status(thm)],
% 2.82/0.99                [c_6642,c_54,c_55,c_56,c_2370]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_21,plain,
% 2.82/0.99      ( ~ r3_waybel_9(X0,X1,X2)
% 2.82/0.99      | r3_waybel_9(X0,X1,sK4(X0,X1))
% 2.82/0.99      | r2_hidden(X2,k10_yellow_6(X0,X1))
% 2.82/0.99      | ~ l1_waybel_0(X1,X0)
% 2.82/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.82/0.99      | ~ v2_pre_topc(X0)
% 2.82/0.99      | ~ v8_pre_topc(X0)
% 2.82/0.99      | ~ v1_compts_1(X0)
% 2.82/0.99      | ~ v4_orders_2(X1)
% 2.82/0.99      | ~ v7_waybel_0(X1)
% 2.82/0.99      | ~ l1_pre_topc(X0)
% 2.82/0.99      | v2_struct_0(X0)
% 2.82/0.99      | v2_struct_0(X1) ),
% 2.82/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_9,plain,
% 2.82/0.99      ( ~ l1_waybel_0(X0,X1)
% 2.82/0.99      | r2_waybel_9(X1,X0)
% 2.82/0.99      | ~ r2_yellow_0(X1,k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0)))
% 2.82/0.99      | ~ l1_orders_2(X1) ),
% 2.82/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_26,negated_conjecture,
% 2.82/0.99      ( ~ r2_hidden(k1_waybel_9(sK7,sK8),k10_yellow_6(sK7,sK8))
% 2.82/0.99      | ~ r2_waybel_9(sK7,sK8) ),
% 2.82/0.99      inference(cnf_transformation,[],[f95]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_466,plain,
% 2.82/0.99      ( ~ r2_hidden(k1_waybel_9(sK7,sK8),k10_yellow_6(sK7,sK8))
% 2.82/0.99      | ~ l1_waybel_0(X0,X1)
% 2.82/0.99      | ~ r2_yellow_0(X1,k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0)))
% 2.82/0.99      | ~ l1_orders_2(X1)
% 2.82/0.99      | sK8 != X0
% 2.82/0.99      | sK7 != X1 ),
% 2.82/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_26]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_467,plain,
% 2.82/0.99      ( ~ r2_hidden(k1_waybel_9(sK7,sK8),k10_yellow_6(sK7,sK8))
% 2.82/0.99      | ~ l1_waybel_0(sK8,sK7)
% 2.82/0.99      | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 2.82/0.99      | ~ l1_orders_2(sK7) ),
% 2.82/0.99      inference(unflattening,[status(thm)],[c_466]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_469,plain,
% 2.82/0.99      ( ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 2.82/0.99      | ~ r2_hidden(k1_waybel_9(sK7,sK8),k10_yellow_6(sK7,sK8)) ),
% 2.82/0.99      inference(global_propositional_subsumption,
% 2.82/0.99                [status(thm)],
% 2.82/0.99                [c_467,c_33,c_28,c_103]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_470,plain,
% 2.82/0.99      ( ~ r2_hidden(k1_waybel_9(sK7,sK8),k10_yellow_6(sK7,sK8))
% 2.82/0.99      | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) ),
% 2.82/0.99      inference(renaming,[status(thm)],[c_469]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_1908,plain,
% 2.82/0.99      ( ~ r3_waybel_9(X0,X1,X2)
% 2.82/0.99      | r3_waybel_9(X0,X1,sK4(X0,X1))
% 2.82/0.99      | ~ l1_waybel_0(X1,X0)
% 2.82/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.82/0.99      | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 2.82/0.99      | ~ v2_pre_topc(X0)
% 2.82/0.99      | ~ v8_pre_topc(X0)
% 2.82/0.99      | ~ v1_compts_1(X0)
% 2.82/0.99      | ~ v4_orders_2(X1)
% 2.82/0.99      | ~ v7_waybel_0(X1)
% 2.82/0.99      | ~ l1_pre_topc(X0)
% 2.82/0.99      | v2_struct_0(X0)
% 2.82/0.99      | v2_struct_0(X1)
% 2.82/0.99      | k1_waybel_9(sK7,sK8) != X2
% 2.82/0.99      | k10_yellow_6(X0,X1) != k10_yellow_6(sK7,sK8) ),
% 2.82/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_470]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_1909,plain,
% 2.82/0.99      ( ~ r3_waybel_9(X0,X1,k1_waybel_9(sK7,sK8))
% 2.82/0.99      | r3_waybel_9(X0,X1,sK4(X0,X1))
% 2.82/0.99      | ~ l1_waybel_0(X1,X0)
% 2.82/0.99      | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(X0))
% 2.82/0.99      | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 2.82/0.99      | ~ v2_pre_topc(X0)
% 2.82/0.99      | ~ v8_pre_topc(X0)
% 2.82/0.99      | ~ v1_compts_1(X0)
% 2.82/0.99      | ~ v4_orders_2(X1)
% 2.82/0.99      | ~ v7_waybel_0(X1)
% 2.82/0.99      | ~ l1_pre_topc(X0)
% 2.82/0.99      | v2_struct_0(X0)
% 2.82/0.99      | v2_struct_0(X1)
% 2.82/0.99      | k10_yellow_6(X0,X1) != k10_yellow_6(sK7,sK8) ),
% 2.82/0.99      inference(unflattening,[status(thm)],[c_1908]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_2135,plain,
% 2.82/0.99      ( ~ r3_waybel_9(X0,X1,k1_waybel_9(sK7,sK8))
% 2.82/0.99      | r3_waybel_9(X0,X1,sK4(X0,X1))
% 2.82/0.99      | ~ l1_waybel_0(X1,X0)
% 2.82/0.99      | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(X0))
% 2.82/0.99      | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 2.82/0.99      | ~ v2_pre_topc(X0)
% 2.82/0.99      | ~ v8_pre_topc(X0)
% 2.82/0.99      | ~ v1_compts_1(X0)
% 2.82/0.99      | ~ v4_orders_2(X1)
% 2.82/0.99      | ~ v7_waybel_0(X1)
% 2.82/0.99      | v2_struct_0(X0)
% 2.82/0.99      | v2_struct_0(X1)
% 2.82/0.99      | k10_yellow_6(X0,X1) != k10_yellow_6(sK7,sK8)
% 2.82/0.99      | sK7 != X0 ),
% 2.82/0.99      inference(resolution_lifted,[status(thm)],[c_1909,c_1316]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_2136,plain,
% 2.82/0.99      ( ~ r3_waybel_9(sK7,X0,k1_waybel_9(sK7,sK8))
% 2.82/0.99      | r3_waybel_9(sK7,X0,sK4(sK7,X0))
% 2.82/0.99      | ~ l1_waybel_0(X0,sK7)
% 2.82/0.99      | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
% 2.82/0.99      | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 2.82/0.99      | ~ v2_pre_topc(sK7)
% 2.82/0.99      | ~ v8_pre_topc(sK7)
% 2.82/0.99      | ~ v1_compts_1(sK7)
% 2.82/0.99      | ~ v4_orders_2(X0)
% 2.82/0.99      | ~ v7_waybel_0(X0)
% 2.82/0.99      | v2_struct_0(X0)
% 2.82/0.99      | v2_struct_0(sK7)
% 2.82/0.99      | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8) ),
% 2.82/0.99      inference(unflattening,[status(thm)],[c_2135]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_2140,plain,
% 2.82/0.99      ( v2_struct_0(X0)
% 2.82/0.99      | ~ v7_waybel_0(X0)
% 2.82/0.99      | ~ v4_orders_2(X0)
% 2.82/0.99      | ~ r3_waybel_9(sK7,X0,k1_waybel_9(sK7,sK8))
% 2.82/0.99      | r3_waybel_9(sK7,X0,sK4(sK7,X0))
% 2.82/0.99      | ~ l1_waybel_0(X0,sK7)
% 2.82/0.99      | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
% 2.82/0.99      | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 2.82/0.99      | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8) ),
% 2.82/0.99      inference(global_propositional_subsumption,
% 2.82/0.99                [status(thm)],
% 2.82/0.99                [c_2136,c_41,c_40,c_36,c_34,c_33,c_103,c_136]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_2141,plain,
% 2.82/0.99      ( ~ r3_waybel_9(sK7,X0,k1_waybel_9(sK7,sK8))
% 2.82/0.99      | r3_waybel_9(sK7,X0,sK4(sK7,X0))
% 2.82/0.99      | ~ l1_waybel_0(X0,sK7)
% 2.82/0.99      | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
% 2.82/0.99      | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 2.82/0.99      | ~ v4_orders_2(X0)
% 2.82/0.99      | ~ v7_waybel_0(X0)
% 2.82/0.99      | v2_struct_0(X0)
% 2.82/0.99      | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8) ),
% 2.82/0.99      inference(renaming,[status(thm)],[c_2140]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_2436,plain,
% 2.82/0.99      ( ~ r3_waybel_9(sK7,X0,k1_waybel_9(sK7,sK8))
% 2.82/0.99      | r3_waybel_9(sK7,X0,sK4(sK7,X0))
% 2.82/0.99      | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
% 2.82/0.99      | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 2.82/0.99      | ~ v4_orders_2(X0)
% 2.82/0.99      | ~ v7_waybel_0(X0)
% 2.82/0.99      | v2_struct_0(X0)
% 2.82/0.99      | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8)
% 2.82/0.99      | sK8 != X0
% 2.82/0.99      | sK7 != sK7 ),
% 2.82/0.99      inference(resolution_lifted,[status(thm)],[c_28,c_2141]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_2437,plain,
% 2.82/0.99      ( ~ r3_waybel_9(sK7,sK8,k1_waybel_9(sK7,sK8))
% 2.82/0.99      | r3_waybel_9(sK7,sK8,sK4(sK7,sK8))
% 2.82/0.99      | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
% 2.82/0.99      | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 2.82/0.99      | ~ v4_orders_2(sK8)
% 2.82/0.99      | ~ v7_waybel_0(sK8)
% 2.82/0.99      | v2_struct_0(sK8)
% 2.82/0.99      | k10_yellow_6(sK7,sK8) != k10_yellow_6(sK7,sK8) ),
% 2.82/0.99      inference(unflattening,[status(thm)],[c_2436]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_2439,plain,
% 2.82/0.99      ( ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 2.82/0.99      | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
% 2.82/0.99      | r3_waybel_9(sK7,sK8,sK4(sK7,sK8))
% 2.82/0.99      | ~ r3_waybel_9(sK7,sK8,k1_waybel_9(sK7,sK8))
% 2.82/0.99      | k10_yellow_6(sK7,sK8) != k10_yellow_6(sK7,sK8) ),
% 2.82/0.99      inference(global_propositional_subsumption,
% 2.82/0.99                [status(thm)],
% 2.82/0.99                [c_2437,c_31,c_30,c_29]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_2440,plain,
% 2.82/0.99      ( ~ r3_waybel_9(sK7,sK8,k1_waybel_9(sK7,sK8))
% 2.82/0.99      | r3_waybel_9(sK7,sK8,sK4(sK7,sK8))
% 2.82/0.99      | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
% 2.82/0.99      | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 2.82/0.99      | k10_yellow_6(sK7,sK8) != k10_yellow_6(sK7,sK8) ),
% 2.82/0.99      inference(renaming,[status(thm)],[c_2439]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_3460,plain,
% 2.82/0.99      ( ~ r3_waybel_9(sK7,sK8,k1_waybel_9(sK7,sK8))
% 2.82/0.99      | r3_waybel_9(sK7,sK8,sK4(sK7,sK8))
% 2.82/0.99      | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
% 2.82/0.99      | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) ),
% 2.82/0.99      inference(equality_resolution_simp,[status(thm)],[c_2440]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_4361,plain,
% 2.82/0.99      ( ~ r3_waybel_9(sK7,sK8,k1_waybel_9(sK7,sK8))
% 2.82/0.99      | r3_waybel_9(sK7,sK8,sK4(sK7,sK8))
% 2.82/0.99      | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
% 2.82/0.99      | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) ),
% 2.82/0.99      inference(subtyping,[status(esa)],[c_3460]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_4901,plain,
% 2.82/0.99      ( r3_waybel_9(sK7,sK8,k1_waybel_9(sK7,sK8)) != iProver_top
% 2.82/0.99      | r3_waybel_9(sK7,sK8,sK4(sK7,sK8)) = iProver_top
% 2.82/0.99      | m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7)) != iProver_top
% 2.82/0.99      | r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) != iProver_top ),
% 2.82/0.99      inference(predicate_to_equality,[status(thm)],[c_4361]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_2381,plain,
% 2.82/0.99      ( r3_waybel_9(sK7,sK8,sK3(sK7,sK8)) = iProver_top
% 2.82/0.99      | v4_orders_2(sK8) != iProver_top
% 2.82/0.99      | v7_waybel_0(sK8) != iProver_top
% 2.82/0.99      | v2_struct_0(sK8) = iProver_top ),
% 2.82/0.99      inference(predicate_to_equality,[status(thm)],[c_2380]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_3461,plain,
% 2.82/0.99      ( r3_waybel_9(sK7,sK8,k1_waybel_9(sK7,sK8)) != iProver_top
% 2.82/0.99      | r3_waybel_9(sK7,sK8,sK4(sK7,sK8)) = iProver_top
% 2.82/0.99      | m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7)) != iProver_top
% 2.82/0.99      | r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) != iProver_top ),
% 2.82/0.99      inference(predicate_to_equality,[status(thm)],[c_3460]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_24,plain,
% 2.82/0.99      ( ~ v5_pre_topc(k4_waybel_1(X0,sK6(X0)),X0,X0)
% 2.82/0.99      | ~ r3_waybel_9(X0,X1,X2)
% 2.82/0.99      | ~ v11_waybel_0(X1,X0)
% 2.82/0.99      | ~ l1_waybel_0(X1,X0)
% 2.82/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.82/0.99      | ~ v2_pre_topc(X0)
% 2.82/0.99      | ~ v8_pre_topc(X0)
% 2.82/0.99      | ~ v3_orders_2(X0)
% 2.82/0.99      | ~ v2_lattice3(X0)
% 2.82/0.99      | ~ v1_compts_1(X0)
% 2.82/0.99      | ~ v4_orders_2(X0)
% 2.82/0.99      | ~ v4_orders_2(X1)
% 2.82/0.99      | ~ v7_waybel_0(X1)
% 2.82/0.99      | ~ l1_waybel_9(X0)
% 2.82/0.99      | ~ v5_orders_2(X0)
% 2.82/0.99      | ~ v1_lattice3(X0)
% 2.82/0.99      | v2_struct_0(X1)
% 2.82/0.99      | k1_waybel_9(X0,X1) = X2 ),
% 2.82/0.99      inference(cnf_transformation,[],[f79]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_828,plain,
% 2.82/0.99      ( ~ r3_waybel_9(X0,X1,X2)
% 2.82/0.99      | ~ v11_waybel_0(X1,X0)
% 2.82/0.99      | ~ l1_waybel_0(X1,X0)
% 2.82/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.82/0.99      | ~ m1_subset_1(X3,u1_struct_0(sK7))
% 2.82/0.99      | ~ v2_pre_topc(X0)
% 2.82/0.99      | ~ v8_pre_topc(X0)
% 2.82/0.99      | ~ v3_orders_2(X0)
% 2.82/0.99      | ~ v2_lattice3(X0)
% 2.82/0.99      | ~ v1_compts_1(X0)
% 2.82/0.99      | ~ v4_orders_2(X0)
% 2.82/0.99      | ~ v4_orders_2(X1)
% 2.82/0.99      | ~ v7_waybel_0(X1)
% 2.82/0.99      | ~ l1_waybel_9(X0)
% 2.82/0.99      | ~ v5_orders_2(X0)
% 2.82/0.99      | ~ v1_lattice3(X0)
% 2.82/0.99      | v2_struct_0(X1)
% 2.82/0.99      | k1_waybel_9(X0,X1) = X2
% 2.82/0.99      | k4_waybel_1(X0,sK6(X0)) != k4_waybel_1(sK7,X3)
% 2.82/0.99      | sK7 != X0 ),
% 2.82/0.99      inference(resolution_lifted,[status(thm)],[c_24,c_32]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_829,plain,
% 2.82/0.99      ( ~ r3_waybel_9(sK7,X0,X1)
% 2.82/0.99      | ~ v11_waybel_0(X0,sK7)
% 2.82/0.99      | ~ l1_waybel_0(X0,sK7)
% 2.82/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 2.82/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 2.82/0.99      | ~ v2_pre_topc(sK7)
% 2.82/0.99      | ~ v8_pre_topc(sK7)
% 2.82/0.99      | ~ v3_orders_2(sK7)
% 2.82/0.99      | ~ v2_lattice3(sK7)
% 2.82/0.99      | ~ v1_compts_1(sK7)
% 2.82/0.99      | ~ v4_orders_2(X0)
% 2.82/0.99      | ~ v4_orders_2(sK7)
% 2.82/0.99      | ~ v7_waybel_0(X0)
% 2.82/0.99      | ~ l1_waybel_9(sK7)
% 2.82/0.99      | ~ v5_orders_2(sK7)
% 2.82/0.99      | ~ v1_lattice3(sK7)
% 2.82/0.99      | v2_struct_0(X0)
% 2.82/0.99      | k1_waybel_9(sK7,X0) = X1
% 2.82/0.99      | k4_waybel_1(sK7,sK6(sK7)) != k4_waybel_1(sK7,X2) ),
% 2.82/0.99      inference(unflattening,[status(thm)],[c_828]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_833,plain,
% 2.82/0.99      ( ~ v7_waybel_0(X0)
% 2.82/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 2.82/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 2.82/0.99      | ~ l1_waybel_0(X0,sK7)
% 2.82/0.99      | ~ v11_waybel_0(X0,sK7)
% 2.82/0.99      | ~ r3_waybel_9(sK7,X0,X1)
% 2.82/0.99      | ~ v4_orders_2(X0)
% 2.82/0.99      | v2_struct_0(X0)
% 2.82/0.99      | k1_waybel_9(sK7,X0) = X1
% 2.82/0.99      | k4_waybel_1(sK7,sK6(sK7)) != k4_waybel_1(sK7,X2) ),
% 2.82/0.99      inference(global_propositional_subsumption,
% 2.82/0.99                [status(thm)],
% 2.82/0.99                [c_829,c_41,c_40,c_39,c_38,c_37,c_36,c_35,c_34,c_33]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_834,plain,
% 2.82/0.99      ( ~ r3_waybel_9(sK7,X0,X1)
% 2.82/0.99      | ~ v11_waybel_0(X0,sK7)
% 2.82/0.99      | ~ l1_waybel_0(X0,sK7)
% 2.82/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 2.82/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 2.82/0.99      | ~ v4_orders_2(X0)
% 2.82/0.99      | ~ v7_waybel_0(X0)
% 2.82/0.99      | v2_struct_0(X0)
% 2.82/0.99      | k1_waybel_9(sK7,X0) = X1
% 2.82/0.99      | k4_waybel_1(sK7,sK6(sK7)) != k4_waybel_1(sK7,X2) ),
% 2.82/0.99      inference(renaming,[status(thm)],[c_833]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_941,plain,
% 2.82/0.99      ( ~ r3_waybel_9(sK7,X0,X1)
% 2.82/0.99      | ~ l1_waybel_0(X0,sK7)
% 2.82/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 2.82/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 2.82/0.99      | ~ v4_orders_2(X0)
% 2.82/0.99      | ~ v7_waybel_0(X0)
% 2.82/0.99      | v2_struct_0(X0)
% 2.82/0.99      | k1_waybel_9(sK7,X0) = X1
% 2.82/0.99      | k4_waybel_1(sK7,sK6(sK7)) != k4_waybel_1(sK7,X2)
% 2.82/0.99      | sK8 != X0
% 2.82/0.99      | sK7 != sK7 ),
% 2.82/0.99      inference(resolution_lifted,[status(thm)],[c_27,c_834]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_942,plain,
% 2.82/0.99      ( ~ r3_waybel_9(sK7,sK8,X0)
% 2.82/0.99      | ~ l1_waybel_0(sK8,sK7)
% 2.82/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 2.82/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 2.82/0.99      | ~ v4_orders_2(sK8)
% 2.82/0.99      | ~ v7_waybel_0(sK8)
% 2.82/0.99      | v2_struct_0(sK8)
% 2.82/0.99      | k1_waybel_9(sK7,sK8) = X0
% 2.82/0.99      | k4_waybel_1(sK7,sK6(sK7)) != k4_waybel_1(sK7,X1) ),
% 2.82/0.99      inference(unflattening,[status(thm)],[c_941]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_946,plain,
% 2.82/0.99      ( ~ m1_subset_1(X1,u1_struct_0(sK7))
% 2.82/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 2.82/0.99      | ~ r3_waybel_9(sK7,sK8,X0)
% 2.82/0.99      | k1_waybel_9(sK7,sK8) = X0
% 2.82/0.99      | k4_waybel_1(sK7,sK6(sK7)) != k4_waybel_1(sK7,X1) ),
% 2.82/0.99      inference(global_propositional_subsumption,
% 2.82/0.99                [status(thm)],
% 2.82/0.99                [c_942,c_31,c_30,c_29,c_28]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_947,plain,
% 2.82/0.99      ( ~ r3_waybel_9(sK7,sK8,X0)
% 2.82/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 2.82/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 2.82/0.99      | k1_waybel_9(sK7,sK8) = X0
% 2.82/0.99      | k4_waybel_1(sK7,sK6(sK7)) != k4_waybel_1(sK7,X1) ),
% 2.82/0.99      inference(renaming,[status(thm)],[c_946]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_4377,plain,
% 2.82/0.99      ( ~ r3_waybel_9(sK7,sK8,X0_68)
% 2.82/0.99      | ~ m1_subset_1(X1_68,u1_struct_0(sK7))
% 2.82/0.99      | ~ m1_subset_1(X0_68,u1_struct_0(sK7))
% 2.82/0.99      | k4_waybel_1(sK7,sK6(sK7)) != k4_waybel_1(sK7,X1_68)
% 2.82/0.99      | k1_waybel_9(sK7,sK8) = X0_68 ),
% 2.82/0.99      inference(subtyping,[status(esa)],[c_947]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_4381,plain,
% 2.82/0.99      ( ~ r3_waybel_9(sK7,sK8,X0_68)
% 2.82/0.99      | ~ m1_subset_1(X0_68,u1_struct_0(sK7))
% 2.82/0.99      | k1_waybel_9(sK7,sK8) = X0_68
% 2.82/0.99      | ~ sP1_iProver_split ),
% 2.82/0.99      inference(splitting,
% 2.82/0.99                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 2.82/0.99                [c_4377]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_4880,plain,
% 2.82/0.99      ( k1_waybel_9(sK7,sK8) = X0_68
% 2.82/0.99      | r3_waybel_9(sK7,sK8,X0_68) != iProver_top
% 2.82/0.99      | m1_subset_1(X0_68,u1_struct_0(sK7)) != iProver_top
% 2.82/0.99      | sP1_iProver_split != iProver_top ),
% 2.82/0.99      inference(predicate_to_equality,[status(thm)],[c_4381]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_25,plain,
% 2.82/0.99      ( ~ r3_waybel_9(X0,X1,X2)
% 2.82/0.99      | ~ v11_waybel_0(X1,X0)
% 2.82/0.99      | ~ l1_waybel_0(X1,X0)
% 2.82/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.82/0.99      | m1_subset_1(sK6(X0),u1_struct_0(X0))
% 2.82/0.99      | ~ v2_pre_topc(X0)
% 2.82/0.99      | ~ v8_pre_topc(X0)
% 2.82/0.99      | ~ v3_orders_2(X0)
% 2.82/0.99      | ~ v2_lattice3(X0)
% 2.82/0.99      | ~ v1_compts_1(X0)
% 2.82/0.99      | ~ v4_orders_2(X0)
% 2.82/0.99      | ~ v4_orders_2(X1)
% 2.82/0.99      | ~ v7_waybel_0(X1)
% 2.82/0.99      | ~ l1_waybel_9(X0)
% 2.82/0.99      | ~ v5_orders_2(X0)
% 2.82/0.99      | ~ v1_lattice3(X0)
% 2.82/0.99      | v2_struct_0(X1)
% 2.82/0.99      | k1_waybel_9(X0,X1) = X2 ),
% 2.82/0.99      inference(cnf_transformation,[],[f78]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_893,plain,
% 2.82/0.99      ( ~ r3_waybel_9(X0,X1,X2)
% 2.82/0.99      | ~ l1_waybel_0(X1,X0)
% 2.82/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.82/0.99      | m1_subset_1(sK6(X0),u1_struct_0(X0))
% 2.82/0.99      | ~ v2_pre_topc(X0)
% 2.82/0.99      | ~ v8_pre_topc(X0)
% 2.82/0.99      | ~ v3_orders_2(X0)
% 2.82/0.99      | ~ v2_lattice3(X0)
% 2.82/0.99      | ~ v1_compts_1(X0)
% 2.82/0.99      | ~ v4_orders_2(X0)
% 2.82/0.99      | ~ v4_orders_2(X1)
% 2.82/0.99      | ~ v7_waybel_0(X1)
% 2.82/0.99      | ~ l1_waybel_9(X0)
% 2.82/0.99      | ~ v5_orders_2(X0)
% 2.82/0.99      | ~ v1_lattice3(X0)
% 2.82/0.99      | v2_struct_0(X1)
% 2.82/0.99      | k1_waybel_9(X0,X1) = X2
% 2.82/0.99      | sK8 != X1
% 2.82/0.99      | sK7 != X0 ),
% 2.82/0.99      inference(resolution_lifted,[status(thm)],[c_25,c_27]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_894,plain,
% 2.82/0.99      ( ~ r3_waybel_9(sK7,sK8,X0)
% 2.82/0.99      | ~ l1_waybel_0(sK8,sK7)
% 2.82/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 2.82/0.99      | m1_subset_1(sK6(sK7),u1_struct_0(sK7))
% 2.82/0.99      | ~ v2_pre_topc(sK7)
% 2.82/0.99      | ~ v8_pre_topc(sK7)
% 2.82/0.99      | ~ v3_orders_2(sK7)
% 2.82/0.99      | ~ v2_lattice3(sK7)
% 2.82/0.99      | ~ v1_compts_1(sK7)
% 2.82/0.99      | ~ v4_orders_2(sK8)
% 2.82/0.99      | ~ v4_orders_2(sK7)
% 2.82/0.99      | ~ v7_waybel_0(sK8)
% 2.82/0.99      | ~ l1_waybel_9(sK7)
% 2.82/0.99      | ~ v5_orders_2(sK7)
% 2.82/0.99      | ~ v1_lattice3(sK7)
% 2.82/0.99      | v2_struct_0(sK8)
% 2.82/0.99      | k1_waybel_9(sK7,sK8) = X0 ),
% 2.82/0.99      inference(unflattening,[status(thm)],[c_893]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_898,plain,
% 2.82/0.99      ( ~ r3_waybel_9(sK7,sK8,X0)
% 2.82/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 2.82/0.99      | m1_subset_1(sK6(sK7),u1_struct_0(sK7))
% 2.82/0.99      | k1_waybel_9(sK7,sK8) = X0 ),
% 2.82/0.99      inference(global_propositional_subsumption,
% 2.82/0.99                [status(thm)],
% 2.82/0.99                [c_894,c_41,c_40,c_39,c_38,c_37,c_36,c_35,c_34,c_33,c_31,
% 2.82/0.99                 c_30,c_29,c_28]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_4379,plain,
% 2.82/0.99      ( ~ r3_waybel_9(sK7,sK8,X0_68)
% 2.82/0.99      | ~ m1_subset_1(X0_68,u1_struct_0(sK7))
% 2.82/0.99      | m1_subset_1(sK6(sK7),u1_struct_0(sK7))
% 2.82/0.99      | k1_waybel_9(sK7,sK8) = X0_68 ),
% 2.82/0.99      inference(subtyping,[status(esa)],[c_898]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_4407,plain,
% 2.82/0.99      ( k1_waybel_9(sK7,sK8) = X0_68
% 2.82/0.99      | r3_waybel_9(sK7,sK8,X0_68) != iProver_top
% 2.82/0.99      | m1_subset_1(X0_68,u1_struct_0(sK7)) != iProver_top
% 2.82/0.99      | m1_subset_1(sK6(sK7),u1_struct_0(sK7)) = iProver_top ),
% 2.82/0.99      inference(predicate_to_equality,[status(thm)],[c_4379]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_4382,plain,
% 2.82/0.99      ( sP1_iProver_split | sP0_iProver_split ),
% 2.82/0.99      inference(splitting,
% 2.82/0.99                [splitting(split),new_symbols(definition,[])],
% 2.82/0.99                [c_4377]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_4413,plain,
% 2.82/0.99      ( sP1_iProver_split = iProver_top
% 2.82/0.99      | sP0_iProver_split = iProver_top ),
% 2.82/0.99      inference(predicate_to_equality,[status(thm)],[c_4382]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_4414,plain,
% 2.82/0.99      ( k1_waybel_9(sK7,sK8) = X0_68
% 2.82/0.99      | r3_waybel_9(sK7,sK8,X0_68) != iProver_top
% 2.82/0.99      | m1_subset_1(X0_68,u1_struct_0(sK7)) != iProver_top
% 2.82/0.99      | sP1_iProver_split != iProver_top ),
% 2.82/0.99      inference(predicate_to_equality,[status(thm)],[c_4381]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_4380,plain,
% 2.82/0.99      ( ~ m1_subset_1(X0_68,u1_struct_0(sK7))
% 2.82/0.99      | k4_waybel_1(sK7,sK6(sK7)) != k4_waybel_1(sK7,X0_68)
% 2.82/0.99      | ~ sP0_iProver_split ),
% 2.82/0.99      inference(splitting,
% 2.82/0.99                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.82/0.99                [c_4377]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_4881,plain,
% 2.82/0.99      ( k4_waybel_1(sK7,sK6(sK7)) != k4_waybel_1(sK7,X0_68)
% 2.82/0.99      | m1_subset_1(X0_68,u1_struct_0(sK7)) != iProver_top
% 2.82/0.99      | sP0_iProver_split != iProver_top ),
% 2.82/0.99      inference(predicate_to_equality,[status(thm)],[c_4380]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_5176,plain,
% 2.82/0.99      ( m1_subset_1(sK6(sK7),u1_struct_0(sK7)) != iProver_top
% 2.82/0.99      | sP0_iProver_split != iProver_top ),
% 2.82/0.99      inference(equality_resolution,[status(thm)],[c_4881]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_5250,plain,
% 2.82/0.99      ( m1_subset_1(X0_68,u1_struct_0(sK7)) != iProver_top
% 2.82/0.99      | r3_waybel_9(sK7,sK8,X0_68) != iProver_top
% 2.82/0.99      | k1_waybel_9(sK7,sK8) = X0_68 ),
% 2.82/0.99      inference(global_propositional_subsumption,
% 2.82/0.99                [status(thm)],
% 2.82/0.99                [c_4880,c_4407,c_4413,c_4414,c_5176]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_5251,plain,
% 2.82/0.99      ( k1_waybel_9(sK7,sK8) = X0_68
% 2.82/0.99      | r3_waybel_9(sK7,sK8,X0_68) != iProver_top
% 2.82/0.99      | m1_subset_1(X0_68,u1_struct_0(sK7)) != iProver_top ),
% 2.82/0.99      inference(renaming,[status(thm)],[c_5250]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_5259,plain,
% 2.82/0.99      ( k1_waybel_9(sK7,sK8) = sK3(sK7,sK8)
% 2.82/0.99      | m1_subset_1(sK3(sK7,sK8),u1_struct_0(sK7)) != iProver_top ),
% 2.82/0.99      inference(superposition,[status(thm)],[c_4894,c_5251]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_4396,plain,
% 2.82/0.99      ( ~ m1_subset_1(X0_68,X0_69)
% 2.82/0.99      | m1_subset_1(X1_68,X0_69)
% 2.82/0.99      | X1_68 != X0_68 ),
% 2.82/0.99      theory(equality) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_5199,plain,
% 2.82/0.99      ( m1_subset_1(X0_68,u1_struct_0(sK7))
% 2.82/0.99      | ~ m1_subset_1(sK3(sK7,sK8),u1_struct_0(sK7))
% 2.82/0.99      | X0_68 != sK3(sK7,sK8) ),
% 2.82/0.99      inference(instantiation,[status(thm)],[c_4396]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_5270,plain,
% 2.82/0.99      ( m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
% 2.82/0.99      | ~ m1_subset_1(sK3(sK7,sK8),u1_struct_0(sK7))
% 2.82/0.99      | k1_waybel_9(sK7,sK8) != sK3(sK7,sK8) ),
% 2.82/0.99      inference(instantiation,[status(thm)],[c_5199]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_5271,plain,
% 2.82/0.99      ( k1_waybel_9(sK7,sK8) != sK3(sK7,sK8)
% 2.82/0.99      | m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7)) = iProver_top
% 2.82/0.99      | m1_subset_1(sK3(sK7,sK8),u1_struct_0(sK7)) != iProver_top ),
% 2.82/0.99      inference(predicate_to_equality,[status(thm)],[c_5270]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_4397,plain,
% 2.82/0.99      ( ~ r3_waybel_9(X0_67,X1_67,X0_68)
% 2.82/0.99      | r3_waybel_9(X0_67,X1_67,X1_68)
% 2.82/0.99      | X1_68 != X0_68 ),
% 2.82/0.99      theory(equality) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_5239,plain,
% 2.82/0.99      ( r3_waybel_9(sK7,sK8,X0_68)
% 2.82/0.99      | ~ r3_waybel_9(sK7,sK8,sK3(sK7,sK8))
% 2.82/0.99      | X0_68 != sK3(sK7,sK8) ),
% 2.82/0.99      inference(instantiation,[status(thm)],[c_4397]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_5275,plain,
% 2.82/0.99      ( r3_waybel_9(sK7,sK8,k1_waybel_9(sK7,sK8))
% 2.82/0.99      | ~ r3_waybel_9(sK7,sK8,sK3(sK7,sK8))
% 2.82/0.99      | k1_waybel_9(sK7,sK8) != sK3(sK7,sK8) ),
% 2.82/0.99      inference(instantiation,[status(thm)],[c_5239]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_5276,plain,
% 2.82/0.99      ( k1_waybel_9(sK7,sK8) != sK3(sK7,sK8)
% 2.82/0.99      | r3_waybel_9(sK7,sK8,k1_waybel_9(sK7,sK8)) = iProver_top
% 2.82/0.99      | r3_waybel_9(sK7,sK8,sK3(sK7,sK8)) != iProver_top ),
% 2.82/0.99      inference(predicate_to_equality,[status(thm)],[c_5275]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_6049,plain,
% 2.82/0.99      ( r3_waybel_9(sK7,sK8,sK4(sK7,sK8)) = iProver_top
% 2.82/0.99      | r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) != iProver_top ),
% 2.82/0.99      inference(global_propositional_subsumption,
% 2.82/0.99                [status(thm)],
% 2.82/0.99                [c_4901,c_54,c_55,c_56,c_2370,c_2381,c_3461,c_5259,
% 2.82/0.99                 c_5271,c_5276]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_6725,plain,
% 2.82/0.99      ( r3_waybel_9(sK7,sK8,sK4(sK7,sK8)) = iProver_top ),
% 2.82/0.99      inference(superposition,[status(thm)],[c_6718,c_6049]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_5300,plain,
% 2.82/0.99      ( k1_waybel_9(sK7,sK8) = sK3(sK7,sK8) ),
% 2.82/0.99      inference(global_propositional_subsumption,
% 2.82/0.99                [status(thm)],
% 2.82/0.99                [c_5259,c_54,c_55,c_56,c_2370]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_5303,plain,
% 2.82/0.99      ( sK3(sK7,sK8) = X0_68
% 2.82/0.99      | r3_waybel_9(sK7,sK8,X0_68) != iProver_top
% 2.82/0.99      | m1_subset_1(X0_68,u1_struct_0(sK7)) != iProver_top ),
% 2.82/0.99      inference(demodulation,[status(thm)],[c_5300,c_5251]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_6776,plain,
% 2.82/0.99      ( sK4(sK7,sK8) = sK3(sK7,sK8)
% 2.82/0.99      | m1_subset_1(sK4(sK7,sK8),u1_struct_0(sK7)) != iProver_top ),
% 2.82/0.99      inference(superposition,[status(thm)],[c_6725,c_5303]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_23,plain,
% 2.82/0.99      ( ~ r3_waybel_9(X0,X1,X2)
% 2.82/0.99      | r2_hidden(X2,k10_yellow_6(X0,X1))
% 2.82/0.99      | ~ l1_waybel_0(X1,X0)
% 2.82/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.82/0.99      | m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
% 2.82/0.99      | ~ v2_pre_topc(X0)
% 2.82/0.99      | ~ v8_pre_topc(X0)
% 2.82/0.99      | ~ v1_compts_1(X0)
% 2.82/0.99      | ~ v4_orders_2(X1)
% 2.82/0.99      | ~ v7_waybel_0(X1)
% 2.82/0.99      | ~ l1_pre_topc(X0)
% 2.82/0.99      | v2_struct_0(X0)
% 2.82/0.99      | v2_struct_0(X1) ),
% 2.82/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_1812,plain,
% 2.82/0.99      ( ~ r3_waybel_9(X0,X1,X2)
% 2.82/0.99      | ~ l1_waybel_0(X1,X0)
% 2.82/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.82/0.99      | m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
% 2.82/0.99      | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 2.82/0.99      | ~ v2_pre_topc(X0)
% 2.82/0.99      | ~ v8_pre_topc(X0)
% 2.82/0.99      | ~ v1_compts_1(X0)
% 2.82/0.99      | ~ v4_orders_2(X1)
% 2.82/0.99      | ~ v7_waybel_0(X1)
% 2.82/0.99      | ~ l1_pre_topc(X0)
% 2.82/0.99      | v2_struct_0(X0)
% 2.82/0.99      | v2_struct_0(X1)
% 2.82/0.99      | k1_waybel_9(sK7,sK8) != X2
% 2.82/0.99      | k10_yellow_6(X0,X1) != k10_yellow_6(sK7,sK8) ),
% 2.82/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_470]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_1813,plain,
% 2.82/0.99      ( ~ r3_waybel_9(X0,X1,k1_waybel_9(sK7,sK8))
% 2.82/0.99      | ~ l1_waybel_0(X1,X0)
% 2.82/0.99      | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(X0))
% 2.82/0.99      | m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
% 2.82/0.99      | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 2.82/0.99      | ~ v2_pre_topc(X0)
% 2.82/0.99      | ~ v8_pre_topc(X0)
% 2.82/0.99      | ~ v1_compts_1(X0)
% 2.82/0.99      | ~ v4_orders_2(X1)
% 2.82/0.99      | ~ v7_waybel_0(X1)
% 2.82/0.99      | ~ l1_pre_topc(X0)
% 2.82/0.99      | v2_struct_0(X0)
% 2.82/0.99      | v2_struct_0(X1)
% 2.82/0.99      | k10_yellow_6(X0,X1) != k10_yellow_6(sK7,sK8) ),
% 2.82/0.99      inference(unflattening,[status(thm)],[c_1812]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_2213,plain,
% 2.82/0.99      ( ~ r3_waybel_9(X0,X1,k1_waybel_9(sK7,sK8))
% 2.82/0.99      | ~ l1_waybel_0(X1,X0)
% 2.82/0.99      | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(X0))
% 2.82/0.99      | m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
% 2.82/0.99      | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 2.82/0.99      | ~ v2_pre_topc(X0)
% 2.82/0.99      | ~ v8_pre_topc(X0)
% 2.82/0.99      | ~ v1_compts_1(X0)
% 2.82/0.99      | ~ v4_orders_2(X1)
% 2.82/0.99      | ~ v7_waybel_0(X1)
% 2.82/0.99      | v2_struct_0(X0)
% 2.82/0.99      | v2_struct_0(X1)
% 2.82/0.99      | k10_yellow_6(X0,X1) != k10_yellow_6(sK7,sK8)
% 2.82/0.99      | sK7 != X0 ),
% 2.82/0.99      inference(resolution_lifted,[status(thm)],[c_1813,c_1316]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_2214,plain,
% 2.82/0.99      ( ~ r3_waybel_9(sK7,X0,k1_waybel_9(sK7,sK8))
% 2.82/0.99      | ~ l1_waybel_0(X0,sK7)
% 2.82/0.99      | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
% 2.82/0.99      | m1_subset_1(sK4(sK7,X0),u1_struct_0(sK7))
% 2.82/0.99      | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 2.82/0.99      | ~ v2_pre_topc(sK7)
% 2.82/0.99      | ~ v8_pre_topc(sK7)
% 2.82/0.99      | ~ v1_compts_1(sK7)
% 2.82/0.99      | ~ v4_orders_2(X0)
% 2.82/0.99      | ~ v7_waybel_0(X0)
% 2.82/0.99      | v2_struct_0(X0)
% 2.82/0.99      | v2_struct_0(sK7)
% 2.82/0.99      | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8) ),
% 2.82/0.99      inference(unflattening,[status(thm)],[c_2213]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_2218,plain,
% 2.82/0.99      ( v2_struct_0(X0)
% 2.82/0.99      | ~ v7_waybel_0(X0)
% 2.82/0.99      | ~ v4_orders_2(X0)
% 2.82/0.99      | ~ r3_waybel_9(sK7,X0,k1_waybel_9(sK7,sK8))
% 2.82/0.99      | ~ l1_waybel_0(X0,sK7)
% 2.82/0.99      | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
% 2.82/0.99      | m1_subset_1(sK4(sK7,X0),u1_struct_0(sK7))
% 2.82/0.99      | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 2.82/0.99      | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8) ),
% 2.82/0.99      inference(global_propositional_subsumption,
% 2.82/0.99                [status(thm)],
% 2.82/0.99                [c_2214,c_41,c_40,c_36,c_34,c_33,c_103,c_136]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_2219,plain,
% 2.82/0.99      ( ~ r3_waybel_9(sK7,X0,k1_waybel_9(sK7,sK8))
% 2.82/0.99      | ~ l1_waybel_0(X0,sK7)
% 2.82/0.99      | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
% 2.82/0.99      | m1_subset_1(sK4(sK7,X0),u1_struct_0(sK7))
% 2.82/0.99      | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 2.82/0.99      | ~ v4_orders_2(X0)
% 2.82/0.99      | ~ v7_waybel_0(X0)
% 2.82/0.99      | v2_struct_0(X0)
% 2.82/0.99      | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8) ),
% 2.82/0.99      inference(renaming,[status(thm)],[c_2218]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_2390,plain,
% 2.82/0.99      ( ~ r3_waybel_9(sK7,X0,k1_waybel_9(sK7,sK8))
% 2.82/0.99      | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
% 2.82/0.99      | m1_subset_1(sK4(sK7,X0),u1_struct_0(sK7))
% 2.82/0.99      | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 2.82/0.99      | ~ v4_orders_2(X0)
% 2.82/0.99      | ~ v7_waybel_0(X0)
% 2.82/0.99      | v2_struct_0(X0)
% 2.82/0.99      | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8)
% 2.82/0.99      | sK8 != X0
% 2.82/0.99      | sK7 != sK7 ),
% 2.82/0.99      inference(resolution_lifted,[status(thm)],[c_28,c_2219]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_2391,plain,
% 2.82/0.99      ( ~ r3_waybel_9(sK7,sK8,k1_waybel_9(sK7,sK8))
% 2.82/0.99      | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
% 2.82/0.99      | m1_subset_1(sK4(sK7,sK8),u1_struct_0(sK7))
% 2.82/0.99      | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 2.82/0.99      | ~ v4_orders_2(sK8)
% 2.82/0.99      | ~ v7_waybel_0(sK8)
% 2.82/0.99      | v2_struct_0(sK8)
% 2.82/0.99      | k10_yellow_6(sK7,sK8) != k10_yellow_6(sK7,sK8) ),
% 2.82/0.99      inference(unflattening,[status(thm)],[c_2390]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_2393,plain,
% 2.82/0.99      ( ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 2.82/0.99      | m1_subset_1(sK4(sK7,sK8),u1_struct_0(sK7))
% 2.82/0.99      | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
% 2.82/0.99      | ~ r3_waybel_9(sK7,sK8,k1_waybel_9(sK7,sK8))
% 2.82/0.99      | k10_yellow_6(sK7,sK8) != k10_yellow_6(sK7,sK8) ),
% 2.82/0.99      inference(global_propositional_subsumption,
% 2.82/0.99                [status(thm)],
% 2.82/0.99                [c_2391,c_31,c_30,c_29]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_2394,plain,
% 2.82/0.99      ( ~ r3_waybel_9(sK7,sK8,k1_waybel_9(sK7,sK8))
% 2.82/0.99      | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
% 2.82/0.99      | m1_subset_1(sK4(sK7,sK8),u1_struct_0(sK7))
% 2.82/0.99      | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 2.82/0.99      | k10_yellow_6(sK7,sK8) != k10_yellow_6(sK7,sK8) ),
% 2.82/0.99      inference(renaming,[status(thm)],[c_2393]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_3464,plain,
% 2.82/0.99      ( ~ r3_waybel_9(sK7,sK8,k1_waybel_9(sK7,sK8))
% 2.82/0.99      | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
% 2.82/0.99      | m1_subset_1(sK4(sK7,sK8),u1_struct_0(sK7))
% 2.82/0.99      | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) ),
% 2.82/0.99      inference(equality_resolution_simp,[status(thm)],[c_2394]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_3465,plain,
% 2.82/0.99      ( r3_waybel_9(sK7,sK8,k1_waybel_9(sK7,sK8)) != iProver_top
% 2.82/0.99      | m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7)) != iProver_top
% 2.82/0.99      | m1_subset_1(sK4(sK7,sK8),u1_struct_0(sK7)) = iProver_top
% 2.82/0.99      | r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) != iProver_top ),
% 2.82/0.99      inference(predicate_to_equality,[status(thm)],[c_3464]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_7091,plain,
% 2.82/0.99      ( sK4(sK7,sK8) = sK3(sK7,sK8) ),
% 2.82/0.99      inference(global_propositional_subsumption,
% 2.82/0.99                [status(thm)],
% 2.82/0.99                [c_6776,c_54,c_55,c_56,c_2370,c_2381,c_3465,c_5259,
% 2.82/0.99                 c_5271,c_5276,c_6642]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_19,plain,
% 2.82/0.99      ( ~ r3_waybel_9(X0,X1,X2)
% 2.82/0.99      | r2_hidden(X2,k10_yellow_6(X0,X1))
% 2.82/0.99      | ~ l1_waybel_0(X1,X0)
% 2.82/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.82/0.99      | ~ v2_pre_topc(X0)
% 2.82/0.99      | ~ v8_pre_topc(X0)
% 2.82/0.99      | ~ v1_compts_1(X0)
% 2.82/0.99      | ~ v4_orders_2(X1)
% 2.82/0.99      | ~ v7_waybel_0(X1)
% 2.82/0.99      | ~ l1_pre_topc(X0)
% 2.82/0.99      | v2_struct_0(X0)
% 2.82/0.99      | v2_struct_0(X1)
% 2.82/0.99      | sK5(X0,X1) != sK4(X0,X1) ),
% 2.82/0.99      inference(cnf_transformation,[],[f77]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_2004,plain,
% 2.82/0.99      ( ~ r3_waybel_9(X0,X1,X2)
% 2.82/0.99      | ~ l1_waybel_0(X1,X0)
% 2.82/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.82/0.99      | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 2.82/0.99      | ~ v2_pre_topc(X0)
% 2.82/0.99      | ~ v8_pre_topc(X0)
% 2.82/0.99      | ~ v1_compts_1(X0)
% 2.82/0.99      | ~ v4_orders_2(X1)
% 2.82/0.99      | ~ v7_waybel_0(X1)
% 2.82/0.99      | ~ l1_pre_topc(X0)
% 2.82/0.99      | v2_struct_0(X0)
% 2.82/0.99      | v2_struct_0(X1)
% 2.82/0.99      | k1_waybel_9(sK7,sK8) != X2
% 2.82/0.99      | sK5(X0,X1) != sK4(X0,X1)
% 2.82/0.99      | k10_yellow_6(X0,X1) != k10_yellow_6(sK7,sK8) ),
% 2.82/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_470]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_2005,plain,
% 2.82/0.99      ( ~ r3_waybel_9(X0,X1,k1_waybel_9(sK7,sK8))
% 2.82/0.99      | ~ l1_waybel_0(X1,X0)
% 2.82/0.99      | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(X0))
% 2.82/0.99      | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 2.82/0.99      | ~ v2_pre_topc(X0)
% 2.82/0.99      | ~ v8_pre_topc(X0)
% 2.82/0.99      | ~ v1_compts_1(X0)
% 2.82/0.99      | ~ v4_orders_2(X1)
% 2.82/0.99      | ~ v7_waybel_0(X1)
% 2.82/0.99      | ~ l1_pre_topc(X0)
% 2.82/0.99      | v2_struct_0(X0)
% 2.82/0.99      | v2_struct_0(X1)
% 2.82/0.99      | sK5(X0,X1) != sK4(X0,X1)
% 2.82/0.99      | k10_yellow_6(X0,X1) != k10_yellow_6(sK7,sK8) ),
% 2.82/0.99      inference(unflattening,[status(thm)],[c_2004]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_2057,plain,
% 2.82/0.99      ( ~ r3_waybel_9(X0,X1,k1_waybel_9(sK7,sK8))
% 2.82/0.99      | ~ l1_waybel_0(X1,X0)
% 2.82/0.99      | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(X0))
% 2.82/0.99      | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 2.82/0.99      | ~ v2_pre_topc(X0)
% 2.82/0.99      | ~ v8_pre_topc(X0)
% 2.82/0.99      | ~ v1_compts_1(X0)
% 2.82/0.99      | ~ v4_orders_2(X1)
% 2.82/0.99      | ~ v7_waybel_0(X1)
% 2.82/0.99      | v2_struct_0(X0)
% 2.82/0.99      | v2_struct_0(X1)
% 2.82/0.99      | sK5(X0,X1) != sK4(X0,X1)
% 2.82/0.99      | k10_yellow_6(X0,X1) != k10_yellow_6(sK7,sK8)
% 2.82/0.99      | sK7 != X0 ),
% 2.82/0.99      inference(resolution_lifted,[status(thm)],[c_2005,c_1316]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_2058,plain,
% 2.82/0.99      ( ~ r3_waybel_9(sK7,X0,k1_waybel_9(sK7,sK8))
% 2.82/0.99      | ~ l1_waybel_0(X0,sK7)
% 2.82/0.99      | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
% 2.82/0.99      | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 2.82/0.99      | ~ v2_pre_topc(sK7)
% 2.82/0.99      | ~ v8_pre_topc(sK7)
% 2.82/0.99      | ~ v1_compts_1(sK7)
% 2.82/0.99      | ~ v4_orders_2(X0)
% 2.82/0.99      | ~ v7_waybel_0(X0)
% 2.82/0.99      | v2_struct_0(X0)
% 2.82/0.99      | v2_struct_0(sK7)
% 2.82/0.99      | sK5(sK7,X0) != sK4(sK7,X0)
% 2.82/0.99      | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8) ),
% 2.82/0.99      inference(unflattening,[status(thm)],[c_2057]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_2062,plain,
% 2.82/0.99      ( v2_struct_0(X0)
% 2.82/0.99      | ~ v7_waybel_0(X0)
% 2.82/0.99      | ~ v4_orders_2(X0)
% 2.82/0.99      | ~ r3_waybel_9(sK7,X0,k1_waybel_9(sK7,sK8))
% 2.82/0.99      | ~ l1_waybel_0(X0,sK7)
% 2.82/0.99      | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
% 2.82/0.99      | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 2.82/0.99      | sK5(sK7,X0) != sK4(sK7,X0)
% 2.82/0.99      | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8) ),
% 2.82/0.99      inference(global_propositional_subsumption,
% 2.82/0.99                [status(thm)],
% 2.82/0.99                [c_2058,c_41,c_40,c_36,c_34,c_33,c_103,c_136]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_2063,plain,
% 2.82/0.99      ( ~ r3_waybel_9(sK7,X0,k1_waybel_9(sK7,sK8))
% 2.82/0.99      | ~ l1_waybel_0(X0,sK7)
% 2.82/0.99      | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
% 2.82/0.99      | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 2.82/0.99      | ~ v4_orders_2(X0)
% 2.82/0.99      | ~ v7_waybel_0(X0)
% 2.82/0.99      | v2_struct_0(X0)
% 2.82/0.99      | sK5(sK7,X0) != sK4(sK7,X0)
% 2.82/0.99      | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8) ),
% 2.82/0.99      inference(renaming,[status(thm)],[c_2062]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_2482,plain,
% 2.82/0.99      ( ~ r3_waybel_9(sK7,X0,k1_waybel_9(sK7,sK8))
% 2.82/0.99      | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
% 2.82/0.99      | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 2.82/0.99      | ~ v4_orders_2(X0)
% 2.82/0.99      | ~ v7_waybel_0(X0)
% 2.82/0.99      | v2_struct_0(X0)
% 2.82/0.99      | sK5(sK7,X0) != sK4(sK7,X0)
% 2.82/0.99      | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8)
% 2.82/0.99      | sK8 != X0
% 2.82/0.99      | sK7 != sK7 ),
% 2.82/0.99      inference(resolution_lifted,[status(thm)],[c_28,c_2063]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_2483,plain,
% 2.82/0.99      ( ~ r3_waybel_9(sK7,sK8,k1_waybel_9(sK7,sK8))
% 2.82/0.99      | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
% 2.82/0.99      | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 2.82/0.99      | ~ v4_orders_2(sK8)
% 2.82/0.99      | ~ v7_waybel_0(sK8)
% 2.82/0.99      | v2_struct_0(sK8)
% 2.82/0.99      | sK5(sK7,sK8) != sK4(sK7,sK8)
% 2.82/0.99      | k10_yellow_6(sK7,sK8) != k10_yellow_6(sK7,sK8) ),
% 2.82/0.99      inference(unflattening,[status(thm)],[c_2482]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_2485,plain,
% 2.82/0.99      ( ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 2.82/0.99      | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
% 2.82/0.99      | ~ r3_waybel_9(sK7,sK8,k1_waybel_9(sK7,sK8))
% 2.82/0.99      | sK5(sK7,sK8) != sK4(sK7,sK8)
% 2.82/0.99      | k10_yellow_6(sK7,sK8) != k10_yellow_6(sK7,sK8) ),
% 2.82/0.99      inference(global_propositional_subsumption,
% 2.82/0.99                [status(thm)],
% 2.82/0.99                [c_2483,c_31,c_30,c_29]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_2486,plain,
% 2.82/0.99      ( ~ r3_waybel_9(sK7,sK8,k1_waybel_9(sK7,sK8))
% 2.82/0.99      | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
% 2.82/0.99      | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 2.82/0.99      | sK5(sK7,sK8) != sK4(sK7,sK8)
% 2.82/0.99      | k10_yellow_6(sK7,sK8) != k10_yellow_6(sK7,sK8) ),
% 2.82/0.99      inference(renaming,[status(thm)],[c_2485]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_3456,plain,
% 2.82/0.99      ( ~ r3_waybel_9(sK7,sK8,k1_waybel_9(sK7,sK8))
% 2.82/0.99      | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
% 2.82/0.99      | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 2.82/0.99      | sK5(sK7,sK8) != sK4(sK7,sK8) ),
% 2.82/0.99      inference(equality_resolution_simp,[status(thm)],[c_2486]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_4363,plain,
% 2.82/0.99      ( ~ r3_waybel_9(sK7,sK8,k1_waybel_9(sK7,sK8))
% 2.82/0.99      | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
% 2.82/0.99      | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 2.82/0.99      | sK5(sK7,sK8) != sK4(sK7,sK8) ),
% 2.82/0.99      inference(subtyping,[status(esa)],[c_3456]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_4899,plain,
% 2.82/0.99      ( sK5(sK7,sK8) != sK4(sK7,sK8)
% 2.82/0.99      | r3_waybel_9(sK7,sK8,k1_waybel_9(sK7,sK8)) != iProver_top
% 2.82/0.99      | m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7)) != iProver_top
% 2.82/0.99      | r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) != iProver_top ),
% 2.82/0.99      inference(predicate_to_equality,[status(thm)],[c_4363]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_4463,plain,
% 2.82/0.99      ( sK5(sK7,sK8) != sK4(sK7,sK8)
% 2.82/0.99      | r3_waybel_9(sK7,sK8,k1_waybel_9(sK7,sK8)) != iProver_top
% 2.82/0.99      | m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7)) != iProver_top
% 2.82/0.99      | r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) != iProver_top ),
% 2.82/0.99      inference(predicate_to_equality,[status(thm)],[c_4363]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_5984,plain,
% 2.82/0.99      ( sK5(sK7,sK8) != sK4(sK7,sK8)
% 2.82/0.99      | r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) != iProver_top ),
% 2.82/0.99      inference(global_propositional_subsumption,
% 2.82/0.99                [status(thm)],
% 2.82/0.99                [c_4899,c_54,c_55,c_56,c_2370,c_2381,c_4463,c_5259,
% 2.82/1.00                 c_5271,c_5276]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_7096,plain,
% 2.82/1.00      ( sK5(sK7,sK8) != sK3(sK7,sK8)
% 2.82/1.00      | r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) != iProver_top ),
% 2.82/1.00      inference(demodulation,[status(thm)],[c_7091,c_5984]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_20,plain,
% 2.82/1.00      ( ~ r3_waybel_9(X0,X1,X2)
% 2.82/1.00      | r3_waybel_9(X0,X1,sK5(X0,X1))
% 2.82/1.00      | r2_hidden(X2,k10_yellow_6(X0,X1))
% 2.82/1.00      | ~ l1_waybel_0(X1,X0)
% 2.82/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.82/1.00      | ~ v2_pre_topc(X0)
% 2.82/1.00      | ~ v8_pre_topc(X0)
% 2.82/1.00      | ~ v1_compts_1(X0)
% 2.82/1.00      | ~ v4_orders_2(X1)
% 2.82/1.00      | ~ v7_waybel_0(X1)
% 2.82/1.00      | ~ l1_pre_topc(X0)
% 2.82/1.00      | v2_struct_0(X0)
% 2.82/1.00      | v2_struct_0(X1) ),
% 2.82/1.00      inference(cnf_transformation,[],[f76]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_1956,plain,
% 2.82/1.00      ( ~ r3_waybel_9(X0,X1,X2)
% 2.82/1.00      | r3_waybel_9(X0,X1,sK5(X0,X1))
% 2.82/1.00      | ~ l1_waybel_0(X1,X0)
% 2.82/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.82/1.00      | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 2.82/1.00      | ~ v2_pre_topc(X0)
% 2.82/1.00      | ~ v8_pre_topc(X0)
% 2.82/1.00      | ~ v1_compts_1(X0)
% 2.82/1.00      | ~ v4_orders_2(X1)
% 2.82/1.00      | ~ v7_waybel_0(X1)
% 2.82/1.00      | ~ l1_pre_topc(X0)
% 2.82/1.00      | v2_struct_0(X0)
% 2.82/1.00      | v2_struct_0(X1)
% 2.82/1.00      | k1_waybel_9(sK7,sK8) != X2
% 2.82/1.00      | k10_yellow_6(X0,X1) != k10_yellow_6(sK7,sK8) ),
% 2.82/1.00      inference(resolution_lifted,[status(thm)],[c_20,c_470]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_1957,plain,
% 2.82/1.00      ( ~ r3_waybel_9(X0,X1,k1_waybel_9(sK7,sK8))
% 2.82/1.00      | r3_waybel_9(X0,X1,sK5(X0,X1))
% 2.82/1.00      | ~ l1_waybel_0(X1,X0)
% 2.82/1.00      | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(X0))
% 2.82/1.00      | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 2.82/1.00      | ~ v2_pre_topc(X0)
% 2.82/1.00      | ~ v8_pre_topc(X0)
% 2.82/1.00      | ~ v1_compts_1(X0)
% 2.82/1.00      | ~ v4_orders_2(X1)
% 2.82/1.00      | ~ v7_waybel_0(X1)
% 2.82/1.00      | ~ l1_pre_topc(X0)
% 2.82/1.00      | v2_struct_0(X0)
% 2.82/1.00      | v2_struct_0(X1)
% 2.82/1.00      | k10_yellow_6(X0,X1) != k10_yellow_6(sK7,sK8) ),
% 2.82/1.00      inference(unflattening,[status(thm)],[c_1956]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_2096,plain,
% 2.82/1.00      ( ~ r3_waybel_9(X0,X1,k1_waybel_9(sK7,sK8))
% 2.82/1.00      | r3_waybel_9(X0,X1,sK5(X0,X1))
% 2.82/1.00      | ~ l1_waybel_0(X1,X0)
% 2.82/1.00      | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(X0))
% 2.82/1.00      | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 2.82/1.00      | ~ v2_pre_topc(X0)
% 2.82/1.00      | ~ v8_pre_topc(X0)
% 2.82/1.00      | ~ v1_compts_1(X0)
% 2.82/1.00      | ~ v4_orders_2(X1)
% 2.82/1.00      | ~ v7_waybel_0(X1)
% 2.82/1.00      | v2_struct_0(X0)
% 2.82/1.00      | v2_struct_0(X1)
% 2.82/1.00      | k10_yellow_6(X0,X1) != k10_yellow_6(sK7,sK8)
% 2.82/1.00      | sK7 != X0 ),
% 2.82/1.00      inference(resolution_lifted,[status(thm)],[c_1957,c_1316]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_2097,plain,
% 2.82/1.00      ( ~ r3_waybel_9(sK7,X0,k1_waybel_9(sK7,sK8))
% 2.82/1.00      | r3_waybel_9(sK7,X0,sK5(sK7,X0))
% 2.82/1.00      | ~ l1_waybel_0(X0,sK7)
% 2.82/1.00      | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
% 2.82/1.00      | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 2.82/1.00      | ~ v2_pre_topc(sK7)
% 2.82/1.00      | ~ v8_pre_topc(sK7)
% 2.82/1.00      | ~ v1_compts_1(sK7)
% 2.82/1.00      | ~ v4_orders_2(X0)
% 2.82/1.00      | ~ v7_waybel_0(X0)
% 2.82/1.00      | v2_struct_0(X0)
% 2.82/1.00      | v2_struct_0(sK7)
% 2.82/1.00      | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8) ),
% 2.82/1.00      inference(unflattening,[status(thm)],[c_2096]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_2101,plain,
% 2.82/1.00      ( v2_struct_0(X0)
% 2.82/1.00      | ~ v7_waybel_0(X0)
% 2.82/1.00      | ~ v4_orders_2(X0)
% 2.82/1.00      | ~ r3_waybel_9(sK7,X0,k1_waybel_9(sK7,sK8))
% 2.82/1.00      | r3_waybel_9(sK7,X0,sK5(sK7,X0))
% 2.82/1.00      | ~ l1_waybel_0(X0,sK7)
% 2.82/1.00      | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
% 2.82/1.00      | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 2.82/1.00      | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8) ),
% 2.82/1.00      inference(global_propositional_subsumption,
% 2.82/1.00                [status(thm)],
% 2.82/1.00                [c_2097,c_41,c_40,c_36,c_34,c_33,c_103,c_136]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_2102,plain,
% 2.82/1.00      ( ~ r3_waybel_9(sK7,X0,k1_waybel_9(sK7,sK8))
% 2.82/1.00      | r3_waybel_9(sK7,X0,sK5(sK7,X0))
% 2.82/1.00      | ~ l1_waybel_0(X0,sK7)
% 2.82/1.00      | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
% 2.82/1.00      | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 2.82/1.00      | ~ v4_orders_2(X0)
% 2.82/1.00      | ~ v7_waybel_0(X0)
% 2.82/1.00      | v2_struct_0(X0)
% 2.82/1.00      | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8) ),
% 2.82/1.00      inference(renaming,[status(thm)],[c_2101]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_2459,plain,
% 2.82/1.00      ( ~ r3_waybel_9(sK7,X0,k1_waybel_9(sK7,sK8))
% 2.82/1.00      | r3_waybel_9(sK7,X0,sK5(sK7,X0))
% 2.82/1.00      | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
% 2.82/1.00      | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 2.82/1.00      | ~ v4_orders_2(X0)
% 2.82/1.00      | ~ v7_waybel_0(X0)
% 2.82/1.00      | v2_struct_0(X0)
% 2.82/1.00      | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8)
% 2.82/1.00      | sK8 != X0
% 2.82/1.00      | sK7 != sK7 ),
% 2.82/1.00      inference(resolution_lifted,[status(thm)],[c_28,c_2102]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_2460,plain,
% 2.82/1.00      ( ~ r3_waybel_9(sK7,sK8,k1_waybel_9(sK7,sK8))
% 2.82/1.00      | r3_waybel_9(sK7,sK8,sK5(sK7,sK8))
% 2.82/1.00      | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
% 2.82/1.00      | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 2.82/1.00      | ~ v4_orders_2(sK8)
% 2.82/1.00      | ~ v7_waybel_0(sK8)
% 2.82/1.00      | v2_struct_0(sK8)
% 2.82/1.00      | k10_yellow_6(sK7,sK8) != k10_yellow_6(sK7,sK8) ),
% 2.82/1.00      inference(unflattening,[status(thm)],[c_2459]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_2462,plain,
% 2.82/1.00      ( ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 2.82/1.00      | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
% 2.82/1.00      | r3_waybel_9(sK7,sK8,sK5(sK7,sK8))
% 2.82/1.00      | ~ r3_waybel_9(sK7,sK8,k1_waybel_9(sK7,sK8))
% 2.82/1.00      | k10_yellow_6(sK7,sK8) != k10_yellow_6(sK7,sK8) ),
% 2.82/1.00      inference(global_propositional_subsumption,
% 2.82/1.00                [status(thm)],
% 2.82/1.00                [c_2460,c_31,c_30,c_29]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_2463,plain,
% 2.82/1.00      ( ~ r3_waybel_9(sK7,sK8,k1_waybel_9(sK7,sK8))
% 2.82/1.00      | r3_waybel_9(sK7,sK8,sK5(sK7,sK8))
% 2.82/1.00      | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
% 2.82/1.00      | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 2.82/1.00      | k10_yellow_6(sK7,sK8) != k10_yellow_6(sK7,sK8) ),
% 2.82/1.00      inference(renaming,[status(thm)],[c_2462]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_3458,plain,
% 2.82/1.00      ( ~ r3_waybel_9(sK7,sK8,k1_waybel_9(sK7,sK8))
% 2.82/1.00      | r3_waybel_9(sK7,sK8,sK5(sK7,sK8))
% 2.82/1.00      | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
% 2.82/1.00      | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) ),
% 2.82/1.00      inference(equality_resolution_simp,[status(thm)],[c_2463]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_4362,plain,
% 2.82/1.00      ( ~ r3_waybel_9(sK7,sK8,k1_waybel_9(sK7,sK8))
% 2.82/1.00      | r3_waybel_9(sK7,sK8,sK5(sK7,sK8))
% 2.82/1.00      | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
% 2.82/1.00      | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) ),
% 2.82/1.00      inference(subtyping,[status(esa)],[c_3458]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_4900,plain,
% 2.82/1.00      ( r3_waybel_9(sK7,sK8,k1_waybel_9(sK7,sK8)) != iProver_top
% 2.82/1.00      | r3_waybel_9(sK7,sK8,sK5(sK7,sK8)) = iProver_top
% 2.82/1.00      | m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7)) != iProver_top
% 2.82/1.00      | r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) != iProver_top ),
% 2.82/1.00      inference(predicate_to_equality,[status(thm)],[c_4362]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_3459,plain,
% 2.82/1.00      ( r3_waybel_9(sK7,sK8,k1_waybel_9(sK7,sK8)) != iProver_top
% 2.82/1.00      | r3_waybel_9(sK7,sK8,sK5(sK7,sK8)) = iProver_top
% 2.82/1.00      | m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7)) != iProver_top
% 2.82/1.00      | r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) != iProver_top ),
% 2.82/1.00      inference(predicate_to_equality,[status(thm)],[c_3458]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_5991,plain,
% 2.82/1.00      ( r3_waybel_9(sK7,sK8,sK5(sK7,sK8)) = iProver_top
% 2.82/1.00      | r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) != iProver_top ),
% 2.82/1.00      inference(global_propositional_subsumption,
% 2.82/1.00                [status(thm)],
% 2.82/1.00                [c_4900,c_54,c_55,c_56,c_2370,c_2381,c_3459,c_5259,
% 2.82/1.00                 c_5271,c_5276]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_6726,plain,
% 2.82/1.00      ( r3_waybel_9(sK7,sK8,sK5(sK7,sK8)) = iProver_top ),
% 2.82/1.00      inference(superposition,[status(thm)],[c_6718,c_5991]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_6825,plain,
% 2.82/1.00      ( sK5(sK7,sK8) = sK3(sK7,sK8)
% 2.82/1.00      | m1_subset_1(sK5(sK7,sK8),u1_struct_0(sK7)) != iProver_top ),
% 2.82/1.00      inference(superposition,[status(thm)],[c_6726,c_5303]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_22,plain,
% 2.82/1.00      ( ~ r3_waybel_9(X0,X1,X2)
% 2.82/1.00      | r2_hidden(X2,k10_yellow_6(X0,X1))
% 2.82/1.00      | ~ l1_waybel_0(X1,X0)
% 2.82/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.82/1.00      | m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
% 2.82/1.00      | ~ v2_pre_topc(X0)
% 2.82/1.00      | ~ v8_pre_topc(X0)
% 2.82/1.00      | ~ v1_compts_1(X0)
% 2.82/1.00      | ~ v4_orders_2(X1)
% 2.82/1.00      | ~ v7_waybel_0(X1)
% 2.82/1.00      | ~ l1_pre_topc(X0)
% 2.82/1.00      | v2_struct_0(X0)
% 2.82/1.00      | v2_struct_0(X1) ),
% 2.82/1.00      inference(cnf_transformation,[],[f74]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_1860,plain,
% 2.82/1.00      ( ~ r3_waybel_9(X0,X1,X2)
% 2.82/1.00      | ~ l1_waybel_0(X1,X0)
% 2.82/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.82/1.00      | m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
% 2.82/1.00      | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 2.82/1.00      | ~ v2_pre_topc(X0)
% 2.82/1.00      | ~ v8_pre_topc(X0)
% 2.82/1.00      | ~ v1_compts_1(X0)
% 2.82/1.00      | ~ v4_orders_2(X1)
% 2.82/1.00      | ~ v7_waybel_0(X1)
% 2.82/1.00      | ~ l1_pre_topc(X0)
% 2.82/1.00      | v2_struct_0(X0)
% 2.82/1.00      | v2_struct_0(X1)
% 2.82/1.00      | k1_waybel_9(sK7,sK8) != X2
% 2.82/1.00      | k10_yellow_6(X0,X1) != k10_yellow_6(sK7,sK8) ),
% 2.82/1.00      inference(resolution_lifted,[status(thm)],[c_22,c_470]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_1861,plain,
% 2.82/1.00      ( ~ r3_waybel_9(X0,X1,k1_waybel_9(sK7,sK8))
% 2.82/1.00      | ~ l1_waybel_0(X1,X0)
% 2.82/1.00      | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(X0))
% 2.82/1.00      | m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
% 2.82/1.00      | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 2.82/1.00      | ~ v2_pre_topc(X0)
% 2.82/1.00      | ~ v8_pre_topc(X0)
% 2.82/1.00      | ~ v1_compts_1(X0)
% 2.82/1.00      | ~ v4_orders_2(X1)
% 2.82/1.00      | ~ v7_waybel_0(X1)
% 2.82/1.00      | ~ l1_pre_topc(X0)
% 2.82/1.00      | v2_struct_0(X0)
% 2.82/1.00      | v2_struct_0(X1)
% 2.82/1.00      | k10_yellow_6(X0,X1) != k10_yellow_6(sK7,sK8) ),
% 2.82/1.00      inference(unflattening,[status(thm)],[c_1860]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_2174,plain,
% 2.82/1.00      ( ~ r3_waybel_9(X0,X1,k1_waybel_9(sK7,sK8))
% 2.82/1.00      | ~ l1_waybel_0(X1,X0)
% 2.82/1.00      | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(X0))
% 2.82/1.00      | m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
% 2.82/1.00      | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 2.82/1.00      | ~ v2_pre_topc(X0)
% 2.82/1.00      | ~ v8_pre_topc(X0)
% 2.82/1.00      | ~ v1_compts_1(X0)
% 2.82/1.00      | ~ v4_orders_2(X1)
% 2.82/1.00      | ~ v7_waybel_0(X1)
% 2.82/1.00      | v2_struct_0(X0)
% 2.82/1.00      | v2_struct_0(X1)
% 2.82/1.00      | k10_yellow_6(X0,X1) != k10_yellow_6(sK7,sK8)
% 2.82/1.00      | sK7 != X0 ),
% 2.82/1.00      inference(resolution_lifted,[status(thm)],[c_1861,c_1316]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_2175,plain,
% 2.82/1.00      ( ~ r3_waybel_9(sK7,X0,k1_waybel_9(sK7,sK8))
% 2.82/1.00      | ~ l1_waybel_0(X0,sK7)
% 2.82/1.00      | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
% 2.82/1.00      | m1_subset_1(sK5(sK7,X0),u1_struct_0(sK7))
% 2.82/1.00      | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 2.82/1.00      | ~ v2_pre_topc(sK7)
% 2.82/1.00      | ~ v8_pre_topc(sK7)
% 2.82/1.00      | ~ v1_compts_1(sK7)
% 2.82/1.00      | ~ v4_orders_2(X0)
% 2.82/1.00      | ~ v7_waybel_0(X0)
% 2.82/1.00      | v2_struct_0(X0)
% 2.82/1.00      | v2_struct_0(sK7)
% 2.82/1.00      | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8) ),
% 2.82/1.00      inference(unflattening,[status(thm)],[c_2174]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_2179,plain,
% 2.82/1.00      ( v2_struct_0(X0)
% 2.82/1.00      | ~ v7_waybel_0(X0)
% 2.82/1.00      | ~ v4_orders_2(X0)
% 2.82/1.00      | ~ r3_waybel_9(sK7,X0,k1_waybel_9(sK7,sK8))
% 2.82/1.00      | ~ l1_waybel_0(X0,sK7)
% 2.82/1.00      | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
% 2.82/1.00      | m1_subset_1(sK5(sK7,X0),u1_struct_0(sK7))
% 2.82/1.00      | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 2.82/1.00      | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8) ),
% 2.82/1.00      inference(global_propositional_subsumption,
% 2.82/1.00                [status(thm)],
% 2.82/1.00                [c_2175,c_41,c_40,c_36,c_34,c_33,c_103,c_136]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_2180,plain,
% 2.82/1.00      ( ~ r3_waybel_9(sK7,X0,k1_waybel_9(sK7,sK8))
% 2.82/1.00      | ~ l1_waybel_0(X0,sK7)
% 2.82/1.00      | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
% 2.82/1.00      | m1_subset_1(sK5(sK7,X0),u1_struct_0(sK7))
% 2.82/1.00      | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 2.82/1.00      | ~ v4_orders_2(X0)
% 2.82/1.00      | ~ v7_waybel_0(X0)
% 2.82/1.00      | v2_struct_0(X0)
% 2.82/1.00      | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8) ),
% 2.82/1.00      inference(renaming,[status(thm)],[c_2179]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_2413,plain,
% 2.82/1.00      ( ~ r3_waybel_9(sK7,X0,k1_waybel_9(sK7,sK8))
% 2.82/1.00      | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
% 2.82/1.00      | m1_subset_1(sK5(sK7,X0),u1_struct_0(sK7))
% 2.82/1.00      | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 2.82/1.00      | ~ v4_orders_2(X0)
% 2.82/1.00      | ~ v7_waybel_0(X0)
% 2.82/1.00      | v2_struct_0(X0)
% 2.82/1.00      | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8)
% 2.82/1.00      | sK8 != X0
% 2.82/1.00      | sK7 != sK7 ),
% 2.82/1.00      inference(resolution_lifted,[status(thm)],[c_28,c_2180]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_2414,plain,
% 2.82/1.00      ( ~ r3_waybel_9(sK7,sK8,k1_waybel_9(sK7,sK8))
% 2.82/1.00      | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
% 2.82/1.00      | m1_subset_1(sK5(sK7,sK8),u1_struct_0(sK7))
% 2.82/1.00      | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 2.82/1.00      | ~ v4_orders_2(sK8)
% 2.82/1.00      | ~ v7_waybel_0(sK8)
% 2.82/1.00      | v2_struct_0(sK8)
% 2.82/1.00      | k10_yellow_6(sK7,sK8) != k10_yellow_6(sK7,sK8) ),
% 2.82/1.00      inference(unflattening,[status(thm)],[c_2413]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_2416,plain,
% 2.82/1.00      ( ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 2.82/1.00      | m1_subset_1(sK5(sK7,sK8),u1_struct_0(sK7))
% 2.82/1.00      | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
% 2.82/1.00      | ~ r3_waybel_9(sK7,sK8,k1_waybel_9(sK7,sK8))
% 2.82/1.00      | k10_yellow_6(sK7,sK8) != k10_yellow_6(sK7,sK8) ),
% 2.82/1.00      inference(global_propositional_subsumption,
% 2.82/1.00                [status(thm)],
% 2.82/1.00                [c_2414,c_31,c_30,c_29]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_2417,plain,
% 2.82/1.00      ( ~ r3_waybel_9(sK7,sK8,k1_waybel_9(sK7,sK8))
% 2.82/1.00      | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
% 2.82/1.00      | m1_subset_1(sK5(sK7,sK8),u1_struct_0(sK7))
% 2.82/1.00      | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 2.82/1.00      | k10_yellow_6(sK7,sK8) != k10_yellow_6(sK7,sK8) ),
% 2.82/1.00      inference(renaming,[status(thm)],[c_2416]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_3462,plain,
% 2.82/1.00      ( ~ r3_waybel_9(sK7,sK8,k1_waybel_9(sK7,sK8))
% 2.82/1.00      | ~ m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7))
% 2.82/1.00      | m1_subset_1(sK5(sK7,sK8),u1_struct_0(sK7))
% 2.82/1.00      | ~ r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) ),
% 2.82/1.00      inference(equality_resolution_simp,[status(thm)],[c_2417]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_3463,plain,
% 2.82/1.00      ( r3_waybel_9(sK7,sK8,k1_waybel_9(sK7,sK8)) != iProver_top
% 2.82/1.00      | m1_subset_1(k1_waybel_9(sK7,sK8),u1_struct_0(sK7)) != iProver_top
% 2.82/1.00      | m1_subset_1(sK5(sK7,sK8),u1_struct_0(sK7)) = iProver_top
% 2.82/1.00      | r2_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) != iProver_top ),
% 2.82/1.00      inference(predicate_to_equality,[status(thm)],[c_3462]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(contradiction,plain,
% 2.82/1.00      ( $false ),
% 2.82/1.00      inference(minisat,
% 2.82/1.00                [status(thm)],
% 2.82/1.00                [c_7096,c_6825,c_6642,c_5276,c_5271,c_5259,c_3463,c_2381,
% 2.82/1.00                 c_2370,c_56,c_55,c_54]) ).
% 2.82/1.00  
% 2.82/1.00  
% 2.82/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.82/1.00  
% 2.82/1.00  ------                               Statistics
% 2.82/1.00  
% 2.82/1.00  ------ General
% 2.82/1.00  
% 2.82/1.00  abstr_ref_over_cycles:                  0
% 2.82/1.00  abstr_ref_under_cycles:                 0
% 2.82/1.00  gc_basic_clause_elim:                   0
% 2.82/1.00  forced_gc_time:                         0
% 2.82/1.00  parsing_time:                           0.013
% 2.82/1.00  unif_index_cands_time:                  0.
% 2.82/1.00  unif_index_add_time:                    0.
% 2.82/1.00  orderings_time:                         0.
% 2.82/1.00  out_proof_time:                         0.025
% 2.82/1.00  total_time:                             0.22
% 2.82/1.00  num_of_symbols:                         82
% 2.82/1.00  num_of_terms:                           2888
% 2.82/1.00  
% 2.82/1.00  ------ Preprocessing
% 2.82/1.00  
% 2.82/1.00  num_of_splits:                          6
% 2.82/1.00  num_of_split_atoms:                     6
% 2.82/1.00  num_of_reused_defs:                     0
% 2.82/1.00  num_eq_ax_congr_red:                    57
% 2.82/1.00  num_of_sem_filtered_clauses:            1
% 2.82/1.00  num_of_subtypes:                        6
% 2.82/1.00  monotx_restored_types:                  0
% 2.82/1.00  sat_num_of_epr_types:                   0
% 2.82/1.00  sat_num_of_non_cyclic_types:            0
% 2.82/1.00  sat_guarded_non_collapsed_types:        1
% 2.82/1.00  num_pure_diseq_elim:                    0
% 2.82/1.00  simp_replaced_by:                       0
% 2.82/1.00  res_preprocessed:                       136
% 2.82/1.00  prep_upred:                             0
% 2.82/1.00  prep_unflattend:                        112
% 2.82/1.00  smt_new_axioms:                         0
% 2.82/1.00  pred_elim_cands:                        5
% 2.82/1.00  pred_elim:                              18
% 2.82/1.00  pred_elim_cl:                           21
% 2.82/1.00  pred_elim_cycles:                       24
% 2.82/1.00  merged_defs:                            0
% 2.82/1.00  merged_defs_ncl:                        0
% 2.82/1.00  bin_hyper_res:                          0
% 2.82/1.00  prep_cycles:                            4
% 2.82/1.00  pred_elim_time:                         0.078
% 2.82/1.00  splitting_time:                         0.
% 2.82/1.00  sem_filter_time:                        0.
% 2.82/1.00  monotx_time:                            0.
% 2.82/1.00  subtype_inf_time:                       0.
% 2.82/1.00  
% 2.82/1.00  ------ Problem properties
% 2.82/1.00  
% 2.82/1.00  clauses:                                27
% 2.82/1.00  conjectures:                            0
% 2.82/1.00  epr:                                    3
% 2.82/1.00  horn:                                   17
% 2.82/1.00  ground:                                 10
% 2.82/1.00  unary:                                  2
% 2.82/1.00  binary:                                 3
% 2.82/1.00  lits:                                   97
% 2.82/1.00  lits_eq:                                9
% 2.82/1.00  fd_pure:                                0
% 2.82/1.00  fd_pseudo:                              0
% 2.82/1.00  fd_cond:                                2
% 2.82/1.00  fd_pseudo_cond:                         3
% 2.82/1.00  ac_symbols:                             0
% 2.82/1.00  
% 2.82/1.00  ------ Propositional Solver
% 2.82/1.00  
% 2.82/1.00  prop_solver_calls:                      28
% 2.82/1.00  prop_fast_solver_calls:                 2545
% 2.82/1.00  smt_solver_calls:                       0
% 2.82/1.00  smt_fast_solver_calls:                  0
% 2.82/1.00  prop_num_of_clauses:                    1627
% 2.82/1.00  prop_preprocess_simplified:             5193
% 2.82/1.00  prop_fo_subsumed:                       167
% 2.82/1.00  prop_solver_time:                       0.
% 2.82/1.00  smt_solver_time:                        0.
% 2.82/1.00  smt_fast_solver_time:                   0.
% 2.82/1.00  prop_fast_solver_time:                  0.
% 2.82/1.00  prop_unsat_core_time:                   0.
% 2.82/1.00  
% 2.82/1.00  ------ QBF
% 2.82/1.00  
% 2.82/1.00  qbf_q_res:                              0
% 2.82/1.00  qbf_num_tautologies:                    0
% 2.82/1.00  qbf_prep_cycles:                        0
% 2.82/1.00  
% 2.82/1.00  ------ BMC1
% 2.82/1.00  
% 2.82/1.00  bmc1_current_bound:                     -1
% 2.82/1.00  bmc1_last_solved_bound:                 -1
% 2.82/1.00  bmc1_unsat_core_size:                   -1
% 2.82/1.00  bmc1_unsat_core_parents_size:           -1
% 2.82/1.00  bmc1_merge_next_fun:                    0
% 2.82/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.82/1.00  
% 2.82/1.00  ------ Instantiation
% 2.82/1.00  
% 2.82/1.00  inst_num_of_clauses:                    314
% 2.82/1.00  inst_num_in_passive:                    1
% 2.82/1.00  inst_num_in_active:                     222
% 2.82/1.00  inst_num_in_unprocessed:                91
% 2.82/1.00  inst_num_of_loops:                      240
% 2.82/1.00  inst_num_of_learning_restarts:          0
% 2.82/1.00  inst_num_moves_active_passive:          14
% 2.82/1.00  inst_lit_activity:                      0
% 2.82/1.00  inst_lit_activity_moves:                0
% 2.82/1.00  inst_num_tautologies:                   0
% 2.82/1.00  inst_num_prop_implied:                  0
% 2.82/1.00  inst_num_existing_simplified:           0
% 2.82/1.00  inst_num_eq_res_simplified:             0
% 2.82/1.00  inst_num_child_elim:                    0
% 2.82/1.00  inst_num_of_dismatching_blockings:      1
% 2.82/1.00  inst_num_of_non_proper_insts:           269
% 2.82/1.00  inst_num_of_duplicates:                 0
% 2.82/1.00  inst_inst_num_from_inst_to_res:         0
% 2.82/1.00  inst_dismatching_checking_time:         0.
% 2.82/1.00  
% 2.82/1.00  ------ Resolution
% 2.82/1.00  
% 2.82/1.00  res_num_of_clauses:                     0
% 2.82/1.00  res_num_in_passive:                     0
% 2.82/1.00  res_num_in_active:                      0
% 2.82/1.00  res_num_of_loops:                       140
% 2.82/1.00  res_forward_subset_subsumed:            9
% 2.82/1.00  res_backward_subset_subsumed:           0
% 2.82/1.00  res_forward_subsumed:                   0
% 2.82/1.00  res_backward_subsumed:                  0
% 2.82/1.00  res_forward_subsumption_resolution:     10
% 2.82/1.00  res_backward_subsumption_resolution:    0
% 2.82/1.00  res_clause_to_clause_subsumption:       234
% 2.82/1.00  res_orphan_elimination:                 0
% 2.82/1.00  res_tautology_del:                      46
% 2.82/1.00  res_num_eq_res_simplified:              5
% 2.82/1.00  res_num_sel_changes:                    0
% 2.82/1.00  res_moves_from_active_to_pass:          0
% 2.82/1.00  
% 2.82/1.00  ------ Superposition
% 2.82/1.00  
% 2.82/1.00  sup_time_total:                         0.
% 2.82/1.00  sup_time_generating:                    0.
% 2.82/1.00  sup_time_sim_full:                      0.
% 2.82/1.00  sup_time_sim_immed:                     0.
% 2.82/1.00  
% 2.82/1.00  sup_num_of_clauses:                     45
% 2.82/1.00  sup_num_in_active:                      37
% 2.82/1.00  sup_num_in_passive:                     8
% 2.82/1.00  sup_num_of_loops:                       47
% 2.82/1.00  sup_fw_superposition:                   14
% 2.82/1.00  sup_bw_superposition:                   21
% 2.82/1.00  sup_immediate_simplified:               10
% 2.82/1.00  sup_given_eliminated:                   0
% 2.82/1.00  comparisons_done:                       0
% 2.82/1.00  comparisons_avoided:                    0
% 2.82/1.00  
% 2.82/1.00  ------ Simplifications
% 2.82/1.00  
% 2.82/1.00  
% 2.82/1.00  sim_fw_subset_subsumed:                 5
% 2.82/1.00  sim_bw_subset_subsumed:                 8
% 2.82/1.00  sim_fw_subsumed:                        1
% 2.82/1.00  sim_bw_subsumed:                        0
% 2.82/1.00  sim_fw_subsumption_res:                 2
% 2.82/1.00  sim_bw_subsumption_res:                 0
% 2.82/1.00  sim_tautology_del:                      0
% 2.82/1.00  sim_eq_tautology_del:                   3
% 2.82/1.00  sim_eq_res_simp:                        0
% 2.82/1.00  sim_fw_demodulated:                     2
% 2.82/1.00  sim_bw_demodulated:                     6
% 2.82/1.00  sim_light_normalised:                   2
% 2.82/1.00  sim_joinable_taut:                      0
% 2.82/1.00  sim_joinable_simp:                      0
% 2.82/1.00  sim_ac_normalised:                      0
% 2.82/1.00  sim_smt_subsumption:                    0
% 2.82/1.00  
%------------------------------------------------------------------------------
