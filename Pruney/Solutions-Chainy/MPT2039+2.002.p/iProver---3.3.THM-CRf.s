%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:59 EST 2020

% Result     : Theorem 3.10s
% Output     : CNFRefutation 3.10s
% Verified   : 
% Statistics : Number of formulae       :  375 (21713 expanded)
%              Number of clauses        :  277 (3705 expanded)
%              Number of leaves         :   22 (5400 expanded)
%              Depth                    :   37
%              Number of atoms          : 3044 (324907 expanded)
%              Number of equality atoms :  418 (3213 expanded)
%              Maximal formula depth    :   28 (   9 average)
%              Maximal clause size      :   36 (   7 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
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
           => ( v10_waybel_0(X1,X0)
             => ( r2_hidden(k1_waybel_2(X0,X1),k10_yellow_6(X0,X1))
                & r1_waybel_9(X0,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
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
             => ( v10_waybel_0(X1,X0)
               => ( r2_hidden(k1_waybel_2(X0,X1),k10_yellow_6(X0,X1))
                  & r1_waybel_9(X0,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f16,plain,(
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
             => ( v10_waybel_0(X2,X0)
               => ( r2_hidden(k1_waybel_2(X0,X2),k10_yellow_6(X0,X2))
                  & r1_waybel_9(X0,X2) ) ) ) ) ) ),
    inference(rectify,[],[f12])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(k1_waybel_2(X0,X2),k10_yellow_6(X0,X2))
            | ~ r1_waybel_9(X0,X2) )
          & v10_waybel_0(X2,X0)
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
    inference(ennf_transformation,[],[f16])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(k1_waybel_2(X0,X2),k10_yellow_6(X0,X2))
            | ~ r1_waybel_9(X0,X2) )
          & v10_waybel_0(X2,X0)
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
    inference(flattening,[],[f35])).

fof(f54,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r2_hidden(k1_waybel_2(X0,X1),k10_yellow_6(X0,X1))
            | ~ r1_waybel_9(X0,X1) )
          & v10_waybel_0(X1,X0)
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
    inference(rectify,[],[f36])).

fof(f56,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ r2_hidden(k1_waybel_2(X0,X1),k10_yellow_6(X0,X1))
            | ~ r1_waybel_9(X0,X1) )
          & v10_waybel_0(X1,X0)
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
     => ( ( ~ r2_hidden(k1_waybel_2(X0,sK8),k10_yellow_6(X0,sK8))
          | ~ r1_waybel_9(X0,sK8) )
        & v10_waybel_0(sK8,X0)
        & l1_waybel_0(sK8,X0)
        & v7_waybel_0(sK8)
        & v4_orders_2(sK8)
        & ~ v2_struct_0(sK8) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r2_hidden(k1_waybel_2(X0,X1),k10_yellow_6(X0,X1))
              | ~ r1_waybel_9(X0,X1) )
            & v10_waybel_0(X1,X0)
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
          ( ( ~ r2_hidden(k1_waybel_2(sK7,X1),k10_yellow_6(sK7,X1))
            | ~ r1_waybel_9(sK7,X1) )
          & v10_waybel_0(X1,sK7)
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

fof(f57,plain,
    ( ( ~ r2_hidden(k1_waybel_2(sK7,sK8),k10_yellow_6(sK7,sK8))
      | ~ r1_waybel_9(sK7,sK8) )
    & v10_waybel_0(sK8,sK7)
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f54,f56,f55])).

fof(f99,plain,(
    l1_waybel_0(sK8,sK7) ),
    inference(cnf_transformation,[],[f57])).

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
         => ? [X2] :
              ( r3_waybel_9(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( r3_waybel_9(X0,X1,X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( r3_waybel_9(X0,X1,sK3(X0,X1))
        & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f46])).

fof(f78,plain,(
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
    inference(cnf_transformation,[],[f47])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_waybel_9(X0)
     => ( l1_orders_2(X0)
        & l1_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & l1_pre_topc(X0) )
      | ~ l1_waybel_9(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f71,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
      | ~ l1_waybel_9(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f94,plain,(
    l1_waybel_9(sK7) ),
    inference(cnf_transformation,[],[f57])).

fof(f86,plain,(
    v2_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f57])).

fof(f87,plain,(
    v8_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f57])).

fof(f91,plain,(
    v1_lattice3(sK7) ),
    inference(cnf_transformation,[],[f57])).

fof(f93,plain,(
    v1_compts_1(sK7) ),
    inference(cnf_transformation,[],[f57])).

fof(f72,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
      | ~ l1_waybel_9(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f19])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f96,plain,(
    ~ v2_struct_0(sK8) ),
    inference(cnf_transformation,[],[f57])).

fof(f97,plain,(
    v4_orders_2(sK8) ),
    inference(cnf_transformation,[],[f57])).

fof(f98,plain,(
    v7_waybel_0(sK8) ),
    inference(cnf_transformation,[],[f57])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X1,X3) ) )
                  & r2_lattice3(X0,X2,X1) )
               => ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 ) )
              & ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
               => ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X1,X3) ) )
                  & r2_lattice3(X0,X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X1,X3) ) )
                  & r2_lattice3(X0,X2,X1) )
               => ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 ) )
              & ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
               => ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X4)
                       => r1_orders_2(X0,X1,X4) ) )
                  & r2_lattice3(X0,X2,X1) ) ) ) ) ) ),
    inference(rectify,[],[f3])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X1,X3)
                    & r2_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X1,X4)
                      | ~ r2_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X2,X1) )
                | ~ r1_yellow_0(X0,X2)
                | k1_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X1,X3)
                    & r2_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X1,X4)
                      | ~ r2_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X2,X1) )
                | ~ r1_yellow_0(X0,X2)
                | k1_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f21])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X1,X3)
          & r2_lattice3(X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X1,sK0(X0,X1,X2))
        & r2_lattice3(X0,X2,sK0(X0,X1,X2))
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
                | ( ~ r1_orders_2(X0,X1,sK0(X0,X1,X2))
                  & r2_lattice3(X0,X2,sK0(X0,X1,X2))
                  & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X1,X4)
                      | ~ r2_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X2,X1) )
                | ~ r1_yellow_0(X0,X2)
                | k1_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f38])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r1_yellow_0(X0,X2)
      | r2_lattice3(X0,X2,sK0(X0,X1,X2))
      | ~ r2_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f90,plain,(
    v5_orders_2(sK7) ),
    inference(cnf_transformation,[],[f57])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_orders_2(X0,X1,X2)
          | ~ r1_orders_2(X0,X1,X2) )
        & ( r1_orders_2(X0,X1,X2)
          | ~ r3_orders_2(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f7,axiom,(
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
                       => ( r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
                         => r3_orders_2(X0,X3,X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
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
                       => ( r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5)
                         => r3_orders_2(X0,X3,X5) ) ) ) ) ) ) ) ),
    inference(rectify,[],[f7])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X5] :
                      ( r3_orders_2(X0,X3,X5)
                      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5)
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
    inference(ennf_transformation,[],[f14])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X5] :
                      ( r3_orders_2(X0,X3,X5)
                      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5)
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
    inference(flattening,[],[f27])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r3_orders_2(X0,X3,X4)
                      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
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
    inference(rectify,[],[f28])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X5] :
          ( ~ v5_pre_topc(k4_waybel_1(X0,X5),X0,X0)
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( ~ v5_pre_topc(k4_waybel_1(X0,sK2(X0)),X0,X0)
        & m1_subset_1(sK2(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r3_orders_2(X0,X3,X4)
                      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f43,f44])).

fof(f76,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r3_orders_2(X0,X3,X4)
      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
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
    inference(cnf_transformation,[],[f45])).

fof(f106,plain,(
    ! [X4,X0,X3,X1] :
      ( r3_orders_2(X0,X3,X4)
      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
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
    inference(equality_resolution,[],[f76])).

fof(f95,plain,(
    ! [X2] :
      ( v5_pre_topc(k4_waybel_1(sK7,X2),sK7,sK7)
      | ~ m1_subset_1(X2,u1_struct_0(sK7)) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f88,plain,(
    v3_orders_2(sK7) ),
    inference(cnf_transformation,[],[f57])).

fof(f89,plain,(
    v4_orders_2(sK7) ),
    inference(cnf_transformation,[],[f57])).

fof(f92,plain,(
    v2_lattice3(sK7) ),
    inference(cnf_transformation,[],[f57])).

fof(f75,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r3_orders_2(X0,X3,X4)
      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
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
    inference(cnf_transformation,[],[f45])).

fof(f107,plain,(
    ! [X4,X0,X3,X1] :
      ( r3_orders_2(X0,X3,X4)
      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
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
    inference(equality_resolution,[],[f75])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r1_yellow_0(X0,X2)
      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
      | ~ r2_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r1_yellow_0(X0,X2)
      | ~ r1_orders_2(X0,X1,sK0(X0,X1,X2))
      | ~ r2_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f100,plain,(
    v10_waybel_0(sK8,sK7) ),
    inference(cnf_transformation,[],[f57])).

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
                      & v10_waybel_0(X1,X0)
                      & ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) )
                      & X2 = X3 )
                   => r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ~ v10_waybel_0(X1,X0)
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
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ~ v10_waybel_0(X1,X0)
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
    inference(flattening,[],[f25])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X4] :
          ( ~ v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ v5_pre_topc(k4_waybel_1(X0,sK1(X0)),X0,X0)
        & m1_subset_1(sK1(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ~ v10_waybel_0(X1,X0)
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f41])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ v10_waybel_0(X1,X0)
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
    inference(cnf_transformation,[],[f42])).

fof(f105,plain,(
    ! [X0,X3,X1] :
      ( r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
      | ~ r3_waybel_9(X0,X1,X3)
      | ~ v10_waybel_0(X1,X0)
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
    inference(equality_resolution,[],[f73])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ v10_waybel_0(X1,X0)
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
    inference(cnf_transformation,[],[f42])).

fof(f104,plain,(
    ! [X0,X3,X1] :
      ( r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
      | ~ r3_waybel_9(X0,X1,X3)
      | ~ v10_waybel_0(X1,X0)
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
    inference(equality_resolution,[],[f74])).

fof(f77,plain,(
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
    inference(cnf_transformation,[],[f47])).

fof(f9,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
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
    inference(rectify,[],[f9])).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f48,plain,(
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
    inference(rectify,[],[f32])).

fof(f50,plain,(
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

fof(f49,plain,(
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

fof(f51,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f48,f50,f49])).

fof(f81,plain,(
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
    inference(cnf_transformation,[],[f51])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => ( r1_waybel_9(X0,X1)
          <=> r1_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_waybel_9(X0,X1)
          <=> r1_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) )
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_waybel_9(X0,X1)
              | ~ r1_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) )
            & ( r1_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
              | ~ r1_waybel_9(X0,X1) ) )
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_waybel_9(X0,X1)
      | ~ r1_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f101,plain,
    ( ~ r2_hidden(k1_waybel_2(sK7,sK8),k10_yellow_6(sK7,sK8))
    | ~ r1_waybel_9(sK7,sK8) ),
    inference(cnf_transformation,[],[f57])).

fof(f10,axiom,(
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
                  & v10_waybel_0(X2,X0)
                  & ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) ) )
               => k1_waybel_2(X0,X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_waybel_2(X0,X2) = X1
              | ~ r3_waybel_9(X0,X2,X1)
              | ~ v10_waybel_0(X2,X0)
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
    inference(ennf_transformation,[],[f10])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_waybel_2(X0,X2) = X1
              | ~ r3_waybel_9(X0,X2,X1)
              | ~ v10_waybel_0(X2,X0)
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
    inference(flattening,[],[f33])).

fof(f52,plain,(
    ! [X0] :
      ( ? [X3] :
          ( ~ v5_pre_topc(k4_waybel_1(X0,X3),X0,X0)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ v5_pre_topc(k4_waybel_1(X0,sK6(X0)),X0,X0)
        & m1_subset_1(sK6(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_waybel_2(X0,X2) = X1
              | ~ r3_waybel_9(X0,X2,X1)
              | ~ v10_waybel_0(X2,X0)
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f34,f52])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k1_waybel_2(X0,X2) = X1
      | ~ r3_waybel_9(X0,X2,X1)
      | ~ v10_waybel_0(X2,X0)
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
    inference(cnf_transformation,[],[f53])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k1_waybel_2(X0,X2) = X1
      | ~ r3_waybel_9(X0,X2,X1)
      | ~ v10_waybel_0(X2,X0)
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
    inference(cnf_transformation,[],[f53])).

fof(f79,plain,(
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
    inference(cnf_transformation,[],[f51])).

fof(f83,plain,(
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
    inference(cnf_transformation,[],[f51])).

fof(f82,plain,(
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
    inference(cnf_transformation,[],[f51])).

fof(f80,plain,(
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
    inference(cnf_transformation,[],[f51])).

cnf(c_30,negated_conjecture,
    ( l1_waybel_0(sK8,sK7) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_19,plain,
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
    inference(cnf_transformation,[],[f78])).

cnf(c_14,plain,
    ( l1_pre_topc(X0)
    | ~ l1_waybel_9(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_35,negated_conjecture,
    ( l1_waybel_9(sK7) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1552,plain,
    ( l1_pre_topc(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_35])).

cnf(c_1553,plain,
    ( l1_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_1552])).

cnf(c_2489,plain,
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
    inference(resolution_lifted,[status(thm)],[c_19,c_1553])).

cnf(c_2490,plain,
    ( r3_waybel_9(sK7,X0,sK3(sK7,X0))
    | ~ l1_waybel_0(X0,sK7)
    | ~ v2_pre_topc(sK7)
    | ~ v8_pre_topc(sK7)
    | ~ v1_compts_1(sK7)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK7) ),
    inference(unflattening,[status(thm)],[c_2489])).

cnf(c_43,negated_conjecture,
    ( v2_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_42,negated_conjecture,
    ( v8_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_38,negated_conjecture,
    ( v1_lattice3(sK7) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_36,negated_conjecture,
    ( v1_compts_1(sK7) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_13,plain,
    ( ~ l1_waybel_9(X0)
    | l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_105,plain,
    ( ~ l1_waybel_9(sK7)
    | l1_orders_2(sK7) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2,plain,
    ( ~ v1_lattice3(X0)
    | ~ v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_138,plain,
    ( ~ v1_lattice3(sK7)
    | ~ v2_struct_0(sK7)
    | ~ l1_orders_2(sK7) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2494,plain,
    ( v2_struct_0(X0)
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | r3_waybel_9(sK7,X0,sK3(sK7,X0))
    | ~ l1_waybel_0(X0,sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2490,c_43,c_42,c_38,c_36,c_35,c_105,c_138])).

cnf(c_2495,plain,
    ( r3_waybel_9(sK7,X0,sK3(sK7,X0))
    | ~ l1_waybel_0(X0,sK7)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_2494])).

cnf(c_2616,plain,
    ( r3_waybel_9(sK7,X0,sK3(sK7,X0))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | sK8 != X0
    | sK7 != sK7 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_2495])).

cnf(c_2617,plain,
    ( r3_waybel_9(sK7,sK8,sK3(sK7,sK8))
    | ~ v4_orders_2(sK8)
    | ~ v7_waybel_0(sK8)
    | v2_struct_0(sK8) ),
    inference(unflattening,[status(thm)],[c_2616])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK8) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_32,negated_conjecture,
    ( v4_orders_2(sK8) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_31,negated_conjecture,
    ( v7_waybel_0(sK8) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_2619,plain,
    ( r3_waybel_9(sK7,sK8,sK3(sK7,sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2617,c_33,c_32,c_31])).

cnf(c_4603,plain,
    ( r3_waybel_9(sK7,sK8,sK3(sK7,sK8)) ),
    inference(subtyping,[status(esa)],[c_2619])).

cnf(c_5131,plain,
    ( r3_waybel_9(sK7,sK8,sK3(sK7,sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4603])).

cnf(c_4,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X1,sK0(X0,X2,X1))
    | r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_912,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X1,sK0(X0,X2,X1))
    | r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0) ),
    inference(resolution,[status(thm)],[c_13,c_4])).

cnf(c_39,negated_conjecture,
    ( v5_orders_2(sK7) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1344,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X1,sK0(X0,X2,X1))
    | r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_waybel_9(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_912,c_39])).

cnf(c_1345,plain,
    ( ~ r2_lattice3(sK7,X0,X1)
    | r2_lattice3(sK7,X0,sK0(sK7,X1,X0))
    | r1_yellow_0(sK7,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ l1_waybel_9(sK7) ),
    inference(unflattening,[status(thm)],[c_1344])).

cnf(c_1349,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK7))
    | r1_yellow_0(sK7,X0)
    | r2_lattice3(sK7,X0,sK0(sK7,X1,X0))
    | ~ r2_lattice3(sK7,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1345,c_35])).

cnf(c_1350,plain,
    ( ~ r2_lattice3(sK7,X0,X1)
    | r2_lattice3(sK7,X0,sK0(sK7,X1,X0))
    | r1_yellow_0(sK7,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK7)) ),
    inference(renaming,[status(thm)],[c_1349])).

cnf(c_4611,plain,
    ( ~ r2_lattice3(sK7,X0_70,X0_69)
    | r2_lattice3(sK7,X0_70,sK0(sK7,X0_69,X0_70))
    | r1_yellow_0(sK7,X0_70)
    | ~ m1_subset_1(X0_69,u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_1350])).

cnf(c_5123,plain,
    ( r2_lattice3(sK7,X0_70,X0_69) != iProver_top
    | r2_lattice3(sK7,X0_70,sK0(sK7,X0_69,X0_70)) = iProver_top
    | r1_yellow_0(sK7,X0_70) = iProver_top
    | m1_subset_1(X0_69,u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4611])).

cnf(c_1,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_17,plain,
    ( ~ v5_pre_topc(k4_waybel_1(X0,sK2(X0)),X0,X0)
    | ~ r3_waybel_9(X0,X1,X2)
    | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
    | r3_orders_2(X0,X2,X3)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v2_lattice3(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X0) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_34,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(sK7,X0),sK7,sK7)
    | ~ m1_subset_1(X0,u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_547,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
    | r3_orders_2(X0,X2,X3)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(sK7))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v2_lattice3(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X0)
    | k4_waybel_1(X0,sK2(X0)) != k4_waybel_1(sK7,X4)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_34])).

cnf(c_548,plain,
    ( ~ r3_waybel_9(sK7,X0,X1)
    | ~ r2_lattice3(sK7,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK7),u1_waybel_0(sK7,X0)),X2)
    | r3_orders_2(sK7,X1,X2)
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ m1_subset_1(X3,u1_struct_0(sK7))
    | ~ v2_pre_topc(sK7)
    | ~ v8_pre_topc(sK7)
    | ~ v2_lattice3(sK7)
    | ~ v1_compts_1(sK7)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(sK7)
    | ~ v7_waybel_0(X0)
    | ~ l1_waybel_9(sK7)
    | ~ v5_orders_2(sK7)
    | ~ v1_lattice3(sK7)
    | v2_struct_0(X0)
    | ~ v3_orders_2(sK7)
    | k4_waybel_1(sK7,sK2(sK7)) != k4_waybel_1(sK7,X3) ),
    inference(unflattening,[status(thm)],[c_547])).

cnf(c_41,negated_conjecture,
    ( v3_orders_2(sK7) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_40,negated_conjecture,
    ( v4_orders_2(sK7) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_37,negated_conjecture,
    ( v2_lattice3(sK7) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_552,plain,
    ( v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ m1_subset_1(X3,u1_struct_0(sK7))
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ l1_waybel_0(X0,sK7)
    | r3_orders_2(sK7,X1,X2)
    | ~ r2_lattice3(sK7,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK7),u1_waybel_0(sK7,X0)),X2)
    | ~ r3_waybel_9(sK7,X0,X1)
    | ~ v7_waybel_0(X0)
    | k4_waybel_1(sK7,sK2(sK7)) != k4_waybel_1(sK7,X3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_548,c_43,c_42,c_41,c_40,c_39,c_38,c_37,c_36,c_35])).

cnf(c_553,plain,
    ( ~ r3_waybel_9(sK7,X0,X1)
    | ~ r2_lattice3(sK7,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK7),u1_waybel_0(sK7,X0)),X2)
    | r3_orders_2(sK7,X1,X2)
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ m1_subset_1(X3,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | k4_waybel_1(sK7,sK2(sK7)) != k4_waybel_1(sK7,X3) ),
    inference(renaming,[status(thm)],[c_552])).

cnf(c_727,plain,
    ( ~ r3_waybel_9(sK7,X0,X1)
    | ~ r2_lattice3(sK7,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK7),u1_waybel_0(sK7,X0)),X2)
    | r1_orders_2(X3,X4,X5)
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X5,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ m1_subset_1(X6,u1_struct_0(sK7))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X3)
    | v2_struct_0(X0)
    | ~ v3_orders_2(X3)
    | ~ l1_orders_2(X3)
    | X1 != X4
    | X2 != X5
    | k4_waybel_1(sK7,sK2(sK7)) != k4_waybel_1(sK7,X6)
    | sK7 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_553])).

cnf(c_728,plain,
    ( ~ r3_waybel_9(sK7,X0,X1)
    | ~ r2_lattice3(sK7,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK7),u1_waybel_0(sK7,X0)),X2)
    | r1_orders_2(sK7,X1,X2)
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X3,u1_struct_0(sK7))
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK7)
    | ~ v3_orders_2(sK7)
    | ~ l1_orders_2(sK7)
    | k4_waybel_1(sK7,sK2(sK7)) != k4_waybel_1(sK7,X3) ),
    inference(unflattening,[status(thm)],[c_727])).

cnf(c_732,plain,
    ( v2_struct_0(X0)
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ m1_subset_1(X3,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ l1_waybel_0(X0,sK7)
    | r1_orders_2(sK7,X1,X2)
    | ~ r2_lattice3(sK7,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK7),u1_waybel_0(sK7,X0)),X2)
    | ~ r3_waybel_9(sK7,X0,X1)
    | k4_waybel_1(sK7,sK2(sK7)) != k4_waybel_1(sK7,X3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_728,c_41,c_38,c_35,c_105,c_138])).

cnf(c_733,plain,
    ( ~ r3_waybel_9(sK7,X0,X1)
    | ~ r2_lattice3(sK7,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK7),u1_waybel_0(sK7,X0)),X2)
    | r1_orders_2(sK7,X1,X2)
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ m1_subset_1(X3,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | k4_waybel_1(sK7,sK2(sK7)) != k4_waybel_1(sK7,X3) ),
    inference(renaming,[status(thm)],[c_732])).

cnf(c_2772,plain,
    ( ~ r3_waybel_9(sK7,X0,X1)
    | ~ r2_lattice3(sK7,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK7),u1_waybel_0(sK7,X0)),X2)
    | r1_orders_2(sK7,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ m1_subset_1(X3,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | k4_waybel_1(sK7,sK2(sK7)) != k4_waybel_1(sK7,X3)
    | sK8 != X0
    | sK7 != sK7 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_733])).

cnf(c_2773,plain,
    ( ~ r3_waybel_9(sK7,sK8,X0)
    | ~ r2_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X1)
    | r1_orders_2(sK7,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ v4_orders_2(sK8)
    | ~ v7_waybel_0(sK8)
    | v2_struct_0(sK8)
    | k4_waybel_1(sK7,sK2(sK7)) != k4_waybel_1(sK7,X2) ),
    inference(unflattening,[status(thm)],[c_2772])).

cnf(c_2777,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | r1_orders_2(sK7,X0,X1)
    | ~ r2_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X1)
    | ~ r3_waybel_9(sK7,sK8,X0)
    | k4_waybel_1(sK7,sK2(sK7)) != k4_waybel_1(sK7,X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2773,c_33,c_32,c_31])).

cnf(c_2778,plain,
    ( ~ r3_waybel_9(sK7,sK8,X0)
    | ~ r2_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X1)
    | r1_orders_2(sK7,X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | k4_waybel_1(sK7,sK2(sK7)) != k4_waybel_1(sK7,X2) ),
    inference(renaming,[status(thm)],[c_2777])).

cnf(c_4601,plain,
    ( ~ r3_waybel_9(sK7,sK8,X0_69)
    | ~ r2_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X1_69)
    | r1_orders_2(sK7,X0_69,X1_69)
    | ~ m1_subset_1(X2_69,u1_struct_0(sK7))
    | ~ m1_subset_1(X0_69,u1_struct_0(sK7))
    | ~ m1_subset_1(X1_69,u1_struct_0(sK7))
    | k4_waybel_1(sK7,sK2(sK7)) != k4_waybel_1(sK7,X2_69) ),
    inference(subtyping,[status(esa)],[c_2778])).

cnf(c_4624,plain,
    ( ~ r3_waybel_9(sK7,sK8,X0_69)
    | ~ r2_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X1_69)
    | r1_orders_2(sK7,X0_69,X1_69)
    | ~ m1_subset_1(X0_69,u1_struct_0(sK7))
    | ~ m1_subset_1(X1_69,u1_struct_0(sK7))
    | ~ sP5_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP5_iProver_split])],[c_4601])).

cnf(c_5134,plain,
    ( r3_waybel_9(sK7,sK8,X0_69) != iProver_top
    | r2_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X1_69) != iProver_top
    | r1_orders_2(sK7,X0_69,X1_69) = iProver_top
    | m1_subset_1(X0_69,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_69,u1_struct_0(sK7)) != iProver_top
    | sP5_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4624])).

cnf(c_18,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
    | r3_orders_2(X0,X2,X3)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK2(X0),u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v2_lattice3(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X0) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_658,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
    | r1_orders_2(X4,X5,X6)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X6,u1_struct_0(X4))
    | ~ m1_subset_1(X5,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK2(X0),u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v2_lattice3(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X4)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X4)
    | X0 != X4
    | X2 != X5
    | X3 != X6 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_18])).

cnf(c_659,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
    | r1_orders_2(X0,X2,X3)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK2(X0),u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v2_lattice3(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(unflattening,[status(thm)],[c_658])).

cnf(c_663,plain,
    ( ~ v3_orders_2(X0)
    | ~ r3_waybel_9(X0,X1,X2)
    | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
    | r1_orders_2(X0,X2,X3)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK2(X0),u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v2_lattice3(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_659,c_13,c_2])).

cnf(c_664,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
    | r1_orders_2(X0,X2,X3)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | m1_subset_1(sK2(X0),u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v2_lattice3(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X0) ),
    inference(renaming,[status(thm)],[c_663])).

cnf(c_1032,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
    | r1_orders_2(X0,X2,X3)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | m1_subset_1(sK2(X0),u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v2_lattice3(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X1)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_664,c_41])).

cnf(c_1033,plain,
    ( ~ r3_waybel_9(sK7,X0,X1)
    | ~ r2_lattice3(sK7,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK7),u1_waybel_0(sK7,X0)),X2)
    | r1_orders_2(sK7,X1,X2)
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | m1_subset_1(sK2(sK7),u1_struct_0(sK7))
    | ~ v2_pre_topc(sK7)
    | ~ v8_pre_topc(sK7)
    | ~ v2_lattice3(sK7)
    | ~ v1_compts_1(sK7)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(sK7)
    | ~ v7_waybel_0(X0)
    | ~ l1_waybel_9(sK7)
    | ~ v5_orders_2(sK7)
    | ~ v1_lattice3(sK7)
    | v2_struct_0(X0) ),
    inference(unflattening,[status(thm)],[c_1032])).

cnf(c_1037,plain,
    ( ~ v7_waybel_0(X0)
    | ~ r3_waybel_9(sK7,X0,X1)
    | ~ r2_lattice3(sK7,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK7),u1_waybel_0(sK7,X0)),X2)
    | r1_orders_2(sK7,X1,X2)
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | m1_subset_1(sK2(sK7),u1_struct_0(sK7))
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1033,c_43,c_42,c_40,c_39,c_38,c_37,c_36,c_35])).

cnf(c_1038,plain,
    ( ~ r3_waybel_9(sK7,X0,X1)
    | ~ r2_lattice3(sK7,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK7),u1_waybel_0(sK7,X0)),X2)
    | r1_orders_2(sK7,X1,X2)
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | m1_subset_1(sK2(sK7),u1_struct_0(sK7))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_1037])).

cnf(c_2742,plain,
    ( ~ r3_waybel_9(sK7,X0,X1)
    | ~ r2_lattice3(sK7,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK7),u1_waybel_0(sK7,X0)),X2)
    | r1_orders_2(sK7,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | m1_subset_1(sK2(sK7),u1_struct_0(sK7))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | sK8 != X0
    | sK7 != sK7 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_1038])).

cnf(c_2743,plain,
    ( ~ r3_waybel_9(sK7,sK8,X0)
    | ~ r2_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X1)
    | r1_orders_2(sK7,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | m1_subset_1(sK2(sK7),u1_struct_0(sK7))
    | ~ v4_orders_2(sK8)
    | ~ v7_waybel_0(sK8)
    | v2_struct_0(sK8) ),
    inference(unflattening,[status(thm)],[c_2742])).

cnf(c_2747,plain,
    ( m1_subset_1(sK2(sK7),u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | r1_orders_2(sK7,X0,X1)
    | ~ r2_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X1)
    | ~ r3_waybel_9(sK7,sK8,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2743,c_33,c_32,c_31])).

cnf(c_2748,plain,
    ( ~ r3_waybel_9(sK7,sK8,X0)
    | ~ r2_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X1)
    | r1_orders_2(sK7,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | m1_subset_1(sK2(sK7),u1_struct_0(sK7)) ),
    inference(renaming,[status(thm)],[c_2747])).

cnf(c_4602,plain,
    ( ~ r3_waybel_9(sK7,sK8,X0_69)
    | ~ r2_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X1_69)
    | r1_orders_2(sK7,X0_69,X1_69)
    | ~ m1_subset_1(X0_69,u1_struct_0(sK7))
    | ~ m1_subset_1(X1_69,u1_struct_0(sK7))
    | m1_subset_1(sK2(sK7),u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_2748])).

cnf(c_4690,plain,
    ( r3_waybel_9(sK7,sK8,X0_69) != iProver_top
    | r2_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X1_69) != iProver_top
    | r1_orders_2(sK7,X0_69,X1_69) = iProver_top
    | m1_subset_1(X0_69,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_69,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK2(sK7),u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4602])).

cnf(c_4625,plain,
    ( sP5_iProver_split
    | sP4_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_4601])).

cnf(c_4693,plain,
    ( sP5_iProver_split = iProver_top
    | sP4_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4625])).

cnf(c_4694,plain,
    ( r3_waybel_9(sK7,sK8,X0_69) != iProver_top
    | r2_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X1_69) != iProver_top
    | r1_orders_2(sK7,X0_69,X1_69) = iProver_top
    | m1_subset_1(X0_69,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_69,u1_struct_0(sK7)) != iProver_top
    | sP5_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4624])).

cnf(c_4623,plain,
    ( ~ m1_subset_1(X0_69,u1_struct_0(sK7))
    | k4_waybel_1(sK7,sK2(sK7)) != k4_waybel_1(sK7,X0_69)
    | ~ sP4_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP4_iProver_split])],[c_4601])).

cnf(c_5135,plain,
    ( k4_waybel_1(sK7,sK2(sK7)) != k4_waybel_1(sK7,X0_69)
    | m1_subset_1(X0_69,u1_struct_0(sK7)) != iProver_top
    | sP4_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4623])).

cnf(c_5455,plain,
    ( m1_subset_1(sK2(sK7),u1_struct_0(sK7)) != iProver_top
    | sP4_iProver_split != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_5135])).

cnf(c_5848,plain,
    ( m1_subset_1(X1_69,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X0_69,u1_struct_0(sK7)) != iProver_top
    | r1_orders_2(sK7,X0_69,X1_69) = iProver_top
    | r2_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X1_69) != iProver_top
    | r3_waybel_9(sK7,sK8,X0_69) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5134,c_4690,c_4693,c_4694,c_5455])).

cnf(c_5849,plain,
    ( r3_waybel_9(sK7,sK8,X0_69) != iProver_top
    | r2_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X1_69) != iProver_top
    | r1_orders_2(sK7,X0_69,X1_69) = iProver_top
    | m1_subset_1(X0_69,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_69,u1_struct_0(sK7)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5848])).

cnf(c_5859,plain,
    ( r3_waybel_9(sK7,sK8,X0_69) != iProver_top
    | r2_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X1_69) != iProver_top
    | r1_orders_2(sK7,X0_69,sK0(sK7,X1_69,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))) = iProver_top
    | r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) = iProver_top
    | m1_subset_1(X1_69,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X0_69,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK0(sK7,X1_69,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))),u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5123,c_5849])).

cnf(c_5,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X2,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_889,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X2,X1),u1_struct_0(X0))
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0) ),
    inference(resolution,[status(thm)],[c_13,c_5])).

cnf(c_1368,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X2,X1),u1_struct_0(X0))
    | ~ l1_waybel_9(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_889,c_39])).

cnf(c_1369,plain,
    ( ~ r2_lattice3(sK7,X0,X1)
    | r1_yellow_0(sK7,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | m1_subset_1(sK0(sK7,X1,X0),u1_struct_0(sK7))
    | ~ l1_waybel_9(sK7) ),
    inference(unflattening,[status(thm)],[c_1368])).

cnf(c_1373,plain,
    ( m1_subset_1(sK0(sK7,X1,X0),u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | r1_yellow_0(sK7,X0)
    | ~ r2_lattice3(sK7,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1369,c_35])).

cnf(c_1374,plain,
    ( ~ r2_lattice3(sK7,X0,X1)
    | r1_yellow_0(sK7,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | m1_subset_1(sK0(sK7,X1,X0),u1_struct_0(sK7)) ),
    inference(renaming,[status(thm)],[c_1373])).

cnf(c_4610,plain,
    ( ~ r2_lattice3(sK7,X0_70,X0_69)
    | r1_yellow_0(sK7,X0_70)
    | ~ m1_subset_1(X0_69,u1_struct_0(sK7))
    | m1_subset_1(sK0(sK7,X0_69,X0_70),u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_1374])).

cnf(c_5124,plain,
    ( r2_lattice3(sK7,X0_70,X0_69) != iProver_top
    | r1_yellow_0(sK7,X0_70) = iProver_top
    | m1_subset_1(X0_69,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK0(sK7,X0_69,X0_70),u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4610])).

cnf(c_6565,plain,
    ( r3_waybel_9(sK7,sK8,X0_69) != iProver_top
    | r2_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X1_69) != iProver_top
    | r1_orders_2(sK7,X0_69,sK0(sK7,X1_69,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))) = iProver_top
    | r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) = iProver_top
    | m1_subset_1(X0_69,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_69,u1_struct_0(sK7)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5859,c_5124])).

cnf(c_3,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK0(X0,X2,X1))
    | r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_935,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK0(X0,X2,X1))
    | r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0) ),
    inference(resolution,[status(thm)],[c_13,c_3])).

cnf(c_1320,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK0(X0,X2,X1))
    | r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_waybel_9(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_935,c_39])).

cnf(c_1321,plain,
    ( ~ r2_lattice3(sK7,X0,X1)
    | ~ r1_orders_2(sK7,X1,sK0(sK7,X1,X0))
    | r1_yellow_0(sK7,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ l1_waybel_9(sK7) ),
    inference(unflattening,[status(thm)],[c_1320])).

cnf(c_1325,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK7))
    | r1_yellow_0(sK7,X0)
    | ~ r1_orders_2(sK7,X1,sK0(sK7,X1,X0))
    | ~ r2_lattice3(sK7,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1321,c_35])).

cnf(c_1326,plain,
    ( ~ r2_lattice3(sK7,X0,X1)
    | ~ r1_orders_2(sK7,X1,sK0(sK7,X1,X0))
    | r1_yellow_0(sK7,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK7)) ),
    inference(renaming,[status(thm)],[c_1325])).

cnf(c_4612,plain,
    ( ~ r2_lattice3(sK7,X0_70,X0_69)
    | ~ r1_orders_2(sK7,X0_69,sK0(sK7,X0_69,X0_70))
    | r1_yellow_0(sK7,X0_70)
    | ~ m1_subset_1(X0_69,u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_1326])).

cnf(c_5122,plain,
    ( r2_lattice3(sK7,X0_70,X0_69) != iProver_top
    | r1_orders_2(sK7,X0_69,sK0(sK7,X0_69,X0_70)) != iProver_top
    | r1_yellow_0(sK7,X0_70) = iProver_top
    | m1_subset_1(X0_69,u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4612])).

cnf(c_6570,plain,
    ( r3_waybel_9(sK7,sK8,X0_69) != iProver_top
    | r2_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X0_69) != iProver_top
    | r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) = iProver_top
    | m1_subset_1(X0_69,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6565,c_5122])).

cnf(c_29,negated_conjecture,
    ( v10_waybel_0(sK8,sK7) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_16,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
    | ~ v10_waybel_0(X1,X0)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK1(X0),u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v2_lattice3(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X0) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1113,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
    | ~ v10_waybel_0(X1,X0)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK1(X0),u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v2_lattice3(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X1)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_41])).

cnf(c_1114,plain,
    ( ~ r3_waybel_9(sK7,X0,X1)
    | r2_lattice3(sK7,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK7),u1_waybel_0(sK7,X0)),X1)
    | ~ v10_waybel_0(X0,sK7)
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | m1_subset_1(sK1(sK7),u1_struct_0(sK7))
    | ~ v2_pre_topc(sK7)
    | ~ v8_pre_topc(sK7)
    | ~ v2_lattice3(sK7)
    | ~ v1_compts_1(sK7)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(sK7)
    | ~ v7_waybel_0(X0)
    | ~ l1_waybel_9(sK7)
    | ~ v5_orders_2(sK7)
    | ~ v1_lattice3(sK7)
    | v2_struct_0(X0) ),
    inference(unflattening,[status(thm)],[c_1113])).

cnf(c_1118,plain,
    ( ~ v7_waybel_0(X0)
    | ~ r3_waybel_9(sK7,X0,X1)
    | r2_lattice3(sK7,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK7),u1_waybel_0(sK7,X0)),X1)
    | ~ v10_waybel_0(X0,sK7)
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | m1_subset_1(sK1(sK7),u1_struct_0(sK7))
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1114,c_43,c_42,c_40,c_39,c_38,c_37,c_36,c_35])).

cnf(c_1119,plain,
    ( ~ r3_waybel_9(sK7,X0,X1)
    | r2_lattice3(sK7,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK7),u1_waybel_0(sK7,X0)),X1)
    | ~ v10_waybel_0(X0,sK7)
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | m1_subset_1(sK1(sK7),u1_struct_0(sK7))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_1118])).

cnf(c_1196,plain,
    ( ~ r3_waybel_9(sK7,X0,X1)
    | r2_lattice3(sK7,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK7),u1_waybel_0(sK7,X0)),X1)
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | m1_subset_1(sK1(sK7),u1_struct_0(sK7))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | sK8 != X0
    | sK7 != sK7 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_1119])).

cnf(c_1197,plain,
    ( ~ r3_waybel_9(sK7,sK8,X0)
    | r2_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X0)
    | ~ l1_waybel_0(sK8,sK7)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | m1_subset_1(sK1(sK7),u1_struct_0(sK7))
    | ~ v4_orders_2(sK8)
    | ~ v7_waybel_0(sK8)
    | v2_struct_0(sK8) ),
    inference(unflattening,[status(thm)],[c_1196])).

cnf(c_1201,plain,
    ( m1_subset_1(sK1(sK7),u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ r3_waybel_9(sK7,sK8,X0)
    | r2_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1197,c_33,c_32,c_31,c_30])).

cnf(c_1202,plain,
    ( ~ r3_waybel_9(sK7,sK8,X0)
    | r2_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | m1_subset_1(sK1(sK7),u1_struct_0(sK7)) ),
    inference(renaming,[status(thm)],[c_1201])).

cnf(c_4616,plain,
    ( ~ r3_waybel_9(sK7,sK8,X0_69)
    | r2_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X0_69)
    | ~ m1_subset_1(X0_69,u1_struct_0(sK7))
    | m1_subset_1(sK1(sK7),u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_1202])).

cnf(c_5114,plain,
    ( r3_waybel_9(sK7,sK8,X0_69) != iProver_top
    | r2_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X0_69) = iProver_top
    | m1_subset_1(X0_69,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK1(sK7),u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4616])).

cnf(c_4644,plain,
    ( r3_waybel_9(sK7,sK8,X0_69) != iProver_top
    | r2_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X0_69) = iProver_top
    | m1_subset_1(X0_69,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK1(sK7),u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4616])).

cnf(c_15,plain,
    ( ~ v5_pre_topc(k4_waybel_1(X0,sK1(X0)),X0,X0)
    | ~ r3_waybel_9(X0,X1,X2)
    | r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
    | ~ v10_waybel_0(X1,X0)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v2_lattice3(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X0) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_505,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
    | ~ v10_waybel_0(X1,X0)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(sK7))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v2_lattice3(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X0)
    | k4_waybel_1(X0,sK1(X0)) != k4_waybel_1(sK7,X3)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_34])).

cnf(c_506,plain,
    ( ~ r3_waybel_9(sK7,X0,X1)
    | r2_lattice3(sK7,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK7),u1_waybel_0(sK7,X0)),X1)
    | ~ v10_waybel_0(X0,sK7)
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ v2_pre_topc(sK7)
    | ~ v8_pre_topc(sK7)
    | ~ v2_lattice3(sK7)
    | ~ v1_compts_1(sK7)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(sK7)
    | ~ v7_waybel_0(X0)
    | ~ l1_waybel_9(sK7)
    | ~ v5_orders_2(sK7)
    | ~ v1_lattice3(sK7)
    | v2_struct_0(X0)
    | ~ v3_orders_2(sK7)
    | k4_waybel_1(sK7,sK1(sK7)) != k4_waybel_1(sK7,X2) ),
    inference(unflattening,[status(thm)],[c_505])).

cnf(c_510,plain,
    ( v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ l1_waybel_0(X0,sK7)
    | ~ v10_waybel_0(X0,sK7)
    | r2_lattice3(sK7,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK7),u1_waybel_0(sK7,X0)),X1)
    | ~ r3_waybel_9(sK7,X0,X1)
    | ~ v7_waybel_0(X0)
    | k4_waybel_1(sK7,sK1(sK7)) != k4_waybel_1(sK7,X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_506,c_43,c_42,c_41,c_40,c_39,c_38,c_37,c_36,c_35])).

cnf(c_511,plain,
    ( ~ r3_waybel_9(sK7,X0,X1)
    | r2_lattice3(sK7,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK7),u1_waybel_0(sK7,X0)),X1)
    | ~ v10_waybel_0(X0,sK7)
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | k4_waybel_1(sK7,sK1(sK7)) != k4_waybel_1(sK7,X2) ),
    inference(renaming,[status(thm)],[c_510])).

cnf(c_1271,plain,
    ( ~ r3_waybel_9(sK7,X0,X1)
    | r2_lattice3(sK7,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK7),u1_waybel_0(sK7,X0)),X1)
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | k4_waybel_1(sK7,sK1(sK7)) != k4_waybel_1(sK7,X2)
    | sK8 != X0
    | sK7 != sK7 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_511])).

cnf(c_1272,plain,
    ( ~ r3_waybel_9(sK7,sK8,X0)
    | r2_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X0)
    | ~ l1_waybel_0(sK8,sK7)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ v4_orders_2(sK8)
    | ~ v7_waybel_0(sK8)
    | v2_struct_0(sK8)
    | k4_waybel_1(sK7,sK1(sK7)) != k4_waybel_1(sK7,X1) ),
    inference(unflattening,[status(thm)],[c_1271])).

cnf(c_1276,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ r3_waybel_9(sK7,sK8,X0)
    | r2_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X0)
    | k4_waybel_1(sK7,sK1(sK7)) != k4_waybel_1(sK7,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1272,c_33,c_32,c_31,c_30])).

cnf(c_1277,plain,
    ( ~ r3_waybel_9(sK7,sK8,X0)
    | r2_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | k4_waybel_1(sK7,sK1(sK7)) != k4_waybel_1(sK7,X1) ),
    inference(renaming,[status(thm)],[c_1276])).

cnf(c_4613,plain,
    ( ~ r3_waybel_9(sK7,sK8,X0_69)
    | r2_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X0_69)
    | ~ m1_subset_1(X0_69,u1_struct_0(sK7))
    | ~ m1_subset_1(X1_69,u1_struct_0(sK7))
    | k4_waybel_1(sK7,sK1(sK7)) != k4_waybel_1(sK7,X1_69) ),
    inference(subtyping,[status(esa)],[c_1277])).

cnf(c_4622,plain,
    ( sP3_iProver_split
    | sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_4613])).

cnf(c_4657,plain,
    ( sP3_iProver_split = iProver_top
    | sP2_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4622])).

cnf(c_4621,plain,
    ( ~ r3_waybel_9(sK7,sK8,X0_69)
    | r2_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X0_69)
    | ~ m1_subset_1(X0_69,u1_struct_0(sK7))
    | ~ sP3_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP3_iProver_split])],[c_4613])).

cnf(c_4658,plain,
    ( r3_waybel_9(sK7,sK8,X0_69) != iProver_top
    | r2_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X0_69) = iProver_top
    | m1_subset_1(X0_69,u1_struct_0(sK7)) != iProver_top
    | sP3_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4621])).

cnf(c_4620,plain,
    ( ~ m1_subset_1(X0_69,u1_struct_0(sK7))
    | k4_waybel_1(sK7,sK1(sK7)) != k4_waybel_1(sK7,X0_69)
    | ~ sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP2_iProver_split])],[c_4613])).

cnf(c_5121,plain,
    ( k4_waybel_1(sK7,sK1(sK7)) != k4_waybel_1(sK7,X0_69)
    | m1_subset_1(X0_69,u1_struct_0(sK7)) != iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4620])).

cnf(c_5419,plain,
    ( m1_subset_1(sK1(sK7),u1_struct_0(sK7)) != iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_5121])).

cnf(c_5537,plain,
    ( m1_subset_1(X0_69,u1_struct_0(sK7)) != iProver_top
    | r2_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X0_69) = iProver_top
    | r3_waybel_9(sK7,sK8,X0_69) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5114,c_4644,c_4657,c_4658,c_5419])).

cnf(c_5538,plain,
    ( r3_waybel_9(sK7,sK8,X0_69) != iProver_top
    | r2_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X0_69) = iProver_top
    | m1_subset_1(X0_69,u1_struct_0(sK7)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5537])).

cnf(c_6640,plain,
    ( r3_waybel_9(sK7,sK8,X0_69) != iProver_top
    | r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) = iProver_top
    | m1_subset_1(X0_69,u1_struct_0(sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6570,c_5538])).

cnf(c_6649,plain,
    ( r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) = iProver_top
    | m1_subset_1(sK3(sK7,sK8),u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5131,c_6640])).

cnf(c_56,plain,
    ( v2_struct_0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_57,plain,
    ( v4_orders_2(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_58,plain,
    ( v7_waybel_0(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_20,plain,
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
    inference(cnf_transformation,[],[f77])).

cnf(c_2516,plain,
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
    inference(resolution_lifted,[status(thm)],[c_20,c_1553])).

cnf(c_2517,plain,
    ( ~ l1_waybel_0(X0,sK7)
    | m1_subset_1(sK3(sK7,X0),u1_struct_0(sK7))
    | ~ v2_pre_topc(sK7)
    | ~ v8_pre_topc(sK7)
    | ~ v1_compts_1(sK7)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK7) ),
    inference(unflattening,[status(thm)],[c_2516])).

cnf(c_2521,plain,
    ( v2_struct_0(X0)
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ l1_waybel_0(X0,sK7)
    | m1_subset_1(sK3(sK7,X0),u1_struct_0(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2517,c_43,c_42,c_38,c_36,c_35,c_105,c_138])).

cnf(c_2522,plain,
    ( ~ l1_waybel_0(X0,sK7)
    | m1_subset_1(sK3(sK7,X0),u1_struct_0(sK7))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_2521])).

cnf(c_2605,plain,
    ( m1_subset_1(sK3(sK7,X0),u1_struct_0(sK7))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | sK8 != X0
    | sK7 != sK7 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_2522])).

cnf(c_2606,plain,
    ( m1_subset_1(sK3(sK7,sK8),u1_struct_0(sK7))
    | ~ v4_orders_2(sK8)
    | ~ v7_waybel_0(sK8)
    | v2_struct_0(sK8) ),
    inference(unflattening,[status(thm)],[c_2605])).

cnf(c_2607,plain,
    ( m1_subset_1(sK3(sK7,sK8),u1_struct_0(sK7)) = iProver_top
    | v4_orders_2(sK8) != iProver_top
    | v7_waybel_0(sK8) != iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2606])).

cnf(c_6652,plain,
    ( r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6649,c_56,c_57,c_58,c_2607])).

cnf(c_23,plain,
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
    inference(cnf_transformation,[],[f81])).

cnf(c_11,plain,
    ( ~ l1_waybel_0(X0,X1)
    | r1_waybel_9(X1,X0)
    | ~ r1_yellow_0(X1,k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0)))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_28,negated_conjecture,
    ( ~ r2_hidden(k1_waybel_2(sK7,sK8),k10_yellow_6(sK7,sK8))
    | ~ r1_waybel_9(sK7,sK8) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_488,plain,
    ( ~ r2_hidden(k1_waybel_2(sK7,sK8),k10_yellow_6(sK7,sK8))
    | ~ l1_waybel_0(X0,X1)
    | ~ r1_yellow_0(X1,k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0)))
    | ~ l1_orders_2(X1)
    | sK8 != X0
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_28])).

cnf(c_489,plain,
    ( ~ r2_hidden(k1_waybel_2(sK7,sK8),k10_yellow_6(sK7,sK8))
    | ~ l1_waybel_0(sK8,sK7)
    | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ l1_orders_2(sK7) ),
    inference(unflattening,[status(thm)],[c_488])).

cnf(c_491,plain,
    ( ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ r2_hidden(k1_waybel_2(sK7,sK8),k10_yellow_6(sK7,sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_489,c_35,c_30,c_105])).

cnf(c_492,plain,
    ( ~ r2_hidden(k1_waybel_2(sK7,sK8),k10_yellow_6(sK7,sK8))
    | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) ),
    inference(renaming,[status(thm)],[c_491])).

cnf(c_2145,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | r3_waybel_9(X0,X1,sK4(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | k1_waybel_2(sK7,sK8) != X2
    | k10_yellow_6(X0,X1) != k10_yellow_6(sK7,sK8) ),
    inference(resolution_lifted,[status(thm)],[c_23,c_492])).

cnf(c_2146,plain,
    ( ~ r3_waybel_9(X0,X1,k1_waybel_2(sK7,sK8))
    | r3_waybel_9(X0,X1,sK4(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | k10_yellow_6(X0,X1) != k10_yellow_6(sK7,sK8) ),
    inference(unflattening,[status(thm)],[c_2145])).

cnf(c_2372,plain,
    ( ~ r3_waybel_9(X0,X1,k1_waybel_2(sK7,sK8))
    | r3_waybel_9(X0,X1,sK4(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | k10_yellow_6(X0,X1) != k10_yellow_6(sK7,sK8)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2146,c_1553])).

cnf(c_2373,plain,
    ( ~ r3_waybel_9(sK7,X0,k1_waybel_2(sK7,sK8))
    | r3_waybel_9(sK7,X0,sK4(sK7,X0))
    | ~ l1_waybel_0(X0,sK7)
    | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
    | ~ v2_pre_topc(sK7)
    | ~ v8_pre_topc(sK7)
    | ~ v1_compts_1(sK7)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK7)
    | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8) ),
    inference(unflattening,[status(thm)],[c_2372])).

cnf(c_2377,plain,
    ( v2_struct_0(X0)
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ r3_waybel_9(sK7,X0,k1_waybel_2(sK7,sK8))
    | r3_waybel_9(sK7,X0,sK4(sK7,X0))
    | ~ l1_waybel_0(X0,sK7)
    | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
    | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2373,c_43,c_42,c_38,c_36,c_35,c_105,c_138])).

cnf(c_2378,plain,
    ( ~ r3_waybel_9(sK7,X0,k1_waybel_2(sK7,sK8))
    | r3_waybel_9(sK7,X0,sK4(sK7,X0))
    | ~ l1_waybel_0(X0,sK7)
    | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8) ),
    inference(renaming,[status(thm)],[c_2377])).

cnf(c_2673,plain,
    ( ~ r3_waybel_9(sK7,X0,k1_waybel_2(sK7,sK8))
    | r3_waybel_9(sK7,X0,sK4(sK7,X0))
    | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8)
    | sK8 != X0
    | sK7 != sK7 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_2378])).

cnf(c_2674,plain,
    ( ~ r3_waybel_9(sK7,sK8,k1_waybel_2(sK7,sK8))
    | r3_waybel_9(sK7,sK8,sK4(sK7,sK8))
    | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
    | ~ v4_orders_2(sK8)
    | ~ v7_waybel_0(sK8)
    | v2_struct_0(sK8)
    | k10_yellow_6(sK7,sK8) != k10_yellow_6(sK7,sK8) ),
    inference(unflattening,[status(thm)],[c_2673])).

cnf(c_2676,plain,
    ( ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
    | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | r3_waybel_9(sK7,sK8,sK4(sK7,sK8))
    | ~ r3_waybel_9(sK7,sK8,k1_waybel_2(sK7,sK8))
    | k10_yellow_6(sK7,sK8) != k10_yellow_6(sK7,sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2674,c_33,c_32,c_31])).

cnf(c_2677,plain,
    ( ~ r3_waybel_9(sK7,sK8,k1_waybel_2(sK7,sK8))
    | r3_waybel_9(sK7,sK8,sK4(sK7,sK8))
    | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
    | k10_yellow_6(sK7,sK8) != k10_yellow_6(sK7,sK8) ),
    inference(renaming,[status(thm)],[c_2676])).

cnf(c_3697,plain,
    ( ~ r3_waybel_9(sK7,sK8,k1_waybel_2(sK7,sK8))
    | r3_waybel_9(sK7,sK8,sK4(sK7,sK8))
    | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7)) ),
    inference(equality_resolution_simp,[status(thm)],[c_2677])).

cnf(c_4598,plain,
    ( ~ r3_waybel_9(sK7,sK8,k1_waybel_2(sK7,sK8))
    | r3_waybel_9(sK7,sK8,sK4(sK7,sK8))
    | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_3697])).

cnf(c_5138,plain,
    ( r3_waybel_9(sK7,sK8,k1_waybel_2(sK7,sK8)) != iProver_top
    | r3_waybel_9(sK7,sK8,sK4(sK7,sK8)) = iProver_top
    | r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) != iProver_top
    | m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4598])).

cnf(c_2618,plain,
    ( r3_waybel_9(sK7,sK8,sK3(sK7,sK8)) = iProver_top
    | v4_orders_2(sK8) != iProver_top
    | v7_waybel_0(sK8) != iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2617])).

cnf(c_3698,plain,
    ( r3_waybel_9(sK7,sK8,k1_waybel_2(sK7,sK8)) != iProver_top
    | r3_waybel_9(sK7,sK8,sK4(sK7,sK8)) = iProver_top
    | r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) != iProver_top
    | m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3697])).

cnf(c_26,plain,
    ( ~ v5_pre_topc(k4_waybel_1(X0,sK6(X0)),X0,X0)
    | ~ r3_waybel_9(X0,X1,X2)
    | ~ v10_waybel_0(X1,X0)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v2_lattice3(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X0)
    | k1_waybel_2(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_592,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | ~ v10_waybel_0(X1,X0)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(sK7))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v2_lattice3(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X0)
    | k1_waybel_2(X0,X1) = X2
    | k4_waybel_1(X0,sK6(X0)) != k4_waybel_1(sK7,X3)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_34])).

cnf(c_593,plain,
    ( ~ r3_waybel_9(sK7,X0,X1)
    | ~ v10_waybel_0(X0,sK7)
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ v2_pre_topc(sK7)
    | ~ v8_pre_topc(sK7)
    | ~ v2_lattice3(sK7)
    | ~ v1_compts_1(sK7)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(sK7)
    | ~ v7_waybel_0(X0)
    | ~ l1_waybel_9(sK7)
    | ~ v5_orders_2(sK7)
    | ~ v1_lattice3(sK7)
    | v2_struct_0(X0)
    | ~ v3_orders_2(sK7)
    | k1_waybel_2(sK7,X0) = X1
    | k4_waybel_1(sK7,sK6(sK7)) != k4_waybel_1(sK7,X2) ),
    inference(unflattening,[status(thm)],[c_592])).

cnf(c_597,plain,
    ( v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ l1_waybel_0(X0,sK7)
    | ~ v10_waybel_0(X0,sK7)
    | ~ r3_waybel_9(sK7,X0,X1)
    | ~ v7_waybel_0(X0)
    | k1_waybel_2(sK7,X0) = X1
    | k4_waybel_1(sK7,sK6(sK7)) != k4_waybel_1(sK7,X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_593,c_43,c_42,c_41,c_40,c_39,c_38,c_37,c_36,c_35])).

cnf(c_598,plain,
    ( ~ r3_waybel_9(sK7,X0,X1)
    | ~ v10_waybel_0(X0,sK7)
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | k1_waybel_2(sK7,X0) = X1
    | k4_waybel_1(sK7,sK6(sK7)) != k4_waybel_1(sK7,X2) ),
    inference(renaming,[status(thm)],[c_597])).

cnf(c_1244,plain,
    ( ~ r3_waybel_9(sK7,X0,X1)
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | k1_waybel_2(sK7,X0) = X1
    | k4_waybel_1(sK7,sK6(sK7)) != k4_waybel_1(sK7,X2)
    | sK8 != X0
    | sK7 != sK7 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_598])).

cnf(c_1245,plain,
    ( ~ r3_waybel_9(sK7,sK8,X0)
    | ~ l1_waybel_0(sK8,sK7)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ v4_orders_2(sK8)
    | ~ v7_waybel_0(sK8)
    | v2_struct_0(sK8)
    | k1_waybel_2(sK7,sK8) = X0
    | k4_waybel_1(sK7,sK6(sK7)) != k4_waybel_1(sK7,X1) ),
    inference(unflattening,[status(thm)],[c_1244])).

cnf(c_1249,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ r3_waybel_9(sK7,sK8,X0)
    | k1_waybel_2(sK7,sK8) = X0
    | k4_waybel_1(sK7,sK6(sK7)) != k4_waybel_1(sK7,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1245,c_33,c_32,c_31,c_30])).

cnf(c_1250,plain,
    ( ~ r3_waybel_9(sK7,sK8,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | k1_waybel_2(sK7,sK8) = X0
    | k4_waybel_1(sK7,sK6(sK7)) != k4_waybel_1(sK7,X1) ),
    inference(renaming,[status(thm)],[c_1249])).

cnf(c_4614,plain,
    ( ~ r3_waybel_9(sK7,sK8,X0_69)
    | ~ m1_subset_1(X0_69,u1_struct_0(sK7))
    | ~ m1_subset_1(X1_69,u1_struct_0(sK7))
    | k4_waybel_1(sK7,sK6(sK7)) != k4_waybel_1(sK7,X1_69)
    | k1_waybel_2(sK7,sK8) = X0_69 ),
    inference(subtyping,[status(esa)],[c_1250])).

cnf(c_4618,plain,
    ( ~ r3_waybel_9(sK7,sK8,X0_69)
    | ~ m1_subset_1(X0_69,u1_struct_0(sK7))
    | k1_waybel_2(sK7,sK8) = X0_69
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_4614])).

cnf(c_5117,plain,
    ( k1_waybel_2(sK7,sK8) = X0_69
    | r3_waybel_9(sK7,sK8,X0_69) != iProver_top
    | m1_subset_1(X0_69,u1_struct_0(sK7)) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4618])).

cnf(c_27,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | ~ v10_waybel_0(X1,X0)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK6(X0),u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v2_lattice3(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X0)
    | k1_waybel_2(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1074,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | ~ v10_waybel_0(X1,X0)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK6(X0),u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v2_lattice3(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X1)
    | k1_waybel_2(X0,X1) = X2
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_41])).

cnf(c_1075,plain,
    ( ~ r3_waybel_9(sK7,X0,X1)
    | ~ v10_waybel_0(X0,sK7)
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | m1_subset_1(sK6(sK7),u1_struct_0(sK7))
    | ~ v2_pre_topc(sK7)
    | ~ v8_pre_topc(sK7)
    | ~ v2_lattice3(sK7)
    | ~ v1_compts_1(sK7)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(sK7)
    | ~ v7_waybel_0(X0)
    | ~ l1_waybel_9(sK7)
    | ~ v5_orders_2(sK7)
    | ~ v1_lattice3(sK7)
    | v2_struct_0(X0)
    | k1_waybel_2(sK7,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_1074])).

cnf(c_1079,plain,
    ( ~ v7_waybel_0(X0)
    | ~ r3_waybel_9(sK7,X0,X1)
    | ~ v10_waybel_0(X0,sK7)
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | m1_subset_1(sK6(sK7),u1_struct_0(sK7))
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | k1_waybel_2(sK7,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1075,c_43,c_42,c_40,c_39,c_38,c_37,c_36,c_35])).

cnf(c_1080,plain,
    ( ~ r3_waybel_9(sK7,X0,X1)
    | ~ v10_waybel_0(X0,sK7)
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | m1_subset_1(sK6(sK7),u1_struct_0(sK7))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | k1_waybel_2(sK7,X0) = X1 ),
    inference(renaming,[status(thm)],[c_1079])).

cnf(c_1220,plain,
    ( ~ r3_waybel_9(sK7,X0,X1)
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | m1_subset_1(sK6(sK7),u1_struct_0(sK7))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | k1_waybel_2(sK7,X0) = X1
    | sK8 != X0
    | sK7 != sK7 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_1080])).

cnf(c_1221,plain,
    ( ~ r3_waybel_9(sK7,sK8,X0)
    | ~ l1_waybel_0(sK8,sK7)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | m1_subset_1(sK6(sK7),u1_struct_0(sK7))
    | ~ v4_orders_2(sK8)
    | ~ v7_waybel_0(sK8)
    | v2_struct_0(sK8)
    | k1_waybel_2(sK7,sK8) = X0 ),
    inference(unflattening,[status(thm)],[c_1220])).

cnf(c_1225,plain,
    ( m1_subset_1(sK6(sK7),u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ r3_waybel_9(sK7,sK8,X0)
    | k1_waybel_2(sK7,sK8) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1221,c_33,c_32,c_31,c_30])).

cnf(c_1226,plain,
    ( ~ r3_waybel_9(sK7,sK8,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | m1_subset_1(sK6(sK7),u1_struct_0(sK7))
    | k1_waybel_2(sK7,sK8) = X0 ),
    inference(renaming,[status(thm)],[c_1225])).

cnf(c_4615,plain,
    ( ~ r3_waybel_9(sK7,sK8,X0_69)
    | ~ m1_subset_1(X0_69,u1_struct_0(sK7))
    | m1_subset_1(sK6(sK7),u1_struct_0(sK7))
    | k1_waybel_2(sK7,sK8) = X0_69 ),
    inference(subtyping,[status(esa)],[c_1226])).

cnf(c_4647,plain,
    ( k1_waybel_2(sK7,sK8) = X0_69
    | r3_waybel_9(sK7,sK8,X0_69) != iProver_top
    | m1_subset_1(X0_69,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK6(sK7),u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4615])).

cnf(c_4619,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_4614])).

cnf(c_4650,plain,
    ( sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4619])).

cnf(c_4651,plain,
    ( k1_waybel_2(sK7,sK8) = X0_69
    | r3_waybel_9(sK7,sK8,X0_69) != iProver_top
    | m1_subset_1(X0_69,u1_struct_0(sK7)) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4618])).

cnf(c_4617,plain,
    ( ~ m1_subset_1(X0_69,u1_struct_0(sK7))
    | k4_waybel_1(sK7,sK6(sK7)) != k4_waybel_1(sK7,X0_69)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_4614])).

cnf(c_5118,plain,
    ( k4_waybel_1(sK7,sK6(sK7)) != k4_waybel_1(sK7,X0_69)
    | m1_subset_1(X0_69,u1_struct_0(sK7)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4617])).

cnf(c_5413,plain,
    ( m1_subset_1(sK6(sK7),u1_struct_0(sK7)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_5118])).

cnf(c_5487,plain,
    ( m1_subset_1(X0_69,u1_struct_0(sK7)) != iProver_top
    | r3_waybel_9(sK7,sK8,X0_69) != iProver_top
    | k1_waybel_2(sK7,sK8) = X0_69 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5117,c_4647,c_4650,c_4651,c_5413])).

cnf(c_5488,plain,
    ( k1_waybel_2(sK7,sK8) = X0_69
    | r3_waybel_9(sK7,sK8,X0_69) != iProver_top
    | m1_subset_1(X0_69,u1_struct_0(sK7)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5487])).

cnf(c_5496,plain,
    ( k1_waybel_2(sK7,sK8) = sK3(sK7,sK8)
    | m1_subset_1(sK3(sK7,sK8),u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5131,c_5488])).

cnf(c_4632,plain,
    ( ~ m1_subset_1(X0_69,X0_71)
    | m1_subset_1(X1_69,X0_71)
    | X1_69 != X0_69 ),
    theory(equality)).

cnf(c_5436,plain,
    ( m1_subset_1(X0_69,u1_struct_0(sK7))
    | ~ m1_subset_1(sK3(sK7,sK8),u1_struct_0(sK7))
    | X0_69 != sK3(sK7,sK8) ),
    inference(instantiation,[status(thm)],[c_4632])).

cnf(c_5507,plain,
    ( m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
    | ~ m1_subset_1(sK3(sK7,sK8),u1_struct_0(sK7))
    | k1_waybel_2(sK7,sK8) != sK3(sK7,sK8) ),
    inference(instantiation,[status(thm)],[c_5436])).

cnf(c_5508,plain,
    ( k1_waybel_2(sK7,sK8) != sK3(sK7,sK8)
    | m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7)) = iProver_top
    | m1_subset_1(sK3(sK7,sK8),u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5507])).

cnf(c_4634,plain,
    ( ~ r3_waybel_9(X0_68,X1_68,X0_69)
    | r3_waybel_9(X0_68,X1_68,X1_69)
    | X1_69 != X0_69 ),
    theory(equality)).

cnf(c_5476,plain,
    ( r3_waybel_9(sK7,sK8,X0_69)
    | ~ r3_waybel_9(sK7,sK8,sK3(sK7,sK8))
    | X0_69 != sK3(sK7,sK8) ),
    inference(instantiation,[status(thm)],[c_4634])).

cnf(c_5512,plain,
    ( r3_waybel_9(sK7,sK8,k1_waybel_2(sK7,sK8))
    | ~ r3_waybel_9(sK7,sK8,sK3(sK7,sK8))
    | k1_waybel_2(sK7,sK8) != sK3(sK7,sK8) ),
    inference(instantiation,[status(thm)],[c_5476])).

cnf(c_5513,plain,
    ( k1_waybel_2(sK7,sK8) != sK3(sK7,sK8)
    | r3_waybel_9(sK7,sK8,k1_waybel_2(sK7,sK8)) = iProver_top
    | r3_waybel_9(sK7,sK8,sK3(sK7,sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5512])).

cnf(c_6269,plain,
    ( r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) != iProver_top
    | r3_waybel_9(sK7,sK8,sK4(sK7,sK8)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5138,c_56,c_57,c_58,c_2607,c_2618,c_3698,c_5496,c_5508,c_5513])).

cnf(c_6270,plain,
    ( r3_waybel_9(sK7,sK8,sK4(sK7,sK8)) = iProver_top
    | r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) != iProver_top ),
    inference(renaming,[status(thm)],[c_6269])).

cnf(c_6659,plain,
    ( r3_waybel_9(sK7,sK8,sK4(sK7,sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6652,c_6270])).

cnf(c_5547,plain,
    ( k1_waybel_2(sK7,sK8) = sK3(sK7,sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5496,c_56,c_57,c_58,c_2607])).

cnf(c_5550,plain,
    ( sK3(sK7,sK8) = X0_69
    | r3_waybel_9(sK7,sK8,X0_69) != iProver_top
    | m1_subset_1(X0_69,u1_struct_0(sK7)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5547,c_5488])).

cnf(c_6946,plain,
    ( sK4(sK7,sK8) = sK3(sK7,sK8)
    | m1_subset_1(sK4(sK7,sK8),u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6659,c_5550])).

cnf(c_25,plain,
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
    inference(cnf_transformation,[],[f79])).

cnf(c_2049,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | k1_waybel_2(sK7,sK8) != X2
    | k10_yellow_6(X0,X1) != k10_yellow_6(sK7,sK8) ),
    inference(resolution_lifted,[status(thm)],[c_25,c_492])).

cnf(c_2050,plain,
    ( ~ r3_waybel_9(X0,X1,k1_waybel_2(sK7,sK8))
    | ~ l1_waybel_0(X1,X0)
    | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(X0))
    | m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | k10_yellow_6(X0,X1) != k10_yellow_6(sK7,sK8) ),
    inference(unflattening,[status(thm)],[c_2049])).

cnf(c_2450,plain,
    ( ~ r3_waybel_9(X0,X1,k1_waybel_2(sK7,sK8))
    | ~ l1_waybel_0(X1,X0)
    | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(X0))
    | m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | k10_yellow_6(X0,X1) != k10_yellow_6(sK7,sK8)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2050,c_1553])).

cnf(c_2451,plain,
    ( ~ r3_waybel_9(sK7,X0,k1_waybel_2(sK7,sK8))
    | ~ l1_waybel_0(X0,sK7)
    | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
    | m1_subset_1(sK4(sK7,X0),u1_struct_0(sK7))
    | ~ v2_pre_topc(sK7)
    | ~ v8_pre_topc(sK7)
    | ~ v1_compts_1(sK7)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK7)
    | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8) ),
    inference(unflattening,[status(thm)],[c_2450])).

cnf(c_2455,plain,
    ( v2_struct_0(X0)
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ r3_waybel_9(sK7,X0,k1_waybel_2(sK7,sK8))
    | ~ l1_waybel_0(X0,sK7)
    | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
    | m1_subset_1(sK4(sK7,X0),u1_struct_0(sK7))
    | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2451,c_43,c_42,c_38,c_36,c_35,c_105,c_138])).

cnf(c_2456,plain,
    ( ~ r3_waybel_9(sK7,X0,k1_waybel_2(sK7,sK8))
    | ~ l1_waybel_0(X0,sK7)
    | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
    | m1_subset_1(sK4(sK7,X0),u1_struct_0(sK7))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8) ),
    inference(renaming,[status(thm)],[c_2455])).

cnf(c_2627,plain,
    ( ~ r3_waybel_9(sK7,X0,k1_waybel_2(sK7,sK8))
    | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
    | m1_subset_1(sK4(sK7,X0),u1_struct_0(sK7))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8)
    | sK8 != X0
    | sK7 != sK7 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_2456])).

cnf(c_2628,plain,
    ( ~ r3_waybel_9(sK7,sK8,k1_waybel_2(sK7,sK8))
    | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
    | m1_subset_1(sK4(sK7,sK8),u1_struct_0(sK7))
    | ~ v4_orders_2(sK8)
    | ~ v7_waybel_0(sK8)
    | v2_struct_0(sK8)
    | k10_yellow_6(sK7,sK8) != k10_yellow_6(sK7,sK8) ),
    inference(unflattening,[status(thm)],[c_2627])).

cnf(c_2630,plain,
    ( m1_subset_1(sK4(sK7,sK8),u1_struct_0(sK7))
    | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
    | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ r3_waybel_9(sK7,sK8,k1_waybel_2(sK7,sK8))
    | k10_yellow_6(sK7,sK8) != k10_yellow_6(sK7,sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2628,c_33,c_32,c_31])).

cnf(c_2631,plain,
    ( ~ r3_waybel_9(sK7,sK8,k1_waybel_2(sK7,sK8))
    | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
    | m1_subset_1(sK4(sK7,sK8),u1_struct_0(sK7))
    | k10_yellow_6(sK7,sK8) != k10_yellow_6(sK7,sK8) ),
    inference(renaming,[status(thm)],[c_2630])).

cnf(c_3701,plain,
    ( ~ r3_waybel_9(sK7,sK8,k1_waybel_2(sK7,sK8))
    | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
    | m1_subset_1(sK4(sK7,sK8),u1_struct_0(sK7)) ),
    inference(equality_resolution_simp,[status(thm)],[c_2631])).

cnf(c_3702,plain,
    ( r3_waybel_9(sK7,sK8,k1_waybel_2(sK7,sK8)) != iProver_top
    | r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) != iProver_top
    | m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK4(sK7,sK8),u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3701])).

cnf(c_7261,plain,
    ( sK4(sK7,sK8) = sK3(sK7,sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6946,c_56,c_57,c_58,c_2607,c_2618,c_3702,c_5496,c_5508,c_5513,c_6649])).

cnf(c_21,plain,
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
    inference(cnf_transformation,[],[f83])).

cnf(c_2241,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | k1_waybel_2(sK7,sK8) != X2
    | sK5(X0,X1) != sK4(X0,X1)
    | k10_yellow_6(X0,X1) != k10_yellow_6(sK7,sK8) ),
    inference(resolution_lifted,[status(thm)],[c_21,c_492])).

cnf(c_2242,plain,
    ( ~ r3_waybel_9(X0,X1,k1_waybel_2(sK7,sK8))
    | ~ l1_waybel_0(X1,X0)
    | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(X0))
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
    inference(unflattening,[status(thm)],[c_2241])).

cnf(c_2294,plain,
    ( ~ r3_waybel_9(X0,X1,k1_waybel_2(sK7,sK8))
    | ~ l1_waybel_0(X1,X0)
    | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(X0))
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
    inference(resolution_lifted,[status(thm)],[c_2242,c_1553])).

cnf(c_2295,plain,
    ( ~ r3_waybel_9(sK7,X0,k1_waybel_2(sK7,sK8))
    | ~ l1_waybel_0(X0,sK7)
    | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
    | ~ v2_pre_topc(sK7)
    | ~ v8_pre_topc(sK7)
    | ~ v1_compts_1(sK7)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK7)
    | sK5(sK7,X0) != sK4(sK7,X0)
    | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8) ),
    inference(unflattening,[status(thm)],[c_2294])).

cnf(c_2299,plain,
    ( v2_struct_0(X0)
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ r3_waybel_9(sK7,X0,k1_waybel_2(sK7,sK8))
    | ~ l1_waybel_0(X0,sK7)
    | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
    | sK5(sK7,X0) != sK4(sK7,X0)
    | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2295,c_43,c_42,c_38,c_36,c_35,c_105,c_138])).

cnf(c_2300,plain,
    ( ~ r3_waybel_9(sK7,X0,k1_waybel_2(sK7,sK8))
    | ~ l1_waybel_0(X0,sK7)
    | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | sK5(sK7,X0) != sK4(sK7,X0)
    | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8) ),
    inference(renaming,[status(thm)],[c_2299])).

cnf(c_2719,plain,
    ( ~ r3_waybel_9(sK7,X0,k1_waybel_2(sK7,sK8))
    | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | sK5(sK7,X0) != sK4(sK7,X0)
    | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8)
    | sK8 != X0
    | sK7 != sK7 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_2300])).

cnf(c_2720,plain,
    ( ~ r3_waybel_9(sK7,sK8,k1_waybel_2(sK7,sK8))
    | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
    | ~ v4_orders_2(sK8)
    | ~ v7_waybel_0(sK8)
    | v2_struct_0(sK8)
    | sK5(sK7,sK8) != sK4(sK7,sK8)
    | k10_yellow_6(sK7,sK8) != k10_yellow_6(sK7,sK8) ),
    inference(unflattening,[status(thm)],[c_2719])).

cnf(c_2722,plain,
    ( ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
    | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ r3_waybel_9(sK7,sK8,k1_waybel_2(sK7,sK8))
    | sK5(sK7,sK8) != sK4(sK7,sK8)
    | k10_yellow_6(sK7,sK8) != k10_yellow_6(sK7,sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2720,c_33,c_32,c_31])).

cnf(c_2723,plain,
    ( ~ r3_waybel_9(sK7,sK8,k1_waybel_2(sK7,sK8))
    | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
    | sK5(sK7,sK8) != sK4(sK7,sK8)
    | k10_yellow_6(sK7,sK8) != k10_yellow_6(sK7,sK8) ),
    inference(renaming,[status(thm)],[c_2722])).

cnf(c_3693,plain,
    ( ~ r3_waybel_9(sK7,sK8,k1_waybel_2(sK7,sK8))
    | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
    | sK5(sK7,sK8) != sK4(sK7,sK8) ),
    inference(equality_resolution_simp,[status(thm)],[c_2723])).

cnf(c_4600,plain,
    ( ~ r3_waybel_9(sK7,sK8,k1_waybel_2(sK7,sK8))
    | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
    | sK5(sK7,sK8) != sK4(sK7,sK8) ),
    inference(subtyping,[status(esa)],[c_3693])).

cnf(c_5136,plain,
    ( sK5(sK7,sK8) != sK4(sK7,sK8)
    | r3_waybel_9(sK7,sK8,k1_waybel_2(sK7,sK8)) != iProver_top
    | r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) != iProver_top
    | m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4600])).

cnf(c_4700,plain,
    ( sK5(sK7,sK8) != sK4(sK7,sK8)
    | r3_waybel_9(sK7,sK8,k1_waybel_2(sK7,sK8)) != iProver_top
    | r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) != iProver_top
    | m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4600])).

cnf(c_6207,plain,
    ( r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) != iProver_top
    | sK5(sK7,sK8) != sK4(sK7,sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5136,c_56,c_57,c_58,c_2607,c_2618,c_4700,c_5496,c_5508,c_5513])).

cnf(c_6208,plain,
    ( sK5(sK7,sK8) != sK4(sK7,sK8)
    | r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) != iProver_top ),
    inference(renaming,[status(thm)],[c_6207])).

cnf(c_7267,plain,
    ( sK5(sK7,sK8) != sK3(sK7,sK8)
    | r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7261,c_6208])).

cnf(c_22,plain,
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
    inference(cnf_transformation,[],[f82])).

cnf(c_2193,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | r3_waybel_9(X0,X1,sK5(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | k1_waybel_2(sK7,sK8) != X2
    | k10_yellow_6(X0,X1) != k10_yellow_6(sK7,sK8) ),
    inference(resolution_lifted,[status(thm)],[c_22,c_492])).

cnf(c_2194,plain,
    ( ~ r3_waybel_9(X0,X1,k1_waybel_2(sK7,sK8))
    | r3_waybel_9(X0,X1,sK5(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | k10_yellow_6(X0,X1) != k10_yellow_6(sK7,sK8) ),
    inference(unflattening,[status(thm)],[c_2193])).

cnf(c_2333,plain,
    ( ~ r3_waybel_9(X0,X1,k1_waybel_2(sK7,sK8))
    | r3_waybel_9(X0,X1,sK5(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | k10_yellow_6(X0,X1) != k10_yellow_6(sK7,sK8)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2194,c_1553])).

cnf(c_2334,plain,
    ( ~ r3_waybel_9(sK7,X0,k1_waybel_2(sK7,sK8))
    | r3_waybel_9(sK7,X0,sK5(sK7,X0))
    | ~ l1_waybel_0(X0,sK7)
    | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
    | ~ v2_pre_topc(sK7)
    | ~ v8_pre_topc(sK7)
    | ~ v1_compts_1(sK7)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK7)
    | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8) ),
    inference(unflattening,[status(thm)],[c_2333])).

cnf(c_2338,plain,
    ( v2_struct_0(X0)
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ r3_waybel_9(sK7,X0,k1_waybel_2(sK7,sK8))
    | r3_waybel_9(sK7,X0,sK5(sK7,X0))
    | ~ l1_waybel_0(X0,sK7)
    | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
    | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2334,c_43,c_42,c_38,c_36,c_35,c_105,c_138])).

cnf(c_2339,plain,
    ( ~ r3_waybel_9(sK7,X0,k1_waybel_2(sK7,sK8))
    | r3_waybel_9(sK7,X0,sK5(sK7,X0))
    | ~ l1_waybel_0(X0,sK7)
    | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8) ),
    inference(renaming,[status(thm)],[c_2338])).

cnf(c_2696,plain,
    ( ~ r3_waybel_9(sK7,X0,k1_waybel_2(sK7,sK8))
    | r3_waybel_9(sK7,X0,sK5(sK7,X0))
    | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8)
    | sK8 != X0
    | sK7 != sK7 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_2339])).

cnf(c_2697,plain,
    ( ~ r3_waybel_9(sK7,sK8,k1_waybel_2(sK7,sK8))
    | r3_waybel_9(sK7,sK8,sK5(sK7,sK8))
    | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
    | ~ v4_orders_2(sK8)
    | ~ v7_waybel_0(sK8)
    | v2_struct_0(sK8)
    | k10_yellow_6(sK7,sK8) != k10_yellow_6(sK7,sK8) ),
    inference(unflattening,[status(thm)],[c_2696])).

cnf(c_2699,plain,
    ( ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
    | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | r3_waybel_9(sK7,sK8,sK5(sK7,sK8))
    | ~ r3_waybel_9(sK7,sK8,k1_waybel_2(sK7,sK8))
    | k10_yellow_6(sK7,sK8) != k10_yellow_6(sK7,sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2697,c_33,c_32,c_31])).

cnf(c_2700,plain,
    ( ~ r3_waybel_9(sK7,sK8,k1_waybel_2(sK7,sK8))
    | r3_waybel_9(sK7,sK8,sK5(sK7,sK8))
    | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
    | k10_yellow_6(sK7,sK8) != k10_yellow_6(sK7,sK8) ),
    inference(renaming,[status(thm)],[c_2699])).

cnf(c_3695,plain,
    ( ~ r3_waybel_9(sK7,sK8,k1_waybel_2(sK7,sK8))
    | r3_waybel_9(sK7,sK8,sK5(sK7,sK8))
    | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7)) ),
    inference(equality_resolution_simp,[status(thm)],[c_2700])).

cnf(c_4599,plain,
    ( ~ r3_waybel_9(sK7,sK8,k1_waybel_2(sK7,sK8))
    | r3_waybel_9(sK7,sK8,sK5(sK7,sK8))
    | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_3695])).

cnf(c_5137,plain,
    ( r3_waybel_9(sK7,sK8,k1_waybel_2(sK7,sK8)) != iProver_top
    | r3_waybel_9(sK7,sK8,sK5(sK7,sK8)) = iProver_top
    | r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) != iProver_top
    | m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4599])).

cnf(c_3696,plain,
    ( r3_waybel_9(sK7,sK8,k1_waybel_2(sK7,sK8)) != iProver_top
    | r3_waybel_9(sK7,sK8,sK5(sK7,sK8)) = iProver_top
    | r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) != iProver_top
    | m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3695])).

cnf(c_6214,plain,
    ( r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) != iProver_top
    | r3_waybel_9(sK7,sK8,sK5(sK7,sK8)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5137,c_56,c_57,c_58,c_2607,c_2618,c_3696,c_5496,c_5508,c_5513])).

cnf(c_6215,plain,
    ( r3_waybel_9(sK7,sK8,sK5(sK7,sK8)) = iProver_top
    | r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) != iProver_top ),
    inference(renaming,[status(thm)],[c_6214])).

cnf(c_6660,plain,
    ( r3_waybel_9(sK7,sK8,sK5(sK7,sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6652,c_6215])).

cnf(c_6992,plain,
    ( sK5(sK7,sK8) = sK3(sK7,sK8)
    | m1_subset_1(sK5(sK7,sK8),u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6660,c_5550])).

cnf(c_24,plain,
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
    inference(cnf_transformation,[],[f80])).

cnf(c_2097,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | k1_waybel_2(sK7,sK8) != X2
    | k10_yellow_6(X0,X1) != k10_yellow_6(sK7,sK8) ),
    inference(resolution_lifted,[status(thm)],[c_24,c_492])).

cnf(c_2098,plain,
    ( ~ r3_waybel_9(X0,X1,k1_waybel_2(sK7,sK8))
    | ~ l1_waybel_0(X1,X0)
    | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(X0))
    | m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | k10_yellow_6(X0,X1) != k10_yellow_6(sK7,sK8) ),
    inference(unflattening,[status(thm)],[c_2097])).

cnf(c_2411,plain,
    ( ~ r3_waybel_9(X0,X1,k1_waybel_2(sK7,sK8))
    | ~ l1_waybel_0(X1,X0)
    | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(X0))
    | m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | k10_yellow_6(X0,X1) != k10_yellow_6(sK7,sK8)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2098,c_1553])).

cnf(c_2412,plain,
    ( ~ r3_waybel_9(sK7,X0,k1_waybel_2(sK7,sK8))
    | ~ l1_waybel_0(X0,sK7)
    | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
    | m1_subset_1(sK5(sK7,X0),u1_struct_0(sK7))
    | ~ v2_pre_topc(sK7)
    | ~ v8_pre_topc(sK7)
    | ~ v1_compts_1(sK7)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK7)
    | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8) ),
    inference(unflattening,[status(thm)],[c_2411])).

cnf(c_2416,plain,
    ( v2_struct_0(X0)
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ r3_waybel_9(sK7,X0,k1_waybel_2(sK7,sK8))
    | ~ l1_waybel_0(X0,sK7)
    | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
    | m1_subset_1(sK5(sK7,X0),u1_struct_0(sK7))
    | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2412,c_43,c_42,c_38,c_36,c_35,c_105,c_138])).

cnf(c_2417,plain,
    ( ~ r3_waybel_9(sK7,X0,k1_waybel_2(sK7,sK8))
    | ~ l1_waybel_0(X0,sK7)
    | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
    | m1_subset_1(sK5(sK7,X0),u1_struct_0(sK7))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8) ),
    inference(renaming,[status(thm)],[c_2416])).

cnf(c_2650,plain,
    ( ~ r3_waybel_9(sK7,X0,k1_waybel_2(sK7,sK8))
    | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
    | m1_subset_1(sK5(sK7,X0),u1_struct_0(sK7))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8)
    | sK8 != X0
    | sK7 != sK7 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_2417])).

cnf(c_2651,plain,
    ( ~ r3_waybel_9(sK7,sK8,k1_waybel_2(sK7,sK8))
    | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
    | m1_subset_1(sK5(sK7,sK8),u1_struct_0(sK7))
    | ~ v4_orders_2(sK8)
    | ~ v7_waybel_0(sK8)
    | v2_struct_0(sK8)
    | k10_yellow_6(sK7,sK8) != k10_yellow_6(sK7,sK8) ),
    inference(unflattening,[status(thm)],[c_2650])).

cnf(c_2653,plain,
    ( m1_subset_1(sK5(sK7,sK8),u1_struct_0(sK7))
    | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
    | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ r3_waybel_9(sK7,sK8,k1_waybel_2(sK7,sK8))
    | k10_yellow_6(sK7,sK8) != k10_yellow_6(sK7,sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2651,c_33,c_32,c_31])).

cnf(c_2654,plain,
    ( ~ r3_waybel_9(sK7,sK8,k1_waybel_2(sK7,sK8))
    | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
    | m1_subset_1(sK5(sK7,sK8),u1_struct_0(sK7))
    | k10_yellow_6(sK7,sK8) != k10_yellow_6(sK7,sK8) ),
    inference(renaming,[status(thm)],[c_2653])).

cnf(c_3699,plain,
    ( ~ r3_waybel_9(sK7,sK8,k1_waybel_2(sK7,sK8))
    | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
    | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
    | m1_subset_1(sK5(sK7,sK8),u1_struct_0(sK7)) ),
    inference(equality_resolution_simp,[status(thm)],[c_2654])).

cnf(c_3700,plain,
    ( r3_waybel_9(sK7,sK8,k1_waybel_2(sK7,sK8)) != iProver_top
    | r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) != iProver_top
    | m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK5(sK7,sK8),u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3699])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7267,c_6992,c_6649,c_5513,c_5508,c_5496,c_3700,c_2618,c_2607,c_58,c_57,c_56])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:09:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.10/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.10/0.98  
% 3.10/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.10/0.98  
% 3.10/0.98  ------  iProver source info
% 3.10/0.98  
% 3.10/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.10/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.10/0.98  git: non_committed_changes: false
% 3.10/0.98  git: last_make_outside_of_git: false
% 3.10/0.98  
% 3.10/0.98  ------ 
% 3.10/0.98  
% 3.10/0.98  ------ Input Options
% 3.10/0.98  
% 3.10/0.98  --out_options                           all
% 3.10/0.98  --tptp_safe_out                         true
% 3.10/0.98  --problem_path                          ""
% 3.10/0.98  --include_path                          ""
% 3.10/0.98  --clausifier                            res/vclausify_rel
% 3.10/0.98  --clausifier_options                    --mode clausify
% 3.10/0.98  --stdin                                 false
% 3.10/0.98  --stats_out                             all
% 3.10/0.98  
% 3.10/0.98  ------ General Options
% 3.10/0.98  
% 3.10/0.98  --fof                                   false
% 3.10/0.98  --time_out_real                         305.
% 3.10/0.98  --time_out_virtual                      -1.
% 3.10/0.98  --symbol_type_check                     false
% 3.10/0.98  --clausify_out                          false
% 3.10/0.98  --sig_cnt_out                           false
% 3.10/0.98  --trig_cnt_out                          false
% 3.10/0.98  --trig_cnt_out_tolerance                1.
% 3.10/0.98  --trig_cnt_out_sk_spl                   false
% 3.10/0.98  --abstr_cl_out                          false
% 3.10/0.98  
% 3.10/0.98  ------ Global Options
% 3.10/0.98  
% 3.10/0.98  --schedule                              default
% 3.10/0.98  --add_important_lit                     false
% 3.10/0.98  --prop_solver_per_cl                    1000
% 3.10/0.98  --min_unsat_core                        false
% 3.10/0.98  --soft_assumptions                      false
% 3.10/0.98  --soft_lemma_size                       3
% 3.10/0.98  --prop_impl_unit_size                   0
% 3.10/0.98  --prop_impl_unit                        []
% 3.10/0.98  --share_sel_clauses                     true
% 3.10/0.98  --reset_solvers                         false
% 3.10/0.98  --bc_imp_inh                            [conj_cone]
% 3.10/0.98  --conj_cone_tolerance                   3.
% 3.10/0.98  --extra_neg_conj                        none
% 3.10/0.98  --large_theory_mode                     true
% 3.10/0.98  --prolific_symb_bound                   200
% 3.10/0.98  --lt_threshold                          2000
% 3.10/0.98  --clause_weak_htbl                      true
% 3.10/0.98  --gc_record_bc_elim                     false
% 3.10/0.98  
% 3.10/0.98  ------ Preprocessing Options
% 3.10/0.98  
% 3.10/0.98  --preprocessing_flag                    true
% 3.10/0.98  --time_out_prep_mult                    0.1
% 3.10/0.98  --splitting_mode                        input
% 3.10/0.98  --splitting_grd                         true
% 3.10/0.98  --splitting_cvd                         false
% 3.10/0.98  --splitting_cvd_svl                     false
% 3.10/0.98  --splitting_nvd                         32
% 3.10/0.98  --sub_typing                            true
% 3.10/0.98  --prep_gs_sim                           true
% 3.10/0.98  --prep_unflatten                        true
% 3.10/0.98  --prep_res_sim                          true
% 3.10/0.98  --prep_upred                            true
% 3.10/0.98  --prep_sem_filter                       exhaustive
% 3.10/0.98  --prep_sem_filter_out                   false
% 3.10/0.98  --pred_elim                             true
% 3.10/0.98  --res_sim_input                         true
% 3.10/0.98  --eq_ax_congr_red                       true
% 3.10/0.98  --pure_diseq_elim                       true
% 3.10/0.98  --brand_transform                       false
% 3.10/0.98  --non_eq_to_eq                          false
% 3.10/0.98  --prep_def_merge                        true
% 3.10/0.98  --prep_def_merge_prop_impl              false
% 3.10/0.98  --prep_def_merge_mbd                    true
% 3.10/0.98  --prep_def_merge_tr_red                 false
% 3.10/0.98  --prep_def_merge_tr_cl                  false
% 3.10/0.98  --smt_preprocessing                     true
% 3.10/0.98  --smt_ac_axioms                         fast
% 3.10/0.98  --preprocessed_out                      false
% 3.10/0.98  --preprocessed_stats                    false
% 3.10/0.98  
% 3.10/0.98  ------ Abstraction refinement Options
% 3.10/0.98  
% 3.10/0.98  --abstr_ref                             []
% 3.10/0.98  --abstr_ref_prep                        false
% 3.10/0.98  --abstr_ref_until_sat                   false
% 3.10/0.98  --abstr_ref_sig_restrict                funpre
% 3.10/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.10/0.98  --abstr_ref_under                       []
% 3.10/0.98  
% 3.10/0.98  ------ SAT Options
% 3.10/0.98  
% 3.10/0.98  --sat_mode                              false
% 3.10/0.98  --sat_fm_restart_options                ""
% 3.10/0.98  --sat_gr_def                            false
% 3.10/0.98  --sat_epr_types                         true
% 3.10/0.98  --sat_non_cyclic_types                  false
% 3.10/0.98  --sat_finite_models                     false
% 3.10/0.98  --sat_fm_lemmas                         false
% 3.10/0.98  --sat_fm_prep                           false
% 3.10/0.98  --sat_fm_uc_incr                        true
% 3.10/0.98  --sat_out_model                         small
% 3.10/0.98  --sat_out_clauses                       false
% 3.10/0.98  
% 3.10/0.98  ------ QBF Options
% 3.10/0.98  
% 3.10/0.98  --qbf_mode                              false
% 3.10/0.98  --qbf_elim_univ                         false
% 3.10/0.98  --qbf_dom_inst                          none
% 3.10/0.98  --qbf_dom_pre_inst                      false
% 3.10/0.98  --qbf_sk_in                             false
% 3.10/0.98  --qbf_pred_elim                         true
% 3.10/0.98  --qbf_split                             512
% 3.10/0.98  
% 3.10/0.98  ------ BMC1 Options
% 3.10/0.98  
% 3.10/0.98  --bmc1_incremental                      false
% 3.10/0.98  --bmc1_axioms                           reachable_all
% 3.10/0.98  --bmc1_min_bound                        0
% 3.10/0.98  --bmc1_max_bound                        -1
% 3.10/0.98  --bmc1_max_bound_default                -1
% 3.10/0.98  --bmc1_symbol_reachability              true
% 3.10/0.98  --bmc1_property_lemmas                  false
% 3.10/0.98  --bmc1_k_induction                      false
% 3.10/0.98  --bmc1_non_equiv_states                 false
% 3.10/0.98  --bmc1_deadlock                         false
% 3.10/0.98  --bmc1_ucm                              false
% 3.10/0.98  --bmc1_add_unsat_core                   none
% 3.10/0.98  --bmc1_unsat_core_children              false
% 3.10/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.10/0.98  --bmc1_out_stat                         full
% 3.10/0.98  --bmc1_ground_init                      false
% 3.10/0.98  --bmc1_pre_inst_next_state              false
% 3.10/0.98  --bmc1_pre_inst_state                   false
% 3.10/0.98  --bmc1_pre_inst_reach_state             false
% 3.10/0.98  --bmc1_out_unsat_core                   false
% 3.10/0.98  --bmc1_aig_witness_out                  false
% 3.10/0.98  --bmc1_verbose                          false
% 3.10/0.98  --bmc1_dump_clauses_tptp                false
% 3.10/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.10/0.98  --bmc1_dump_file                        -
% 3.10/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.10/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.10/0.98  --bmc1_ucm_extend_mode                  1
% 3.10/0.98  --bmc1_ucm_init_mode                    2
% 3.10/0.98  --bmc1_ucm_cone_mode                    none
% 3.10/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.10/0.98  --bmc1_ucm_relax_model                  4
% 3.10/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.10/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.10/0.98  --bmc1_ucm_layered_model                none
% 3.10/0.98  --bmc1_ucm_max_lemma_size               10
% 3.10/0.98  
% 3.10/0.98  ------ AIG Options
% 3.10/0.98  
% 3.10/0.98  --aig_mode                              false
% 3.10/0.98  
% 3.10/0.98  ------ Instantiation Options
% 3.10/0.98  
% 3.10/0.98  --instantiation_flag                    true
% 3.10/0.98  --inst_sos_flag                         false
% 3.10/0.98  --inst_sos_phase                        true
% 3.10/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.10/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.10/0.98  --inst_lit_sel_side                     num_symb
% 3.10/0.98  --inst_solver_per_active                1400
% 3.10/0.98  --inst_solver_calls_frac                1.
% 3.10/0.98  --inst_passive_queue_type               priority_queues
% 3.10/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.10/0.98  --inst_passive_queues_freq              [25;2]
% 3.10/0.98  --inst_dismatching                      true
% 3.10/0.98  --inst_eager_unprocessed_to_passive     true
% 3.10/0.98  --inst_prop_sim_given                   true
% 3.10/0.98  --inst_prop_sim_new                     false
% 3.10/0.98  --inst_subs_new                         false
% 3.10/0.98  --inst_eq_res_simp                      false
% 3.10/0.98  --inst_subs_given                       false
% 3.10/0.98  --inst_orphan_elimination               true
% 3.10/0.98  --inst_learning_loop_flag               true
% 3.10/0.98  --inst_learning_start                   3000
% 3.10/0.98  --inst_learning_factor                  2
% 3.10/0.98  --inst_start_prop_sim_after_learn       3
% 3.10/0.98  --inst_sel_renew                        solver
% 3.10/0.98  --inst_lit_activity_flag                true
% 3.10/0.98  --inst_restr_to_given                   false
% 3.10/0.98  --inst_activity_threshold               500
% 3.10/0.98  --inst_out_proof                        true
% 3.10/0.98  
% 3.10/0.98  ------ Resolution Options
% 3.10/0.98  
% 3.10/0.98  --resolution_flag                       true
% 3.10/0.98  --res_lit_sel                           adaptive
% 3.10/0.98  --res_lit_sel_side                      none
% 3.10/0.98  --res_ordering                          kbo
% 3.10/0.98  --res_to_prop_solver                    active
% 3.10/0.98  --res_prop_simpl_new                    false
% 3.10/0.98  --res_prop_simpl_given                  true
% 3.10/0.98  --res_passive_queue_type                priority_queues
% 3.10/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.10/0.98  --res_passive_queues_freq               [15;5]
% 3.10/0.98  --res_forward_subs                      full
% 3.10/0.98  --res_backward_subs                     full
% 3.10/0.98  --res_forward_subs_resolution           true
% 3.10/0.98  --res_backward_subs_resolution          true
% 3.10/0.98  --res_orphan_elimination                true
% 3.10/0.98  --res_time_limit                        2.
% 3.10/0.98  --res_out_proof                         true
% 3.10/0.98  
% 3.10/0.98  ------ Superposition Options
% 3.10/0.98  
% 3.10/0.98  --superposition_flag                    true
% 3.10/0.98  --sup_passive_queue_type                priority_queues
% 3.10/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.10/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.10/0.98  --demod_completeness_check              fast
% 3.10/0.98  --demod_use_ground                      true
% 3.10/0.98  --sup_to_prop_solver                    passive
% 3.10/0.98  --sup_prop_simpl_new                    true
% 3.10/0.98  --sup_prop_simpl_given                  true
% 3.10/0.98  --sup_fun_splitting                     false
% 3.10/0.98  --sup_smt_interval                      50000
% 3.10/0.98  
% 3.10/0.98  ------ Superposition Simplification Setup
% 3.10/0.98  
% 3.10/0.98  --sup_indices_passive                   []
% 3.10/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.10/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.10/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.10/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.10/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.10/0.98  --sup_full_bw                           [BwDemod]
% 3.10/0.98  --sup_immed_triv                        [TrivRules]
% 3.10/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.10/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.10/0.98  --sup_immed_bw_main                     []
% 3.10/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.10/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.10/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.10/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.10/0.98  
% 3.10/0.98  ------ Combination Options
% 3.10/0.98  
% 3.10/0.98  --comb_res_mult                         3
% 3.10/0.98  --comb_sup_mult                         2
% 3.10/0.98  --comb_inst_mult                        10
% 3.10/0.98  
% 3.10/0.98  ------ Debug Options
% 3.10/0.98  
% 3.10/0.98  --dbg_backtrace                         false
% 3.10/0.98  --dbg_dump_prop_clauses                 false
% 3.10/0.98  --dbg_dump_prop_clauses_file            -
% 3.10/0.98  --dbg_out_stat                          false
% 3.10/0.98  ------ Parsing...
% 3.10/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.10/0.98  
% 3.10/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe:16:0s pe_e  sf_s  rm: 17 0s  sf_e  pe_s  pe_e 
% 3.10/0.98  
% 3.10/0.98  ------ Preprocessing... gs_s  sp: 6 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.10/0.98  
% 3.10/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.10/0.98  ------ Proving...
% 3.10/0.98  ------ Problem Properties 
% 3.10/0.98  
% 3.10/0.98  
% 3.10/0.98  clauses                                 27
% 3.10/0.98  conjectures                             0
% 3.10/0.98  EPR                                     3
% 3.10/0.98  Horn                                    17
% 3.10/0.98  unary                                   2
% 3.10/0.98  binary                                  3
% 3.10/0.98  lits                                    97
% 3.10/0.98  lits eq                                 9
% 3.10/0.98  fd_pure                                 0
% 3.10/0.98  fd_pseudo                               0
% 3.10/0.98  fd_cond                                 2
% 3.10/0.98  fd_pseudo_cond                          3
% 3.10/0.98  AC symbols                              0
% 3.10/0.98  
% 3.10/0.98  ------ Schedule dynamic 5 is on 
% 3.10/0.98  
% 3.10/0.98  ------ no conjectures: strip conj schedule 
% 3.10/0.98  
% 3.10/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" stripped conjectures Time Limit: 10.
% 3.10/0.98  
% 3.10/0.98  
% 3.10/0.98  ------ 
% 3.10/0.98  Current options:
% 3.10/0.98  ------ 
% 3.10/0.98  
% 3.10/0.98  ------ Input Options
% 3.10/0.98  
% 3.10/0.98  --out_options                           all
% 3.10/0.98  --tptp_safe_out                         true
% 3.10/0.98  --problem_path                          ""
% 3.10/0.98  --include_path                          ""
% 3.10/0.98  --clausifier                            res/vclausify_rel
% 3.10/0.98  --clausifier_options                    --mode clausify
% 3.10/0.98  --stdin                                 false
% 3.10/0.98  --stats_out                             all
% 3.10/0.98  
% 3.10/0.98  ------ General Options
% 3.10/0.98  
% 3.10/0.98  --fof                                   false
% 3.10/0.98  --time_out_real                         305.
% 3.10/0.98  --time_out_virtual                      -1.
% 3.10/0.98  --symbol_type_check                     false
% 3.10/0.98  --clausify_out                          false
% 3.10/0.98  --sig_cnt_out                           false
% 3.10/0.98  --trig_cnt_out                          false
% 3.10/0.98  --trig_cnt_out_tolerance                1.
% 3.10/0.98  --trig_cnt_out_sk_spl                   false
% 3.10/0.98  --abstr_cl_out                          false
% 3.10/0.98  
% 3.10/0.98  ------ Global Options
% 3.10/0.98  
% 3.10/0.98  --schedule                              default
% 3.10/0.98  --add_important_lit                     false
% 3.10/0.98  --prop_solver_per_cl                    1000
% 3.10/0.98  --min_unsat_core                        false
% 3.10/0.98  --soft_assumptions                      false
% 3.10/0.98  --soft_lemma_size                       3
% 3.10/0.98  --prop_impl_unit_size                   0
% 3.10/0.98  --prop_impl_unit                        []
% 3.10/0.98  --share_sel_clauses                     true
% 3.10/0.98  --reset_solvers                         false
% 3.10/0.98  --bc_imp_inh                            [conj_cone]
% 3.10/0.98  --conj_cone_tolerance                   3.
% 3.10/0.98  --extra_neg_conj                        none
% 3.10/0.98  --large_theory_mode                     true
% 3.10/0.98  --prolific_symb_bound                   200
% 3.10/0.98  --lt_threshold                          2000
% 3.10/0.98  --clause_weak_htbl                      true
% 3.10/0.98  --gc_record_bc_elim                     false
% 3.10/0.98  
% 3.10/0.98  ------ Preprocessing Options
% 3.10/0.98  
% 3.10/0.98  --preprocessing_flag                    true
% 3.10/0.98  --time_out_prep_mult                    0.1
% 3.10/0.98  --splitting_mode                        input
% 3.10/0.98  --splitting_grd                         true
% 3.10/0.98  --splitting_cvd                         false
% 3.10/0.98  --splitting_cvd_svl                     false
% 3.10/0.98  --splitting_nvd                         32
% 3.10/0.98  --sub_typing                            true
% 3.10/0.98  --prep_gs_sim                           true
% 3.10/0.98  --prep_unflatten                        true
% 3.10/0.98  --prep_res_sim                          true
% 3.10/0.98  --prep_upred                            true
% 3.10/0.98  --prep_sem_filter                       exhaustive
% 3.10/0.98  --prep_sem_filter_out                   false
% 3.10/0.98  --pred_elim                             true
% 3.10/0.98  --res_sim_input                         true
% 3.10/0.98  --eq_ax_congr_red                       true
% 3.10/0.98  --pure_diseq_elim                       true
% 3.10/0.98  --brand_transform                       false
% 3.10/0.98  --non_eq_to_eq                          false
% 3.10/0.98  --prep_def_merge                        true
% 3.10/0.98  --prep_def_merge_prop_impl              false
% 3.10/0.98  --prep_def_merge_mbd                    true
% 3.10/0.98  --prep_def_merge_tr_red                 false
% 3.10/0.98  --prep_def_merge_tr_cl                  false
% 3.10/0.98  --smt_preprocessing                     true
% 3.10/0.98  --smt_ac_axioms                         fast
% 3.10/0.98  --preprocessed_out                      false
% 3.10/0.98  --preprocessed_stats                    false
% 3.10/0.98  
% 3.10/0.98  ------ Abstraction refinement Options
% 3.10/0.98  
% 3.10/0.98  --abstr_ref                             []
% 3.10/0.98  --abstr_ref_prep                        false
% 3.10/0.98  --abstr_ref_until_sat                   false
% 3.10/0.98  --abstr_ref_sig_restrict                funpre
% 3.10/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.10/0.98  --abstr_ref_under                       []
% 3.10/0.98  
% 3.10/0.98  ------ SAT Options
% 3.10/0.98  
% 3.10/0.98  --sat_mode                              false
% 3.10/0.98  --sat_fm_restart_options                ""
% 3.10/0.98  --sat_gr_def                            false
% 3.10/0.98  --sat_epr_types                         true
% 3.10/0.98  --sat_non_cyclic_types                  false
% 3.10/0.98  --sat_finite_models                     false
% 3.10/0.98  --sat_fm_lemmas                         false
% 3.10/0.98  --sat_fm_prep                           false
% 3.10/0.98  --sat_fm_uc_incr                        true
% 3.10/0.98  --sat_out_model                         small
% 3.10/0.98  --sat_out_clauses                       false
% 3.10/0.98  
% 3.10/0.98  ------ QBF Options
% 3.10/0.98  
% 3.10/0.98  --qbf_mode                              false
% 3.10/0.98  --qbf_elim_univ                         false
% 3.10/0.98  --qbf_dom_inst                          none
% 3.10/0.98  --qbf_dom_pre_inst                      false
% 3.10/0.98  --qbf_sk_in                             false
% 3.10/0.98  --qbf_pred_elim                         true
% 3.10/0.98  --qbf_split                             512
% 3.10/0.98  
% 3.10/0.98  ------ BMC1 Options
% 3.10/0.98  
% 3.10/0.98  --bmc1_incremental                      false
% 3.10/0.98  --bmc1_axioms                           reachable_all
% 3.10/0.98  --bmc1_min_bound                        0
% 3.10/0.98  --bmc1_max_bound                        -1
% 3.10/0.98  --bmc1_max_bound_default                -1
% 3.10/0.98  --bmc1_symbol_reachability              true
% 3.10/0.98  --bmc1_property_lemmas                  false
% 3.10/0.98  --bmc1_k_induction                      false
% 3.10/0.98  --bmc1_non_equiv_states                 false
% 3.10/0.98  --bmc1_deadlock                         false
% 3.10/0.98  --bmc1_ucm                              false
% 3.10/0.98  --bmc1_add_unsat_core                   none
% 3.10/0.98  --bmc1_unsat_core_children              false
% 3.10/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.10/0.98  --bmc1_out_stat                         full
% 3.10/0.98  --bmc1_ground_init                      false
% 3.10/0.98  --bmc1_pre_inst_next_state              false
% 3.10/0.98  --bmc1_pre_inst_state                   false
% 3.10/0.98  --bmc1_pre_inst_reach_state             false
% 3.10/0.98  --bmc1_out_unsat_core                   false
% 3.10/0.98  --bmc1_aig_witness_out                  false
% 3.10/0.98  --bmc1_verbose                          false
% 3.10/0.98  --bmc1_dump_clauses_tptp                false
% 3.10/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.10/0.98  --bmc1_dump_file                        -
% 3.10/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.10/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.10/0.98  --bmc1_ucm_extend_mode                  1
% 3.10/0.98  --bmc1_ucm_init_mode                    2
% 3.10/0.98  --bmc1_ucm_cone_mode                    none
% 3.10/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.10/0.98  --bmc1_ucm_relax_model                  4
% 3.10/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.10/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.10/0.98  --bmc1_ucm_layered_model                none
% 3.10/0.98  --bmc1_ucm_max_lemma_size               10
% 3.10/0.98  
% 3.10/0.98  ------ AIG Options
% 3.10/0.98  
% 3.10/0.98  --aig_mode                              false
% 3.10/0.98  
% 3.10/0.98  ------ Instantiation Options
% 3.10/0.98  
% 3.10/0.98  --instantiation_flag                    true
% 3.10/0.98  --inst_sos_flag                         false
% 3.10/0.98  --inst_sos_phase                        true
% 3.10/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.10/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.10/0.98  --inst_lit_sel_side                     none
% 3.10/0.98  --inst_solver_per_active                1400
% 3.10/0.98  --inst_solver_calls_frac                1.
% 3.10/0.98  --inst_passive_queue_type               priority_queues
% 3.10/0.98  --inst_passive_queues                   [[-num_var];[+age;-num_symb]]
% 3.10/0.98  --inst_passive_queues_freq              [25;2]
% 3.10/0.98  --inst_dismatching                      true
% 3.10/0.98  --inst_eager_unprocessed_to_passive     true
% 3.10/0.98  --inst_prop_sim_given                   true
% 3.10/0.98  --inst_prop_sim_new                     false
% 3.10/0.98  --inst_subs_new                         false
% 3.10/0.98  --inst_eq_res_simp                      false
% 3.10/0.98  --inst_subs_given                       false
% 3.10/0.98  --inst_orphan_elimination               true
% 3.10/0.98  --inst_learning_loop_flag               true
% 3.10/0.98  --inst_learning_start                   3000
% 3.10/0.98  --inst_learning_factor                  2
% 3.10/0.98  --inst_start_prop_sim_after_learn       3
% 3.10/0.98  --inst_sel_renew                        solver
% 3.10/0.98  --inst_lit_activity_flag                true
% 3.10/0.98  --inst_restr_to_given                   false
% 3.10/0.98  --inst_activity_threshold               500
% 3.10/0.98  --inst_out_proof                        true
% 3.10/0.98  
% 3.10/0.98  ------ Resolution Options
% 3.10/0.98  
% 3.10/0.98  --resolution_flag                       false
% 3.10/0.98  --res_lit_sel                           adaptive
% 3.10/0.98  --res_lit_sel_side                      none
% 3.10/0.98  --res_ordering                          kbo
% 3.10/0.98  --res_to_prop_solver                    active
% 3.10/0.98  --res_prop_simpl_new                    false
% 3.10/0.98  --res_prop_simpl_given                  true
% 3.10/0.98  --res_passive_queue_type                priority_queues
% 3.10/0.98  --res_passive_queues                    [[-num_symb];[+age;-num_symb]]
% 3.10/0.98  --res_passive_queues_freq               [15;5]
% 3.10/0.98  --res_forward_subs                      full
% 3.10/0.98  --res_backward_subs                     full
% 3.10/0.98  --res_forward_subs_resolution           true
% 3.10/0.98  --res_backward_subs_resolution          true
% 3.10/0.98  --res_orphan_elimination                true
% 3.10/0.98  --res_time_limit                        2.
% 3.10/0.98  --res_out_proof                         true
% 3.10/0.98  
% 3.10/0.98  ------ Superposition Options
% 3.10/0.98  
% 3.10/0.98  --superposition_flag                    true
% 3.10/0.98  --sup_passive_queue_type                priority_queues
% 3.10/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.10/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.10/0.98  --demod_completeness_check              fast
% 3.10/0.98  --demod_use_ground                      true
% 3.10/0.98  --sup_to_prop_solver                    passive
% 3.10/0.98  --sup_prop_simpl_new                    true
% 3.10/0.98  --sup_prop_simpl_given                  true
% 3.10/0.98  --sup_fun_splitting                     false
% 3.10/0.98  --sup_smt_interval                      50000
% 3.10/0.98  
% 3.10/0.98  ------ Superposition Simplification Setup
% 3.10/0.98  
% 3.10/0.98  --sup_indices_passive                   []
% 3.10/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.10/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.10/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.10/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.10/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.10/0.98  --sup_full_bw                           [BwDemod]
% 3.10/0.98  --sup_immed_triv                        [TrivRules]
% 3.10/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.10/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.10/0.98  --sup_immed_bw_main                     []
% 3.10/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.10/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.10/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.10/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.10/0.98  
% 3.10/0.98  ------ Combination Options
% 3.10/0.98  
% 3.10/0.98  --comb_res_mult                         3
% 3.10/0.98  --comb_sup_mult                         2
% 3.10/0.98  --comb_inst_mult                        10
% 3.10/0.98  
% 3.10/0.98  ------ Debug Options
% 3.10/0.98  
% 3.10/0.98  --dbg_backtrace                         false
% 3.10/0.98  --dbg_dump_prop_clauses                 false
% 3.10/0.98  --dbg_dump_prop_clauses_file            -
% 3.10/0.98  --dbg_out_stat                          false
% 3.10/0.98  
% 3.10/0.98  
% 3.10/0.98  
% 3.10/0.98  
% 3.10/0.98  ------ Proving...
% 3.10/0.98  
% 3.10/0.98  
% 3.10/0.98  % SZS status Theorem for theBenchmark.p
% 3.10/0.98  
% 3.10/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.10/0.98  
% 3.10/0.98  fof(f11,conjecture,(
% 3.10/0.98    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => (! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X1),X0,X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (v10_waybel_0(X1,X0) => (r2_hidden(k1_waybel_2(X0,X1),k10_yellow_6(X0,X1)) & r1_waybel_9(X0,X1))))))),
% 3.10/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/0.98  
% 3.10/0.98  fof(f12,negated_conjecture,(
% 3.10/0.98    ~! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => (! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X1),X0,X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (v10_waybel_0(X1,X0) => (r2_hidden(k1_waybel_2(X0,X1),k10_yellow_6(X0,X1)) & r1_waybel_9(X0,X1))))))),
% 3.10/0.98    inference(negated_conjecture,[],[f11])).
% 3.10/0.98  
% 3.10/0.98  fof(f16,plain,(
% 3.10/0.98    ~! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => (! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X1),X0,X0)) => ! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => (v10_waybel_0(X2,X0) => (r2_hidden(k1_waybel_2(X0,X2),k10_yellow_6(X0,X2)) & r1_waybel_9(X0,X2))))))),
% 3.10/0.98    inference(rectify,[],[f12])).
% 3.10/0.98  
% 3.10/0.98  fof(f35,plain,(
% 3.10/0.98    ? [X0] : ((? [X2] : (((~r2_hidden(k1_waybel_2(X0,X2),k10_yellow_6(X0,X2)) | ~r1_waybel_9(X0,X2)) & v10_waybel_0(X2,X0)) & (l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2))) & ! [X1] : (v5_pre_topc(k4_waybel_1(X0,X1),X0,X0) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.10/0.98    inference(ennf_transformation,[],[f16])).
% 3.10/0.98  
% 3.10/0.98  fof(f36,plain,(
% 3.10/0.98    ? [X0] : (? [X2] : ((~r2_hidden(k1_waybel_2(X0,X2),k10_yellow_6(X0,X2)) | ~r1_waybel_9(X0,X2)) & v10_waybel_0(X2,X0) & l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & ! [X1] : (v5_pre_topc(k4_waybel_1(X0,X1),X0,X0) | ~m1_subset_1(X1,u1_struct_0(X0))) & l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0))),
% 3.10/0.98    inference(flattening,[],[f35])).
% 3.10/0.98  
% 3.10/0.98  fof(f54,plain,(
% 3.10/0.98    ? [X0] : (? [X1] : ((~r2_hidden(k1_waybel_2(X0,X1),k10_yellow_6(X0,X1)) | ~r1_waybel_9(X0,X1)) & v10_waybel_0(X1,X0) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & ! [X2] : (v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0))),
% 3.10/0.98    inference(rectify,[],[f36])).
% 3.10/0.98  
% 3.10/0.98  fof(f56,plain,(
% 3.10/0.98    ( ! [X0] : (? [X1] : ((~r2_hidden(k1_waybel_2(X0,X1),k10_yellow_6(X0,X1)) | ~r1_waybel_9(X0,X1)) & v10_waybel_0(X1,X0) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ((~r2_hidden(k1_waybel_2(X0,sK8),k10_yellow_6(X0,sK8)) | ~r1_waybel_9(X0,sK8)) & v10_waybel_0(sK8,X0) & l1_waybel_0(sK8,X0) & v7_waybel_0(sK8) & v4_orders_2(sK8) & ~v2_struct_0(sK8))) )),
% 3.10/0.98    introduced(choice_axiom,[])).
% 3.10/0.98  
% 3.10/0.98  fof(f55,plain,(
% 3.10/0.98    ? [X0] : (? [X1] : ((~r2_hidden(k1_waybel_2(X0,X1),k10_yellow_6(X0,X1)) | ~r1_waybel_9(X0,X1)) & v10_waybel_0(X1,X0) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & ! [X2] : (v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((~r2_hidden(k1_waybel_2(sK7,X1),k10_yellow_6(sK7,X1)) | ~r1_waybel_9(sK7,X1)) & v10_waybel_0(X1,sK7) & l1_waybel_0(X1,sK7) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & ! [X2] : (v5_pre_topc(k4_waybel_1(sK7,X2),sK7,sK7) | ~m1_subset_1(X2,u1_struct_0(sK7))) & l1_waybel_9(sK7) & v1_compts_1(sK7) & v2_lattice3(sK7) & v1_lattice3(sK7) & v5_orders_2(sK7) & v4_orders_2(sK7) & v3_orders_2(sK7) & v8_pre_topc(sK7) & v2_pre_topc(sK7))),
% 3.10/0.98    introduced(choice_axiom,[])).
% 3.10/0.98  
% 3.10/0.98  fof(f57,plain,(
% 3.10/0.98    ((~r2_hidden(k1_waybel_2(sK7,sK8),k10_yellow_6(sK7,sK8)) | ~r1_waybel_9(sK7,sK8)) & v10_waybel_0(sK8,sK7) & l1_waybel_0(sK8,sK7) & v7_waybel_0(sK8) & v4_orders_2(sK8) & ~v2_struct_0(sK8)) & ! [X2] : (v5_pre_topc(k4_waybel_1(sK7,X2),sK7,sK7) | ~m1_subset_1(X2,u1_struct_0(sK7))) & l1_waybel_9(sK7) & v1_compts_1(sK7) & v2_lattice3(sK7) & v1_lattice3(sK7) & v5_orders_2(sK7) & v4_orders_2(sK7) & v3_orders_2(sK7) & v8_pre_topc(sK7) & v2_pre_topc(sK7)),
% 3.10/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f54,f56,f55])).
% 3.10/0.98  
% 3.10/0.98  fof(f99,plain,(
% 3.10/0.98    l1_waybel_0(sK8,sK7)),
% 3.10/0.98    inference(cnf_transformation,[],[f57])).
% 3.10/0.98  
% 3.10/0.98  fof(f8,axiom,(
% 3.10/0.98    ! [X0] : ((l1_pre_topc(X0) & v1_compts_1(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0)))))),
% 3.10/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/0.98  
% 3.10/0.98  fof(f29,plain,(
% 3.10/0.98    ! [X0] : (! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.10/0.98    inference(ennf_transformation,[],[f8])).
% 3.10/0.98  
% 3.10/0.98  fof(f30,plain,(
% 3.10/0.98    ! [X0] : (! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.10/0.98    inference(flattening,[],[f29])).
% 3.10/0.98  
% 3.10/0.98  fof(f46,plain,(
% 3.10/0.98    ! [X1,X0] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) => (r3_waybel_9(X0,X1,sK3(X0,X1)) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))))),
% 3.10/0.98    introduced(choice_axiom,[])).
% 3.10/0.98  
% 3.10/0.98  fof(f47,plain,(
% 3.10/0.98    ! [X0] : (! [X1] : ((r3_waybel_9(X0,X1,sK3(X0,X1)) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.10/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f46])).
% 3.10/0.98  
% 3.10/0.98  fof(f78,plain,(
% 3.10/0.98    ( ! [X0,X1] : (r3_waybel_9(X0,X1,sK3(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.10/0.98    inference(cnf_transformation,[],[f47])).
% 3.10/0.98  
% 3.10/0.98  fof(f5,axiom,(
% 3.10/0.98    ! [X0] : (l1_waybel_9(X0) => (l1_orders_2(X0) & l1_pre_topc(X0)))),
% 3.10/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/0.98  
% 3.10/0.98  fof(f24,plain,(
% 3.10/0.98    ! [X0] : ((l1_orders_2(X0) & l1_pre_topc(X0)) | ~l1_waybel_9(X0))),
% 3.10/0.98    inference(ennf_transformation,[],[f5])).
% 3.10/0.98  
% 3.10/0.98  fof(f71,plain,(
% 3.10/0.98    ( ! [X0] : (l1_pre_topc(X0) | ~l1_waybel_9(X0)) )),
% 3.10/0.98    inference(cnf_transformation,[],[f24])).
% 3.10/0.98  
% 3.10/0.98  fof(f94,plain,(
% 3.10/0.98    l1_waybel_9(sK7)),
% 3.10/0.98    inference(cnf_transformation,[],[f57])).
% 3.10/0.98  
% 3.10/0.98  fof(f86,plain,(
% 3.10/0.98    v2_pre_topc(sK7)),
% 3.10/0.98    inference(cnf_transformation,[],[f57])).
% 3.10/0.98  
% 3.10/0.98  fof(f87,plain,(
% 3.10/0.98    v8_pre_topc(sK7)),
% 3.10/0.98    inference(cnf_transformation,[],[f57])).
% 3.10/0.98  
% 3.10/0.98  fof(f91,plain,(
% 3.10/0.98    v1_lattice3(sK7)),
% 3.10/0.98    inference(cnf_transformation,[],[f57])).
% 3.10/0.98  
% 3.10/0.98  fof(f93,plain,(
% 3.10/0.98    v1_compts_1(sK7)),
% 3.10/0.98    inference(cnf_transformation,[],[f57])).
% 3.10/0.98  
% 3.10/0.98  fof(f72,plain,(
% 3.10/0.98    ( ! [X0] : (l1_orders_2(X0) | ~l1_waybel_9(X0)) )),
% 3.10/0.98    inference(cnf_transformation,[],[f24])).
% 3.10/0.98  
% 3.10/0.98  fof(f2,axiom,(
% 3.10/0.98    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 3.10/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/0.98  
% 3.10/0.98  fof(f19,plain,(
% 3.10/0.98    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 3.10/0.98    inference(ennf_transformation,[],[f2])).
% 3.10/0.98  
% 3.10/0.98  fof(f20,plain,(
% 3.10/0.98    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 3.10/0.98    inference(flattening,[],[f19])).
% 3.10/0.98  
% 3.10/0.98  fof(f60,plain,(
% 3.10/0.98    ( ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0)) )),
% 3.10/0.98    inference(cnf_transformation,[],[f20])).
% 3.10/0.98  
% 3.10/0.98  fof(f96,plain,(
% 3.10/0.98    ~v2_struct_0(sK8)),
% 3.10/0.98    inference(cnf_transformation,[],[f57])).
% 3.10/0.98  
% 3.10/0.98  fof(f97,plain,(
% 3.10/0.98    v4_orders_2(sK8)),
% 3.10/0.98    inference(cnf_transformation,[],[f57])).
% 3.10/0.98  
% 3.10/0.98  fof(f98,plain,(
% 3.10/0.98    v7_waybel_0(sK8)),
% 3.10/0.98    inference(cnf_transformation,[],[f57])).
% 3.10/0.98  
% 3.10/0.98  fof(f3,axiom,(
% 3.10/0.98    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1)) => (r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1)) & ((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1))))))),
% 3.10/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/0.98  
% 3.10/0.98  fof(f13,plain,(
% 3.10/0.98    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1)) => (r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1)) & ((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) => (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X4) => r1_orders_2(X0,X1,X4))) & r2_lattice3(X0,X2,X1))))))),
% 3.10/0.98    inference(rectify,[],[f3])).
% 3.10/0.98  
% 3.10/0.98  fof(f21,plain,(
% 3.10/0.98    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | (? [X3] : ((~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3)) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1))) & ((! [X4] : ((r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | (~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0)))),
% 3.10/0.98    inference(ennf_transformation,[],[f13])).
% 3.10/0.98  
% 3.10/0.98  fof(f22,plain,(
% 3.10/0.98    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | ? [X3] : (~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | ~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 3.10/0.98    inference(flattening,[],[f21])).
% 3.10/0.98  
% 3.10/0.98  fof(f38,plain,(
% 3.10/0.98    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X1,sK0(X0,X1,X2)) & r2_lattice3(X0,X2,sK0(X0,X1,X2)) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 3.10/0.98    introduced(choice_axiom,[])).
% 3.10/0.98  
% 3.10/0.98  fof(f39,plain,(
% 3.10/0.98    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | (~r1_orders_2(X0,X1,sK0(X0,X1,X2)) & r2_lattice3(X0,X2,sK0(X0,X1,X2)) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | ~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 3.10/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f38])).
% 3.10/0.98  
% 3.10/0.98  fof(f67,plain,(
% 3.10/0.98    ( ! [X2,X0,X1] : (r1_yellow_0(X0,X2) | r2_lattice3(X0,X2,sK0(X0,X1,X2)) | ~r2_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 3.10/0.98    inference(cnf_transformation,[],[f39])).
% 3.10/0.98  
% 3.10/0.98  fof(f90,plain,(
% 3.10/0.98    v5_orders_2(sK7)),
% 3.10/0.98    inference(cnf_transformation,[],[f57])).
% 3.10/0.98  
% 3.10/0.98  fof(f1,axiom,(
% 3.10/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 3.10/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/0.98  
% 3.10/0.98  fof(f17,plain,(
% 3.10/0.98    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 3.10/0.98    inference(ennf_transformation,[],[f1])).
% 3.10/0.98  
% 3.10/0.98  fof(f18,plain,(
% 3.10/0.98    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.10/0.98    inference(flattening,[],[f17])).
% 3.10/0.98  
% 3.10/0.98  fof(f37,plain,(
% 3.10/0.98    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.10/0.98    inference(nnf_transformation,[],[f18])).
% 3.10/0.98  
% 3.10/0.98  fof(f58,plain,(
% 3.10/0.98    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.10/0.98    inference(cnf_transformation,[],[f37])).
% 3.10/0.98  
% 3.10/0.98  fof(f7,axiom,(
% 3.10/0.98    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X2) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)) & X2 = X3) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) => r3_orders_2(X0,X3,X4))))))))),
% 3.10/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/0.98  
% 3.10/0.98  fof(f14,plain,(
% 3.10/0.98    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X2) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)) & X2 = X3) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X0)) => (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5) => r3_orders_2(X0,X3,X5))))))))),
% 3.10/0.98    inference(rectify,[],[f7])).
% 3.10/0.98  
% 3.10/0.98  fof(f27,plain,(
% 3.10/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((! [X5] : ((r3_orders_2(X0,X3,X5) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5)) | ~m1_subset_1(X5,u1_struct_0(X0))) | (~r3_waybel_9(X0,X1,X2) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.10/0.98    inference(ennf_transformation,[],[f14])).
% 3.10/0.98  
% 3.10/0.98  fof(f28,plain,(
% 3.10/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X5] : (r3_orders_2(X0,X3,X5) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~r3_waybel_9(X0,X1,X2) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.10/0.98    inference(flattening,[],[f27])).
% 3.10/0.98  
% 3.10/0.98  fof(f43,plain,(
% 3.10/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r3_orders_2(X0,X3,X4) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_waybel_9(X0,X1,X2) | ? [X5] : (~v5_pre_topc(k4_waybel_1(X0,X5),X0,X0) & m1_subset_1(X5,u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.10/0.98    inference(rectify,[],[f28])).
% 3.10/0.98  
% 3.10/0.98  fof(f44,plain,(
% 3.10/0.98    ! [X0] : (? [X5] : (~v5_pre_topc(k4_waybel_1(X0,X5),X0,X0) & m1_subset_1(X5,u1_struct_0(X0))) => (~v5_pre_topc(k4_waybel_1(X0,sK2(X0)),X0,X0) & m1_subset_1(sK2(X0),u1_struct_0(X0))))),
% 3.10/0.98    introduced(choice_axiom,[])).
% 3.10/0.98  
% 3.10/0.98  fof(f45,plain,(
% 3.10/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r3_orders_2(X0,X3,X4) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_waybel_9(X0,X1,X2) | (~v5_pre_topc(k4_waybel_1(X0,sK2(X0)),X0,X0) & m1_subset_1(sK2(X0),u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.10/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f43,f44])).
% 3.10/0.98  
% 3.10/0.98  fof(f76,plain,(
% 3.10/0.98    ( ! [X4,X2,X0,X3,X1] : (r3_orders_2(X0,X3,X4) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X2) | ~v5_pre_topc(k4_waybel_1(X0,sK2(X0)),X0,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.10/0.98    inference(cnf_transformation,[],[f45])).
% 3.10/0.98  
% 3.10/0.98  fof(f106,plain,(
% 3.10/0.98    ( ! [X4,X0,X3,X1] : (r3_orders_2(X0,X3,X4) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X3) | ~v5_pre_topc(k4_waybel_1(X0,sK2(X0)),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.10/0.98    inference(equality_resolution,[],[f76])).
% 3.10/0.98  
% 3.10/0.98  fof(f95,plain,(
% 3.10/0.98    ( ! [X2] : (v5_pre_topc(k4_waybel_1(sK7,X2),sK7,sK7) | ~m1_subset_1(X2,u1_struct_0(sK7))) )),
% 3.10/0.98    inference(cnf_transformation,[],[f57])).
% 3.10/0.98  
% 3.10/0.98  fof(f88,plain,(
% 3.10/0.98    v3_orders_2(sK7)),
% 3.10/0.98    inference(cnf_transformation,[],[f57])).
% 3.10/0.98  
% 3.10/0.98  fof(f89,plain,(
% 3.10/0.98    v4_orders_2(sK7)),
% 3.10/0.98    inference(cnf_transformation,[],[f57])).
% 3.10/0.98  
% 3.10/0.98  fof(f92,plain,(
% 3.10/0.98    v2_lattice3(sK7)),
% 3.10/0.98    inference(cnf_transformation,[],[f57])).
% 3.10/0.98  
% 3.10/0.98  fof(f75,plain,(
% 3.10/0.98    ( ! [X4,X2,X0,X3,X1] : (r3_orders_2(X0,X3,X4) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X2) | m1_subset_1(sK2(X0),u1_struct_0(X0)) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.10/0.98    inference(cnf_transformation,[],[f45])).
% 3.10/0.98  
% 3.10/0.98  fof(f107,plain,(
% 3.10/0.98    ( ! [X4,X0,X3,X1] : (r3_orders_2(X0,X3,X4) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X3) | m1_subset_1(sK2(X0),u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.10/0.98    inference(equality_resolution,[],[f75])).
% 3.10/0.98  
% 3.10/0.98  fof(f66,plain,(
% 3.10/0.98    ( ! [X2,X0,X1] : (r1_yellow_0(X0,X2) | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) | ~r2_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 3.10/0.98    inference(cnf_transformation,[],[f39])).
% 3.10/0.98  
% 3.10/0.98  fof(f68,plain,(
% 3.10/0.98    ( ! [X2,X0,X1] : (r1_yellow_0(X0,X2) | ~r1_orders_2(X0,X1,sK0(X0,X1,X2)) | ~r2_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 3.10/0.98    inference(cnf_transformation,[],[f39])).
% 3.10/0.98  
% 3.10/0.98  fof(f100,plain,(
% 3.10/0.98    v10_waybel_0(sK8,sK7)),
% 3.10/0.98    inference(cnf_transformation,[],[f57])).
% 3.10/0.98  
% 3.10/0.98  fof(f6,axiom,(
% 3.10/0.98    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X2) & v10_waybel_0(X1,X0) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)) & X2 = X3) => r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3))))))),
% 3.10/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/0.98  
% 3.10/0.98  fof(f25,plain,(
% 3.10/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | (~r3_waybel_9(X0,X1,X2) | ~v10_waybel_0(X1,X0) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.10/0.98    inference(ennf_transformation,[],[f6])).
% 3.10/0.98  
% 3.10/0.98  fof(f26,plain,(
% 3.10/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X2) | ~v10_waybel_0(X1,X0) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.10/0.98    inference(flattening,[],[f25])).
% 3.10/0.98  
% 3.10/0.98  fof(f41,plain,(
% 3.10/0.98    ! [X0] : (? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) => (~v5_pre_topc(k4_waybel_1(X0,sK1(X0)),X0,X0) & m1_subset_1(sK1(X0),u1_struct_0(X0))))),
% 3.10/0.98    introduced(choice_axiom,[])).
% 3.10/0.98  
% 3.10/0.98  fof(f42,plain,(
% 3.10/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X2) | ~v10_waybel_0(X1,X0) | (~v5_pre_topc(k4_waybel_1(X0,sK1(X0)),X0,X0) & m1_subset_1(sK1(X0),u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.10/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f41])).
% 3.10/0.98  
% 3.10/0.98  fof(f73,plain,(
% 3.10/0.98    ( ! [X2,X0,X3,X1] : (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X2) | ~v10_waybel_0(X1,X0) | m1_subset_1(sK1(X0),u1_struct_0(X0)) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.10/0.98    inference(cnf_transformation,[],[f42])).
% 3.10/0.98  
% 3.10/0.98  fof(f105,plain,(
% 3.10/0.98    ( ! [X0,X3,X1] : (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X3) | ~v10_waybel_0(X1,X0) | m1_subset_1(sK1(X0),u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.10/0.98    inference(equality_resolution,[],[f73])).
% 3.10/0.98  
% 3.10/0.98  fof(f74,plain,(
% 3.10/0.98    ( ! [X2,X0,X3,X1] : (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X2) | ~v10_waybel_0(X1,X0) | ~v5_pre_topc(k4_waybel_1(X0,sK1(X0)),X0,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.10/0.98    inference(cnf_transformation,[],[f42])).
% 3.10/0.98  
% 3.10/0.98  fof(f104,plain,(
% 3.10/0.98    ( ! [X0,X3,X1] : (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X3) | ~v10_waybel_0(X1,X0) | ~v5_pre_topc(k4_waybel_1(X0,sK1(X0)),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.10/0.98    inference(equality_resolution,[],[f74])).
% 3.10/0.98  
% 3.10/0.98  fof(f77,plain,(
% 3.10/0.98    ( ! [X0,X1] : (m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.10/0.98    inference(cnf_transformation,[],[f47])).
% 3.10/0.98  
% 3.10/0.98  fof(f9,axiom,(
% 3.10/0.98    ! [X0] : ((l1_pre_topc(X0) & v1_compts_1(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X3) & r3_waybel_9(X0,X1,X2)) => X2 = X3))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,X1,X2) => r2_hidden(X2,k10_yellow_6(X0,X1)))))))),
% 3.10/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/0.98  
% 3.10/0.98  fof(f15,plain,(
% 3.10/0.98    ! [X0] : ((l1_pre_topc(X0) & v1_compts_1(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X3) & r3_waybel_9(X0,X1,X2)) => X2 = X3))) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r3_waybel_9(X0,X1,X4) => r2_hidden(X4,k10_yellow_6(X0,X1)))))))),
% 3.10/0.98    inference(rectify,[],[f9])).
% 3.10/0.98  
% 3.10/0.98  fof(f31,plain,(
% 3.10/0.98    ! [X0] : (! [X1] : ((! [X4] : ((r2_hidden(X4,k10_yellow_6(X0,X1)) | ~r3_waybel_9(X0,X1,X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) | ? [X2] : (? [X3] : ((X2 != X3 & (r3_waybel_9(X0,X1,X3) & r3_waybel_9(X0,X1,X2))) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.10/0.98    inference(ennf_transformation,[],[f15])).
% 3.10/0.98  
% 3.10/0.98  fof(f32,plain,(
% 3.10/0.98    ! [X0] : (! [X1] : (! [X4] : (r2_hidden(X4,k10_yellow_6(X0,X1)) | ~r3_waybel_9(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ? [X2] : (? [X3] : (X2 != X3 & r3_waybel_9(X0,X1,X3) & r3_waybel_9(X0,X1,X2) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.10/0.98    inference(flattening,[],[f31])).
% 3.10/0.98  
% 3.10/0.98  fof(f48,plain,(
% 3.10/0.98    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,k10_yellow_6(X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ? [X3] : (? [X4] : (X3 != X4 & r3_waybel_9(X0,X1,X4) & r3_waybel_9(X0,X1,X3) & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.10/0.98    inference(rectify,[],[f32])).
% 3.10/0.98  
% 3.10/0.98  fof(f50,plain,(
% 3.10/0.98    ( ! [X3] : (! [X1,X0] : (? [X4] : (X3 != X4 & r3_waybel_9(X0,X1,X4) & r3_waybel_9(X0,X1,X3) & m1_subset_1(X4,u1_struct_0(X0))) => (sK5(X0,X1) != X3 & r3_waybel_9(X0,X1,sK5(X0,X1)) & r3_waybel_9(X0,X1,X3) & m1_subset_1(sK5(X0,X1),u1_struct_0(X0))))) )),
% 3.10/0.98    introduced(choice_axiom,[])).
% 3.10/0.98  
% 3.10/0.98  fof(f49,plain,(
% 3.10/0.98    ! [X1,X0] : (? [X3] : (? [X4] : (X3 != X4 & r3_waybel_9(X0,X1,X4) & r3_waybel_9(X0,X1,X3) & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0))) => (? [X4] : (sK4(X0,X1) != X4 & r3_waybel_9(X0,X1,X4) & r3_waybel_9(X0,X1,sK4(X0,X1)) & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(sK4(X0,X1),u1_struct_0(X0))))),
% 3.10/0.98    introduced(choice_axiom,[])).
% 3.10/0.98  
% 3.10/0.98  fof(f51,plain,(
% 3.10/0.98    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,k10_yellow_6(X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ((sK4(X0,X1) != sK5(X0,X1) & r3_waybel_9(X0,X1,sK5(X0,X1)) & r3_waybel_9(X0,X1,sK4(X0,X1)) & m1_subset_1(sK5(X0,X1),u1_struct_0(X0))) & m1_subset_1(sK4(X0,X1),u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.10/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f48,f50,f49])).
% 3.10/0.98  
% 3.10/0.98  fof(f81,plain,(
% 3.10/0.98    ( ! [X2,X0,X1] : (r2_hidden(X2,k10_yellow_6(X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | r3_waybel_9(X0,X1,sK4(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.10/0.98    inference(cnf_transformation,[],[f51])).
% 3.10/0.98  
% 3.10/0.98  fof(f4,axiom,(
% 3.10/0.98    ! [X0] : (l1_orders_2(X0) => ! [X1] : (l1_waybel_0(X1,X0) => (r1_waybel_9(X0,X1) <=> r1_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))))))),
% 3.10/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/0.98  
% 3.10/0.98  fof(f23,plain,(
% 3.10/0.98    ! [X0] : (! [X1] : ((r1_waybel_9(X0,X1) <=> r1_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))) | ~l1_waybel_0(X1,X0)) | ~l1_orders_2(X0))),
% 3.10/0.98    inference(ennf_transformation,[],[f4])).
% 3.10/0.98  
% 3.10/0.98  fof(f40,plain,(
% 3.10/0.98    ! [X0] : (! [X1] : (((r1_waybel_9(X0,X1) | ~r1_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))) & (r1_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) | ~r1_waybel_9(X0,X1))) | ~l1_waybel_0(X1,X0)) | ~l1_orders_2(X0))),
% 3.10/0.98    inference(nnf_transformation,[],[f23])).
% 3.10/0.98  
% 3.10/0.98  fof(f70,plain,(
% 3.10/0.98    ( ! [X0,X1] : (r1_waybel_9(X0,X1) | ~r1_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) | ~l1_waybel_0(X1,X0) | ~l1_orders_2(X0)) )),
% 3.10/0.98    inference(cnf_transformation,[],[f40])).
% 3.10/0.98  
% 3.10/0.98  fof(f101,plain,(
% 3.10/0.98    ~r2_hidden(k1_waybel_2(sK7,sK8),k10_yellow_6(sK7,sK8)) | ~r1_waybel_9(sK7,sK8)),
% 3.10/0.98    inference(cnf_transformation,[],[f57])).
% 3.10/0.98  
% 3.10/0.98  fof(f10,axiom,(
% 3.10/0.98    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => ((r3_waybel_9(X0,X2,X1) & v10_waybel_0(X2,X0) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X3),X0,X0))) => k1_waybel_2(X0,X2) = X1))))),
% 3.10/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/0.98  
% 3.10/0.98  fof(f33,plain,(
% 3.10/0.98    ! [X0] : (! [X1] : (! [X2] : ((k1_waybel_2(X0,X2) = X1 | (~r3_waybel_9(X0,X2,X1) | ~v10_waybel_0(X2,X0) | ? [X3] : (~v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) & m1_subset_1(X3,u1_struct_0(X0))))) | (~l1_waybel_0(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.10/0.98    inference(ennf_transformation,[],[f10])).
% 3.10/0.98  
% 3.10/0.98  fof(f34,plain,(
% 3.10/0.98    ! [X0] : (! [X1] : (! [X2] : (k1_waybel_2(X0,X2) = X1 | ~r3_waybel_9(X0,X2,X1) | ~v10_waybel_0(X2,X0) | ? [X3] : (~v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) & m1_subset_1(X3,u1_struct_0(X0))) | ~l1_waybel_0(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.10/0.98    inference(flattening,[],[f33])).
% 3.10/0.98  
% 3.10/0.98  fof(f52,plain,(
% 3.10/0.98    ! [X0] : (? [X3] : (~v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) & m1_subset_1(X3,u1_struct_0(X0))) => (~v5_pre_topc(k4_waybel_1(X0,sK6(X0)),X0,X0) & m1_subset_1(sK6(X0),u1_struct_0(X0))))),
% 3.10/0.98    introduced(choice_axiom,[])).
% 3.10/0.98  
% 3.10/0.98  fof(f53,plain,(
% 3.10/0.98    ! [X0] : (! [X1] : (! [X2] : (k1_waybel_2(X0,X2) = X1 | ~r3_waybel_9(X0,X2,X1) | ~v10_waybel_0(X2,X0) | (~v5_pre_topc(k4_waybel_1(X0,sK6(X0)),X0,X0) & m1_subset_1(sK6(X0),u1_struct_0(X0))) | ~l1_waybel_0(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.10/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f34,f52])).
% 3.10/0.98  
% 3.10/0.98  fof(f85,plain,(
% 3.10/0.98    ( ! [X2,X0,X1] : (k1_waybel_2(X0,X2) = X1 | ~r3_waybel_9(X0,X2,X1) | ~v10_waybel_0(X2,X0) | ~v5_pre_topc(k4_waybel_1(X0,sK6(X0)),X0,X0) | ~l1_waybel_0(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.10/0.98    inference(cnf_transformation,[],[f53])).
% 3.10/0.98  
% 3.10/0.98  fof(f84,plain,(
% 3.10/0.98    ( ! [X2,X0,X1] : (k1_waybel_2(X0,X2) = X1 | ~r3_waybel_9(X0,X2,X1) | ~v10_waybel_0(X2,X0) | m1_subset_1(sK6(X0),u1_struct_0(X0)) | ~l1_waybel_0(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.10/0.98    inference(cnf_transformation,[],[f53])).
% 3.10/0.98  
% 3.10/0.98  fof(f79,plain,(
% 3.10/0.98    ( ! [X2,X0,X1] : (r2_hidden(X2,k10_yellow_6(X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.10/0.98    inference(cnf_transformation,[],[f51])).
% 3.10/0.98  
% 3.10/0.98  fof(f83,plain,(
% 3.10/0.98    ( ! [X2,X0,X1] : (r2_hidden(X2,k10_yellow_6(X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | sK4(X0,X1) != sK5(X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.10/0.98    inference(cnf_transformation,[],[f51])).
% 3.10/0.98  
% 3.10/0.98  fof(f82,plain,(
% 3.10/0.98    ( ! [X2,X0,X1] : (r2_hidden(X2,k10_yellow_6(X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | r3_waybel_9(X0,X1,sK5(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.10/0.98    inference(cnf_transformation,[],[f51])).
% 3.10/0.98  
% 3.10/0.98  fof(f80,plain,(
% 3.10/0.98    ( ! [X2,X0,X1] : (r2_hidden(X2,k10_yellow_6(X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | m1_subset_1(sK5(X0,X1),u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.10/0.98    inference(cnf_transformation,[],[f51])).
% 3.10/0.98  
% 3.10/0.98  cnf(c_30,negated_conjecture,
% 3.10/0.98      ( l1_waybel_0(sK8,sK7) ),
% 3.10/0.98      inference(cnf_transformation,[],[f99]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_19,plain,
% 3.10/0.98      ( r3_waybel_9(X0,X1,sK3(X0,X1))
% 3.10/0.98      | ~ l1_waybel_0(X1,X0)
% 3.10/0.98      | ~ v2_pre_topc(X0)
% 3.10/0.98      | ~ v8_pre_topc(X0)
% 3.10/0.98      | ~ v1_compts_1(X0)
% 3.10/0.98      | ~ v4_orders_2(X1)
% 3.10/0.98      | ~ v7_waybel_0(X1)
% 3.10/0.98      | ~ l1_pre_topc(X0)
% 3.10/0.98      | v2_struct_0(X0)
% 3.10/0.98      | v2_struct_0(X1) ),
% 3.10/0.98      inference(cnf_transformation,[],[f78]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_14,plain,
% 3.10/0.98      ( l1_pre_topc(X0) | ~ l1_waybel_9(X0) ),
% 3.10/0.98      inference(cnf_transformation,[],[f71]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_35,negated_conjecture,
% 3.10/0.98      ( l1_waybel_9(sK7) ),
% 3.10/0.98      inference(cnf_transformation,[],[f94]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_1552,plain,
% 3.10/0.98      ( l1_pre_topc(X0) | sK7 != X0 ),
% 3.10/0.98      inference(resolution_lifted,[status(thm)],[c_14,c_35]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_1553,plain,
% 3.10/0.98      ( l1_pre_topc(sK7) ),
% 3.10/0.98      inference(unflattening,[status(thm)],[c_1552]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_2489,plain,
% 3.10/0.98      ( r3_waybel_9(X0,X1,sK3(X0,X1))
% 3.10/0.98      | ~ l1_waybel_0(X1,X0)
% 3.10/0.98      | ~ v2_pre_topc(X0)
% 3.10/0.98      | ~ v8_pre_topc(X0)
% 3.10/0.98      | ~ v1_compts_1(X0)
% 3.10/0.98      | ~ v4_orders_2(X1)
% 3.10/0.98      | ~ v7_waybel_0(X1)
% 3.10/0.98      | v2_struct_0(X0)
% 3.10/0.98      | v2_struct_0(X1)
% 3.10/0.98      | sK7 != X0 ),
% 3.10/0.98      inference(resolution_lifted,[status(thm)],[c_19,c_1553]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_2490,plain,
% 3.10/0.98      ( r3_waybel_9(sK7,X0,sK3(sK7,X0))
% 3.10/0.98      | ~ l1_waybel_0(X0,sK7)
% 3.10/0.98      | ~ v2_pre_topc(sK7)
% 3.10/0.98      | ~ v8_pre_topc(sK7)
% 3.10/0.98      | ~ v1_compts_1(sK7)
% 3.10/0.98      | ~ v4_orders_2(X0)
% 3.10/0.98      | ~ v7_waybel_0(X0)
% 3.10/0.98      | v2_struct_0(X0)
% 3.10/0.98      | v2_struct_0(sK7) ),
% 3.10/0.98      inference(unflattening,[status(thm)],[c_2489]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_43,negated_conjecture,
% 3.10/0.98      ( v2_pre_topc(sK7) ),
% 3.10/0.98      inference(cnf_transformation,[],[f86]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_42,negated_conjecture,
% 3.10/0.98      ( v8_pre_topc(sK7) ),
% 3.10/0.98      inference(cnf_transformation,[],[f87]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_38,negated_conjecture,
% 3.10/0.98      ( v1_lattice3(sK7) ),
% 3.10/0.98      inference(cnf_transformation,[],[f91]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_36,negated_conjecture,
% 3.10/0.98      ( v1_compts_1(sK7) ),
% 3.10/0.98      inference(cnf_transformation,[],[f93]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_13,plain,
% 3.10/0.98      ( ~ l1_waybel_9(X0) | l1_orders_2(X0) ),
% 3.10/0.98      inference(cnf_transformation,[],[f72]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_105,plain,
% 3.10/0.98      ( ~ l1_waybel_9(sK7) | l1_orders_2(sK7) ),
% 3.10/0.98      inference(instantiation,[status(thm)],[c_13]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_2,plain,
% 3.10/0.98      ( ~ v1_lattice3(X0) | ~ v2_struct_0(X0) | ~ l1_orders_2(X0) ),
% 3.10/0.98      inference(cnf_transformation,[],[f60]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_138,plain,
% 3.10/0.98      ( ~ v1_lattice3(sK7) | ~ v2_struct_0(sK7) | ~ l1_orders_2(sK7) ),
% 3.10/0.98      inference(instantiation,[status(thm)],[c_2]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_2494,plain,
% 3.10/0.98      ( v2_struct_0(X0)
% 3.10/0.98      | ~ v7_waybel_0(X0)
% 3.10/0.98      | ~ v4_orders_2(X0)
% 3.10/0.98      | r3_waybel_9(sK7,X0,sK3(sK7,X0))
% 3.10/0.98      | ~ l1_waybel_0(X0,sK7) ),
% 3.10/0.98      inference(global_propositional_subsumption,
% 3.10/0.98                [status(thm)],
% 3.10/0.98                [c_2490,c_43,c_42,c_38,c_36,c_35,c_105,c_138]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_2495,plain,
% 3.10/0.98      ( r3_waybel_9(sK7,X0,sK3(sK7,X0))
% 3.10/0.98      | ~ l1_waybel_0(X0,sK7)
% 3.10/0.98      | ~ v4_orders_2(X0)
% 3.10/0.98      | ~ v7_waybel_0(X0)
% 3.10/0.98      | v2_struct_0(X0) ),
% 3.10/0.98      inference(renaming,[status(thm)],[c_2494]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_2616,plain,
% 3.10/0.98      ( r3_waybel_9(sK7,X0,sK3(sK7,X0))
% 3.10/0.98      | ~ v4_orders_2(X0)
% 3.10/0.98      | ~ v7_waybel_0(X0)
% 3.10/0.98      | v2_struct_0(X0)
% 3.10/0.98      | sK8 != X0
% 3.10/0.98      | sK7 != sK7 ),
% 3.10/0.98      inference(resolution_lifted,[status(thm)],[c_30,c_2495]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_2617,plain,
% 3.10/0.98      ( r3_waybel_9(sK7,sK8,sK3(sK7,sK8))
% 3.10/0.98      | ~ v4_orders_2(sK8)
% 3.10/0.98      | ~ v7_waybel_0(sK8)
% 3.10/0.98      | v2_struct_0(sK8) ),
% 3.10/0.98      inference(unflattening,[status(thm)],[c_2616]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_33,negated_conjecture,
% 3.10/0.98      ( ~ v2_struct_0(sK8) ),
% 3.10/0.98      inference(cnf_transformation,[],[f96]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_32,negated_conjecture,
% 3.10/0.98      ( v4_orders_2(sK8) ),
% 3.10/0.98      inference(cnf_transformation,[],[f97]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_31,negated_conjecture,
% 3.10/0.98      ( v7_waybel_0(sK8) ),
% 3.10/0.98      inference(cnf_transformation,[],[f98]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_2619,plain,
% 3.10/0.98      ( r3_waybel_9(sK7,sK8,sK3(sK7,sK8)) ),
% 3.10/0.98      inference(global_propositional_subsumption,
% 3.10/0.98                [status(thm)],
% 3.10/0.98                [c_2617,c_33,c_32,c_31]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_4603,plain,
% 3.10/0.98      ( r3_waybel_9(sK7,sK8,sK3(sK7,sK8)) ),
% 3.10/0.98      inference(subtyping,[status(esa)],[c_2619]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_5131,plain,
% 3.10/0.98      ( r3_waybel_9(sK7,sK8,sK3(sK7,sK8)) = iProver_top ),
% 3.10/0.98      inference(predicate_to_equality,[status(thm)],[c_4603]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_4,plain,
% 3.10/0.98      ( ~ r2_lattice3(X0,X1,X2)
% 3.10/0.98      | r2_lattice3(X0,X1,sK0(X0,X2,X1))
% 3.10/0.98      | r1_yellow_0(X0,X1)
% 3.10/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.10/0.98      | ~ v5_orders_2(X0)
% 3.10/0.98      | ~ l1_orders_2(X0) ),
% 3.10/0.98      inference(cnf_transformation,[],[f67]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_912,plain,
% 3.10/0.98      ( ~ r2_lattice3(X0,X1,X2)
% 3.10/0.98      | r2_lattice3(X0,X1,sK0(X0,X2,X1))
% 3.10/0.98      | r1_yellow_0(X0,X1)
% 3.10/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.10/0.98      | ~ l1_waybel_9(X0)
% 3.10/0.98      | ~ v5_orders_2(X0) ),
% 3.10/0.98      inference(resolution,[status(thm)],[c_13,c_4]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_39,negated_conjecture,
% 3.10/0.98      ( v5_orders_2(sK7) ),
% 3.10/0.98      inference(cnf_transformation,[],[f90]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_1344,plain,
% 3.10/0.98      ( ~ r2_lattice3(X0,X1,X2)
% 3.10/0.98      | r2_lattice3(X0,X1,sK0(X0,X2,X1))
% 3.10/0.98      | r1_yellow_0(X0,X1)
% 3.10/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.10/0.98      | ~ l1_waybel_9(X0)
% 3.10/0.98      | sK7 != X0 ),
% 3.10/0.98      inference(resolution_lifted,[status(thm)],[c_912,c_39]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_1345,plain,
% 3.10/0.98      ( ~ r2_lattice3(sK7,X0,X1)
% 3.10/0.98      | r2_lattice3(sK7,X0,sK0(sK7,X1,X0))
% 3.10/0.98      | r1_yellow_0(sK7,X0)
% 3.10/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.10/0.98      | ~ l1_waybel_9(sK7) ),
% 3.10/0.98      inference(unflattening,[status(thm)],[c_1344]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_1349,plain,
% 3.10/0.98      ( ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.10/0.98      | r1_yellow_0(sK7,X0)
% 3.10/0.98      | r2_lattice3(sK7,X0,sK0(sK7,X1,X0))
% 3.10/0.98      | ~ r2_lattice3(sK7,X0,X1) ),
% 3.10/0.98      inference(global_propositional_subsumption,
% 3.10/0.98                [status(thm)],
% 3.10/0.98                [c_1345,c_35]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_1350,plain,
% 3.10/0.98      ( ~ r2_lattice3(sK7,X0,X1)
% 3.10/0.98      | r2_lattice3(sK7,X0,sK0(sK7,X1,X0))
% 3.10/0.98      | r1_yellow_0(sK7,X0)
% 3.10/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK7)) ),
% 3.10/0.98      inference(renaming,[status(thm)],[c_1349]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_4611,plain,
% 3.10/0.98      ( ~ r2_lattice3(sK7,X0_70,X0_69)
% 3.10/0.98      | r2_lattice3(sK7,X0_70,sK0(sK7,X0_69,X0_70))
% 3.10/0.98      | r1_yellow_0(sK7,X0_70)
% 3.10/0.98      | ~ m1_subset_1(X0_69,u1_struct_0(sK7)) ),
% 3.10/0.98      inference(subtyping,[status(esa)],[c_1350]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_5123,plain,
% 3.10/0.98      ( r2_lattice3(sK7,X0_70,X0_69) != iProver_top
% 3.10/0.98      | r2_lattice3(sK7,X0_70,sK0(sK7,X0_69,X0_70)) = iProver_top
% 3.10/0.98      | r1_yellow_0(sK7,X0_70) = iProver_top
% 3.10/0.98      | m1_subset_1(X0_69,u1_struct_0(sK7)) != iProver_top ),
% 3.10/0.98      inference(predicate_to_equality,[status(thm)],[c_4611]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_1,plain,
% 3.10/0.98      ( r1_orders_2(X0,X1,X2)
% 3.10/0.98      | ~ r3_orders_2(X0,X1,X2)
% 3.10/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.10/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.10/0.98      | v2_struct_0(X0)
% 3.10/0.98      | ~ v3_orders_2(X0)
% 3.10/0.98      | ~ l1_orders_2(X0) ),
% 3.10/0.98      inference(cnf_transformation,[],[f58]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_17,plain,
% 3.10/0.98      ( ~ v5_pre_topc(k4_waybel_1(X0,sK2(X0)),X0,X0)
% 3.10/0.98      | ~ r3_waybel_9(X0,X1,X2)
% 3.10/0.98      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
% 3.10/0.98      | r3_orders_2(X0,X2,X3)
% 3.10/0.98      | ~ l1_waybel_0(X1,X0)
% 3.10/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.10/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.10/0.98      | ~ v2_pre_topc(X0)
% 3.10/0.98      | ~ v8_pre_topc(X0)
% 3.10/0.98      | ~ v2_lattice3(X0)
% 3.10/0.98      | ~ v1_compts_1(X0)
% 3.10/0.98      | ~ v4_orders_2(X1)
% 3.10/0.98      | ~ v4_orders_2(X0)
% 3.10/0.98      | ~ v7_waybel_0(X1)
% 3.10/0.98      | ~ l1_waybel_9(X0)
% 3.10/0.98      | ~ v5_orders_2(X0)
% 3.10/0.98      | ~ v1_lattice3(X0)
% 3.10/0.98      | v2_struct_0(X1)
% 3.10/0.98      | ~ v3_orders_2(X0) ),
% 3.10/0.98      inference(cnf_transformation,[],[f106]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_34,negated_conjecture,
% 3.10/0.98      ( v5_pre_topc(k4_waybel_1(sK7,X0),sK7,sK7)
% 3.10/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK7)) ),
% 3.10/0.98      inference(cnf_transformation,[],[f95]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_547,plain,
% 3.10/0.98      ( ~ r3_waybel_9(X0,X1,X2)
% 3.10/0.98      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
% 3.10/0.98      | r3_orders_2(X0,X2,X3)
% 3.10/0.98      | ~ l1_waybel_0(X1,X0)
% 3.10/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.10/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.10/0.98      | ~ m1_subset_1(X4,u1_struct_0(sK7))
% 3.10/0.98      | ~ v2_pre_topc(X0)
% 3.10/0.98      | ~ v8_pre_topc(X0)
% 3.10/0.98      | ~ v2_lattice3(X0)
% 3.10/0.98      | ~ v1_compts_1(X0)
% 3.10/0.98      | ~ v4_orders_2(X1)
% 3.10/0.98      | ~ v4_orders_2(X0)
% 3.10/0.98      | ~ v7_waybel_0(X1)
% 3.10/0.98      | ~ l1_waybel_9(X0)
% 3.10/0.98      | ~ v5_orders_2(X0)
% 3.10/0.98      | ~ v1_lattice3(X0)
% 3.10/0.98      | v2_struct_0(X1)
% 3.10/0.98      | ~ v3_orders_2(X0)
% 3.10/0.98      | k4_waybel_1(X0,sK2(X0)) != k4_waybel_1(sK7,X4)
% 3.10/0.98      | sK7 != X0 ),
% 3.10/0.98      inference(resolution_lifted,[status(thm)],[c_17,c_34]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_548,plain,
% 3.10/0.98      ( ~ r3_waybel_9(sK7,X0,X1)
% 3.10/0.98      | ~ r2_lattice3(sK7,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK7),u1_waybel_0(sK7,X0)),X2)
% 3.10/0.98      | r3_orders_2(sK7,X1,X2)
% 3.10/0.98      | ~ l1_waybel_0(X0,sK7)
% 3.10/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.10/0.98      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 3.10/0.98      | ~ m1_subset_1(X3,u1_struct_0(sK7))
% 3.10/0.98      | ~ v2_pre_topc(sK7)
% 3.10/0.98      | ~ v8_pre_topc(sK7)
% 3.10/0.98      | ~ v2_lattice3(sK7)
% 3.10/0.98      | ~ v1_compts_1(sK7)
% 3.10/0.98      | ~ v4_orders_2(X0)
% 3.10/0.98      | ~ v4_orders_2(sK7)
% 3.10/0.98      | ~ v7_waybel_0(X0)
% 3.10/0.98      | ~ l1_waybel_9(sK7)
% 3.10/0.98      | ~ v5_orders_2(sK7)
% 3.10/0.98      | ~ v1_lattice3(sK7)
% 3.10/0.98      | v2_struct_0(X0)
% 3.10/0.98      | ~ v3_orders_2(sK7)
% 3.10/0.98      | k4_waybel_1(sK7,sK2(sK7)) != k4_waybel_1(sK7,X3) ),
% 3.10/0.98      inference(unflattening,[status(thm)],[c_547]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_41,negated_conjecture,
% 3.10/0.98      ( v3_orders_2(sK7) ),
% 3.10/0.98      inference(cnf_transformation,[],[f88]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_40,negated_conjecture,
% 3.10/0.98      ( v4_orders_2(sK7) ),
% 3.10/0.98      inference(cnf_transformation,[],[f89]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_37,negated_conjecture,
% 3.10/0.98      ( v2_lattice3(sK7) ),
% 3.10/0.98      inference(cnf_transformation,[],[f92]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_552,plain,
% 3.10/0.98      ( v2_struct_0(X0)
% 3.10/0.98      | ~ v4_orders_2(X0)
% 3.10/0.98      | ~ m1_subset_1(X3,u1_struct_0(sK7))
% 3.10/0.98      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 3.10/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.10/0.98      | ~ l1_waybel_0(X0,sK7)
% 3.10/0.98      | r3_orders_2(sK7,X1,X2)
% 3.10/0.98      | ~ r2_lattice3(sK7,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK7),u1_waybel_0(sK7,X0)),X2)
% 3.10/0.98      | ~ r3_waybel_9(sK7,X0,X1)
% 3.10/0.98      | ~ v7_waybel_0(X0)
% 3.10/0.98      | k4_waybel_1(sK7,sK2(sK7)) != k4_waybel_1(sK7,X3) ),
% 3.10/0.98      inference(global_propositional_subsumption,
% 3.10/0.98                [status(thm)],
% 3.10/0.98                [c_548,c_43,c_42,c_41,c_40,c_39,c_38,c_37,c_36,c_35]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_553,plain,
% 3.10/0.98      ( ~ r3_waybel_9(sK7,X0,X1)
% 3.10/0.98      | ~ r2_lattice3(sK7,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK7),u1_waybel_0(sK7,X0)),X2)
% 3.10/0.98      | r3_orders_2(sK7,X1,X2)
% 3.10/0.98      | ~ l1_waybel_0(X0,sK7)
% 3.10/0.98      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 3.10/0.98      | ~ m1_subset_1(X3,u1_struct_0(sK7))
% 3.10/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.10/0.98      | ~ v4_orders_2(X0)
% 3.10/0.98      | ~ v7_waybel_0(X0)
% 3.10/0.98      | v2_struct_0(X0)
% 3.10/0.98      | k4_waybel_1(sK7,sK2(sK7)) != k4_waybel_1(sK7,X3) ),
% 3.10/0.98      inference(renaming,[status(thm)],[c_552]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_727,plain,
% 3.10/0.98      ( ~ r3_waybel_9(sK7,X0,X1)
% 3.10/0.98      | ~ r2_lattice3(sK7,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK7),u1_waybel_0(sK7,X0)),X2)
% 3.10/0.98      | r1_orders_2(X3,X4,X5)
% 3.10/0.98      | ~ l1_waybel_0(X0,sK7)
% 3.10/0.98      | ~ m1_subset_1(X5,u1_struct_0(X3))
% 3.10/0.98      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.10/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.10/0.98      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 3.10/0.98      | ~ m1_subset_1(X6,u1_struct_0(sK7))
% 3.10/0.98      | ~ v4_orders_2(X0)
% 3.10/0.98      | ~ v7_waybel_0(X0)
% 3.10/0.98      | v2_struct_0(X3)
% 3.10/0.98      | v2_struct_0(X0)
% 3.10/0.98      | ~ v3_orders_2(X3)
% 3.10/0.98      | ~ l1_orders_2(X3)
% 3.10/0.98      | X1 != X4
% 3.10/0.98      | X2 != X5
% 3.10/0.98      | k4_waybel_1(sK7,sK2(sK7)) != k4_waybel_1(sK7,X6)
% 3.10/0.98      | sK7 != X3 ),
% 3.10/0.98      inference(resolution_lifted,[status(thm)],[c_1,c_553]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_728,plain,
% 3.10/0.98      ( ~ r3_waybel_9(sK7,X0,X1)
% 3.10/0.98      | ~ r2_lattice3(sK7,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK7),u1_waybel_0(sK7,X0)),X2)
% 3.10/0.98      | r1_orders_2(sK7,X1,X2)
% 3.10/0.98      | ~ l1_waybel_0(X0,sK7)
% 3.10/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.10/0.98      | ~ m1_subset_1(X3,u1_struct_0(sK7))
% 3.10/0.98      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 3.10/0.98      | ~ v4_orders_2(X0)
% 3.10/0.98      | ~ v7_waybel_0(X0)
% 3.10/0.98      | v2_struct_0(X0)
% 3.10/0.98      | v2_struct_0(sK7)
% 3.10/0.98      | ~ v3_orders_2(sK7)
% 3.10/0.98      | ~ l1_orders_2(sK7)
% 3.10/0.98      | k4_waybel_1(sK7,sK2(sK7)) != k4_waybel_1(sK7,X3) ),
% 3.10/0.98      inference(unflattening,[status(thm)],[c_727]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_732,plain,
% 3.10/0.98      ( v2_struct_0(X0)
% 3.10/0.98      | ~ v7_waybel_0(X0)
% 3.10/0.98      | ~ v4_orders_2(X0)
% 3.10/0.98      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 3.10/0.98      | ~ m1_subset_1(X3,u1_struct_0(sK7))
% 3.10/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.10/0.98      | ~ l1_waybel_0(X0,sK7)
% 3.10/0.98      | r1_orders_2(sK7,X1,X2)
% 3.10/0.98      | ~ r2_lattice3(sK7,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK7),u1_waybel_0(sK7,X0)),X2)
% 3.10/0.98      | ~ r3_waybel_9(sK7,X0,X1)
% 3.10/0.98      | k4_waybel_1(sK7,sK2(sK7)) != k4_waybel_1(sK7,X3) ),
% 3.10/0.98      inference(global_propositional_subsumption,
% 3.10/0.98                [status(thm)],
% 3.10/0.98                [c_728,c_41,c_38,c_35,c_105,c_138]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_733,plain,
% 3.10/0.98      ( ~ r3_waybel_9(sK7,X0,X1)
% 3.10/0.98      | ~ r2_lattice3(sK7,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK7),u1_waybel_0(sK7,X0)),X2)
% 3.10/0.98      | r1_orders_2(sK7,X1,X2)
% 3.10/0.98      | ~ l1_waybel_0(X0,sK7)
% 3.10/0.98      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 3.10/0.98      | ~ m1_subset_1(X3,u1_struct_0(sK7))
% 3.10/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.10/0.98      | ~ v4_orders_2(X0)
% 3.10/0.98      | ~ v7_waybel_0(X0)
% 3.10/0.98      | v2_struct_0(X0)
% 3.10/0.98      | k4_waybel_1(sK7,sK2(sK7)) != k4_waybel_1(sK7,X3) ),
% 3.10/0.98      inference(renaming,[status(thm)],[c_732]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_2772,plain,
% 3.10/0.98      ( ~ r3_waybel_9(sK7,X0,X1)
% 3.10/0.98      | ~ r2_lattice3(sK7,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK7),u1_waybel_0(sK7,X0)),X2)
% 3.10/0.98      | r1_orders_2(sK7,X1,X2)
% 3.10/0.98      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 3.10/0.98      | ~ m1_subset_1(X3,u1_struct_0(sK7))
% 3.10/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.10/0.98      | ~ v4_orders_2(X0)
% 3.10/0.98      | ~ v7_waybel_0(X0)
% 3.10/0.98      | v2_struct_0(X0)
% 3.10/0.98      | k4_waybel_1(sK7,sK2(sK7)) != k4_waybel_1(sK7,X3)
% 3.10/0.98      | sK8 != X0
% 3.10/0.98      | sK7 != sK7 ),
% 3.10/0.98      inference(resolution_lifted,[status(thm)],[c_30,c_733]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_2773,plain,
% 3.10/0.98      ( ~ r3_waybel_9(sK7,sK8,X0)
% 3.10/0.98      | ~ r2_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X1)
% 3.10/0.98      | r1_orders_2(sK7,X0,X1)
% 3.10/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.10/0.98      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 3.10/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.10/0.98      | ~ v4_orders_2(sK8)
% 3.10/0.98      | ~ v7_waybel_0(sK8)
% 3.10/0.98      | v2_struct_0(sK8)
% 3.10/0.98      | k4_waybel_1(sK7,sK2(sK7)) != k4_waybel_1(sK7,X2) ),
% 3.10/0.98      inference(unflattening,[status(thm)],[c_2772]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_2777,plain,
% 3.10/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.10/0.98      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 3.10/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.10/0.98      | r1_orders_2(sK7,X0,X1)
% 3.10/0.98      | ~ r2_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X1)
% 3.10/0.98      | ~ r3_waybel_9(sK7,sK8,X0)
% 3.10/0.98      | k4_waybel_1(sK7,sK2(sK7)) != k4_waybel_1(sK7,X2) ),
% 3.10/0.98      inference(global_propositional_subsumption,
% 3.10/0.98                [status(thm)],
% 3.10/0.98                [c_2773,c_33,c_32,c_31]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_2778,plain,
% 3.10/0.98      ( ~ r3_waybel_9(sK7,sK8,X0)
% 3.10/0.98      | ~ r2_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X1)
% 3.10/0.98      | r1_orders_2(sK7,X0,X1)
% 3.10/0.98      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 3.10/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.10/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.10/0.98      | k4_waybel_1(sK7,sK2(sK7)) != k4_waybel_1(sK7,X2) ),
% 3.10/0.98      inference(renaming,[status(thm)],[c_2777]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_4601,plain,
% 3.10/0.98      ( ~ r3_waybel_9(sK7,sK8,X0_69)
% 3.10/0.98      | ~ r2_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X1_69)
% 3.10/0.98      | r1_orders_2(sK7,X0_69,X1_69)
% 3.10/0.98      | ~ m1_subset_1(X2_69,u1_struct_0(sK7))
% 3.10/0.98      | ~ m1_subset_1(X0_69,u1_struct_0(sK7))
% 3.10/0.98      | ~ m1_subset_1(X1_69,u1_struct_0(sK7))
% 3.10/0.98      | k4_waybel_1(sK7,sK2(sK7)) != k4_waybel_1(sK7,X2_69) ),
% 3.10/0.98      inference(subtyping,[status(esa)],[c_2778]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_4624,plain,
% 3.10/0.98      ( ~ r3_waybel_9(sK7,sK8,X0_69)
% 3.10/0.98      | ~ r2_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X1_69)
% 3.10/0.98      | r1_orders_2(sK7,X0_69,X1_69)
% 3.10/0.98      | ~ m1_subset_1(X0_69,u1_struct_0(sK7))
% 3.10/0.98      | ~ m1_subset_1(X1_69,u1_struct_0(sK7))
% 3.10/0.98      | ~ sP5_iProver_split ),
% 3.10/0.98      inference(splitting,
% 3.10/0.98                [splitting(split),new_symbols(definition,[sP5_iProver_split])],
% 3.10/0.98                [c_4601]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_5134,plain,
% 3.10/0.98      ( r3_waybel_9(sK7,sK8,X0_69) != iProver_top
% 3.10/0.98      | r2_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X1_69) != iProver_top
% 3.10/0.98      | r1_orders_2(sK7,X0_69,X1_69) = iProver_top
% 3.10/0.98      | m1_subset_1(X0_69,u1_struct_0(sK7)) != iProver_top
% 3.10/0.98      | m1_subset_1(X1_69,u1_struct_0(sK7)) != iProver_top
% 3.10/0.98      | sP5_iProver_split != iProver_top ),
% 3.10/0.98      inference(predicate_to_equality,[status(thm)],[c_4624]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_18,plain,
% 3.10/0.98      ( ~ r3_waybel_9(X0,X1,X2)
% 3.10/0.98      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
% 3.10/0.98      | r3_orders_2(X0,X2,X3)
% 3.10/0.98      | ~ l1_waybel_0(X1,X0)
% 3.10/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.10/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.10/0.98      | m1_subset_1(sK2(X0),u1_struct_0(X0))
% 3.10/0.98      | ~ v2_pre_topc(X0)
% 3.10/0.98      | ~ v8_pre_topc(X0)
% 3.10/0.98      | ~ v2_lattice3(X0)
% 3.10/0.98      | ~ v1_compts_1(X0)
% 3.10/0.98      | ~ v4_orders_2(X1)
% 3.10/0.98      | ~ v4_orders_2(X0)
% 3.10/0.98      | ~ v7_waybel_0(X1)
% 3.10/0.98      | ~ l1_waybel_9(X0)
% 3.10/0.98      | ~ v5_orders_2(X0)
% 3.10/0.98      | ~ v1_lattice3(X0)
% 3.10/0.98      | v2_struct_0(X1)
% 3.10/0.98      | ~ v3_orders_2(X0) ),
% 3.10/0.98      inference(cnf_transformation,[],[f107]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_658,plain,
% 3.10/0.98      ( ~ r3_waybel_9(X0,X1,X2)
% 3.10/0.98      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
% 3.10/0.98      | r1_orders_2(X4,X5,X6)
% 3.10/0.98      | ~ l1_waybel_0(X1,X0)
% 3.10/0.98      | ~ m1_subset_1(X6,u1_struct_0(X4))
% 3.10/0.98      | ~ m1_subset_1(X5,u1_struct_0(X4))
% 3.10/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.10/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.10/0.98      | m1_subset_1(sK2(X0),u1_struct_0(X0))
% 3.10/0.98      | ~ v2_pre_topc(X0)
% 3.10/0.98      | ~ v8_pre_topc(X0)
% 3.10/0.98      | ~ v2_lattice3(X0)
% 3.10/0.98      | ~ v1_compts_1(X0)
% 3.10/0.98      | ~ v4_orders_2(X1)
% 3.10/0.98      | ~ v4_orders_2(X0)
% 3.10/0.98      | ~ v7_waybel_0(X1)
% 3.10/0.98      | ~ l1_waybel_9(X0)
% 3.10/0.98      | ~ v5_orders_2(X0)
% 3.10/0.98      | ~ v1_lattice3(X0)
% 3.10/0.98      | v2_struct_0(X4)
% 3.10/0.98      | v2_struct_0(X1)
% 3.10/0.98      | ~ v3_orders_2(X4)
% 3.10/0.98      | ~ v3_orders_2(X0)
% 3.10/0.98      | ~ l1_orders_2(X4)
% 3.10/0.98      | X0 != X4
% 3.10/0.98      | X2 != X5
% 3.10/0.98      | X3 != X6 ),
% 3.10/0.98      inference(resolution_lifted,[status(thm)],[c_1,c_18]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_659,plain,
% 3.10/0.98      ( ~ r3_waybel_9(X0,X1,X2)
% 3.10/0.98      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
% 3.10/0.98      | r1_orders_2(X0,X2,X3)
% 3.10/0.98      | ~ l1_waybel_0(X1,X0)
% 3.10/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.10/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.10/0.98      | m1_subset_1(sK2(X0),u1_struct_0(X0))
% 3.10/0.98      | ~ v2_pre_topc(X0)
% 3.10/0.98      | ~ v8_pre_topc(X0)
% 3.10/0.98      | ~ v2_lattice3(X0)
% 3.10/0.98      | ~ v1_compts_1(X0)
% 3.10/0.98      | ~ v4_orders_2(X1)
% 3.10/0.98      | ~ v4_orders_2(X0)
% 3.10/0.98      | ~ v7_waybel_0(X1)
% 3.10/0.98      | ~ l1_waybel_9(X0)
% 3.10/0.98      | ~ v5_orders_2(X0)
% 3.10/0.98      | ~ v1_lattice3(X0)
% 3.10/0.98      | v2_struct_0(X1)
% 3.10/0.98      | v2_struct_0(X0)
% 3.10/0.98      | ~ v3_orders_2(X0)
% 3.10/0.98      | ~ l1_orders_2(X0) ),
% 3.10/0.98      inference(unflattening,[status(thm)],[c_658]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_663,plain,
% 3.10/0.98      ( ~ v3_orders_2(X0)
% 3.10/0.98      | ~ r3_waybel_9(X0,X1,X2)
% 3.10/0.98      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
% 3.10/0.98      | r1_orders_2(X0,X2,X3)
% 3.10/0.98      | ~ l1_waybel_0(X1,X0)
% 3.10/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.10/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.10/0.98      | m1_subset_1(sK2(X0),u1_struct_0(X0))
% 3.10/0.98      | ~ v2_pre_topc(X0)
% 3.10/0.98      | ~ v8_pre_topc(X0)
% 3.10/0.98      | ~ v2_lattice3(X0)
% 3.10/0.98      | ~ v1_compts_1(X0)
% 3.10/0.98      | ~ v4_orders_2(X1)
% 3.10/0.98      | ~ v4_orders_2(X0)
% 3.10/0.98      | ~ v7_waybel_0(X1)
% 3.10/0.98      | ~ l1_waybel_9(X0)
% 3.10/0.98      | ~ v5_orders_2(X0)
% 3.10/0.98      | ~ v1_lattice3(X0)
% 3.10/0.98      | v2_struct_0(X1) ),
% 3.10/0.98      inference(global_propositional_subsumption,
% 3.10/0.98                [status(thm)],
% 3.10/0.98                [c_659,c_13,c_2]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_664,plain,
% 3.10/0.98      ( ~ r3_waybel_9(X0,X1,X2)
% 3.10/0.98      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
% 3.10/0.98      | r1_orders_2(X0,X2,X3)
% 3.10/0.98      | ~ l1_waybel_0(X1,X0)
% 3.10/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.10/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.10/0.98      | m1_subset_1(sK2(X0),u1_struct_0(X0))
% 3.10/0.98      | ~ v2_pre_topc(X0)
% 3.10/0.98      | ~ v8_pre_topc(X0)
% 3.10/0.98      | ~ v2_lattice3(X0)
% 3.10/0.98      | ~ v1_compts_1(X0)
% 3.10/0.98      | ~ v4_orders_2(X1)
% 3.10/0.98      | ~ v4_orders_2(X0)
% 3.10/0.98      | ~ v7_waybel_0(X1)
% 3.10/0.98      | ~ l1_waybel_9(X0)
% 3.10/0.98      | ~ v5_orders_2(X0)
% 3.10/0.98      | ~ v1_lattice3(X0)
% 3.10/0.98      | v2_struct_0(X1)
% 3.10/0.98      | ~ v3_orders_2(X0) ),
% 3.10/0.98      inference(renaming,[status(thm)],[c_663]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_1032,plain,
% 3.10/0.98      ( ~ r3_waybel_9(X0,X1,X2)
% 3.10/0.98      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
% 3.10/0.98      | r1_orders_2(X0,X2,X3)
% 3.10/0.98      | ~ l1_waybel_0(X1,X0)
% 3.10/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.10/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.10/0.98      | m1_subset_1(sK2(X0),u1_struct_0(X0))
% 3.10/0.98      | ~ v2_pre_topc(X0)
% 3.10/0.98      | ~ v8_pre_topc(X0)
% 3.10/0.98      | ~ v2_lattice3(X0)
% 3.10/0.98      | ~ v1_compts_1(X0)
% 3.10/0.98      | ~ v4_orders_2(X1)
% 3.10/0.98      | ~ v4_orders_2(X0)
% 3.10/0.98      | ~ v7_waybel_0(X1)
% 3.10/0.98      | ~ l1_waybel_9(X0)
% 3.10/0.98      | ~ v5_orders_2(X0)
% 3.10/0.98      | ~ v1_lattice3(X0)
% 3.10/0.98      | v2_struct_0(X1)
% 3.10/0.98      | sK7 != X0 ),
% 3.10/0.98      inference(resolution_lifted,[status(thm)],[c_664,c_41]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_1033,plain,
% 3.10/0.98      ( ~ r3_waybel_9(sK7,X0,X1)
% 3.10/0.98      | ~ r2_lattice3(sK7,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK7),u1_waybel_0(sK7,X0)),X2)
% 3.10/0.98      | r1_orders_2(sK7,X1,X2)
% 3.10/0.98      | ~ l1_waybel_0(X0,sK7)
% 3.10/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.10/0.98      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 3.10/0.98      | m1_subset_1(sK2(sK7),u1_struct_0(sK7))
% 3.10/0.98      | ~ v2_pre_topc(sK7)
% 3.10/0.98      | ~ v8_pre_topc(sK7)
% 3.10/0.98      | ~ v2_lattice3(sK7)
% 3.10/0.98      | ~ v1_compts_1(sK7)
% 3.10/0.98      | ~ v4_orders_2(X0)
% 3.10/0.98      | ~ v4_orders_2(sK7)
% 3.10/0.98      | ~ v7_waybel_0(X0)
% 3.10/0.98      | ~ l1_waybel_9(sK7)
% 3.10/0.98      | ~ v5_orders_2(sK7)
% 3.10/0.98      | ~ v1_lattice3(sK7)
% 3.10/0.98      | v2_struct_0(X0) ),
% 3.10/0.98      inference(unflattening,[status(thm)],[c_1032]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_1037,plain,
% 3.10/0.98      ( ~ v7_waybel_0(X0)
% 3.10/0.98      | ~ r3_waybel_9(sK7,X0,X1)
% 3.10/0.98      | ~ r2_lattice3(sK7,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK7),u1_waybel_0(sK7,X0)),X2)
% 3.10/0.98      | r1_orders_2(sK7,X1,X2)
% 3.10/0.98      | ~ l1_waybel_0(X0,sK7)
% 3.10/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.10/0.98      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 3.10/0.98      | m1_subset_1(sK2(sK7),u1_struct_0(sK7))
% 3.10/0.98      | ~ v4_orders_2(X0)
% 3.10/0.98      | v2_struct_0(X0) ),
% 3.10/0.98      inference(global_propositional_subsumption,
% 3.10/0.98                [status(thm)],
% 3.10/0.98                [c_1033,c_43,c_42,c_40,c_39,c_38,c_37,c_36,c_35]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_1038,plain,
% 3.10/0.98      ( ~ r3_waybel_9(sK7,X0,X1)
% 3.10/0.98      | ~ r2_lattice3(sK7,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK7),u1_waybel_0(sK7,X0)),X2)
% 3.10/0.98      | r1_orders_2(sK7,X1,X2)
% 3.10/0.98      | ~ l1_waybel_0(X0,sK7)
% 3.10/0.98      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 3.10/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.10/0.98      | m1_subset_1(sK2(sK7),u1_struct_0(sK7))
% 3.10/0.98      | ~ v4_orders_2(X0)
% 3.10/0.98      | ~ v7_waybel_0(X0)
% 3.10/0.98      | v2_struct_0(X0) ),
% 3.10/0.98      inference(renaming,[status(thm)],[c_1037]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_2742,plain,
% 3.10/0.98      ( ~ r3_waybel_9(sK7,X0,X1)
% 3.10/0.98      | ~ r2_lattice3(sK7,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK7),u1_waybel_0(sK7,X0)),X2)
% 3.10/0.98      | r1_orders_2(sK7,X1,X2)
% 3.10/0.98      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 3.10/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.10/0.98      | m1_subset_1(sK2(sK7),u1_struct_0(sK7))
% 3.10/0.98      | ~ v4_orders_2(X0)
% 3.10/0.98      | ~ v7_waybel_0(X0)
% 3.10/0.98      | v2_struct_0(X0)
% 3.10/0.98      | sK8 != X0
% 3.10/0.98      | sK7 != sK7 ),
% 3.10/0.98      inference(resolution_lifted,[status(thm)],[c_30,c_1038]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_2743,plain,
% 3.10/0.98      ( ~ r3_waybel_9(sK7,sK8,X0)
% 3.10/0.98      | ~ r2_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X1)
% 3.10/0.98      | r1_orders_2(sK7,X0,X1)
% 3.10/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.10/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.10/0.98      | m1_subset_1(sK2(sK7),u1_struct_0(sK7))
% 3.10/0.98      | ~ v4_orders_2(sK8)
% 3.10/0.98      | ~ v7_waybel_0(sK8)
% 3.10/0.98      | v2_struct_0(sK8) ),
% 3.10/0.98      inference(unflattening,[status(thm)],[c_2742]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_2747,plain,
% 3.10/0.98      ( m1_subset_1(sK2(sK7),u1_struct_0(sK7))
% 3.10/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.10/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.10/0.98      | r1_orders_2(sK7,X0,X1)
% 3.10/0.98      | ~ r2_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X1)
% 3.10/0.98      | ~ r3_waybel_9(sK7,sK8,X0) ),
% 3.10/0.98      inference(global_propositional_subsumption,
% 3.10/0.98                [status(thm)],
% 3.10/0.98                [c_2743,c_33,c_32,c_31]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_2748,plain,
% 3.10/0.98      ( ~ r3_waybel_9(sK7,sK8,X0)
% 3.10/0.98      | ~ r2_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X1)
% 3.10/0.98      | r1_orders_2(sK7,X0,X1)
% 3.10/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.10/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.10/0.98      | m1_subset_1(sK2(sK7),u1_struct_0(sK7)) ),
% 3.10/0.98      inference(renaming,[status(thm)],[c_2747]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_4602,plain,
% 3.10/0.98      ( ~ r3_waybel_9(sK7,sK8,X0_69)
% 3.10/0.98      | ~ r2_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X1_69)
% 3.10/0.98      | r1_orders_2(sK7,X0_69,X1_69)
% 3.10/0.98      | ~ m1_subset_1(X0_69,u1_struct_0(sK7))
% 3.10/0.98      | ~ m1_subset_1(X1_69,u1_struct_0(sK7))
% 3.10/0.98      | m1_subset_1(sK2(sK7),u1_struct_0(sK7)) ),
% 3.10/0.98      inference(subtyping,[status(esa)],[c_2748]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_4690,plain,
% 3.10/0.98      ( r3_waybel_9(sK7,sK8,X0_69) != iProver_top
% 3.10/0.98      | r2_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X1_69) != iProver_top
% 3.10/0.98      | r1_orders_2(sK7,X0_69,X1_69) = iProver_top
% 3.10/0.98      | m1_subset_1(X0_69,u1_struct_0(sK7)) != iProver_top
% 3.10/0.98      | m1_subset_1(X1_69,u1_struct_0(sK7)) != iProver_top
% 3.10/0.98      | m1_subset_1(sK2(sK7),u1_struct_0(sK7)) = iProver_top ),
% 3.10/0.98      inference(predicate_to_equality,[status(thm)],[c_4602]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_4625,plain,
% 3.10/0.98      ( sP5_iProver_split | sP4_iProver_split ),
% 3.10/0.98      inference(splitting,
% 3.10/0.98                [splitting(split),new_symbols(definition,[])],
% 3.10/0.98                [c_4601]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_4693,plain,
% 3.10/0.98      ( sP5_iProver_split = iProver_top
% 3.10/0.98      | sP4_iProver_split = iProver_top ),
% 3.10/0.98      inference(predicate_to_equality,[status(thm)],[c_4625]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_4694,plain,
% 3.10/0.98      ( r3_waybel_9(sK7,sK8,X0_69) != iProver_top
% 3.10/0.98      | r2_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X1_69) != iProver_top
% 3.10/0.98      | r1_orders_2(sK7,X0_69,X1_69) = iProver_top
% 3.10/0.98      | m1_subset_1(X0_69,u1_struct_0(sK7)) != iProver_top
% 3.10/0.98      | m1_subset_1(X1_69,u1_struct_0(sK7)) != iProver_top
% 3.10/0.98      | sP5_iProver_split != iProver_top ),
% 3.10/0.98      inference(predicate_to_equality,[status(thm)],[c_4624]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_4623,plain,
% 3.10/0.98      ( ~ m1_subset_1(X0_69,u1_struct_0(sK7))
% 3.10/0.98      | k4_waybel_1(sK7,sK2(sK7)) != k4_waybel_1(sK7,X0_69)
% 3.10/0.98      | ~ sP4_iProver_split ),
% 3.10/0.98      inference(splitting,
% 3.10/0.98                [splitting(split),new_symbols(definition,[sP4_iProver_split])],
% 3.10/0.98                [c_4601]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_5135,plain,
% 3.10/0.98      ( k4_waybel_1(sK7,sK2(sK7)) != k4_waybel_1(sK7,X0_69)
% 3.10/0.98      | m1_subset_1(X0_69,u1_struct_0(sK7)) != iProver_top
% 3.10/0.98      | sP4_iProver_split != iProver_top ),
% 3.10/0.98      inference(predicate_to_equality,[status(thm)],[c_4623]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_5455,plain,
% 3.10/0.98      ( m1_subset_1(sK2(sK7),u1_struct_0(sK7)) != iProver_top
% 3.10/0.98      | sP4_iProver_split != iProver_top ),
% 3.10/0.98      inference(equality_resolution,[status(thm)],[c_5135]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_5848,plain,
% 3.10/0.98      ( m1_subset_1(X1_69,u1_struct_0(sK7)) != iProver_top
% 3.10/0.98      | m1_subset_1(X0_69,u1_struct_0(sK7)) != iProver_top
% 3.10/0.98      | r1_orders_2(sK7,X0_69,X1_69) = iProver_top
% 3.10/0.98      | r2_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X1_69) != iProver_top
% 3.10/0.98      | r3_waybel_9(sK7,sK8,X0_69) != iProver_top ),
% 3.10/0.98      inference(global_propositional_subsumption,
% 3.10/0.98                [status(thm)],
% 3.10/0.98                [c_5134,c_4690,c_4693,c_4694,c_5455]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_5849,plain,
% 3.10/0.98      ( r3_waybel_9(sK7,sK8,X0_69) != iProver_top
% 3.10/0.98      | r2_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X1_69) != iProver_top
% 3.10/0.98      | r1_orders_2(sK7,X0_69,X1_69) = iProver_top
% 3.10/0.98      | m1_subset_1(X0_69,u1_struct_0(sK7)) != iProver_top
% 3.10/0.98      | m1_subset_1(X1_69,u1_struct_0(sK7)) != iProver_top ),
% 3.10/0.98      inference(renaming,[status(thm)],[c_5848]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_5859,plain,
% 3.10/0.98      ( r3_waybel_9(sK7,sK8,X0_69) != iProver_top
% 3.10/0.98      | r2_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X1_69) != iProver_top
% 3.10/0.98      | r1_orders_2(sK7,X0_69,sK0(sK7,X1_69,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))) = iProver_top
% 3.10/0.98      | r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) = iProver_top
% 3.10/0.98      | m1_subset_1(X1_69,u1_struct_0(sK7)) != iProver_top
% 3.10/0.98      | m1_subset_1(X0_69,u1_struct_0(sK7)) != iProver_top
% 3.10/0.98      | m1_subset_1(sK0(sK7,X1_69,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))),u1_struct_0(sK7)) != iProver_top ),
% 3.10/0.98      inference(superposition,[status(thm)],[c_5123,c_5849]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_5,plain,
% 3.10/0.98      ( ~ r2_lattice3(X0,X1,X2)
% 3.10/0.98      | r1_yellow_0(X0,X1)
% 3.10/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.10/0.98      | m1_subset_1(sK0(X0,X2,X1),u1_struct_0(X0))
% 3.10/0.98      | ~ v5_orders_2(X0)
% 3.10/0.98      | ~ l1_orders_2(X0) ),
% 3.10/0.98      inference(cnf_transformation,[],[f66]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_889,plain,
% 3.10/0.98      ( ~ r2_lattice3(X0,X1,X2)
% 3.10/0.98      | r1_yellow_0(X0,X1)
% 3.10/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.10/0.98      | m1_subset_1(sK0(X0,X2,X1),u1_struct_0(X0))
% 3.10/0.98      | ~ l1_waybel_9(X0)
% 3.10/0.98      | ~ v5_orders_2(X0) ),
% 3.10/0.98      inference(resolution,[status(thm)],[c_13,c_5]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_1368,plain,
% 3.10/0.98      ( ~ r2_lattice3(X0,X1,X2)
% 3.10/0.98      | r1_yellow_0(X0,X1)
% 3.10/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.10/0.98      | m1_subset_1(sK0(X0,X2,X1),u1_struct_0(X0))
% 3.10/0.98      | ~ l1_waybel_9(X0)
% 3.10/0.98      | sK7 != X0 ),
% 3.10/0.98      inference(resolution_lifted,[status(thm)],[c_889,c_39]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_1369,plain,
% 3.10/0.98      ( ~ r2_lattice3(sK7,X0,X1)
% 3.10/0.98      | r1_yellow_0(sK7,X0)
% 3.10/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.10/0.98      | m1_subset_1(sK0(sK7,X1,X0),u1_struct_0(sK7))
% 3.10/0.98      | ~ l1_waybel_9(sK7) ),
% 3.10/0.98      inference(unflattening,[status(thm)],[c_1368]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_1373,plain,
% 3.10/0.98      ( m1_subset_1(sK0(sK7,X1,X0),u1_struct_0(sK7))
% 3.10/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.10/0.98      | r1_yellow_0(sK7,X0)
% 3.10/0.98      | ~ r2_lattice3(sK7,X0,X1) ),
% 3.10/0.98      inference(global_propositional_subsumption,
% 3.10/0.98                [status(thm)],
% 3.10/0.98                [c_1369,c_35]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_1374,plain,
% 3.10/0.98      ( ~ r2_lattice3(sK7,X0,X1)
% 3.10/0.98      | r1_yellow_0(sK7,X0)
% 3.10/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.10/0.98      | m1_subset_1(sK0(sK7,X1,X0),u1_struct_0(sK7)) ),
% 3.10/0.98      inference(renaming,[status(thm)],[c_1373]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_4610,plain,
% 3.10/0.98      ( ~ r2_lattice3(sK7,X0_70,X0_69)
% 3.10/0.98      | r1_yellow_0(sK7,X0_70)
% 3.10/0.98      | ~ m1_subset_1(X0_69,u1_struct_0(sK7))
% 3.10/0.98      | m1_subset_1(sK0(sK7,X0_69,X0_70),u1_struct_0(sK7)) ),
% 3.10/0.98      inference(subtyping,[status(esa)],[c_1374]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_5124,plain,
% 3.10/0.98      ( r2_lattice3(sK7,X0_70,X0_69) != iProver_top
% 3.10/0.98      | r1_yellow_0(sK7,X0_70) = iProver_top
% 3.10/0.98      | m1_subset_1(X0_69,u1_struct_0(sK7)) != iProver_top
% 3.10/0.98      | m1_subset_1(sK0(sK7,X0_69,X0_70),u1_struct_0(sK7)) = iProver_top ),
% 3.10/0.98      inference(predicate_to_equality,[status(thm)],[c_4610]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_6565,plain,
% 3.10/0.98      ( r3_waybel_9(sK7,sK8,X0_69) != iProver_top
% 3.10/0.98      | r2_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X1_69) != iProver_top
% 3.10/0.98      | r1_orders_2(sK7,X0_69,sK0(sK7,X1_69,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))) = iProver_top
% 3.10/0.98      | r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) = iProver_top
% 3.10/0.98      | m1_subset_1(X0_69,u1_struct_0(sK7)) != iProver_top
% 3.10/0.98      | m1_subset_1(X1_69,u1_struct_0(sK7)) != iProver_top ),
% 3.10/0.98      inference(forward_subsumption_resolution,
% 3.10/0.98                [status(thm)],
% 3.10/0.98                [c_5859,c_5124]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_3,plain,
% 3.10/0.98      ( ~ r2_lattice3(X0,X1,X2)
% 3.10/0.98      | ~ r1_orders_2(X0,X2,sK0(X0,X2,X1))
% 3.10/0.98      | r1_yellow_0(X0,X1)
% 3.10/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.10/0.98      | ~ v5_orders_2(X0)
% 3.10/0.98      | ~ l1_orders_2(X0) ),
% 3.10/0.98      inference(cnf_transformation,[],[f68]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_935,plain,
% 3.10/0.98      ( ~ r2_lattice3(X0,X1,X2)
% 3.10/0.98      | ~ r1_orders_2(X0,X2,sK0(X0,X2,X1))
% 3.10/0.98      | r1_yellow_0(X0,X1)
% 3.10/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.10/0.98      | ~ l1_waybel_9(X0)
% 3.10/0.98      | ~ v5_orders_2(X0) ),
% 3.10/0.98      inference(resolution,[status(thm)],[c_13,c_3]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_1320,plain,
% 3.10/0.98      ( ~ r2_lattice3(X0,X1,X2)
% 3.10/0.98      | ~ r1_orders_2(X0,X2,sK0(X0,X2,X1))
% 3.10/0.98      | r1_yellow_0(X0,X1)
% 3.10/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.10/0.98      | ~ l1_waybel_9(X0)
% 3.10/0.98      | sK7 != X0 ),
% 3.10/0.98      inference(resolution_lifted,[status(thm)],[c_935,c_39]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_1321,plain,
% 3.10/0.98      ( ~ r2_lattice3(sK7,X0,X1)
% 3.10/0.98      | ~ r1_orders_2(sK7,X1,sK0(sK7,X1,X0))
% 3.10/0.98      | r1_yellow_0(sK7,X0)
% 3.10/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.10/0.98      | ~ l1_waybel_9(sK7) ),
% 3.10/0.98      inference(unflattening,[status(thm)],[c_1320]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_1325,plain,
% 3.10/0.98      ( ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.10/0.98      | r1_yellow_0(sK7,X0)
% 3.10/0.98      | ~ r1_orders_2(sK7,X1,sK0(sK7,X1,X0))
% 3.10/0.98      | ~ r2_lattice3(sK7,X0,X1) ),
% 3.10/0.98      inference(global_propositional_subsumption,
% 3.10/0.98                [status(thm)],
% 3.10/0.98                [c_1321,c_35]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_1326,plain,
% 3.10/0.98      ( ~ r2_lattice3(sK7,X0,X1)
% 3.10/0.98      | ~ r1_orders_2(sK7,X1,sK0(sK7,X1,X0))
% 3.10/0.98      | r1_yellow_0(sK7,X0)
% 3.10/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK7)) ),
% 3.10/0.98      inference(renaming,[status(thm)],[c_1325]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_4612,plain,
% 3.10/0.98      ( ~ r2_lattice3(sK7,X0_70,X0_69)
% 3.10/0.98      | ~ r1_orders_2(sK7,X0_69,sK0(sK7,X0_69,X0_70))
% 3.10/0.98      | r1_yellow_0(sK7,X0_70)
% 3.10/0.98      | ~ m1_subset_1(X0_69,u1_struct_0(sK7)) ),
% 3.10/0.98      inference(subtyping,[status(esa)],[c_1326]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_5122,plain,
% 3.10/0.98      ( r2_lattice3(sK7,X0_70,X0_69) != iProver_top
% 3.10/0.98      | r1_orders_2(sK7,X0_69,sK0(sK7,X0_69,X0_70)) != iProver_top
% 3.10/0.98      | r1_yellow_0(sK7,X0_70) = iProver_top
% 3.10/0.98      | m1_subset_1(X0_69,u1_struct_0(sK7)) != iProver_top ),
% 3.10/0.98      inference(predicate_to_equality,[status(thm)],[c_4612]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_6570,plain,
% 3.10/0.98      ( r3_waybel_9(sK7,sK8,X0_69) != iProver_top
% 3.10/0.98      | r2_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X0_69) != iProver_top
% 3.10/0.98      | r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) = iProver_top
% 3.10/0.98      | m1_subset_1(X0_69,u1_struct_0(sK7)) != iProver_top ),
% 3.10/0.98      inference(superposition,[status(thm)],[c_6565,c_5122]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_29,negated_conjecture,
% 3.10/0.98      ( v10_waybel_0(sK8,sK7) ),
% 3.10/0.98      inference(cnf_transformation,[],[f100]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_16,plain,
% 3.10/0.98      ( ~ r3_waybel_9(X0,X1,X2)
% 3.10/0.98      | r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
% 3.10/0.98      | ~ v10_waybel_0(X1,X0)
% 3.10/0.98      | ~ l1_waybel_0(X1,X0)
% 3.10/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.10/0.98      | m1_subset_1(sK1(X0),u1_struct_0(X0))
% 3.10/0.98      | ~ v2_pre_topc(X0)
% 3.10/0.98      | ~ v8_pre_topc(X0)
% 3.10/0.98      | ~ v2_lattice3(X0)
% 3.10/0.98      | ~ v1_compts_1(X0)
% 3.10/0.98      | ~ v4_orders_2(X1)
% 3.10/0.98      | ~ v4_orders_2(X0)
% 3.10/0.98      | ~ v7_waybel_0(X1)
% 3.10/0.98      | ~ l1_waybel_9(X0)
% 3.10/0.98      | ~ v5_orders_2(X0)
% 3.10/0.98      | ~ v1_lattice3(X0)
% 3.10/0.98      | v2_struct_0(X1)
% 3.10/0.98      | ~ v3_orders_2(X0) ),
% 3.10/0.98      inference(cnf_transformation,[],[f105]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_1113,plain,
% 3.10/0.98      ( ~ r3_waybel_9(X0,X1,X2)
% 3.10/0.98      | r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
% 3.10/0.98      | ~ v10_waybel_0(X1,X0)
% 3.10/0.98      | ~ l1_waybel_0(X1,X0)
% 3.10/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.10/0.98      | m1_subset_1(sK1(X0),u1_struct_0(X0))
% 3.10/0.98      | ~ v2_pre_topc(X0)
% 3.10/0.98      | ~ v8_pre_topc(X0)
% 3.10/0.98      | ~ v2_lattice3(X0)
% 3.10/0.98      | ~ v1_compts_1(X0)
% 3.10/0.98      | ~ v4_orders_2(X1)
% 3.10/0.98      | ~ v4_orders_2(X0)
% 3.10/0.98      | ~ v7_waybel_0(X1)
% 3.10/0.98      | ~ l1_waybel_9(X0)
% 3.10/0.98      | ~ v5_orders_2(X0)
% 3.10/0.98      | ~ v1_lattice3(X0)
% 3.10/0.98      | v2_struct_0(X1)
% 3.10/0.98      | sK7 != X0 ),
% 3.10/0.98      inference(resolution_lifted,[status(thm)],[c_16,c_41]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_1114,plain,
% 3.10/0.98      ( ~ r3_waybel_9(sK7,X0,X1)
% 3.10/0.98      | r2_lattice3(sK7,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK7),u1_waybel_0(sK7,X0)),X1)
% 3.10/0.98      | ~ v10_waybel_0(X0,sK7)
% 3.10/0.98      | ~ l1_waybel_0(X0,sK7)
% 3.10/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.10/0.98      | m1_subset_1(sK1(sK7),u1_struct_0(sK7))
% 3.10/0.98      | ~ v2_pre_topc(sK7)
% 3.10/0.98      | ~ v8_pre_topc(sK7)
% 3.10/0.98      | ~ v2_lattice3(sK7)
% 3.10/0.98      | ~ v1_compts_1(sK7)
% 3.10/0.98      | ~ v4_orders_2(X0)
% 3.10/0.98      | ~ v4_orders_2(sK7)
% 3.10/0.98      | ~ v7_waybel_0(X0)
% 3.10/0.98      | ~ l1_waybel_9(sK7)
% 3.10/0.98      | ~ v5_orders_2(sK7)
% 3.10/0.98      | ~ v1_lattice3(sK7)
% 3.10/0.98      | v2_struct_0(X0) ),
% 3.10/0.98      inference(unflattening,[status(thm)],[c_1113]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_1118,plain,
% 3.10/0.98      ( ~ v7_waybel_0(X0)
% 3.10/0.98      | ~ r3_waybel_9(sK7,X0,X1)
% 3.10/0.98      | r2_lattice3(sK7,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK7),u1_waybel_0(sK7,X0)),X1)
% 3.10/0.98      | ~ v10_waybel_0(X0,sK7)
% 3.10/0.98      | ~ l1_waybel_0(X0,sK7)
% 3.10/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.10/0.98      | m1_subset_1(sK1(sK7),u1_struct_0(sK7))
% 3.10/0.98      | ~ v4_orders_2(X0)
% 3.10/0.98      | v2_struct_0(X0) ),
% 3.10/0.98      inference(global_propositional_subsumption,
% 3.10/0.98                [status(thm)],
% 3.10/0.98                [c_1114,c_43,c_42,c_40,c_39,c_38,c_37,c_36,c_35]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_1119,plain,
% 3.10/0.98      ( ~ r3_waybel_9(sK7,X0,X1)
% 3.10/0.98      | r2_lattice3(sK7,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK7),u1_waybel_0(sK7,X0)),X1)
% 3.10/0.98      | ~ v10_waybel_0(X0,sK7)
% 3.10/0.98      | ~ l1_waybel_0(X0,sK7)
% 3.10/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.10/0.98      | m1_subset_1(sK1(sK7),u1_struct_0(sK7))
% 3.10/0.98      | ~ v4_orders_2(X0)
% 3.10/0.98      | ~ v7_waybel_0(X0)
% 3.10/0.98      | v2_struct_0(X0) ),
% 3.10/0.98      inference(renaming,[status(thm)],[c_1118]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_1196,plain,
% 3.10/0.98      ( ~ r3_waybel_9(sK7,X0,X1)
% 3.10/0.98      | r2_lattice3(sK7,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK7),u1_waybel_0(sK7,X0)),X1)
% 3.10/0.98      | ~ l1_waybel_0(X0,sK7)
% 3.10/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.10/0.98      | m1_subset_1(sK1(sK7),u1_struct_0(sK7))
% 3.10/0.98      | ~ v4_orders_2(X0)
% 3.10/0.98      | ~ v7_waybel_0(X0)
% 3.10/0.98      | v2_struct_0(X0)
% 3.10/0.98      | sK8 != X0
% 3.10/0.98      | sK7 != sK7 ),
% 3.10/0.98      inference(resolution_lifted,[status(thm)],[c_29,c_1119]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_1197,plain,
% 3.10/0.98      ( ~ r3_waybel_9(sK7,sK8,X0)
% 3.10/0.98      | r2_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X0)
% 3.10/0.98      | ~ l1_waybel_0(sK8,sK7)
% 3.10/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.10/0.98      | m1_subset_1(sK1(sK7),u1_struct_0(sK7))
% 3.10/0.98      | ~ v4_orders_2(sK8)
% 3.10/0.98      | ~ v7_waybel_0(sK8)
% 3.10/0.98      | v2_struct_0(sK8) ),
% 3.10/0.98      inference(unflattening,[status(thm)],[c_1196]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_1201,plain,
% 3.10/0.98      ( m1_subset_1(sK1(sK7),u1_struct_0(sK7))
% 3.10/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.10/0.98      | ~ r3_waybel_9(sK7,sK8,X0)
% 3.10/0.98      | r2_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X0) ),
% 3.10/0.98      inference(global_propositional_subsumption,
% 3.10/0.98                [status(thm)],
% 3.10/0.98                [c_1197,c_33,c_32,c_31,c_30]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_1202,plain,
% 3.10/0.98      ( ~ r3_waybel_9(sK7,sK8,X0)
% 3.10/0.98      | r2_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X0)
% 3.10/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.10/0.98      | m1_subset_1(sK1(sK7),u1_struct_0(sK7)) ),
% 3.10/0.98      inference(renaming,[status(thm)],[c_1201]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_4616,plain,
% 3.10/0.98      ( ~ r3_waybel_9(sK7,sK8,X0_69)
% 3.10/0.98      | r2_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X0_69)
% 3.10/0.98      | ~ m1_subset_1(X0_69,u1_struct_0(sK7))
% 3.10/0.98      | m1_subset_1(sK1(sK7),u1_struct_0(sK7)) ),
% 3.10/0.98      inference(subtyping,[status(esa)],[c_1202]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_5114,plain,
% 3.10/0.98      ( r3_waybel_9(sK7,sK8,X0_69) != iProver_top
% 3.10/0.98      | r2_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X0_69) = iProver_top
% 3.10/0.98      | m1_subset_1(X0_69,u1_struct_0(sK7)) != iProver_top
% 3.10/0.98      | m1_subset_1(sK1(sK7),u1_struct_0(sK7)) = iProver_top ),
% 3.10/0.98      inference(predicate_to_equality,[status(thm)],[c_4616]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_4644,plain,
% 3.10/0.98      ( r3_waybel_9(sK7,sK8,X0_69) != iProver_top
% 3.10/0.98      | r2_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X0_69) = iProver_top
% 3.10/0.98      | m1_subset_1(X0_69,u1_struct_0(sK7)) != iProver_top
% 3.10/0.98      | m1_subset_1(sK1(sK7),u1_struct_0(sK7)) = iProver_top ),
% 3.10/0.98      inference(predicate_to_equality,[status(thm)],[c_4616]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_15,plain,
% 3.10/0.98      ( ~ v5_pre_topc(k4_waybel_1(X0,sK1(X0)),X0,X0)
% 3.10/0.98      | ~ r3_waybel_9(X0,X1,X2)
% 3.10/0.98      | r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
% 3.10/0.98      | ~ v10_waybel_0(X1,X0)
% 3.10/0.98      | ~ l1_waybel_0(X1,X0)
% 3.10/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.10/0.98      | ~ v2_pre_topc(X0)
% 3.10/0.98      | ~ v8_pre_topc(X0)
% 3.10/0.98      | ~ v2_lattice3(X0)
% 3.10/0.98      | ~ v1_compts_1(X0)
% 3.10/0.98      | ~ v4_orders_2(X1)
% 3.10/0.98      | ~ v4_orders_2(X0)
% 3.10/0.98      | ~ v7_waybel_0(X1)
% 3.10/0.98      | ~ l1_waybel_9(X0)
% 3.10/0.98      | ~ v5_orders_2(X0)
% 3.10/0.98      | ~ v1_lattice3(X0)
% 3.10/0.98      | v2_struct_0(X1)
% 3.10/0.98      | ~ v3_orders_2(X0) ),
% 3.10/0.98      inference(cnf_transformation,[],[f104]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_505,plain,
% 3.10/0.98      ( ~ r3_waybel_9(X0,X1,X2)
% 3.10/0.98      | r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
% 3.10/0.98      | ~ v10_waybel_0(X1,X0)
% 3.10/0.98      | ~ l1_waybel_0(X1,X0)
% 3.10/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.10/0.98      | ~ m1_subset_1(X3,u1_struct_0(sK7))
% 3.10/0.98      | ~ v2_pre_topc(X0)
% 3.10/0.98      | ~ v8_pre_topc(X0)
% 3.10/0.98      | ~ v2_lattice3(X0)
% 3.10/0.98      | ~ v1_compts_1(X0)
% 3.10/0.98      | ~ v4_orders_2(X1)
% 3.10/0.98      | ~ v4_orders_2(X0)
% 3.10/0.98      | ~ v7_waybel_0(X1)
% 3.10/0.98      | ~ l1_waybel_9(X0)
% 3.10/0.98      | ~ v5_orders_2(X0)
% 3.10/0.98      | ~ v1_lattice3(X0)
% 3.10/0.98      | v2_struct_0(X1)
% 3.10/0.98      | ~ v3_orders_2(X0)
% 3.10/0.98      | k4_waybel_1(X0,sK1(X0)) != k4_waybel_1(sK7,X3)
% 3.10/0.98      | sK7 != X0 ),
% 3.10/0.98      inference(resolution_lifted,[status(thm)],[c_15,c_34]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_506,plain,
% 3.10/0.98      ( ~ r3_waybel_9(sK7,X0,X1)
% 3.10/0.98      | r2_lattice3(sK7,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK7),u1_waybel_0(sK7,X0)),X1)
% 3.10/0.98      | ~ v10_waybel_0(X0,sK7)
% 3.10/0.98      | ~ l1_waybel_0(X0,sK7)
% 3.10/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.10/0.98      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 3.10/0.98      | ~ v2_pre_topc(sK7)
% 3.10/0.98      | ~ v8_pre_topc(sK7)
% 3.10/0.98      | ~ v2_lattice3(sK7)
% 3.10/0.98      | ~ v1_compts_1(sK7)
% 3.10/0.98      | ~ v4_orders_2(X0)
% 3.10/0.98      | ~ v4_orders_2(sK7)
% 3.10/0.98      | ~ v7_waybel_0(X0)
% 3.10/0.98      | ~ l1_waybel_9(sK7)
% 3.10/0.98      | ~ v5_orders_2(sK7)
% 3.10/0.98      | ~ v1_lattice3(sK7)
% 3.10/0.98      | v2_struct_0(X0)
% 3.10/0.98      | ~ v3_orders_2(sK7)
% 3.10/0.98      | k4_waybel_1(sK7,sK1(sK7)) != k4_waybel_1(sK7,X2) ),
% 3.10/0.98      inference(unflattening,[status(thm)],[c_505]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_510,plain,
% 3.10/0.98      ( v2_struct_0(X0)
% 3.10/0.98      | ~ v4_orders_2(X0)
% 3.10/0.98      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 3.10/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.10/0.98      | ~ l1_waybel_0(X0,sK7)
% 3.10/0.98      | ~ v10_waybel_0(X0,sK7)
% 3.10/0.98      | r2_lattice3(sK7,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK7),u1_waybel_0(sK7,X0)),X1)
% 3.10/0.98      | ~ r3_waybel_9(sK7,X0,X1)
% 3.10/0.98      | ~ v7_waybel_0(X0)
% 3.10/0.98      | k4_waybel_1(sK7,sK1(sK7)) != k4_waybel_1(sK7,X2) ),
% 3.10/0.98      inference(global_propositional_subsumption,
% 3.10/0.98                [status(thm)],
% 3.10/0.98                [c_506,c_43,c_42,c_41,c_40,c_39,c_38,c_37,c_36,c_35]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_511,plain,
% 3.10/0.98      ( ~ r3_waybel_9(sK7,X0,X1)
% 3.10/0.98      | r2_lattice3(sK7,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK7),u1_waybel_0(sK7,X0)),X1)
% 3.10/0.98      | ~ v10_waybel_0(X0,sK7)
% 3.10/0.98      | ~ l1_waybel_0(X0,sK7)
% 3.10/0.98      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 3.10/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.10/0.98      | ~ v4_orders_2(X0)
% 3.10/0.98      | ~ v7_waybel_0(X0)
% 3.10/0.98      | v2_struct_0(X0)
% 3.10/0.98      | k4_waybel_1(sK7,sK1(sK7)) != k4_waybel_1(sK7,X2) ),
% 3.10/0.98      inference(renaming,[status(thm)],[c_510]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_1271,plain,
% 3.10/0.98      ( ~ r3_waybel_9(sK7,X0,X1)
% 3.10/0.98      | r2_lattice3(sK7,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK7),u1_waybel_0(sK7,X0)),X1)
% 3.10/0.98      | ~ l1_waybel_0(X0,sK7)
% 3.10/0.98      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 3.10/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.10/0.98      | ~ v4_orders_2(X0)
% 3.10/0.98      | ~ v7_waybel_0(X0)
% 3.10/0.98      | v2_struct_0(X0)
% 3.10/0.98      | k4_waybel_1(sK7,sK1(sK7)) != k4_waybel_1(sK7,X2)
% 3.10/0.98      | sK8 != X0
% 3.10/0.98      | sK7 != sK7 ),
% 3.10/0.98      inference(resolution_lifted,[status(thm)],[c_29,c_511]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_1272,plain,
% 3.10/0.98      ( ~ r3_waybel_9(sK7,sK8,X0)
% 3.10/0.98      | r2_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X0)
% 3.10/0.98      | ~ l1_waybel_0(sK8,sK7)
% 3.10/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.10/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.10/0.98      | ~ v4_orders_2(sK8)
% 3.10/0.98      | ~ v7_waybel_0(sK8)
% 3.10/0.98      | v2_struct_0(sK8)
% 3.10/0.98      | k4_waybel_1(sK7,sK1(sK7)) != k4_waybel_1(sK7,X1) ),
% 3.10/0.98      inference(unflattening,[status(thm)],[c_1271]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_1276,plain,
% 3.10/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.10/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.10/0.98      | ~ r3_waybel_9(sK7,sK8,X0)
% 3.10/0.98      | r2_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X0)
% 3.10/0.98      | k4_waybel_1(sK7,sK1(sK7)) != k4_waybel_1(sK7,X1) ),
% 3.10/0.98      inference(global_propositional_subsumption,
% 3.10/0.98                [status(thm)],
% 3.10/0.98                [c_1272,c_33,c_32,c_31,c_30]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_1277,plain,
% 3.10/0.98      ( ~ r3_waybel_9(sK7,sK8,X0)
% 3.10/0.98      | r2_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X0)
% 3.10/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.10/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.10/0.98      | k4_waybel_1(sK7,sK1(sK7)) != k4_waybel_1(sK7,X1) ),
% 3.10/0.98      inference(renaming,[status(thm)],[c_1276]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_4613,plain,
% 3.10/0.98      ( ~ r3_waybel_9(sK7,sK8,X0_69)
% 3.10/0.98      | r2_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X0_69)
% 3.10/0.98      | ~ m1_subset_1(X0_69,u1_struct_0(sK7))
% 3.10/0.98      | ~ m1_subset_1(X1_69,u1_struct_0(sK7))
% 3.10/0.98      | k4_waybel_1(sK7,sK1(sK7)) != k4_waybel_1(sK7,X1_69) ),
% 3.10/0.98      inference(subtyping,[status(esa)],[c_1277]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_4622,plain,
% 3.10/0.98      ( sP3_iProver_split | sP2_iProver_split ),
% 3.10/0.98      inference(splitting,
% 3.10/0.98                [splitting(split),new_symbols(definition,[])],
% 3.10/0.98                [c_4613]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_4657,plain,
% 3.10/0.98      ( sP3_iProver_split = iProver_top
% 3.10/0.98      | sP2_iProver_split = iProver_top ),
% 3.10/0.98      inference(predicate_to_equality,[status(thm)],[c_4622]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_4621,plain,
% 3.10/0.98      ( ~ r3_waybel_9(sK7,sK8,X0_69)
% 3.10/0.98      | r2_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X0_69)
% 3.10/0.98      | ~ m1_subset_1(X0_69,u1_struct_0(sK7))
% 3.10/0.98      | ~ sP3_iProver_split ),
% 3.10/0.98      inference(splitting,
% 3.10/0.98                [splitting(split),new_symbols(definition,[sP3_iProver_split])],
% 3.10/0.98                [c_4613]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_4658,plain,
% 3.10/0.98      ( r3_waybel_9(sK7,sK8,X0_69) != iProver_top
% 3.10/0.98      | r2_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X0_69) = iProver_top
% 3.10/0.98      | m1_subset_1(X0_69,u1_struct_0(sK7)) != iProver_top
% 3.10/0.98      | sP3_iProver_split != iProver_top ),
% 3.10/0.98      inference(predicate_to_equality,[status(thm)],[c_4621]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_4620,plain,
% 3.10/0.98      ( ~ m1_subset_1(X0_69,u1_struct_0(sK7))
% 3.10/0.98      | k4_waybel_1(sK7,sK1(sK7)) != k4_waybel_1(sK7,X0_69)
% 3.10/0.98      | ~ sP2_iProver_split ),
% 3.10/0.98      inference(splitting,
% 3.10/0.98                [splitting(split),new_symbols(definition,[sP2_iProver_split])],
% 3.10/0.98                [c_4613]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_5121,plain,
% 3.10/0.98      ( k4_waybel_1(sK7,sK1(sK7)) != k4_waybel_1(sK7,X0_69)
% 3.10/0.98      | m1_subset_1(X0_69,u1_struct_0(sK7)) != iProver_top
% 3.10/0.98      | sP2_iProver_split != iProver_top ),
% 3.10/0.98      inference(predicate_to_equality,[status(thm)],[c_4620]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_5419,plain,
% 3.10/0.98      ( m1_subset_1(sK1(sK7),u1_struct_0(sK7)) != iProver_top
% 3.10/0.98      | sP2_iProver_split != iProver_top ),
% 3.10/0.98      inference(equality_resolution,[status(thm)],[c_5121]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_5537,plain,
% 3.10/0.98      ( m1_subset_1(X0_69,u1_struct_0(sK7)) != iProver_top
% 3.10/0.98      | r2_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X0_69) = iProver_top
% 3.10/0.98      | r3_waybel_9(sK7,sK8,X0_69) != iProver_top ),
% 3.10/0.98      inference(global_propositional_subsumption,
% 3.10/0.98                [status(thm)],
% 3.10/0.98                [c_5114,c_4644,c_4657,c_4658,c_5419]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_5538,plain,
% 3.10/0.98      ( r3_waybel_9(sK7,sK8,X0_69) != iProver_top
% 3.10/0.98      | r2_lattice3(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)),X0_69) = iProver_top
% 3.10/0.98      | m1_subset_1(X0_69,u1_struct_0(sK7)) != iProver_top ),
% 3.10/0.98      inference(renaming,[status(thm)],[c_5537]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_6640,plain,
% 3.10/0.98      ( r3_waybel_9(sK7,sK8,X0_69) != iProver_top
% 3.10/0.98      | r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) = iProver_top
% 3.10/0.98      | m1_subset_1(X0_69,u1_struct_0(sK7)) != iProver_top ),
% 3.10/0.98      inference(global_propositional_subsumption,
% 3.10/0.98                [status(thm)],
% 3.10/0.98                [c_6570,c_5538]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_6649,plain,
% 3.10/0.98      ( r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) = iProver_top
% 3.10/0.98      | m1_subset_1(sK3(sK7,sK8),u1_struct_0(sK7)) != iProver_top ),
% 3.10/0.98      inference(superposition,[status(thm)],[c_5131,c_6640]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_56,plain,
% 3.10/0.98      ( v2_struct_0(sK8) != iProver_top ),
% 3.10/0.98      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_57,plain,
% 3.10/0.98      ( v4_orders_2(sK8) = iProver_top ),
% 3.10/0.98      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_58,plain,
% 3.10/0.98      ( v7_waybel_0(sK8) = iProver_top ),
% 3.10/0.98      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_20,plain,
% 3.10/0.98      ( ~ l1_waybel_0(X0,X1)
% 3.10/0.98      | m1_subset_1(sK3(X1,X0),u1_struct_0(X1))
% 3.10/0.98      | ~ v2_pre_topc(X1)
% 3.10/0.98      | ~ v8_pre_topc(X1)
% 3.10/0.98      | ~ v1_compts_1(X1)
% 3.10/0.98      | ~ v4_orders_2(X0)
% 3.10/0.98      | ~ v7_waybel_0(X0)
% 3.10/0.98      | ~ l1_pre_topc(X1)
% 3.10/0.98      | v2_struct_0(X1)
% 3.10/0.98      | v2_struct_0(X0) ),
% 3.10/0.98      inference(cnf_transformation,[],[f77]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_2516,plain,
% 3.10/0.98      ( ~ l1_waybel_0(X0,X1)
% 3.10/0.98      | m1_subset_1(sK3(X1,X0),u1_struct_0(X1))
% 3.10/0.98      | ~ v2_pre_topc(X1)
% 3.10/0.98      | ~ v8_pre_topc(X1)
% 3.10/0.98      | ~ v1_compts_1(X1)
% 3.10/0.98      | ~ v4_orders_2(X0)
% 3.10/0.98      | ~ v7_waybel_0(X0)
% 3.10/0.98      | v2_struct_0(X0)
% 3.10/0.98      | v2_struct_0(X1)
% 3.10/0.98      | sK7 != X1 ),
% 3.10/0.98      inference(resolution_lifted,[status(thm)],[c_20,c_1553]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_2517,plain,
% 3.10/0.98      ( ~ l1_waybel_0(X0,sK7)
% 3.10/0.98      | m1_subset_1(sK3(sK7,X0),u1_struct_0(sK7))
% 3.10/0.98      | ~ v2_pre_topc(sK7)
% 3.10/0.98      | ~ v8_pre_topc(sK7)
% 3.10/0.98      | ~ v1_compts_1(sK7)
% 3.10/0.98      | ~ v4_orders_2(X0)
% 3.10/0.98      | ~ v7_waybel_0(X0)
% 3.10/0.98      | v2_struct_0(X0)
% 3.10/0.98      | v2_struct_0(sK7) ),
% 3.10/0.98      inference(unflattening,[status(thm)],[c_2516]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_2521,plain,
% 3.10/0.98      ( v2_struct_0(X0)
% 3.10/0.98      | ~ v7_waybel_0(X0)
% 3.10/0.98      | ~ v4_orders_2(X0)
% 3.10/0.98      | ~ l1_waybel_0(X0,sK7)
% 3.10/0.98      | m1_subset_1(sK3(sK7,X0),u1_struct_0(sK7)) ),
% 3.10/0.98      inference(global_propositional_subsumption,
% 3.10/0.98                [status(thm)],
% 3.10/0.98                [c_2517,c_43,c_42,c_38,c_36,c_35,c_105,c_138]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_2522,plain,
% 3.10/0.98      ( ~ l1_waybel_0(X0,sK7)
% 3.10/0.98      | m1_subset_1(sK3(sK7,X0),u1_struct_0(sK7))
% 3.10/0.98      | ~ v4_orders_2(X0)
% 3.10/0.98      | ~ v7_waybel_0(X0)
% 3.10/0.98      | v2_struct_0(X0) ),
% 3.10/0.98      inference(renaming,[status(thm)],[c_2521]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_2605,plain,
% 3.10/0.98      ( m1_subset_1(sK3(sK7,X0),u1_struct_0(sK7))
% 3.10/0.98      | ~ v4_orders_2(X0)
% 3.10/0.98      | ~ v7_waybel_0(X0)
% 3.10/0.98      | v2_struct_0(X0)
% 3.10/0.98      | sK8 != X0
% 3.10/0.98      | sK7 != sK7 ),
% 3.10/0.98      inference(resolution_lifted,[status(thm)],[c_30,c_2522]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_2606,plain,
% 3.10/0.98      ( m1_subset_1(sK3(sK7,sK8),u1_struct_0(sK7))
% 3.10/0.98      | ~ v4_orders_2(sK8)
% 3.10/0.98      | ~ v7_waybel_0(sK8)
% 3.10/0.98      | v2_struct_0(sK8) ),
% 3.10/0.98      inference(unflattening,[status(thm)],[c_2605]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_2607,plain,
% 3.10/0.98      ( m1_subset_1(sK3(sK7,sK8),u1_struct_0(sK7)) = iProver_top
% 3.10/0.98      | v4_orders_2(sK8) != iProver_top
% 3.10/0.98      | v7_waybel_0(sK8) != iProver_top
% 3.10/0.98      | v2_struct_0(sK8) = iProver_top ),
% 3.10/0.98      inference(predicate_to_equality,[status(thm)],[c_2606]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_6652,plain,
% 3.10/0.98      ( r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) = iProver_top ),
% 3.10/0.98      inference(global_propositional_subsumption,
% 3.10/0.98                [status(thm)],
% 3.10/0.98                [c_6649,c_56,c_57,c_58,c_2607]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_23,plain,
% 3.10/0.98      ( ~ r3_waybel_9(X0,X1,X2)
% 3.10/0.98      | r3_waybel_9(X0,X1,sK4(X0,X1))
% 3.10/0.98      | r2_hidden(X2,k10_yellow_6(X0,X1))
% 3.10/0.98      | ~ l1_waybel_0(X1,X0)
% 3.10/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.10/0.98      | ~ v2_pre_topc(X0)
% 3.10/0.98      | ~ v8_pre_topc(X0)
% 3.10/0.98      | ~ v1_compts_1(X0)
% 3.10/0.98      | ~ v4_orders_2(X1)
% 3.10/0.98      | ~ v7_waybel_0(X1)
% 3.10/0.98      | ~ l1_pre_topc(X0)
% 3.10/0.98      | v2_struct_0(X0)
% 3.10/0.98      | v2_struct_0(X1) ),
% 3.10/0.98      inference(cnf_transformation,[],[f81]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_11,plain,
% 3.10/0.98      ( ~ l1_waybel_0(X0,X1)
% 3.10/0.98      | r1_waybel_9(X1,X0)
% 3.10/0.98      | ~ r1_yellow_0(X1,k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0)))
% 3.10/0.98      | ~ l1_orders_2(X1) ),
% 3.10/0.98      inference(cnf_transformation,[],[f70]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_28,negated_conjecture,
% 3.10/0.98      ( ~ r2_hidden(k1_waybel_2(sK7,sK8),k10_yellow_6(sK7,sK8))
% 3.10/0.98      | ~ r1_waybel_9(sK7,sK8) ),
% 3.10/0.98      inference(cnf_transformation,[],[f101]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_488,plain,
% 3.10/0.98      ( ~ r2_hidden(k1_waybel_2(sK7,sK8),k10_yellow_6(sK7,sK8))
% 3.10/0.98      | ~ l1_waybel_0(X0,X1)
% 3.10/0.98      | ~ r1_yellow_0(X1,k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0)))
% 3.10/0.98      | ~ l1_orders_2(X1)
% 3.10/0.98      | sK8 != X0
% 3.10/0.98      | sK7 != X1 ),
% 3.10/0.98      inference(resolution_lifted,[status(thm)],[c_11,c_28]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_489,plain,
% 3.10/0.98      ( ~ r2_hidden(k1_waybel_2(sK7,sK8),k10_yellow_6(sK7,sK8))
% 3.10/0.98      | ~ l1_waybel_0(sK8,sK7)
% 3.10/0.98      | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 3.10/0.98      | ~ l1_orders_2(sK7) ),
% 3.10/0.98      inference(unflattening,[status(thm)],[c_488]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_491,plain,
% 3.10/0.98      ( ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 3.10/0.98      | ~ r2_hidden(k1_waybel_2(sK7,sK8),k10_yellow_6(sK7,sK8)) ),
% 3.10/0.98      inference(global_propositional_subsumption,
% 3.10/0.98                [status(thm)],
% 3.10/0.98                [c_489,c_35,c_30,c_105]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_492,plain,
% 3.10/0.98      ( ~ r2_hidden(k1_waybel_2(sK7,sK8),k10_yellow_6(sK7,sK8))
% 3.10/0.98      | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) ),
% 3.10/0.98      inference(renaming,[status(thm)],[c_491]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_2145,plain,
% 3.10/0.98      ( ~ r3_waybel_9(X0,X1,X2)
% 3.10/0.98      | r3_waybel_9(X0,X1,sK4(X0,X1))
% 3.10/0.98      | ~ l1_waybel_0(X1,X0)
% 3.10/0.98      | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 3.10/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.10/0.98      | ~ v2_pre_topc(X0)
% 3.10/0.98      | ~ v8_pre_topc(X0)
% 3.10/0.98      | ~ v1_compts_1(X0)
% 3.10/0.98      | ~ v4_orders_2(X1)
% 3.10/0.98      | ~ v7_waybel_0(X1)
% 3.10/0.98      | ~ l1_pre_topc(X0)
% 3.10/0.98      | v2_struct_0(X0)
% 3.10/0.98      | v2_struct_0(X1)
% 3.10/0.98      | k1_waybel_2(sK7,sK8) != X2
% 3.10/0.98      | k10_yellow_6(X0,X1) != k10_yellow_6(sK7,sK8) ),
% 3.10/0.98      inference(resolution_lifted,[status(thm)],[c_23,c_492]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_2146,plain,
% 3.10/0.98      ( ~ r3_waybel_9(X0,X1,k1_waybel_2(sK7,sK8))
% 3.10/0.98      | r3_waybel_9(X0,X1,sK4(X0,X1))
% 3.10/0.98      | ~ l1_waybel_0(X1,X0)
% 3.10/0.98      | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 3.10/0.98      | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(X0))
% 3.10/0.98      | ~ v2_pre_topc(X0)
% 3.10/0.98      | ~ v8_pre_topc(X0)
% 3.10/0.98      | ~ v1_compts_1(X0)
% 3.10/0.98      | ~ v4_orders_2(X1)
% 3.10/0.98      | ~ v7_waybel_0(X1)
% 3.10/0.98      | ~ l1_pre_topc(X0)
% 3.10/0.98      | v2_struct_0(X0)
% 3.10/0.98      | v2_struct_0(X1)
% 3.10/0.98      | k10_yellow_6(X0,X1) != k10_yellow_6(sK7,sK8) ),
% 3.10/0.98      inference(unflattening,[status(thm)],[c_2145]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_2372,plain,
% 3.10/0.98      ( ~ r3_waybel_9(X0,X1,k1_waybel_2(sK7,sK8))
% 3.10/0.98      | r3_waybel_9(X0,X1,sK4(X0,X1))
% 3.10/0.98      | ~ l1_waybel_0(X1,X0)
% 3.10/0.98      | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 3.10/0.98      | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(X0))
% 3.10/0.98      | ~ v2_pre_topc(X0)
% 3.10/0.98      | ~ v8_pre_topc(X0)
% 3.10/0.98      | ~ v1_compts_1(X0)
% 3.10/0.98      | ~ v4_orders_2(X1)
% 3.10/0.98      | ~ v7_waybel_0(X1)
% 3.10/0.98      | v2_struct_0(X0)
% 3.10/0.98      | v2_struct_0(X1)
% 3.10/0.98      | k10_yellow_6(X0,X1) != k10_yellow_6(sK7,sK8)
% 3.10/0.98      | sK7 != X0 ),
% 3.10/0.98      inference(resolution_lifted,[status(thm)],[c_2146,c_1553]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_2373,plain,
% 3.10/0.98      ( ~ r3_waybel_9(sK7,X0,k1_waybel_2(sK7,sK8))
% 3.10/0.98      | r3_waybel_9(sK7,X0,sK4(sK7,X0))
% 3.10/0.98      | ~ l1_waybel_0(X0,sK7)
% 3.10/0.98      | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 3.10/0.98      | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
% 3.10/0.98      | ~ v2_pre_topc(sK7)
% 3.10/0.98      | ~ v8_pre_topc(sK7)
% 3.10/0.98      | ~ v1_compts_1(sK7)
% 3.10/0.98      | ~ v4_orders_2(X0)
% 3.10/0.98      | ~ v7_waybel_0(X0)
% 3.10/0.98      | v2_struct_0(X0)
% 3.10/0.98      | v2_struct_0(sK7)
% 3.10/0.98      | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8) ),
% 3.10/0.98      inference(unflattening,[status(thm)],[c_2372]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_2377,plain,
% 3.10/0.98      ( v2_struct_0(X0)
% 3.10/0.98      | ~ v7_waybel_0(X0)
% 3.10/0.98      | ~ v4_orders_2(X0)
% 3.10/0.98      | ~ r3_waybel_9(sK7,X0,k1_waybel_2(sK7,sK8))
% 3.10/0.98      | r3_waybel_9(sK7,X0,sK4(sK7,X0))
% 3.10/0.98      | ~ l1_waybel_0(X0,sK7)
% 3.10/0.98      | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 3.10/0.98      | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
% 3.10/0.98      | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8) ),
% 3.10/0.98      inference(global_propositional_subsumption,
% 3.10/0.98                [status(thm)],
% 3.10/0.98                [c_2373,c_43,c_42,c_38,c_36,c_35,c_105,c_138]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_2378,plain,
% 3.10/0.98      ( ~ r3_waybel_9(sK7,X0,k1_waybel_2(sK7,sK8))
% 3.10/0.98      | r3_waybel_9(sK7,X0,sK4(sK7,X0))
% 3.10/0.98      | ~ l1_waybel_0(X0,sK7)
% 3.10/0.98      | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 3.10/0.98      | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
% 3.10/0.98      | ~ v4_orders_2(X0)
% 3.10/0.98      | ~ v7_waybel_0(X0)
% 3.10/0.98      | v2_struct_0(X0)
% 3.10/0.98      | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8) ),
% 3.10/0.98      inference(renaming,[status(thm)],[c_2377]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_2673,plain,
% 3.10/0.98      ( ~ r3_waybel_9(sK7,X0,k1_waybel_2(sK7,sK8))
% 3.10/0.98      | r3_waybel_9(sK7,X0,sK4(sK7,X0))
% 3.10/0.98      | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 3.10/0.98      | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
% 3.10/0.98      | ~ v4_orders_2(X0)
% 3.10/0.98      | ~ v7_waybel_0(X0)
% 3.10/0.98      | v2_struct_0(X0)
% 3.10/0.98      | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8)
% 3.10/0.98      | sK8 != X0
% 3.10/0.98      | sK7 != sK7 ),
% 3.10/0.98      inference(resolution_lifted,[status(thm)],[c_30,c_2378]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_2674,plain,
% 3.10/0.98      ( ~ r3_waybel_9(sK7,sK8,k1_waybel_2(sK7,sK8))
% 3.10/0.98      | r3_waybel_9(sK7,sK8,sK4(sK7,sK8))
% 3.10/0.98      | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 3.10/0.98      | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
% 3.10/0.98      | ~ v4_orders_2(sK8)
% 3.10/0.98      | ~ v7_waybel_0(sK8)
% 3.10/0.98      | v2_struct_0(sK8)
% 3.10/0.98      | k10_yellow_6(sK7,sK8) != k10_yellow_6(sK7,sK8) ),
% 3.10/0.98      inference(unflattening,[status(thm)],[c_2673]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_2676,plain,
% 3.10/0.98      ( ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
% 3.10/0.98      | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 3.10/0.98      | r3_waybel_9(sK7,sK8,sK4(sK7,sK8))
% 3.10/0.98      | ~ r3_waybel_9(sK7,sK8,k1_waybel_2(sK7,sK8))
% 3.10/0.98      | k10_yellow_6(sK7,sK8) != k10_yellow_6(sK7,sK8) ),
% 3.10/0.98      inference(global_propositional_subsumption,
% 3.10/0.98                [status(thm)],
% 3.10/0.98                [c_2674,c_33,c_32,c_31]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_2677,plain,
% 3.10/0.98      ( ~ r3_waybel_9(sK7,sK8,k1_waybel_2(sK7,sK8))
% 3.10/0.98      | r3_waybel_9(sK7,sK8,sK4(sK7,sK8))
% 3.10/0.98      | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 3.10/0.98      | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
% 3.10/0.98      | k10_yellow_6(sK7,sK8) != k10_yellow_6(sK7,sK8) ),
% 3.10/0.98      inference(renaming,[status(thm)],[c_2676]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_3697,plain,
% 3.10/0.98      ( ~ r3_waybel_9(sK7,sK8,k1_waybel_2(sK7,sK8))
% 3.10/0.98      | r3_waybel_9(sK7,sK8,sK4(sK7,sK8))
% 3.10/0.98      | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 3.10/0.98      | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7)) ),
% 3.10/0.98      inference(equality_resolution_simp,[status(thm)],[c_2677]) ).
% 3.10/0.98  
% 3.10/0.98  cnf(c_4598,plain,
% 3.10/0.98      ( ~ r3_waybel_9(sK7,sK8,k1_waybel_2(sK7,sK8))
% 3.10/0.98      | r3_waybel_9(sK7,sK8,sK4(sK7,sK8))
% 3.10/0.99      | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 3.10/0.99      | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7)) ),
% 3.10/0.99      inference(subtyping,[status(esa)],[c_3697]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_5138,plain,
% 3.10/0.99      ( r3_waybel_9(sK7,sK8,k1_waybel_2(sK7,sK8)) != iProver_top
% 3.10/0.99      | r3_waybel_9(sK7,sK8,sK4(sK7,sK8)) = iProver_top
% 3.10/0.99      | r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) != iProver_top
% 3.10/0.99      | m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7)) != iProver_top ),
% 3.10/0.99      inference(predicate_to_equality,[status(thm)],[c_4598]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_2618,plain,
% 3.10/0.99      ( r3_waybel_9(sK7,sK8,sK3(sK7,sK8)) = iProver_top
% 3.10/0.99      | v4_orders_2(sK8) != iProver_top
% 3.10/0.99      | v7_waybel_0(sK8) != iProver_top
% 3.10/0.99      | v2_struct_0(sK8) = iProver_top ),
% 3.10/0.99      inference(predicate_to_equality,[status(thm)],[c_2617]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_3698,plain,
% 3.10/0.99      ( r3_waybel_9(sK7,sK8,k1_waybel_2(sK7,sK8)) != iProver_top
% 3.10/0.99      | r3_waybel_9(sK7,sK8,sK4(sK7,sK8)) = iProver_top
% 3.10/0.99      | r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) != iProver_top
% 3.10/0.99      | m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7)) != iProver_top ),
% 3.10/0.99      inference(predicate_to_equality,[status(thm)],[c_3697]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_26,plain,
% 3.10/0.99      ( ~ v5_pre_topc(k4_waybel_1(X0,sK6(X0)),X0,X0)
% 3.10/0.99      | ~ r3_waybel_9(X0,X1,X2)
% 3.10/0.99      | ~ v10_waybel_0(X1,X0)
% 3.10/0.99      | ~ l1_waybel_0(X1,X0)
% 3.10/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.10/0.99      | ~ v2_pre_topc(X0)
% 3.10/0.99      | ~ v8_pre_topc(X0)
% 3.10/0.99      | ~ v2_lattice3(X0)
% 3.10/0.99      | ~ v1_compts_1(X0)
% 3.10/0.99      | ~ v4_orders_2(X0)
% 3.10/0.99      | ~ v4_orders_2(X1)
% 3.10/0.99      | ~ v7_waybel_0(X1)
% 3.10/0.99      | ~ l1_waybel_9(X0)
% 3.10/0.99      | ~ v5_orders_2(X0)
% 3.10/0.99      | ~ v1_lattice3(X0)
% 3.10/0.99      | v2_struct_0(X1)
% 3.10/0.99      | ~ v3_orders_2(X0)
% 3.10/0.99      | k1_waybel_2(X0,X1) = X2 ),
% 3.10/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_592,plain,
% 3.10/0.99      ( ~ r3_waybel_9(X0,X1,X2)
% 3.10/0.99      | ~ v10_waybel_0(X1,X0)
% 3.10/0.99      | ~ l1_waybel_0(X1,X0)
% 3.10/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.10/0.99      | ~ m1_subset_1(X3,u1_struct_0(sK7))
% 3.10/0.99      | ~ v2_pre_topc(X0)
% 3.10/0.99      | ~ v8_pre_topc(X0)
% 3.10/0.99      | ~ v2_lattice3(X0)
% 3.10/0.99      | ~ v1_compts_1(X0)
% 3.10/0.99      | ~ v4_orders_2(X1)
% 3.10/0.99      | ~ v4_orders_2(X0)
% 3.10/0.99      | ~ v7_waybel_0(X1)
% 3.10/0.99      | ~ l1_waybel_9(X0)
% 3.10/0.99      | ~ v5_orders_2(X0)
% 3.10/0.99      | ~ v1_lattice3(X0)
% 3.10/0.99      | v2_struct_0(X1)
% 3.10/0.99      | ~ v3_orders_2(X0)
% 3.10/0.99      | k1_waybel_2(X0,X1) = X2
% 3.10/0.99      | k4_waybel_1(X0,sK6(X0)) != k4_waybel_1(sK7,X3)
% 3.10/0.99      | sK7 != X0 ),
% 3.10/0.99      inference(resolution_lifted,[status(thm)],[c_26,c_34]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_593,plain,
% 3.10/0.99      ( ~ r3_waybel_9(sK7,X0,X1)
% 3.10/0.99      | ~ v10_waybel_0(X0,sK7)
% 3.10/0.99      | ~ l1_waybel_0(X0,sK7)
% 3.10/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.10/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 3.10/0.99      | ~ v2_pre_topc(sK7)
% 3.10/0.99      | ~ v8_pre_topc(sK7)
% 3.10/0.99      | ~ v2_lattice3(sK7)
% 3.10/0.99      | ~ v1_compts_1(sK7)
% 3.10/0.99      | ~ v4_orders_2(X0)
% 3.10/0.99      | ~ v4_orders_2(sK7)
% 3.10/0.99      | ~ v7_waybel_0(X0)
% 3.10/0.99      | ~ l1_waybel_9(sK7)
% 3.10/0.99      | ~ v5_orders_2(sK7)
% 3.10/0.99      | ~ v1_lattice3(sK7)
% 3.10/0.99      | v2_struct_0(X0)
% 3.10/0.99      | ~ v3_orders_2(sK7)
% 3.10/0.99      | k1_waybel_2(sK7,X0) = X1
% 3.10/0.99      | k4_waybel_1(sK7,sK6(sK7)) != k4_waybel_1(sK7,X2) ),
% 3.10/0.99      inference(unflattening,[status(thm)],[c_592]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_597,plain,
% 3.10/0.99      ( v2_struct_0(X0)
% 3.10/0.99      | ~ v4_orders_2(X0)
% 3.10/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 3.10/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.10/0.99      | ~ l1_waybel_0(X0,sK7)
% 3.10/0.99      | ~ v10_waybel_0(X0,sK7)
% 3.10/0.99      | ~ r3_waybel_9(sK7,X0,X1)
% 3.10/0.99      | ~ v7_waybel_0(X0)
% 3.10/0.99      | k1_waybel_2(sK7,X0) = X1
% 3.10/0.99      | k4_waybel_1(sK7,sK6(sK7)) != k4_waybel_1(sK7,X2) ),
% 3.10/0.99      inference(global_propositional_subsumption,
% 3.10/0.99                [status(thm)],
% 3.10/0.99                [c_593,c_43,c_42,c_41,c_40,c_39,c_38,c_37,c_36,c_35]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_598,plain,
% 3.10/0.99      ( ~ r3_waybel_9(sK7,X0,X1)
% 3.10/0.99      | ~ v10_waybel_0(X0,sK7)
% 3.10/0.99      | ~ l1_waybel_0(X0,sK7)
% 3.10/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 3.10/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.10/0.99      | ~ v4_orders_2(X0)
% 3.10/0.99      | ~ v7_waybel_0(X0)
% 3.10/0.99      | v2_struct_0(X0)
% 3.10/0.99      | k1_waybel_2(sK7,X0) = X1
% 3.10/0.99      | k4_waybel_1(sK7,sK6(sK7)) != k4_waybel_1(sK7,X2) ),
% 3.10/0.99      inference(renaming,[status(thm)],[c_597]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_1244,plain,
% 3.10/0.99      ( ~ r3_waybel_9(sK7,X0,X1)
% 3.10/0.99      | ~ l1_waybel_0(X0,sK7)
% 3.10/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 3.10/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.10/0.99      | ~ v4_orders_2(X0)
% 3.10/0.99      | ~ v7_waybel_0(X0)
% 3.10/0.99      | v2_struct_0(X0)
% 3.10/0.99      | k1_waybel_2(sK7,X0) = X1
% 3.10/0.99      | k4_waybel_1(sK7,sK6(sK7)) != k4_waybel_1(sK7,X2)
% 3.10/0.99      | sK8 != X0
% 3.10/0.99      | sK7 != sK7 ),
% 3.10/0.99      inference(resolution_lifted,[status(thm)],[c_29,c_598]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_1245,plain,
% 3.10/0.99      ( ~ r3_waybel_9(sK7,sK8,X0)
% 3.10/0.99      | ~ l1_waybel_0(sK8,sK7)
% 3.10/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.10/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.10/0.99      | ~ v4_orders_2(sK8)
% 3.10/0.99      | ~ v7_waybel_0(sK8)
% 3.10/0.99      | v2_struct_0(sK8)
% 3.10/0.99      | k1_waybel_2(sK7,sK8) = X0
% 3.10/0.99      | k4_waybel_1(sK7,sK6(sK7)) != k4_waybel_1(sK7,X1) ),
% 3.10/0.99      inference(unflattening,[status(thm)],[c_1244]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_1249,plain,
% 3.10/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.10/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.10/0.99      | ~ r3_waybel_9(sK7,sK8,X0)
% 3.10/0.99      | k1_waybel_2(sK7,sK8) = X0
% 3.10/0.99      | k4_waybel_1(sK7,sK6(sK7)) != k4_waybel_1(sK7,X1) ),
% 3.10/0.99      inference(global_propositional_subsumption,
% 3.10/0.99                [status(thm)],
% 3.10/0.99                [c_1245,c_33,c_32,c_31,c_30]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_1250,plain,
% 3.10/0.99      ( ~ r3_waybel_9(sK7,sK8,X0)
% 3.10/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.10/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.10/0.99      | k1_waybel_2(sK7,sK8) = X0
% 3.10/0.99      | k4_waybel_1(sK7,sK6(sK7)) != k4_waybel_1(sK7,X1) ),
% 3.10/0.99      inference(renaming,[status(thm)],[c_1249]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_4614,plain,
% 3.10/0.99      ( ~ r3_waybel_9(sK7,sK8,X0_69)
% 3.10/0.99      | ~ m1_subset_1(X0_69,u1_struct_0(sK7))
% 3.10/0.99      | ~ m1_subset_1(X1_69,u1_struct_0(sK7))
% 3.10/0.99      | k4_waybel_1(sK7,sK6(sK7)) != k4_waybel_1(sK7,X1_69)
% 3.10/0.99      | k1_waybel_2(sK7,sK8) = X0_69 ),
% 3.10/0.99      inference(subtyping,[status(esa)],[c_1250]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_4618,plain,
% 3.10/0.99      ( ~ r3_waybel_9(sK7,sK8,X0_69)
% 3.10/0.99      | ~ m1_subset_1(X0_69,u1_struct_0(sK7))
% 3.10/0.99      | k1_waybel_2(sK7,sK8) = X0_69
% 3.10/0.99      | ~ sP1_iProver_split ),
% 3.10/0.99      inference(splitting,
% 3.10/0.99                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 3.10/0.99                [c_4614]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_5117,plain,
% 3.10/0.99      ( k1_waybel_2(sK7,sK8) = X0_69
% 3.10/0.99      | r3_waybel_9(sK7,sK8,X0_69) != iProver_top
% 3.10/0.99      | m1_subset_1(X0_69,u1_struct_0(sK7)) != iProver_top
% 3.10/0.99      | sP1_iProver_split != iProver_top ),
% 3.10/0.99      inference(predicate_to_equality,[status(thm)],[c_4618]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_27,plain,
% 3.10/0.99      ( ~ r3_waybel_9(X0,X1,X2)
% 3.10/0.99      | ~ v10_waybel_0(X1,X0)
% 3.10/0.99      | ~ l1_waybel_0(X1,X0)
% 3.10/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.10/0.99      | m1_subset_1(sK6(X0),u1_struct_0(X0))
% 3.10/0.99      | ~ v2_pre_topc(X0)
% 3.10/0.99      | ~ v8_pre_topc(X0)
% 3.10/0.99      | ~ v2_lattice3(X0)
% 3.10/0.99      | ~ v1_compts_1(X0)
% 3.10/0.99      | ~ v4_orders_2(X0)
% 3.10/0.99      | ~ v4_orders_2(X1)
% 3.10/0.99      | ~ v7_waybel_0(X1)
% 3.10/0.99      | ~ l1_waybel_9(X0)
% 3.10/0.99      | ~ v5_orders_2(X0)
% 3.10/0.99      | ~ v1_lattice3(X0)
% 3.10/0.99      | v2_struct_0(X1)
% 3.10/0.99      | ~ v3_orders_2(X0)
% 3.10/0.99      | k1_waybel_2(X0,X1) = X2 ),
% 3.10/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_1074,plain,
% 3.10/0.99      ( ~ r3_waybel_9(X0,X1,X2)
% 3.10/0.99      | ~ v10_waybel_0(X1,X0)
% 3.10/0.99      | ~ l1_waybel_0(X1,X0)
% 3.10/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.10/0.99      | m1_subset_1(sK6(X0),u1_struct_0(X0))
% 3.10/0.99      | ~ v2_pre_topc(X0)
% 3.10/0.99      | ~ v8_pre_topc(X0)
% 3.10/0.99      | ~ v2_lattice3(X0)
% 3.10/0.99      | ~ v1_compts_1(X0)
% 3.10/0.99      | ~ v4_orders_2(X1)
% 3.10/0.99      | ~ v4_orders_2(X0)
% 3.10/0.99      | ~ v7_waybel_0(X1)
% 3.10/0.99      | ~ l1_waybel_9(X0)
% 3.10/0.99      | ~ v5_orders_2(X0)
% 3.10/0.99      | ~ v1_lattice3(X0)
% 3.10/0.99      | v2_struct_0(X1)
% 3.10/0.99      | k1_waybel_2(X0,X1) = X2
% 3.10/0.99      | sK7 != X0 ),
% 3.10/0.99      inference(resolution_lifted,[status(thm)],[c_27,c_41]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_1075,plain,
% 3.10/0.99      ( ~ r3_waybel_9(sK7,X0,X1)
% 3.10/0.99      | ~ v10_waybel_0(X0,sK7)
% 3.10/0.99      | ~ l1_waybel_0(X0,sK7)
% 3.10/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.10/0.99      | m1_subset_1(sK6(sK7),u1_struct_0(sK7))
% 3.10/0.99      | ~ v2_pre_topc(sK7)
% 3.10/0.99      | ~ v8_pre_topc(sK7)
% 3.10/0.99      | ~ v2_lattice3(sK7)
% 3.10/0.99      | ~ v1_compts_1(sK7)
% 3.10/0.99      | ~ v4_orders_2(X0)
% 3.10/0.99      | ~ v4_orders_2(sK7)
% 3.10/0.99      | ~ v7_waybel_0(X0)
% 3.10/0.99      | ~ l1_waybel_9(sK7)
% 3.10/0.99      | ~ v5_orders_2(sK7)
% 3.10/0.99      | ~ v1_lattice3(sK7)
% 3.10/0.99      | v2_struct_0(X0)
% 3.10/0.99      | k1_waybel_2(sK7,X0) = X1 ),
% 3.10/0.99      inference(unflattening,[status(thm)],[c_1074]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_1079,plain,
% 3.10/0.99      ( ~ v7_waybel_0(X0)
% 3.10/0.99      | ~ r3_waybel_9(sK7,X0,X1)
% 3.10/0.99      | ~ v10_waybel_0(X0,sK7)
% 3.10/0.99      | ~ l1_waybel_0(X0,sK7)
% 3.10/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.10/0.99      | m1_subset_1(sK6(sK7),u1_struct_0(sK7))
% 3.10/0.99      | ~ v4_orders_2(X0)
% 3.10/0.99      | v2_struct_0(X0)
% 3.10/0.99      | k1_waybel_2(sK7,X0) = X1 ),
% 3.10/0.99      inference(global_propositional_subsumption,
% 3.10/0.99                [status(thm)],
% 3.10/0.99                [c_1075,c_43,c_42,c_40,c_39,c_38,c_37,c_36,c_35]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_1080,plain,
% 3.10/0.99      ( ~ r3_waybel_9(sK7,X0,X1)
% 3.10/0.99      | ~ v10_waybel_0(X0,sK7)
% 3.10/0.99      | ~ l1_waybel_0(X0,sK7)
% 3.10/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.10/0.99      | m1_subset_1(sK6(sK7),u1_struct_0(sK7))
% 3.10/0.99      | ~ v4_orders_2(X0)
% 3.10/0.99      | ~ v7_waybel_0(X0)
% 3.10/0.99      | v2_struct_0(X0)
% 3.10/0.99      | k1_waybel_2(sK7,X0) = X1 ),
% 3.10/0.99      inference(renaming,[status(thm)],[c_1079]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_1220,plain,
% 3.10/0.99      ( ~ r3_waybel_9(sK7,X0,X1)
% 3.10/0.99      | ~ l1_waybel_0(X0,sK7)
% 3.10/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.10/0.99      | m1_subset_1(sK6(sK7),u1_struct_0(sK7))
% 3.10/0.99      | ~ v4_orders_2(X0)
% 3.10/0.99      | ~ v7_waybel_0(X0)
% 3.10/0.99      | v2_struct_0(X0)
% 3.10/0.99      | k1_waybel_2(sK7,X0) = X1
% 3.10/0.99      | sK8 != X0
% 3.10/0.99      | sK7 != sK7 ),
% 3.10/0.99      inference(resolution_lifted,[status(thm)],[c_29,c_1080]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_1221,plain,
% 3.10/0.99      ( ~ r3_waybel_9(sK7,sK8,X0)
% 3.10/0.99      | ~ l1_waybel_0(sK8,sK7)
% 3.10/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.10/0.99      | m1_subset_1(sK6(sK7),u1_struct_0(sK7))
% 3.10/0.99      | ~ v4_orders_2(sK8)
% 3.10/0.99      | ~ v7_waybel_0(sK8)
% 3.10/0.99      | v2_struct_0(sK8)
% 3.10/0.99      | k1_waybel_2(sK7,sK8) = X0 ),
% 3.10/0.99      inference(unflattening,[status(thm)],[c_1220]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_1225,plain,
% 3.10/0.99      ( m1_subset_1(sK6(sK7),u1_struct_0(sK7))
% 3.10/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.10/0.99      | ~ r3_waybel_9(sK7,sK8,X0)
% 3.10/0.99      | k1_waybel_2(sK7,sK8) = X0 ),
% 3.10/0.99      inference(global_propositional_subsumption,
% 3.10/0.99                [status(thm)],
% 3.10/0.99                [c_1221,c_33,c_32,c_31,c_30]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_1226,plain,
% 3.10/0.99      ( ~ r3_waybel_9(sK7,sK8,X0)
% 3.10/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.10/0.99      | m1_subset_1(sK6(sK7),u1_struct_0(sK7))
% 3.10/0.99      | k1_waybel_2(sK7,sK8) = X0 ),
% 3.10/0.99      inference(renaming,[status(thm)],[c_1225]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_4615,plain,
% 3.10/0.99      ( ~ r3_waybel_9(sK7,sK8,X0_69)
% 3.10/0.99      | ~ m1_subset_1(X0_69,u1_struct_0(sK7))
% 3.10/0.99      | m1_subset_1(sK6(sK7),u1_struct_0(sK7))
% 3.10/0.99      | k1_waybel_2(sK7,sK8) = X0_69 ),
% 3.10/0.99      inference(subtyping,[status(esa)],[c_1226]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_4647,plain,
% 3.10/0.99      ( k1_waybel_2(sK7,sK8) = X0_69
% 3.10/0.99      | r3_waybel_9(sK7,sK8,X0_69) != iProver_top
% 3.10/0.99      | m1_subset_1(X0_69,u1_struct_0(sK7)) != iProver_top
% 3.10/0.99      | m1_subset_1(sK6(sK7),u1_struct_0(sK7)) = iProver_top ),
% 3.10/0.99      inference(predicate_to_equality,[status(thm)],[c_4615]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_4619,plain,
% 3.10/0.99      ( sP1_iProver_split | sP0_iProver_split ),
% 3.10/0.99      inference(splitting,
% 3.10/0.99                [splitting(split),new_symbols(definition,[])],
% 3.10/0.99                [c_4614]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_4650,plain,
% 3.10/0.99      ( sP1_iProver_split = iProver_top
% 3.10/0.99      | sP0_iProver_split = iProver_top ),
% 3.10/0.99      inference(predicate_to_equality,[status(thm)],[c_4619]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_4651,plain,
% 3.10/0.99      ( k1_waybel_2(sK7,sK8) = X0_69
% 3.10/0.99      | r3_waybel_9(sK7,sK8,X0_69) != iProver_top
% 3.10/0.99      | m1_subset_1(X0_69,u1_struct_0(sK7)) != iProver_top
% 3.10/0.99      | sP1_iProver_split != iProver_top ),
% 3.10/0.99      inference(predicate_to_equality,[status(thm)],[c_4618]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_4617,plain,
% 3.10/0.99      ( ~ m1_subset_1(X0_69,u1_struct_0(sK7))
% 3.10/0.99      | k4_waybel_1(sK7,sK6(sK7)) != k4_waybel_1(sK7,X0_69)
% 3.10/0.99      | ~ sP0_iProver_split ),
% 3.10/0.99      inference(splitting,
% 3.10/0.99                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 3.10/0.99                [c_4614]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_5118,plain,
% 3.10/0.99      ( k4_waybel_1(sK7,sK6(sK7)) != k4_waybel_1(sK7,X0_69)
% 3.10/0.99      | m1_subset_1(X0_69,u1_struct_0(sK7)) != iProver_top
% 3.10/0.99      | sP0_iProver_split != iProver_top ),
% 3.10/0.99      inference(predicate_to_equality,[status(thm)],[c_4617]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_5413,plain,
% 3.10/0.99      ( m1_subset_1(sK6(sK7),u1_struct_0(sK7)) != iProver_top
% 3.10/0.99      | sP0_iProver_split != iProver_top ),
% 3.10/0.99      inference(equality_resolution,[status(thm)],[c_5118]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_5487,plain,
% 3.10/0.99      ( m1_subset_1(X0_69,u1_struct_0(sK7)) != iProver_top
% 3.10/0.99      | r3_waybel_9(sK7,sK8,X0_69) != iProver_top
% 3.10/0.99      | k1_waybel_2(sK7,sK8) = X0_69 ),
% 3.10/0.99      inference(global_propositional_subsumption,
% 3.10/0.99                [status(thm)],
% 3.10/0.99                [c_5117,c_4647,c_4650,c_4651,c_5413]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_5488,plain,
% 3.10/0.99      ( k1_waybel_2(sK7,sK8) = X0_69
% 3.10/0.99      | r3_waybel_9(sK7,sK8,X0_69) != iProver_top
% 3.10/0.99      | m1_subset_1(X0_69,u1_struct_0(sK7)) != iProver_top ),
% 3.10/0.99      inference(renaming,[status(thm)],[c_5487]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_5496,plain,
% 3.10/0.99      ( k1_waybel_2(sK7,sK8) = sK3(sK7,sK8)
% 3.10/0.99      | m1_subset_1(sK3(sK7,sK8),u1_struct_0(sK7)) != iProver_top ),
% 3.10/0.99      inference(superposition,[status(thm)],[c_5131,c_5488]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_4632,plain,
% 3.10/0.99      ( ~ m1_subset_1(X0_69,X0_71)
% 3.10/0.99      | m1_subset_1(X1_69,X0_71)
% 3.10/0.99      | X1_69 != X0_69 ),
% 3.10/0.99      theory(equality) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_5436,plain,
% 3.10/0.99      ( m1_subset_1(X0_69,u1_struct_0(sK7))
% 3.10/0.99      | ~ m1_subset_1(sK3(sK7,sK8),u1_struct_0(sK7))
% 3.10/0.99      | X0_69 != sK3(sK7,sK8) ),
% 3.10/0.99      inference(instantiation,[status(thm)],[c_4632]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_5507,plain,
% 3.10/0.99      ( m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
% 3.10/0.99      | ~ m1_subset_1(sK3(sK7,sK8),u1_struct_0(sK7))
% 3.10/0.99      | k1_waybel_2(sK7,sK8) != sK3(sK7,sK8) ),
% 3.10/0.99      inference(instantiation,[status(thm)],[c_5436]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_5508,plain,
% 3.10/0.99      ( k1_waybel_2(sK7,sK8) != sK3(sK7,sK8)
% 3.10/0.99      | m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7)) = iProver_top
% 3.10/0.99      | m1_subset_1(sK3(sK7,sK8),u1_struct_0(sK7)) != iProver_top ),
% 3.10/0.99      inference(predicate_to_equality,[status(thm)],[c_5507]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_4634,plain,
% 3.10/0.99      ( ~ r3_waybel_9(X0_68,X1_68,X0_69)
% 3.10/0.99      | r3_waybel_9(X0_68,X1_68,X1_69)
% 3.10/0.99      | X1_69 != X0_69 ),
% 3.10/0.99      theory(equality) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_5476,plain,
% 3.10/0.99      ( r3_waybel_9(sK7,sK8,X0_69)
% 3.10/0.99      | ~ r3_waybel_9(sK7,sK8,sK3(sK7,sK8))
% 3.10/0.99      | X0_69 != sK3(sK7,sK8) ),
% 3.10/0.99      inference(instantiation,[status(thm)],[c_4634]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_5512,plain,
% 3.10/0.99      ( r3_waybel_9(sK7,sK8,k1_waybel_2(sK7,sK8))
% 3.10/0.99      | ~ r3_waybel_9(sK7,sK8,sK3(sK7,sK8))
% 3.10/0.99      | k1_waybel_2(sK7,sK8) != sK3(sK7,sK8) ),
% 3.10/0.99      inference(instantiation,[status(thm)],[c_5476]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_5513,plain,
% 3.10/0.99      ( k1_waybel_2(sK7,sK8) != sK3(sK7,sK8)
% 3.10/0.99      | r3_waybel_9(sK7,sK8,k1_waybel_2(sK7,sK8)) = iProver_top
% 3.10/0.99      | r3_waybel_9(sK7,sK8,sK3(sK7,sK8)) != iProver_top ),
% 3.10/0.99      inference(predicate_to_equality,[status(thm)],[c_5512]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_6269,plain,
% 3.10/0.99      ( r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) != iProver_top
% 3.10/0.99      | r3_waybel_9(sK7,sK8,sK4(sK7,sK8)) = iProver_top ),
% 3.10/0.99      inference(global_propositional_subsumption,
% 3.10/0.99                [status(thm)],
% 3.10/0.99                [c_5138,c_56,c_57,c_58,c_2607,c_2618,c_3698,c_5496,
% 3.10/0.99                 c_5508,c_5513]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_6270,plain,
% 3.10/0.99      ( r3_waybel_9(sK7,sK8,sK4(sK7,sK8)) = iProver_top
% 3.10/0.99      | r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) != iProver_top ),
% 3.10/0.99      inference(renaming,[status(thm)],[c_6269]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_6659,plain,
% 3.10/0.99      ( r3_waybel_9(sK7,sK8,sK4(sK7,sK8)) = iProver_top ),
% 3.10/0.99      inference(superposition,[status(thm)],[c_6652,c_6270]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_5547,plain,
% 3.10/0.99      ( k1_waybel_2(sK7,sK8) = sK3(sK7,sK8) ),
% 3.10/0.99      inference(global_propositional_subsumption,
% 3.10/0.99                [status(thm)],
% 3.10/0.99                [c_5496,c_56,c_57,c_58,c_2607]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_5550,plain,
% 3.10/0.99      ( sK3(sK7,sK8) = X0_69
% 3.10/0.99      | r3_waybel_9(sK7,sK8,X0_69) != iProver_top
% 3.10/0.99      | m1_subset_1(X0_69,u1_struct_0(sK7)) != iProver_top ),
% 3.10/0.99      inference(demodulation,[status(thm)],[c_5547,c_5488]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_6946,plain,
% 3.10/0.99      ( sK4(sK7,sK8) = sK3(sK7,sK8)
% 3.10/0.99      | m1_subset_1(sK4(sK7,sK8),u1_struct_0(sK7)) != iProver_top ),
% 3.10/0.99      inference(superposition,[status(thm)],[c_6659,c_5550]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_25,plain,
% 3.10/0.99      ( ~ r3_waybel_9(X0,X1,X2)
% 3.10/0.99      | r2_hidden(X2,k10_yellow_6(X0,X1))
% 3.10/0.99      | ~ l1_waybel_0(X1,X0)
% 3.10/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.10/0.99      | m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
% 3.10/0.99      | ~ v2_pre_topc(X0)
% 3.10/0.99      | ~ v8_pre_topc(X0)
% 3.10/0.99      | ~ v1_compts_1(X0)
% 3.10/0.99      | ~ v4_orders_2(X1)
% 3.10/0.99      | ~ v7_waybel_0(X1)
% 3.10/0.99      | ~ l1_pre_topc(X0)
% 3.10/0.99      | v2_struct_0(X0)
% 3.10/0.99      | v2_struct_0(X1) ),
% 3.10/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_2049,plain,
% 3.10/0.99      ( ~ r3_waybel_9(X0,X1,X2)
% 3.10/0.99      | ~ l1_waybel_0(X1,X0)
% 3.10/0.99      | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 3.10/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.10/0.99      | m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
% 3.10/0.99      | ~ v2_pre_topc(X0)
% 3.10/0.99      | ~ v8_pre_topc(X0)
% 3.10/0.99      | ~ v1_compts_1(X0)
% 3.10/0.99      | ~ v4_orders_2(X1)
% 3.10/0.99      | ~ v7_waybel_0(X1)
% 3.10/0.99      | ~ l1_pre_topc(X0)
% 3.10/0.99      | v2_struct_0(X0)
% 3.10/0.99      | v2_struct_0(X1)
% 3.10/0.99      | k1_waybel_2(sK7,sK8) != X2
% 3.10/0.99      | k10_yellow_6(X0,X1) != k10_yellow_6(sK7,sK8) ),
% 3.10/0.99      inference(resolution_lifted,[status(thm)],[c_25,c_492]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_2050,plain,
% 3.10/0.99      ( ~ r3_waybel_9(X0,X1,k1_waybel_2(sK7,sK8))
% 3.10/0.99      | ~ l1_waybel_0(X1,X0)
% 3.10/0.99      | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 3.10/0.99      | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(X0))
% 3.10/0.99      | m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
% 3.10/0.99      | ~ v2_pre_topc(X0)
% 3.10/0.99      | ~ v8_pre_topc(X0)
% 3.10/0.99      | ~ v1_compts_1(X0)
% 3.10/0.99      | ~ v4_orders_2(X1)
% 3.10/0.99      | ~ v7_waybel_0(X1)
% 3.10/0.99      | ~ l1_pre_topc(X0)
% 3.10/0.99      | v2_struct_0(X0)
% 3.10/0.99      | v2_struct_0(X1)
% 3.10/0.99      | k10_yellow_6(X0,X1) != k10_yellow_6(sK7,sK8) ),
% 3.10/0.99      inference(unflattening,[status(thm)],[c_2049]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_2450,plain,
% 3.10/0.99      ( ~ r3_waybel_9(X0,X1,k1_waybel_2(sK7,sK8))
% 3.10/0.99      | ~ l1_waybel_0(X1,X0)
% 3.10/0.99      | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 3.10/0.99      | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(X0))
% 3.10/0.99      | m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
% 3.10/0.99      | ~ v2_pre_topc(X0)
% 3.10/0.99      | ~ v8_pre_topc(X0)
% 3.10/0.99      | ~ v1_compts_1(X0)
% 3.10/0.99      | ~ v4_orders_2(X1)
% 3.10/0.99      | ~ v7_waybel_0(X1)
% 3.10/0.99      | v2_struct_0(X0)
% 3.10/0.99      | v2_struct_0(X1)
% 3.10/0.99      | k10_yellow_6(X0,X1) != k10_yellow_6(sK7,sK8)
% 3.10/0.99      | sK7 != X0 ),
% 3.10/0.99      inference(resolution_lifted,[status(thm)],[c_2050,c_1553]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_2451,plain,
% 3.10/0.99      ( ~ r3_waybel_9(sK7,X0,k1_waybel_2(sK7,sK8))
% 3.10/0.99      | ~ l1_waybel_0(X0,sK7)
% 3.10/0.99      | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 3.10/0.99      | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
% 3.10/0.99      | m1_subset_1(sK4(sK7,X0),u1_struct_0(sK7))
% 3.10/0.99      | ~ v2_pre_topc(sK7)
% 3.10/0.99      | ~ v8_pre_topc(sK7)
% 3.10/0.99      | ~ v1_compts_1(sK7)
% 3.10/0.99      | ~ v4_orders_2(X0)
% 3.10/0.99      | ~ v7_waybel_0(X0)
% 3.10/0.99      | v2_struct_0(X0)
% 3.10/0.99      | v2_struct_0(sK7)
% 3.10/0.99      | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8) ),
% 3.10/0.99      inference(unflattening,[status(thm)],[c_2450]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_2455,plain,
% 3.10/0.99      ( v2_struct_0(X0)
% 3.10/0.99      | ~ v7_waybel_0(X0)
% 3.10/0.99      | ~ v4_orders_2(X0)
% 3.10/0.99      | ~ r3_waybel_9(sK7,X0,k1_waybel_2(sK7,sK8))
% 3.10/0.99      | ~ l1_waybel_0(X0,sK7)
% 3.10/0.99      | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 3.10/0.99      | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
% 3.10/0.99      | m1_subset_1(sK4(sK7,X0),u1_struct_0(sK7))
% 3.10/0.99      | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8) ),
% 3.10/0.99      inference(global_propositional_subsumption,
% 3.10/0.99                [status(thm)],
% 3.10/0.99                [c_2451,c_43,c_42,c_38,c_36,c_35,c_105,c_138]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_2456,plain,
% 3.10/0.99      ( ~ r3_waybel_9(sK7,X0,k1_waybel_2(sK7,sK8))
% 3.10/0.99      | ~ l1_waybel_0(X0,sK7)
% 3.10/0.99      | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 3.10/0.99      | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
% 3.10/0.99      | m1_subset_1(sK4(sK7,X0),u1_struct_0(sK7))
% 3.10/0.99      | ~ v4_orders_2(X0)
% 3.10/0.99      | ~ v7_waybel_0(X0)
% 3.10/0.99      | v2_struct_0(X0)
% 3.10/0.99      | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8) ),
% 3.10/0.99      inference(renaming,[status(thm)],[c_2455]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_2627,plain,
% 3.10/0.99      ( ~ r3_waybel_9(sK7,X0,k1_waybel_2(sK7,sK8))
% 3.10/0.99      | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 3.10/0.99      | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
% 3.10/0.99      | m1_subset_1(sK4(sK7,X0),u1_struct_0(sK7))
% 3.10/0.99      | ~ v4_orders_2(X0)
% 3.10/0.99      | ~ v7_waybel_0(X0)
% 3.10/0.99      | v2_struct_0(X0)
% 3.10/0.99      | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8)
% 3.10/0.99      | sK8 != X0
% 3.10/0.99      | sK7 != sK7 ),
% 3.10/0.99      inference(resolution_lifted,[status(thm)],[c_30,c_2456]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_2628,plain,
% 3.10/0.99      ( ~ r3_waybel_9(sK7,sK8,k1_waybel_2(sK7,sK8))
% 3.10/0.99      | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 3.10/0.99      | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
% 3.10/0.99      | m1_subset_1(sK4(sK7,sK8),u1_struct_0(sK7))
% 3.10/0.99      | ~ v4_orders_2(sK8)
% 3.10/0.99      | ~ v7_waybel_0(sK8)
% 3.10/0.99      | v2_struct_0(sK8)
% 3.10/0.99      | k10_yellow_6(sK7,sK8) != k10_yellow_6(sK7,sK8) ),
% 3.10/0.99      inference(unflattening,[status(thm)],[c_2627]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_2630,plain,
% 3.10/0.99      ( m1_subset_1(sK4(sK7,sK8),u1_struct_0(sK7))
% 3.10/0.99      | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
% 3.10/0.99      | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 3.10/0.99      | ~ r3_waybel_9(sK7,sK8,k1_waybel_2(sK7,sK8))
% 3.10/0.99      | k10_yellow_6(sK7,sK8) != k10_yellow_6(sK7,sK8) ),
% 3.10/0.99      inference(global_propositional_subsumption,
% 3.10/0.99                [status(thm)],
% 3.10/0.99                [c_2628,c_33,c_32,c_31]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_2631,plain,
% 3.10/0.99      ( ~ r3_waybel_9(sK7,sK8,k1_waybel_2(sK7,sK8))
% 3.10/0.99      | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 3.10/0.99      | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
% 3.10/0.99      | m1_subset_1(sK4(sK7,sK8),u1_struct_0(sK7))
% 3.10/0.99      | k10_yellow_6(sK7,sK8) != k10_yellow_6(sK7,sK8) ),
% 3.10/0.99      inference(renaming,[status(thm)],[c_2630]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_3701,plain,
% 3.10/0.99      ( ~ r3_waybel_9(sK7,sK8,k1_waybel_2(sK7,sK8))
% 3.10/0.99      | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 3.10/0.99      | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
% 3.10/0.99      | m1_subset_1(sK4(sK7,sK8),u1_struct_0(sK7)) ),
% 3.10/0.99      inference(equality_resolution_simp,[status(thm)],[c_2631]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_3702,plain,
% 3.10/0.99      ( r3_waybel_9(sK7,sK8,k1_waybel_2(sK7,sK8)) != iProver_top
% 3.10/0.99      | r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) != iProver_top
% 3.10/0.99      | m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7)) != iProver_top
% 3.10/0.99      | m1_subset_1(sK4(sK7,sK8),u1_struct_0(sK7)) = iProver_top ),
% 3.10/0.99      inference(predicate_to_equality,[status(thm)],[c_3701]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_7261,plain,
% 3.10/0.99      ( sK4(sK7,sK8) = sK3(sK7,sK8) ),
% 3.10/0.99      inference(global_propositional_subsumption,
% 3.10/0.99                [status(thm)],
% 3.10/0.99                [c_6946,c_56,c_57,c_58,c_2607,c_2618,c_3702,c_5496,
% 3.10/0.99                 c_5508,c_5513,c_6649]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_21,plain,
% 3.10/0.99      ( ~ r3_waybel_9(X0,X1,X2)
% 3.10/0.99      | r2_hidden(X2,k10_yellow_6(X0,X1))
% 3.10/0.99      | ~ l1_waybel_0(X1,X0)
% 3.10/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.10/0.99      | ~ v2_pre_topc(X0)
% 3.10/0.99      | ~ v8_pre_topc(X0)
% 3.10/0.99      | ~ v1_compts_1(X0)
% 3.10/0.99      | ~ v4_orders_2(X1)
% 3.10/0.99      | ~ v7_waybel_0(X1)
% 3.10/0.99      | ~ l1_pre_topc(X0)
% 3.10/0.99      | v2_struct_0(X0)
% 3.10/0.99      | v2_struct_0(X1)
% 3.10/0.99      | sK5(X0,X1) != sK4(X0,X1) ),
% 3.10/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_2241,plain,
% 3.10/0.99      ( ~ r3_waybel_9(X0,X1,X2)
% 3.10/0.99      | ~ l1_waybel_0(X1,X0)
% 3.10/0.99      | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 3.10/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.10/0.99      | ~ v2_pre_topc(X0)
% 3.10/0.99      | ~ v8_pre_topc(X0)
% 3.10/0.99      | ~ v1_compts_1(X0)
% 3.10/0.99      | ~ v4_orders_2(X1)
% 3.10/0.99      | ~ v7_waybel_0(X1)
% 3.10/0.99      | ~ l1_pre_topc(X0)
% 3.10/0.99      | v2_struct_0(X0)
% 3.10/0.99      | v2_struct_0(X1)
% 3.10/0.99      | k1_waybel_2(sK7,sK8) != X2
% 3.10/0.99      | sK5(X0,X1) != sK4(X0,X1)
% 3.10/0.99      | k10_yellow_6(X0,X1) != k10_yellow_6(sK7,sK8) ),
% 3.10/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_492]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_2242,plain,
% 3.10/0.99      ( ~ r3_waybel_9(X0,X1,k1_waybel_2(sK7,sK8))
% 3.10/0.99      | ~ l1_waybel_0(X1,X0)
% 3.10/0.99      | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 3.10/0.99      | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(X0))
% 3.10/0.99      | ~ v2_pre_topc(X0)
% 3.10/0.99      | ~ v8_pre_topc(X0)
% 3.10/0.99      | ~ v1_compts_1(X0)
% 3.10/0.99      | ~ v4_orders_2(X1)
% 3.10/0.99      | ~ v7_waybel_0(X1)
% 3.10/0.99      | ~ l1_pre_topc(X0)
% 3.10/0.99      | v2_struct_0(X0)
% 3.10/0.99      | v2_struct_0(X1)
% 3.10/0.99      | sK5(X0,X1) != sK4(X0,X1)
% 3.10/0.99      | k10_yellow_6(X0,X1) != k10_yellow_6(sK7,sK8) ),
% 3.10/0.99      inference(unflattening,[status(thm)],[c_2241]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_2294,plain,
% 3.10/0.99      ( ~ r3_waybel_9(X0,X1,k1_waybel_2(sK7,sK8))
% 3.10/0.99      | ~ l1_waybel_0(X1,X0)
% 3.10/0.99      | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 3.10/0.99      | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(X0))
% 3.10/0.99      | ~ v2_pre_topc(X0)
% 3.10/0.99      | ~ v8_pre_topc(X0)
% 3.10/0.99      | ~ v1_compts_1(X0)
% 3.10/0.99      | ~ v4_orders_2(X1)
% 3.10/0.99      | ~ v7_waybel_0(X1)
% 3.10/0.99      | v2_struct_0(X0)
% 3.10/0.99      | v2_struct_0(X1)
% 3.10/0.99      | sK5(X0,X1) != sK4(X0,X1)
% 3.10/0.99      | k10_yellow_6(X0,X1) != k10_yellow_6(sK7,sK8)
% 3.10/0.99      | sK7 != X0 ),
% 3.10/0.99      inference(resolution_lifted,[status(thm)],[c_2242,c_1553]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_2295,plain,
% 3.10/0.99      ( ~ r3_waybel_9(sK7,X0,k1_waybel_2(sK7,sK8))
% 3.10/0.99      | ~ l1_waybel_0(X0,sK7)
% 3.10/0.99      | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 3.10/0.99      | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
% 3.10/0.99      | ~ v2_pre_topc(sK7)
% 3.10/0.99      | ~ v8_pre_topc(sK7)
% 3.10/0.99      | ~ v1_compts_1(sK7)
% 3.10/0.99      | ~ v4_orders_2(X0)
% 3.10/0.99      | ~ v7_waybel_0(X0)
% 3.10/0.99      | v2_struct_0(X0)
% 3.10/0.99      | v2_struct_0(sK7)
% 3.10/0.99      | sK5(sK7,X0) != sK4(sK7,X0)
% 3.10/0.99      | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8) ),
% 3.10/0.99      inference(unflattening,[status(thm)],[c_2294]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_2299,plain,
% 3.10/0.99      ( v2_struct_0(X0)
% 3.10/0.99      | ~ v7_waybel_0(X0)
% 3.10/0.99      | ~ v4_orders_2(X0)
% 3.10/0.99      | ~ r3_waybel_9(sK7,X0,k1_waybel_2(sK7,sK8))
% 3.10/0.99      | ~ l1_waybel_0(X0,sK7)
% 3.10/0.99      | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 3.10/0.99      | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
% 3.10/0.99      | sK5(sK7,X0) != sK4(sK7,X0)
% 3.10/0.99      | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8) ),
% 3.10/0.99      inference(global_propositional_subsumption,
% 3.10/0.99                [status(thm)],
% 3.10/0.99                [c_2295,c_43,c_42,c_38,c_36,c_35,c_105,c_138]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_2300,plain,
% 3.10/0.99      ( ~ r3_waybel_9(sK7,X0,k1_waybel_2(sK7,sK8))
% 3.10/0.99      | ~ l1_waybel_0(X0,sK7)
% 3.10/0.99      | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 3.10/0.99      | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
% 3.10/0.99      | ~ v4_orders_2(X0)
% 3.10/0.99      | ~ v7_waybel_0(X0)
% 3.10/0.99      | v2_struct_0(X0)
% 3.10/0.99      | sK5(sK7,X0) != sK4(sK7,X0)
% 3.10/0.99      | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8) ),
% 3.10/0.99      inference(renaming,[status(thm)],[c_2299]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_2719,plain,
% 3.10/0.99      ( ~ r3_waybel_9(sK7,X0,k1_waybel_2(sK7,sK8))
% 3.10/0.99      | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 3.10/0.99      | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
% 3.10/0.99      | ~ v4_orders_2(X0)
% 3.10/0.99      | ~ v7_waybel_0(X0)
% 3.10/0.99      | v2_struct_0(X0)
% 3.10/0.99      | sK5(sK7,X0) != sK4(sK7,X0)
% 3.10/0.99      | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8)
% 3.10/0.99      | sK8 != X0
% 3.10/0.99      | sK7 != sK7 ),
% 3.10/0.99      inference(resolution_lifted,[status(thm)],[c_30,c_2300]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_2720,plain,
% 3.10/0.99      ( ~ r3_waybel_9(sK7,sK8,k1_waybel_2(sK7,sK8))
% 3.10/0.99      | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 3.10/0.99      | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
% 3.10/0.99      | ~ v4_orders_2(sK8)
% 3.10/0.99      | ~ v7_waybel_0(sK8)
% 3.10/0.99      | v2_struct_0(sK8)
% 3.10/0.99      | sK5(sK7,sK8) != sK4(sK7,sK8)
% 3.10/0.99      | k10_yellow_6(sK7,sK8) != k10_yellow_6(sK7,sK8) ),
% 3.10/0.99      inference(unflattening,[status(thm)],[c_2719]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_2722,plain,
% 3.10/0.99      ( ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
% 3.10/0.99      | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 3.10/0.99      | ~ r3_waybel_9(sK7,sK8,k1_waybel_2(sK7,sK8))
% 3.10/0.99      | sK5(sK7,sK8) != sK4(sK7,sK8)
% 3.10/0.99      | k10_yellow_6(sK7,sK8) != k10_yellow_6(sK7,sK8) ),
% 3.10/0.99      inference(global_propositional_subsumption,
% 3.10/0.99                [status(thm)],
% 3.10/0.99                [c_2720,c_33,c_32,c_31]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_2723,plain,
% 3.10/0.99      ( ~ r3_waybel_9(sK7,sK8,k1_waybel_2(sK7,sK8))
% 3.10/0.99      | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 3.10/0.99      | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
% 3.10/0.99      | sK5(sK7,sK8) != sK4(sK7,sK8)
% 3.10/0.99      | k10_yellow_6(sK7,sK8) != k10_yellow_6(sK7,sK8) ),
% 3.10/0.99      inference(renaming,[status(thm)],[c_2722]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_3693,plain,
% 3.10/0.99      ( ~ r3_waybel_9(sK7,sK8,k1_waybel_2(sK7,sK8))
% 3.10/0.99      | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 3.10/0.99      | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
% 3.10/0.99      | sK5(sK7,sK8) != sK4(sK7,sK8) ),
% 3.10/0.99      inference(equality_resolution_simp,[status(thm)],[c_2723]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_4600,plain,
% 3.10/0.99      ( ~ r3_waybel_9(sK7,sK8,k1_waybel_2(sK7,sK8))
% 3.10/0.99      | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 3.10/0.99      | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
% 3.10/0.99      | sK5(sK7,sK8) != sK4(sK7,sK8) ),
% 3.10/0.99      inference(subtyping,[status(esa)],[c_3693]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_5136,plain,
% 3.10/0.99      ( sK5(sK7,sK8) != sK4(sK7,sK8)
% 3.10/0.99      | r3_waybel_9(sK7,sK8,k1_waybel_2(sK7,sK8)) != iProver_top
% 3.10/0.99      | r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) != iProver_top
% 3.10/0.99      | m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7)) != iProver_top ),
% 3.10/0.99      inference(predicate_to_equality,[status(thm)],[c_4600]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_4700,plain,
% 3.10/0.99      ( sK5(sK7,sK8) != sK4(sK7,sK8)
% 3.10/0.99      | r3_waybel_9(sK7,sK8,k1_waybel_2(sK7,sK8)) != iProver_top
% 3.10/0.99      | r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) != iProver_top
% 3.10/0.99      | m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7)) != iProver_top ),
% 3.10/0.99      inference(predicate_to_equality,[status(thm)],[c_4600]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_6207,plain,
% 3.10/0.99      ( r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) != iProver_top
% 3.10/0.99      | sK5(sK7,sK8) != sK4(sK7,sK8) ),
% 3.10/0.99      inference(global_propositional_subsumption,
% 3.10/0.99                [status(thm)],
% 3.10/0.99                [c_5136,c_56,c_57,c_58,c_2607,c_2618,c_4700,c_5496,
% 3.10/0.99                 c_5508,c_5513]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_6208,plain,
% 3.10/0.99      ( sK5(sK7,sK8) != sK4(sK7,sK8)
% 3.10/0.99      | r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) != iProver_top ),
% 3.10/0.99      inference(renaming,[status(thm)],[c_6207]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_7267,plain,
% 3.10/0.99      ( sK5(sK7,sK8) != sK3(sK7,sK8)
% 3.10/0.99      | r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) != iProver_top ),
% 3.10/0.99      inference(demodulation,[status(thm)],[c_7261,c_6208]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_22,plain,
% 3.10/0.99      ( ~ r3_waybel_9(X0,X1,X2)
% 3.10/0.99      | r3_waybel_9(X0,X1,sK5(X0,X1))
% 3.10/0.99      | r2_hidden(X2,k10_yellow_6(X0,X1))
% 3.10/0.99      | ~ l1_waybel_0(X1,X0)
% 3.10/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.10/0.99      | ~ v2_pre_topc(X0)
% 3.10/0.99      | ~ v8_pre_topc(X0)
% 3.10/0.99      | ~ v1_compts_1(X0)
% 3.10/0.99      | ~ v4_orders_2(X1)
% 3.10/0.99      | ~ v7_waybel_0(X1)
% 3.10/0.99      | ~ l1_pre_topc(X0)
% 3.10/0.99      | v2_struct_0(X0)
% 3.10/0.99      | v2_struct_0(X1) ),
% 3.10/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_2193,plain,
% 3.10/0.99      ( ~ r3_waybel_9(X0,X1,X2)
% 3.10/0.99      | r3_waybel_9(X0,X1,sK5(X0,X1))
% 3.10/0.99      | ~ l1_waybel_0(X1,X0)
% 3.10/0.99      | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 3.10/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.10/0.99      | ~ v2_pre_topc(X0)
% 3.10/0.99      | ~ v8_pre_topc(X0)
% 3.10/0.99      | ~ v1_compts_1(X0)
% 3.10/0.99      | ~ v4_orders_2(X1)
% 3.10/0.99      | ~ v7_waybel_0(X1)
% 3.10/0.99      | ~ l1_pre_topc(X0)
% 3.10/0.99      | v2_struct_0(X0)
% 3.10/0.99      | v2_struct_0(X1)
% 3.10/0.99      | k1_waybel_2(sK7,sK8) != X2
% 3.10/0.99      | k10_yellow_6(X0,X1) != k10_yellow_6(sK7,sK8) ),
% 3.10/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_492]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_2194,plain,
% 3.10/0.99      ( ~ r3_waybel_9(X0,X1,k1_waybel_2(sK7,sK8))
% 3.10/0.99      | r3_waybel_9(X0,X1,sK5(X0,X1))
% 3.10/0.99      | ~ l1_waybel_0(X1,X0)
% 3.10/0.99      | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 3.10/0.99      | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(X0))
% 3.10/0.99      | ~ v2_pre_topc(X0)
% 3.10/0.99      | ~ v8_pre_topc(X0)
% 3.10/0.99      | ~ v1_compts_1(X0)
% 3.10/0.99      | ~ v4_orders_2(X1)
% 3.10/0.99      | ~ v7_waybel_0(X1)
% 3.10/0.99      | ~ l1_pre_topc(X0)
% 3.10/0.99      | v2_struct_0(X0)
% 3.10/0.99      | v2_struct_0(X1)
% 3.10/0.99      | k10_yellow_6(X0,X1) != k10_yellow_6(sK7,sK8) ),
% 3.10/0.99      inference(unflattening,[status(thm)],[c_2193]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_2333,plain,
% 3.10/0.99      ( ~ r3_waybel_9(X0,X1,k1_waybel_2(sK7,sK8))
% 3.10/0.99      | r3_waybel_9(X0,X1,sK5(X0,X1))
% 3.10/0.99      | ~ l1_waybel_0(X1,X0)
% 3.10/0.99      | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 3.10/0.99      | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(X0))
% 3.10/0.99      | ~ v2_pre_topc(X0)
% 3.10/0.99      | ~ v8_pre_topc(X0)
% 3.10/0.99      | ~ v1_compts_1(X0)
% 3.10/0.99      | ~ v4_orders_2(X1)
% 3.10/0.99      | ~ v7_waybel_0(X1)
% 3.10/0.99      | v2_struct_0(X0)
% 3.10/0.99      | v2_struct_0(X1)
% 3.10/0.99      | k10_yellow_6(X0,X1) != k10_yellow_6(sK7,sK8)
% 3.10/0.99      | sK7 != X0 ),
% 3.10/0.99      inference(resolution_lifted,[status(thm)],[c_2194,c_1553]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_2334,plain,
% 3.10/0.99      ( ~ r3_waybel_9(sK7,X0,k1_waybel_2(sK7,sK8))
% 3.10/0.99      | r3_waybel_9(sK7,X0,sK5(sK7,X0))
% 3.10/0.99      | ~ l1_waybel_0(X0,sK7)
% 3.10/0.99      | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 3.10/0.99      | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
% 3.10/0.99      | ~ v2_pre_topc(sK7)
% 3.10/0.99      | ~ v8_pre_topc(sK7)
% 3.10/0.99      | ~ v1_compts_1(sK7)
% 3.10/0.99      | ~ v4_orders_2(X0)
% 3.10/0.99      | ~ v7_waybel_0(X0)
% 3.10/0.99      | v2_struct_0(X0)
% 3.10/0.99      | v2_struct_0(sK7)
% 3.10/0.99      | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8) ),
% 3.10/0.99      inference(unflattening,[status(thm)],[c_2333]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_2338,plain,
% 3.10/0.99      ( v2_struct_0(X0)
% 3.10/0.99      | ~ v7_waybel_0(X0)
% 3.10/0.99      | ~ v4_orders_2(X0)
% 3.10/0.99      | ~ r3_waybel_9(sK7,X0,k1_waybel_2(sK7,sK8))
% 3.10/0.99      | r3_waybel_9(sK7,X0,sK5(sK7,X0))
% 3.10/0.99      | ~ l1_waybel_0(X0,sK7)
% 3.10/0.99      | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 3.10/0.99      | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
% 3.10/0.99      | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8) ),
% 3.10/0.99      inference(global_propositional_subsumption,
% 3.10/0.99                [status(thm)],
% 3.10/0.99                [c_2334,c_43,c_42,c_38,c_36,c_35,c_105,c_138]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_2339,plain,
% 3.10/0.99      ( ~ r3_waybel_9(sK7,X0,k1_waybel_2(sK7,sK8))
% 3.10/0.99      | r3_waybel_9(sK7,X0,sK5(sK7,X0))
% 3.10/0.99      | ~ l1_waybel_0(X0,sK7)
% 3.10/0.99      | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 3.10/0.99      | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
% 3.10/0.99      | ~ v4_orders_2(X0)
% 3.10/0.99      | ~ v7_waybel_0(X0)
% 3.10/0.99      | v2_struct_0(X0)
% 3.10/0.99      | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8) ),
% 3.10/0.99      inference(renaming,[status(thm)],[c_2338]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_2696,plain,
% 3.10/0.99      ( ~ r3_waybel_9(sK7,X0,k1_waybel_2(sK7,sK8))
% 3.10/0.99      | r3_waybel_9(sK7,X0,sK5(sK7,X0))
% 3.10/0.99      | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 3.10/0.99      | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
% 3.10/0.99      | ~ v4_orders_2(X0)
% 3.10/0.99      | ~ v7_waybel_0(X0)
% 3.10/0.99      | v2_struct_0(X0)
% 3.10/0.99      | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8)
% 3.10/0.99      | sK8 != X0
% 3.10/0.99      | sK7 != sK7 ),
% 3.10/0.99      inference(resolution_lifted,[status(thm)],[c_30,c_2339]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_2697,plain,
% 3.10/0.99      ( ~ r3_waybel_9(sK7,sK8,k1_waybel_2(sK7,sK8))
% 3.10/0.99      | r3_waybel_9(sK7,sK8,sK5(sK7,sK8))
% 3.10/0.99      | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 3.10/0.99      | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
% 3.10/0.99      | ~ v4_orders_2(sK8)
% 3.10/0.99      | ~ v7_waybel_0(sK8)
% 3.10/0.99      | v2_struct_0(sK8)
% 3.10/0.99      | k10_yellow_6(sK7,sK8) != k10_yellow_6(sK7,sK8) ),
% 3.10/0.99      inference(unflattening,[status(thm)],[c_2696]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_2699,plain,
% 3.10/0.99      ( ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
% 3.10/0.99      | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 3.10/0.99      | r3_waybel_9(sK7,sK8,sK5(sK7,sK8))
% 3.10/0.99      | ~ r3_waybel_9(sK7,sK8,k1_waybel_2(sK7,sK8))
% 3.10/0.99      | k10_yellow_6(sK7,sK8) != k10_yellow_6(sK7,sK8) ),
% 3.10/0.99      inference(global_propositional_subsumption,
% 3.10/0.99                [status(thm)],
% 3.10/0.99                [c_2697,c_33,c_32,c_31]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_2700,plain,
% 3.10/0.99      ( ~ r3_waybel_9(sK7,sK8,k1_waybel_2(sK7,sK8))
% 3.10/0.99      | r3_waybel_9(sK7,sK8,sK5(sK7,sK8))
% 3.10/0.99      | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 3.10/0.99      | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
% 3.10/0.99      | k10_yellow_6(sK7,sK8) != k10_yellow_6(sK7,sK8) ),
% 3.10/0.99      inference(renaming,[status(thm)],[c_2699]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_3695,plain,
% 3.10/0.99      ( ~ r3_waybel_9(sK7,sK8,k1_waybel_2(sK7,sK8))
% 3.10/0.99      | r3_waybel_9(sK7,sK8,sK5(sK7,sK8))
% 3.10/0.99      | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 3.10/0.99      | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7)) ),
% 3.10/0.99      inference(equality_resolution_simp,[status(thm)],[c_2700]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_4599,plain,
% 3.10/0.99      ( ~ r3_waybel_9(sK7,sK8,k1_waybel_2(sK7,sK8))
% 3.10/0.99      | r3_waybel_9(sK7,sK8,sK5(sK7,sK8))
% 3.10/0.99      | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 3.10/0.99      | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7)) ),
% 3.10/0.99      inference(subtyping,[status(esa)],[c_3695]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_5137,plain,
% 3.10/0.99      ( r3_waybel_9(sK7,sK8,k1_waybel_2(sK7,sK8)) != iProver_top
% 3.10/0.99      | r3_waybel_9(sK7,sK8,sK5(sK7,sK8)) = iProver_top
% 3.10/0.99      | r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) != iProver_top
% 3.10/0.99      | m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7)) != iProver_top ),
% 3.10/0.99      inference(predicate_to_equality,[status(thm)],[c_4599]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_3696,plain,
% 3.10/0.99      ( r3_waybel_9(sK7,sK8,k1_waybel_2(sK7,sK8)) != iProver_top
% 3.10/0.99      | r3_waybel_9(sK7,sK8,sK5(sK7,sK8)) = iProver_top
% 3.10/0.99      | r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) != iProver_top
% 3.10/0.99      | m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7)) != iProver_top ),
% 3.10/0.99      inference(predicate_to_equality,[status(thm)],[c_3695]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_6214,plain,
% 3.10/0.99      ( r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) != iProver_top
% 3.10/0.99      | r3_waybel_9(sK7,sK8,sK5(sK7,sK8)) = iProver_top ),
% 3.10/0.99      inference(global_propositional_subsumption,
% 3.10/0.99                [status(thm)],
% 3.10/0.99                [c_5137,c_56,c_57,c_58,c_2607,c_2618,c_3696,c_5496,
% 3.10/0.99                 c_5508,c_5513]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_6215,plain,
% 3.10/0.99      ( r3_waybel_9(sK7,sK8,sK5(sK7,sK8)) = iProver_top
% 3.10/0.99      | r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) != iProver_top ),
% 3.10/0.99      inference(renaming,[status(thm)],[c_6214]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_6660,plain,
% 3.10/0.99      ( r3_waybel_9(sK7,sK8,sK5(sK7,sK8)) = iProver_top ),
% 3.10/0.99      inference(superposition,[status(thm)],[c_6652,c_6215]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_6992,plain,
% 3.10/0.99      ( sK5(sK7,sK8) = sK3(sK7,sK8)
% 3.10/0.99      | m1_subset_1(sK5(sK7,sK8),u1_struct_0(sK7)) != iProver_top ),
% 3.10/0.99      inference(superposition,[status(thm)],[c_6660,c_5550]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_24,plain,
% 3.10/0.99      ( ~ r3_waybel_9(X0,X1,X2)
% 3.10/0.99      | r2_hidden(X2,k10_yellow_6(X0,X1))
% 3.10/0.99      | ~ l1_waybel_0(X1,X0)
% 3.10/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.10/0.99      | m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
% 3.10/0.99      | ~ v2_pre_topc(X0)
% 3.10/0.99      | ~ v8_pre_topc(X0)
% 3.10/0.99      | ~ v1_compts_1(X0)
% 3.10/0.99      | ~ v4_orders_2(X1)
% 3.10/0.99      | ~ v7_waybel_0(X1)
% 3.10/0.99      | ~ l1_pre_topc(X0)
% 3.10/0.99      | v2_struct_0(X0)
% 3.10/0.99      | v2_struct_0(X1) ),
% 3.10/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_2097,plain,
% 3.10/0.99      ( ~ r3_waybel_9(X0,X1,X2)
% 3.10/0.99      | ~ l1_waybel_0(X1,X0)
% 3.10/0.99      | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 3.10/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.10/0.99      | m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
% 3.10/0.99      | ~ v2_pre_topc(X0)
% 3.10/0.99      | ~ v8_pre_topc(X0)
% 3.10/0.99      | ~ v1_compts_1(X0)
% 3.10/0.99      | ~ v4_orders_2(X1)
% 3.10/0.99      | ~ v7_waybel_0(X1)
% 3.10/0.99      | ~ l1_pre_topc(X0)
% 3.10/0.99      | v2_struct_0(X0)
% 3.10/0.99      | v2_struct_0(X1)
% 3.10/0.99      | k1_waybel_2(sK7,sK8) != X2
% 3.10/0.99      | k10_yellow_6(X0,X1) != k10_yellow_6(sK7,sK8) ),
% 3.10/0.99      inference(resolution_lifted,[status(thm)],[c_24,c_492]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_2098,plain,
% 3.10/0.99      ( ~ r3_waybel_9(X0,X1,k1_waybel_2(sK7,sK8))
% 3.10/0.99      | ~ l1_waybel_0(X1,X0)
% 3.10/0.99      | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 3.10/0.99      | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(X0))
% 3.10/0.99      | m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
% 3.10/0.99      | ~ v2_pre_topc(X0)
% 3.10/0.99      | ~ v8_pre_topc(X0)
% 3.10/0.99      | ~ v1_compts_1(X0)
% 3.10/0.99      | ~ v4_orders_2(X1)
% 3.10/0.99      | ~ v7_waybel_0(X1)
% 3.10/0.99      | ~ l1_pre_topc(X0)
% 3.10/0.99      | v2_struct_0(X0)
% 3.10/0.99      | v2_struct_0(X1)
% 3.10/0.99      | k10_yellow_6(X0,X1) != k10_yellow_6(sK7,sK8) ),
% 3.10/0.99      inference(unflattening,[status(thm)],[c_2097]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_2411,plain,
% 3.10/0.99      ( ~ r3_waybel_9(X0,X1,k1_waybel_2(sK7,sK8))
% 3.10/0.99      | ~ l1_waybel_0(X1,X0)
% 3.10/0.99      | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 3.10/0.99      | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(X0))
% 3.10/0.99      | m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
% 3.10/0.99      | ~ v2_pre_topc(X0)
% 3.10/0.99      | ~ v8_pre_topc(X0)
% 3.10/0.99      | ~ v1_compts_1(X0)
% 3.10/0.99      | ~ v4_orders_2(X1)
% 3.10/0.99      | ~ v7_waybel_0(X1)
% 3.10/0.99      | v2_struct_0(X0)
% 3.10/0.99      | v2_struct_0(X1)
% 3.10/0.99      | k10_yellow_6(X0,X1) != k10_yellow_6(sK7,sK8)
% 3.10/0.99      | sK7 != X0 ),
% 3.10/0.99      inference(resolution_lifted,[status(thm)],[c_2098,c_1553]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_2412,plain,
% 3.10/0.99      ( ~ r3_waybel_9(sK7,X0,k1_waybel_2(sK7,sK8))
% 3.10/0.99      | ~ l1_waybel_0(X0,sK7)
% 3.10/0.99      | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 3.10/0.99      | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
% 3.10/0.99      | m1_subset_1(sK5(sK7,X0),u1_struct_0(sK7))
% 3.10/0.99      | ~ v2_pre_topc(sK7)
% 3.10/0.99      | ~ v8_pre_topc(sK7)
% 3.10/0.99      | ~ v1_compts_1(sK7)
% 3.10/0.99      | ~ v4_orders_2(X0)
% 3.10/0.99      | ~ v7_waybel_0(X0)
% 3.10/0.99      | v2_struct_0(X0)
% 3.10/0.99      | v2_struct_0(sK7)
% 3.10/0.99      | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8) ),
% 3.10/0.99      inference(unflattening,[status(thm)],[c_2411]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_2416,plain,
% 3.10/0.99      ( v2_struct_0(X0)
% 3.10/0.99      | ~ v7_waybel_0(X0)
% 3.10/0.99      | ~ v4_orders_2(X0)
% 3.10/0.99      | ~ r3_waybel_9(sK7,X0,k1_waybel_2(sK7,sK8))
% 3.10/0.99      | ~ l1_waybel_0(X0,sK7)
% 3.10/0.99      | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 3.10/0.99      | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
% 3.10/0.99      | m1_subset_1(sK5(sK7,X0),u1_struct_0(sK7))
% 3.10/0.99      | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8) ),
% 3.10/0.99      inference(global_propositional_subsumption,
% 3.10/0.99                [status(thm)],
% 3.10/0.99                [c_2412,c_43,c_42,c_38,c_36,c_35,c_105,c_138]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_2417,plain,
% 3.10/0.99      ( ~ r3_waybel_9(sK7,X0,k1_waybel_2(sK7,sK8))
% 3.10/0.99      | ~ l1_waybel_0(X0,sK7)
% 3.10/0.99      | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 3.10/0.99      | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
% 3.10/0.99      | m1_subset_1(sK5(sK7,X0),u1_struct_0(sK7))
% 3.10/0.99      | ~ v4_orders_2(X0)
% 3.10/0.99      | ~ v7_waybel_0(X0)
% 3.10/0.99      | v2_struct_0(X0)
% 3.10/0.99      | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8) ),
% 3.10/0.99      inference(renaming,[status(thm)],[c_2416]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_2650,plain,
% 3.10/0.99      ( ~ r3_waybel_9(sK7,X0,k1_waybel_2(sK7,sK8))
% 3.10/0.99      | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 3.10/0.99      | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
% 3.10/0.99      | m1_subset_1(sK5(sK7,X0),u1_struct_0(sK7))
% 3.10/0.99      | ~ v4_orders_2(X0)
% 3.10/0.99      | ~ v7_waybel_0(X0)
% 3.10/0.99      | v2_struct_0(X0)
% 3.10/0.99      | k10_yellow_6(sK7,X0) != k10_yellow_6(sK7,sK8)
% 3.10/0.99      | sK8 != X0
% 3.10/0.99      | sK7 != sK7 ),
% 3.10/0.99      inference(resolution_lifted,[status(thm)],[c_30,c_2417]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_2651,plain,
% 3.10/0.99      ( ~ r3_waybel_9(sK7,sK8,k1_waybel_2(sK7,sK8))
% 3.10/0.99      | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 3.10/0.99      | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
% 3.10/0.99      | m1_subset_1(sK5(sK7,sK8),u1_struct_0(sK7))
% 3.10/0.99      | ~ v4_orders_2(sK8)
% 3.10/0.99      | ~ v7_waybel_0(sK8)
% 3.10/0.99      | v2_struct_0(sK8)
% 3.10/0.99      | k10_yellow_6(sK7,sK8) != k10_yellow_6(sK7,sK8) ),
% 3.10/0.99      inference(unflattening,[status(thm)],[c_2650]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_2653,plain,
% 3.10/0.99      ( m1_subset_1(sK5(sK7,sK8),u1_struct_0(sK7))
% 3.10/0.99      | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
% 3.10/0.99      | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 3.10/0.99      | ~ r3_waybel_9(sK7,sK8,k1_waybel_2(sK7,sK8))
% 3.10/0.99      | k10_yellow_6(sK7,sK8) != k10_yellow_6(sK7,sK8) ),
% 3.10/0.99      inference(global_propositional_subsumption,
% 3.10/0.99                [status(thm)],
% 3.10/0.99                [c_2651,c_33,c_32,c_31]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_2654,plain,
% 3.10/0.99      ( ~ r3_waybel_9(sK7,sK8,k1_waybel_2(sK7,sK8))
% 3.10/0.99      | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 3.10/0.99      | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
% 3.10/0.99      | m1_subset_1(sK5(sK7,sK8),u1_struct_0(sK7))
% 3.10/0.99      | k10_yellow_6(sK7,sK8) != k10_yellow_6(sK7,sK8) ),
% 3.10/0.99      inference(renaming,[status(thm)],[c_2653]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_3699,plain,
% 3.10/0.99      ( ~ r3_waybel_9(sK7,sK8,k1_waybel_2(sK7,sK8))
% 3.10/0.99      | ~ r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8)))
% 3.10/0.99      | ~ m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7))
% 3.10/0.99      | m1_subset_1(sK5(sK7,sK8),u1_struct_0(sK7)) ),
% 3.10/0.99      inference(equality_resolution_simp,[status(thm)],[c_2654]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_3700,plain,
% 3.10/0.99      ( r3_waybel_9(sK7,sK8,k1_waybel_2(sK7,sK8)) != iProver_top
% 3.10/0.99      | r1_yellow_0(sK7,k2_relset_1(u1_struct_0(sK8),u1_struct_0(sK7),u1_waybel_0(sK7,sK8))) != iProver_top
% 3.10/0.99      | m1_subset_1(k1_waybel_2(sK7,sK8),u1_struct_0(sK7)) != iProver_top
% 3.10/0.99      | m1_subset_1(sK5(sK7,sK8),u1_struct_0(sK7)) = iProver_top ),
% 3.10/0.99      inference(predicate_to_equality,[status(thm)],[c_3699]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(contradiction,plain,
% 3.10/0.99      ( $false ),
% 3.10/0.99      inference(minisat,
% 3.10/0.99                [status(thm)],
% 3.10/0.99                [c_7267,c_6992,c_6649,c_5513,c_5508,c_5496,c_3700,c_2618,
% 3.10/0.99                 c_2607,c_58,c_57,c_56]) ).
% 3.10/0.99  
% 3.10/0.99  
% 3.10/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.10/0.99  
% 3.10/0.99  ------                               Statistics
% 3.10/0.99  
% 3.10/0.99  ------ General
% 3.10/0.99  
% 3.10/0.99  abstr_ref_over_cycles:                  0
% 3.10/0.99  abstr_ref_under_cycles:                 0
% 3.10/0.99  gc_basic_clause_elim:                   0
% 3.10/0.99  forced_gc_time:                         0
% 3.10/0.99  parsing_time:                           0.014
% 3.10/0.99  unif_index_cands_time:                  0.
% 3.10/0.99  unif_index_add_time:                    0.
% 3.10/0.99  orderings_time:                         0.
% 3.10/0.99  out_proof_time:                         0.027
% 3.10/0.99  total_time:                             0.301
% 3.10/0.99  num_of_symbols:                         83
% 3.10/0.99  num_of_terms:                           2949
% 3.10/0.99  
% 3.10/0.99  ------ Preprocessing
% 3.10/0.99  
% 3.10/0.99  num_of_splits:                          6
% 3.10/0.99  num_of_split_atoms:                     6
% 3.10/0.99  num_of_reused_defs:                     0
% 3.10/0.99  num_eq_ax_congr_red:                    60
% 3.10/0.99  num_of_sem_filtered_clauses:            1
% 3.10/0.99  num_of_subtypes:                        6
% 3.10/0.99  monotx_restored_types:                  0
% 3.10/0.99  sat_num_of_epr_types:                   0
% 3.10/0.99  sat_num_of_non_cyclic_types:            0
% 3.10/0.99  sat_guarded_non_collapsed_types:        1
% 3.10/0.99  num_pure_diseq_elim:                    0
% 3.10/0.99  simp_replaced_by:                       0
% 3.10/0.99  res_preprocessed:                       138
% 3.10/0.99  prep_upred:                             0
% 3.10/0.99  prep_unflattend:                        118
% 3.10/0.99  smt_new_axioms:                         0
% 3.10/0.99  pred_elim_cands:                        5
% 3.10/0.99  pred_elim:                              19
% 3.10/0.99  pred_elim_cl:                           23
% 3.10/0.99  pred_elim_cycles:                       25
% 3.10/0.99  merged_defs:                            0
% 3.10/0.99  merged_defs_ncl:                        0
% 3.10/0.99  bin_hyper_res:                          0
% 3.10/0.99  prep_cycles:                            4
% 3.10/0.99  pred_elim_time:                         0.112
% 3.10/0.99  splitting_time:                         0.
% 3.10/0.99  sem_filter_time:                        0.
% 3.10/0.99  monotx_time:                            0.
% 3.10/0.99  subtype_inf_time:                       0.
% 3.10/0.99  
% 3.10/0.99  ------ Problem properties
% 3.10/0.99  
% 3.10/0.99  clauses:                                27
% 3.10/0.99  conjectures:                            0
% 3.10/0.99  epr:                                    3
% 3.10/0.99  horn:                                   17
% 3.10/0.99  ground:                                 10
% 3.10/0.99  unary:                                  2
% 3.10/0.99  binary:                                 3
% 3.10/0.99  lits:                                   97
% 3.10/0.99  lits_eq:                                9
% 3.10/0.99  fd_pure:                                0
% 3.10/0.99  fd_pseudo:                              0
% 3.10/0.99  fd_cond:                                2
% 3.10/0.99  fd_pseudo_cond:                         3
% 3.10/0.99  ac_symbols:                             0
% 3.10/0.99  
% 3.10/0.99  ------ Propositional Solver
% 3.10/0.99  
% 3.10/0.99  prop_solver_calls:                      28
% 3.10/0.99  prop_fast_solver_calls:                 2672
% 3.10/0.99  smt_solver_calls:                       0
% 3.10/0.99  smt_fast_solver_calls:                  0
% 3.10/0.99  prop_num_of_clauses:                    1628
% 3.10/0.99  prop_preprocess_simplified:             5258
% 3.10/0.99  prop_fo_subsumed:                       170
% 3.10/0.99  prop_solver_time:                       0.
% 3.10/0.99  smt_solver_time:                        0.
% 3.10/0.99  smt_fast_solver_time:                   0.
% 3.10/0.99  prop_fast_solver_time:                  0.
% 3.10/0.99  prop_unsat_core_time:                   0.
% 3.10/0.99  
% 3.10/0.99  ------ QBF
% 3.10/0.99  
% 3.10/0.99  qbf_q_res:                              0
% 3.10/0.99  qbf_num_tautologies:                    0
% 3.10/0.99  qbf_prep_cycles:                        0
% 3.10/0.99  
% 3.10/0.99  ------ BMC1
% 3.10/0.99  
% 3.10/0.99  bmc1_current_bound:                     -1
% 3.10/0.99  bmc1_last_solved_bound:                 -1
% 3.10/0.99  bmc1_unsat_core_size:                   -1
% 3.10/0.99  bmc1_unsat_core_parents_size:           -1
% 3.10/0.99  bmc1_merge_next_fun:                    0
% 3.10/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.10/0.99  
% 3.10/0.99  ------ Instantiation
% 3.10/0.99  
% 3.10/0.99  inst_num_of_clauses:                    302
% 3.10/0.99  inst_num_in_passive:                    1
% 3.10/0.99  inst_num_in_active:                     220
% 3.10/0.99  inst_num_in_unprocessed:                81
% 3.10/0.99  inst_num_of_loops:                      240
% 3.10/0.99  inst_num_of_learning_restarts:          0
% 3.10/0.99  inst_num_moves_active_passive:          16
% 3.10/0.99  inst_lit_activity:                      0
% 3.10/0.99  inst_lit_activity_moves:                0
% 3.10/0.99  inst_num_tautologies:                   0
% 3.10/0.99  inst_num_prop_implied:                  0
% 3.10/0.99  inst_num_existing_simplified:           0
% 3.10/0.99  inst_num_eq_res_simplified:             0
% 3.10/0.99  inst_num_child_elim:                    0
% 3.10/0.99  inst_num_of_dismatching_blockings:      1
% 3.10/0.99  inst_num_of_non_proper_insts:           271
% 3.10/0.99  inst_num_of_duplicates:                 0
% 3.10/0.99  inst_inst_num_from_inst_to_res:         0
% 3.10/0.99  inst_dismatching_checking_time:         0.
% 3.10/0.99  
% 3.10/0.99  ------ Resolution
% 3.10/0.99  
% 3.10/0.99  res_num_of_clauses:                     0
% 3.10/0.99  res_num_in_passive:                     0
% 3.10/0.99  res_num_in_active:                      0
% 3.10/0.99  res_num_of_loops:                       142
% 3.10/0.99  res_forward_subset_subsumed:            9
% 3.10/0.99  res_backward_subset_subsumed:           0
% 3.10/0.99  res_forward_subsumed:                   0
% 3.10/0.99  res_backward_subsumed:                  0
% 3.10/0.99  res_forward_subsumption_resolution:     10
% 3.10/0.99  res_backward_subsumption_resolution:    0
% 3.10/0.99  res_clause_to_clause_subsumption:       233
% 3.10/0.99  res_orphan_elimination:                 0
% 3.10/0.99  res_tautology_del:                      47
% 3.10/0.99  res_num_eq_res_simplified:              5
% 3.10/0.99  res_num_sel_changes:                    0
% 3.10/0.99  res_moves_from_active_to_pass:          0
% 3.10/0.99  
% 3.10/0.99  ------ Superposition
% 3.10/0.99  
% 3.10/0.99  sup_time_total:                         0.
% 3.10/0.99  sup_time_generating:                    0.
% 3.10/0.99  sup_time_sim_full:                      0.
% 3.10/0.99  sup_time_sim_immed:                     0.
% 3.10/0.99  
% 3.10/0.99  sup_num_of_clauses:                     46
% 3.10/0.99  sup_num_in_active:                      38
% 3.10/0.99  sup_num_in_passive:                     8
% 3.10/0.99  sup_num_of_loops:                       47
% 3.10/0.99  sup_fw_superposition:                   13
% 3.10/0.99  sup_bw_superposition:                   22
% 3.10/0.99  sup_immediate_simplified:               11
% 3.10/0.99  sup_given_eliminated:                   0
% 3.10/0.99  comparisons_done:                       0
% 3.10/0.99  comparisons_avoided:                    0
% 3.10/0.99  
% 3.10/0.99  ------ Simplifications
% 3.10/0.99  
% 3.10/0.99  
% 3.10/0.99  sim_fw_subset_subsumed:                 7
% 3.10/0.99  sim_bw_subset_subsumed:                 5
% 3.10/0.99  sim_fw_subsumed:                        1
% 3.10/0.99  sim_bw_subsumed:                        0
% 3.10/0.99  sim_fw_subsumption_res:                 2
% 3.10/0.99  sim_bw_subsumption_res:                 0
% 3.10/0.99  sim_tautology_del:                      0
% 3.10/0.99  sim_eq_tautology_del:                   3
% 3.10/0.99  sim_eq_res_simp:                        0
% 3.10/0.99  sim_fw_demodulated:                     2
% 3.10/0.99  sim_bw_demodulated:                     7
% 3.10/0.99  sim_light_normalised:                   2
% 3.10/0.99  sim_joinable_taut:                      0
% 3.10/0.99  sim_joinable_simp:                      0
% 3.10/0.99  sim_ac_normalised:                      0
% 3.10/0.99  sim_smt_subsumption:                    0
% 3.10/0.99  
%------------------------------------------------------------------------------
