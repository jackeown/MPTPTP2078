%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT2042+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:03 EST 2020

% Result     : Theorem 0.53s
% Output     : CNFRefutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :  114 (3643 expanded)
%              Number of clauses        :   66 ( 574 expanded)
%              Number of leaves         :    8 ( 900 expanded)
%              Depth                    :   17
%              Number of atoms          :  753 (38432 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal clause size      :   24 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,conjecture,(
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
       => v2_waybel_2(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
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
         => v2_waybel_2(X0) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f11,plain,(
    ? [X0] :
      ( ~ v2_waybel_2(X0)
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
    inference(ennf_transformation,[],[f4])).

fof(f12,plain,(
    ? [X0] :
      ( ~ v2_waybel_2(X0)
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
    inference(flattening,[],[f11])).

fof(f24,plain,
    ( ? [X0] :
        ( ~ v2_waybel_2(X0)
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
        & v2_pre_topc(X0) )
   => ( ~ v2_waybel_2(sK4)
      & ! [X1] :
          ( v5_pre_topc(k4_waybel_1(sK4,X1),sK4,sK4)
          | ~ m1_subset_1(X1,u1_struct_0(sK4)) )
      & l1_waybel_9(sK4)
      & v1_compts_1(sK4)
      & v2_lattice3(sK4)
      & v1_lattice3(sK4)
      & v5_orders_2(sK4)
      & v4_orders_2(sK4)
      & v3_orders_2(sK4)
      & v8_pre_topc(sK4)
      & v2_pre_topc(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ~ v2_waybel_2(sK4)
    & ! [X1] :
        ( v5_pre_topc(k4_waybel_1(sK4,X1),sK4,sK4)
        | ~ m1_subset_1(X1,u1_struct_0(sK4)) )
    & l1_waybel_9(sK4)
    & v1_compts_1(sK4)
    & v2_lattice3(sK4)
    & v1_lattice3(sK4)
    & v5_orders_2(sK4)
    & v4_orders_2(sK4)
    & v3_orders_2(sK4)
    & v8_pre_topc(sK4)
    & v2_pre_topc(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f12,f24])).

fof(f47,plain,(
    ! [X1] :
      ( v5_pre_topc(k4_waybel_1(sK4,X1),sK4,sK4)
      | ~ m1_subset_1(X1,u1_struct_0(sK4)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f13,plain,(
    ! [X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(k1_waybel_2(X0,X2),k10_yellow_6(X0,X2))
            | ~ r1_waybel_9(X0,X2) )
          & v10_waybel_0(X2,X0)
          & l1_waybel_0(X2,X0)
          & v7_waybel_0(X2)
          & v4_orders_2(X2)
          & ~ v2_struct_0(X2) )
      | ~ sP0(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f15,plain,(
    ! [X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(k1_waybel_2(X0,X2),k10_yellow_6(X0,X2))
            | ~ r1_waybel_9(X0,X2) )
          & v10_waybel_0(X2,X0)
          & l1_waybel_0(X2,X0)
          & v7_waybel_0(X2)
          & v4_orders_2(X2)
          & ~ v2_struct_0(X2) )
      | ~ sP0(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ r2_hidden(k1_waybel_2(X0,X1),k10_yellow_6(X0,X1))
            | ~ r1_waybel_9(X0,X1) )
          & v10_waybel_0(X1,X0)
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      | ~ sP0(X0) ) ),
    inference(rectify,[],[f15])).

fof(f17,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ r2_hidden(k1_waybel_2(X0,X1),k10_yellow_6(X0,X1))
            | ~ r1_waybel_9(X0,X1) )
          & v10_waybel_0(X1,X0)
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
     => ( ( ~ r2_hidden(k1_waybel_2(X0,sK1(X0)),k10_yellow_6(X0,sK1(X0)))
          | ~ r1_waybel_9(X0,sK1(X0)) )
        & v10_waybel_0(sK1(X0),X0)
        & l1_waybel_0(sK1(X0),X0)
        & v7_waybel_0(sK1(X0))
        & v4_orders_2(sK1(X0))
        & ~ v2_struct_0(sK1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ( ( ~ r2_hidden(k1_waybel_2(X0,sK1(X0)),k10_yellow_6(X0,sK1(X0)))
          | ~ r1_waybel_9(X0,sK1(X0)) )
        & v10_waybel_0(sK1(X0),X0)
        & l1_waybel_0(sK1(X0),X0)
        & v7_waybel_0(sK1(X0))
        & v4_orders_2(sK1(X0))
        & ~ v2_struct_0(sK1(X0)) )
      | ~ sP0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f17])).

fof(f31,plain,(
    ! [X0] :
      ( ~ r2_hidden(k1_waybel_2(X0,sK1(X0)),k10_yellow_6(X0,sK1(X0)))
      | ~ r1_waybel_9(X0,sK1(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_waybel_9(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( ( ! [X1] :
              ( m1_subset_1(X1,u1_struct_0(X0))
             => v5_pre_topc(k4_waybel_1(X0,X1),X0,X0) )
          & ! [X1] :
              ( ( l1_waybel_0(X1,X0)
                & v7_waybel_0(X1)
                & v4_orders_2(X1)
                & ~ v2_struct_0(X1) )
             => ( v10_waybel_0(X1,X0)
               => ( r2_hidden(k1_waybel_2(X0,X1),k10_yellow_6(X0,X1))
                  & r1_waybel_9(X0,X1) ) ) ) )
       => v2_waybel_2(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0] :
      ( ( l1_waybel_9(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( ( ! [X1] :
              ( m1_subset_1(X1,u1_struct_0(X0))
             => v5_pre_topc(k4_waybel_1(X0,X1),X0,X0) )
          & ! [X2] :
              ( ( l1_waybel_0(X2,X0)
                & v7_waybel_0(X2)
                & v4_orders_2(X2)
                & ~ v2_struct_0(X2) )
             => ( v10_waybel_0(X2,X0)
               => ( r2_hidden(k1_waybel_2(X0,X2),k10_yellow_6(X0,X2))
                  & r1_waybel_9(X0,X2) ) ) ) )
       => v2_waybel_2(X0) ) ) ),
    inference(rectify,[],[f1])).

fof(f7,plain,(
    ! [X0] :
      ( v2_waybel_2(X0)
      | ? [X1] :
          ( ~ v5_pre_topc(k4_waybel_1(X0,X1),X0,X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      | ? [X2] :
          ( ( ~ r2_hidden(k1_waybel_2(X0,X2),k10_yellow_6(X0,X2))
            | ~ r1_waybel_9(X0,X2) )
          & v10_waybel_0(X2,X0)
          & l1_waybel_0(X2,X0)
          & v7_waybel_0(X2)
          & v4_orders_2(X2)
          & ~ v2_struct_0(X2) )
      | ~ l1_waybel_9(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f8,plain,(
    ! [X0] :
      ( v2_waybel_2(X0)
      | ? [X1] :
          ( ~ v5_pre_topc(k4_waybel_1(X0,X1),X0,X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      | ? [X2] :
          ( ( ~ r2_hidden(k1_waybel_2(X0,X2),k10_yellow_6(X0,X2))
            | ~ r1_waybel_9(X0,X2) )
          & v10_waybel_0(X2,X0)
          & l1_waybel_0(X2,X0)
          & v7_waybel_0(X2)
          & v4_orders_2(X2)
          & ~ v2_struct_0(X2) )
      | ~ l1_waybel_9(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f7])).

fof(f14,plain,(
    ! [X0] :
      ( v2_waybel_2(X0)
      | ? [X1] :
          ( ~ v5_pre_topc(k4_waybel_1(X0,X1),X0,X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      | sP0(X0)
      | ~ l1_waybel_9(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(definition_folding,[],[f8,f13])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v5_pre_topc(k4_waybel_1(X0,X1),X0,X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ~ v5_pre_topc(k4_waybel_1(X0,sK2(X0)),X0,X0)
        & m1_subset_1(sK2(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( v2_waybel_2(X0)
      | ( ~ v5_pre_topc(k4_waybel_1(X0,sK2(X0)),X0,X0)
        & m1_subset_1(sK2(X0),u1_struct_0(X0)) )
      | sP0(X0)
      | ~ l1_waybel_9(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f14,f19])).

fof(f33,plain,(
    ! [X0] :
      ( v2_waybel_2(X0)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK2(X0)),X0,X0)
      | sP0(X0)
      | ~ l1_waybel_9(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f48,plain,(
    ~ v2_waybel_2(sK4) ),
    inference(cnf_transformation,[],[f25])).

fof(f38,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f25])).

fof(f39,plain,(
    v8_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f25])).

fof(f40,plain,(
    v3_orders_2(sK4) ),
    inference(cnf_transformation,[],[f25])).

fof(f41,plain,(
    v4_orders_2(sK4) ),
    inference(cnf_transformation,[],[f25])).

fof(f42,plain,(
    v5_orders_2(sK4) ),
    inference(cnf_transformation,[],[f25])).

fof(f43,plain,(
    v1_lattice3(sK4) ),
    inference(cnf_transformation,[],[f25])).

fof(f44,plain,(
    v2_lattice3(sK4) ),
    inference(cnf_transformation,[],[f25])).

fof(f46,plain,(
    l1_waybel_9(sK4) ),
    inference(cnf_transformation,[],[f25])).

fof(f32,plain,(
    ! [X0] :
      ( v2_waybel_2(X0)
      | m1_subset_1(sK2(X0),u1_struct_0(X0))
      | sP0(X0)
      | ~ l1_waybel_9(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
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
       => ! [X2] :
            ( ( l1_waybel_0(X2,X0)
              & v7_waybel_0(X2)
              & v4_orders_2(X2)
              & ~ v2_struct_0(X2) )
           => ( v10_waybel_0(X2,X0)
             => ( r2_hidden(k1_waybel_2(X0,X2),k10_yellow_6(X0,X2))
                & r1_waybel_9(X0,X2) ) ) ) ) ) ),
    inference(rectify,[],[f2])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X2] :
          ( ( r2_hidden(k1_waybel_2(X0,X2),k10_yellow_6(X0,X2))
            & r1_waybel_9(X0,X2) )
          | ~ v10_waybel_0(X2,X0)
          | ~ l1_waybel_0(X2,X0)
          | ~ v7_waybel_0(X2)
          | ~ v4_orders_2(X2)
          | v2_struct_0(X2) )
      | ? [X1] :
          ( ~ v5_pre_topc(k4_waybel_1(X0,X1),X0,X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
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

fof(f10,plain,(
    ! [X0] :
      ( ! [X2] :
          ( ( r2_hidden(k1_waybel_2(X0,X2),k10_yellow_6(X0,X2))
            & r1_waybel_9(X0,X2) )
          | ~ v10_waybel_0(X2,X0)
          | ~ l1_waybel_0(X2,X0)
          | ~ v7_waybel_0(X2)
          | ~ v4_orders_2(X2)
          | v2_struct_0(X2) )
      | ? [X1] :
          ( ~ v5_pre_topc(k4_waybel_1(X0,X1),X0,X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f9])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(k1_waybel_2(X0,X1),k10_yellow_6(X0,X1))
            & r1_waybel_9(X0,X1) )
          | ~ v10_waybel_0(X1,X0)
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ? [X2] :
          ( ~ v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)
          & m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f10])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X2] :
          ( ~ v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ~ v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0)
        & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(k1_waybel_2(X0,X1),k10_yellow_6(X0,X1))
            & r1_waybel_9(X0,X1) )
          | ~ v10_waybel_0(X1,X0)
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ( ~ v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0)
        & m1_subset_1(sK3(X0),u1_struct_0(X0)) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f22])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_waybel_2(X0,X1),k10_yellow_6(X0,X1))
      | ~ v10_waybel_0(X1,X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f45,plain,(
    v1_compts_1(sK4) ),
    inference(cnf_transformation,[],[f25])).

fof(f30,plain,(
    ! [X0] :
      ( v10_waybel_0(sK1(X0),X0)
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f29,plain,(
    ! [X0] :
      ( l1_waybel_0(sK1(X0),X0)
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f28,plain,(
    ! [X0] :
      ( v7_waybel_0(sK1(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f27,plain,(
    ! [X0] :
      ( v4_orders_2(sK1(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v2_struct_0(sK1(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_waybel_2(X0,X1),k10_yellow_6(X0,X1))
      | ~ v10_waybel_0(X1,X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | m1_subset_1(sK3(X0),u1_struct_0(X0))
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_waybel_9(X0,X1)
      | ~ v10_waybel_0(X1,X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | m1_subset_1(sK3(X0),u1_struct_0(X0))
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_waybel_9(X0,X1)
      | ~ v10_waybel_0(X1,X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_13,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(sK4,X0),sK4,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_0,plain,
    ( ~ r1_waybel_9(X0,sK1(X0))
    | ~ r2_hidden(k1_waybel_2(X0,sK1(X0)),k10_yellow_6(X0,sK1(X0)))
    | ~ sP0(X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_6,plain,
    ( ~ v5_pre_topc(k4_waybel_1(X0,sK2(X0)),X0,X0)
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v3_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | ~ v2_lattice3(X0)
    | ~ l1_waybel_9(X0)
    | v2_waybel_2(X0)
    | ~ v4_orders_2(X0)
    | sP0(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_12,negated_conjecture,
    ( ~ v2_waybel_2(sK4) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_252,plain,
    ( ~ v5_pre_topc(k4_waybel_1(sK4,sK2(sK4)),sK4,sK4)
    | ~ v2_pre_topc(sK4)
    | ~ v8_pre_topc(sK4)
    | ~ v3_orders_2(sK4)
    | ~ v5_orders_2(sK4)
    | ~ v1_lattice3(sK4)
    | ~ v2_lattice3(sK4)
    | ~ l1_waybel_9(sK4)
    | ~ v4_orders_2(sK4)
    | sP0(sK4) ),
    inference(resolution,[status(thm)],[c_6,c_12])).

cnf(c_22,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_21,negated_conjecture,
    ( v8_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_20,negated_conjecture,
    ( v3_orders_2(sK4) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_19,negated_conjecture,
    ( v4_orders_2(sK4) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_18,negated_conjecture,
    ( v5_orders_2(sK4) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_17,negated_conjecture,
    ( v1_lattice3(sK4) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_16,negated_conjecture,
    ( v2_lattice3(sK4) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_14,negated_conjecture,
    ( l1_waybel_9(sK4) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_254,plain,
    ( ~ v5_pre_topc(k4_waybel_1(sK4,sK2(sK4)),sK4,sK4)
    | sP0(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_252,c_22,c_21,c_20,c_19,c_18,c_17,c_16,c_14])).

cnf(c_361,plain,
    ( ~ v5_pre_topc(k4_waybel_1(sK4,sK2(sK4)),sK4,sK4)
    | ~ r1_waybel_9(sK4,sK1(sK4))
    | ~ r2_hidden(k1_waybel_2(sK4,sK1(sK4)),k10_yellow_6(sK4,sK1(sK4))) ),
    inference(resolution,[status(thm)],[c_0,c_254])).

cnf(c_487,plain,
    ( ~ m1_subset_1(sK2(sK4),u1_struct_0(sK4))
    | ~ r1_waybel_9(sK4,sK1(sK4))
    | ~ r2_hidden(k1_waybel_2(sK4,sK1(sK4)),k10_yellow_6(sK4,sK1(sK4))) ),
    inference(resolution,[status(thm)],[c_13,c_361])).

cnf(c_7,plain,
    ( m1_subset_1(sK2(X0),u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v3_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | ~ v2_lattice3(X0)
    | ~ l1_waybel_9(X0)
    | v2_waybel_2(X0)
    | ~ v4_orders_2(X0)
    | sP0(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_239,plain,
    ( m1_subset_1(sK2(sK4),u1_struct_0(sK4))
    | ~ v2_pre_topc(sK4)
    | ~ v8_pre_topc(sK4)
    | ~ v3_orders_2(sK4)
    | ~ v5_orders_2(sK4)
    | ~ v1_lattice3(sK4)
    | ~ v2_lattice3(sK4)
    | ~ l1_waybel_9(sK4)
    | ~ v4_orders_2(sK4)
    | sP0(sK4) ),
    inference(resolution,[status(thm)],[c_7,c_12])).

cnf(c_241,plain,
    ( m1_subset_1(sK2(sK4),u1_struct_0(sK4))
    | sP0(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_239,c_22,c_21,c_20,c_19,c_18,c_17,c_16,c_14])).

cnf(c_373,plain,
    ( m1_subset_1(sK2(sK4),u1_struct_0(sK4))
    | ~ r1_waybel_9(sK4,sK1(sK4))
    | ~ r2_hidden(k1_waybel_2(sK4,sK1(sK4)),k10_yellow_6(sK4,sK1(sK4))) ),
    inference(resolution,[status(thm)],[c_0,c_241])).

cnf(c_489,plain,
    ( ~ r1_waybel_9(sK4,sK1(sK4))
    | ~ r2_hidden(k1_waybel_2(sK4,sK1(sK4)),k10_yellow_6(sK4,sK1(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_487,c_373])).

cnf(c_8,plain,
    ( ~ v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0)
    | ~ l1_waybel_0(X1,X0)
    | ~ v10_waybel_0(X1,X0)
    | r2_hidden(k1_waybel_2(X0,X1),k10_yellow_6(X0,X1))
    | ~ v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v3_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | ~ v2_lattice3(X0)
    | ~ l1_waybel_9(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_455,plain,
    ( ~ m1_subset_1(sK3(sK4),u1_struct_0(sK4))
    | ~ l1_waybel_0(X0,sK4)
    | ~ v10_waybel_0(X0,sK4)
    | r2_hidden(k1_waybel_2(sK4,X0),k10_yellow_6(sK4,X0))
    | ~ v1_compts_1(sK4)
    | ~ v2_pre_topc(sK4)
    | ~ v8_pre_topc(sK4)
    | ~ v3_orders_2(sK4)
    | ~ v5_orders_2(sK4)
    | ~ v1_lattice3(sK4)
    | ~ v2_lattice3(sK4)
    | ~ l1_waybel_9(sK4)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(sK4)
    | ~ v7_waybel_0(X0) ),
    inference(resolution,[status(thm)],[c_8,c_13])).

cnf(c_15,negated_conjecture,
    ( v1_compts_1(sK4) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_459,plain,
    ( ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | r2_hidden(k1_waybel_2(sK4,X0),k10_yellow_6(sK4,X0))
    | ~ v10_waybel_0(X0,sK4)
    | ~ l1_waybel_0(X0,sK4)
    | ~ m1_subset_1(sK3(sK4),u1_struct_0(sK4))
    | ~ v7_waybel_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_455,c_22,c_21,c_20,c_19,c_18,c_17,c_16,c_15,c_14])).

cnf(c_460,plain,
    ( ~ m1_subset_1(sK3(sK4),u1_struct_0(sK4))
    | ~ l1_waybel_0(X0,sK4)
    | ~ v10_waybel_0(X0,sK4)
    | r2_hidden(k1_waybel_2(sK4,X0),k10_yellow_6(sK4,X0))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_459])).

cnf(c_592,plain,
    ( ~ m1_subset_1(sK3(sK4),u1_struct_0(sK4))
    | ~ l1_waybel_0(sK1(sK4),sK4)
    | ~ v10_waybel_0(sK1(sK4),sK4)
    | ~ r1_waybel_9(sK4,sK1(sK4))
    | v2_struct_0(sK1(sK4))
    | ~ v4_orders_2(sK1(sK4))
    | ~ v7_waybel_0(sK1(sK4)) ),
    inference(resolution,[status(thm)],[c_489,c_460])).

cnf(c_1,plain,
    ( v10_waybel_0(sK1(X0),X0)
    | ~ sP0(X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_343,plain,
    ( ~ v5_pre_topc(k4_waybel_1(sK4,sK2(sK4)),sK4,sK4)
    | v10_waybel_0(sK1(sK4),sK4) ),
    inference(resolution,[status(thm)],[c_1,c_254])).

cnf(c_500,plain,
    ( ~ m1_subset_1(sK2(sK4),u1_struct_0(sK4))
    | v10_waybel_0(sK1(sK4),sK4) ),
    inference(resolution,[status(thm)],[c_13,c_343])).

cnf(c_352,plain,
    ( m1_subset_1(sK2(sK4),u1_struct_0(sK4))
    | v10_waybel_0(sK1(sK4),sK4) ),
    inference(resolution,[status(thm)],[c_1,c_241])).

cnf(c_502,plain,
    ( v10_waybel_0(sK1(sK4),sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_500,c_352])).

cnf(c_2,plain,
    ( l1_waybel_0(sK1(X0),X0)
    | ~ sP0(X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_325,plain,
    ( ~ v5_pre_topc(k4_waybel_1(sK4,sK2(sK4)),sK4,sK4)
    | l1_waybel_0(sK1(sK4),sK4) ),
    inference(resolution,[status(thm)],[c_2,c_254])).

cnf(c_510,plain,
    ( ~ m1_subset_1(sK2(sK4),u1_struct_0(sK4))
    | l1_waybel_0(sK1(sK4),sK4) ),
    inference(resolution,[status(thm)],[c_13,c_325])).

cnf(c_334,plain,
    ( m1_subset_1(sK2(sK4),u1_struct_0(sK4))
    | l1_waybel_0(sK1(sK4),sK4) ),
    inference(resolution,[status(thm)],[c_2,c_241])).

cnf(c_512,plain,
    ( l1_waybel_0(sK1(sK4),sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_510,c_334])).

cnf(c_3,plain,
    ( v7_waybel_0(sK1(X0))
    | ~ sP0(X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_307,plain,
    ( ~ v5_pre_topc(k4_waybel_1(sK4,sK2(sK4)),sK4,sK4)
    | v7_waybel_0(sK1(sK4)) ),
    inference(resolution,[status(thm)],[c_3,c_254])).

cnf(c_520,plain,
    ( ~ m1_subset_1(sK2(sK4),u1_struct_0(sK4))
    | v7_waybel_0(sK1(sK4)) ),
    inference(resolution,[status(thm)],[c_13,c_307])).

cnf(c_316,plain,
    ( m1_subset_1(sK2(sK4),u1_struct_0(sK4))
    | v7_waybel_0(sK1(sK4)) ),
    inference(resolution,[status(thm)],[c_3,c_241])).

cnf(c_522,plain,
    ( v7_waybel_0(sK1(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_520,c_316])).

cnf(c_4,plain,
    ( v4_orders_2(sK1(X0))
    | ~ sP0(X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_289,plain,
    ( ~ v5_pre_topc(k4_waybel_1(sK4,sK2(sK4)),sK4,sK4)
    | v4_orders_2(sK1(sK4)) ),
    inference(resolution,[status(thm)],[c_4,c_254])).

cnf(c_530,plain,
    ( ~ m1_subset_1(sK2(sK4),u1_struct_0(sK4))
    | v4_orders_2(sK1(sK4)) ),
    inference(resolution,[status(thm)],[c_13,c_289])).

cnf(c_298,plain,
    ( m1_subset_1(sK2(sK4),u1_struct_0(sK4))
    | v4_orders_2(sK1(sK4)) ),
    inference(resolution,[status(thm)],[c_4,c_241])).

cnf(c_532,plain,
    ( v4_orders_2(sK1(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_530,c_298])).

cnf(c_5,plain,
    ( ~ v2_struct_0(sK1(X0))
    | ~ sP0(X0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_271,plain,
    ( ~ v5_pre_topc(k4_waybel_1(sK4,sK2(sK4)),sK4,sK4)
    | ~ v2_struct_0(sK1(sK4)) ),
    inference(resolution,[status(thm)],[c_5,c_254])).

cnf(c_540,plain,
    ( ~ m1_subset_1(sK2(sK4),u1_struct_0(sK4))
    | ~ v2_struct_0(sK1(sK4)) ),
    inference(resolution,[status(thm)],[c_13,c_271])).

cnf(c_280,plain,
    ( m1_subset_1(sK2(sK4),u1_struct_0(sK4))
    | ~ v2_struct_0(sK1(sK4)) ),
    inference(resolution,[status(thm)],[c_5,c_241])).

cnf(c_542,plain,
    ( ~ v2_struct_0(sK1(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_540,c_280])).

cnf(c_9,plain,
    ( m1_subset_1(sK3(X0),u1_struct_0(X0))
    | ~ l1_waybel_0(X1,X0)
    | ~ v10_waybel_0(X1,X0)
    | r2_hidden(k1_waybel_2(X0,X1),k10_yellow_6(X0,X1))
    | ~ v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v3_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | ~ v2_lattice3(X0)
    | ~ l1_waybel_9(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_579,plain,
    ( m1_subset_1(sK3(sK4),u1_struct_0(sK4))
    | ~ l1_waybel_0(sK1(sK4),sK4)
    | ~ v10_waybel_0(sK1(sK4),sK4)
    | ~ r1_waybel_9(sK4,sK1(sK4))
    | ~ v1_compts_1(sK4)
    | ~ v2_pre_topc(sK4)
    | ~ v8_pre_topc(sK4)
    | ~ v3_orders_2(sK4)
    | ~ v5_orders_2(sK4)
    | ~ v1_lattice3(sK4)
    | ~ v2_lattice3(sK4)
    | ~ l1_waybel_9(sK4)
    | v2_struct_0(sK1(sK4))
    | ~ v4_orders_2(sK1(sK4))
    | ~ v4_orders_2(sK4)
    | ~ v7_waybel_0(sK1(sK4)) ),
    inference(resolution,[status(thm)],[c_9,c_489])).

cnf(c_581,plain,
    ( m1_subset_1(sK3(sK4),u1_struct_0(sK4))
    | ~ r1_waybel_9(sK4,sK1(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_579,c_22,c_21,c_20,c_19,c_18,c_17,c_16,c_15,c_14,c_280,c_298,c_316,c_334,c_352,c_500,c_510,c_520,c_530,c_540])).

cnf(c_594,plain,
    ( ~ r1_waybel_9(sK4,sK1(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_592,c_280,c_298,c_316,c_334,c_352,c_500,c_510,c_520,c_530,c_540,c_581])).

cnf(c_11,plain,
    ( m1_subset_1(sK3(X0),u1_struct_0(X0))
    | ~ l1_waybel_0(X1,X0)
    | ~ v10_waybel_0(X1,X0)
    | r1_waybel_9(X0,X1)
    | ~ v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v3_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | ~ v2_lattice3(X0)
    | ~ l1_waybel_9(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_604,plain,
    ( m1_subset_1(sK3(sK4),u1_struct_0(sK4))
    | ~ l1_waybel_0(X0,sK4)
    | ~ v10_waybel_0(X0,sK4)
    | r1_waybel_9(sK4,X0)
    | ~ v1_compts_1(sK4)
    | ~ v2_pre_topc(sK4)
    | ~ v8_pre_topc(sK4)
    | ~ v3_orders_2(sK4)
    | ~ v5_orders_2(sK4)
    | ~ v1_lattice3(sK4)
    | ~ v2_lattice3(sK4)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(sK4)
    | ~ v7_waybel_0(X0) ),
    inference(resolution,[status(thm)],[c_11,c_14])).

cnf(c_10,plain,
    ( ~ v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0)
    | ~ l1_waybel_0(X1,X0)
    | ~ v10_waybel_0(X1,X0)
    | r1_waybel_9(X0,X1)
    | ~ v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v3_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | ~ v2_lattice3(X0)
    | ~ l1_waybel_9(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_423,plain,
    ( ~ m1_subset_1(sK3(sK4),u1_struct_0(sK4))
    | ~ l1_waybel_0(X0,sK4)
    | ~ v10_waybel_0(X0,sK4)
    | r1_waybel_9(sK4,X0)
    | ~ v1_compts_1(sK4)
    | ~ v2_pre_topc(sK4)
    | ~ v8_pre_topc(sK4)
    | ~ v3_orders_2(sK4)
    | ~ v5_orders_2(sK4)
    | ~ v1_lattice3(sK4)
    | ~ v2_lattice3(sK4)
    | ~ l1_waybel_9(sK4)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(sK4)
    | ~ v7_waybel_0(X0) ),
    inference(resolution,[status(thm)],[c_10,c_13])).

cnf(c_427,plain,
    ( ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | r1_waybel_9(sK4,X0)
    | ~ v10_waybel_0(X0,sK4)
    | ~ l1_waybel_0(X0,sK4)
    | ~ m1_subset_1(sK3(sK4),u1_struct_0(sK4))
    | ~ v7_waybel_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_423,c_22,c_21,c_20,c_19,c_18,c_17,c_16,c_15,c_14])).

cnf(c_428,plain,
    ( ~ m1_subset_1(sK3(sK4),u1_struct_0(sK4))
    | ~ l1_waybel_0(X0,sK4)
    | ~ v10_waybel_0(X0,sK4)
    | r1_waybel_9(sK4,X0)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_427])).

cnf(c_608,plain,
    ( ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | ~ l1_waybel_0(X0,sK4)
    | ~ v10_waybel_0(X0,sK4)
    | r1_waybel_9(sK4,X0)
    | ~ v7_waybel_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_604,c_22,c_21,c_20,c_19,c_18,c_17,c_16,c_15,c_428])).

cnf(c_609,plain,
    ( ~ l1_waybel_0(X0,sK4)
    | ~ v10_waybel_0(X0,sK4)
    | r1_waybel_9(sK4,X0)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_608])).

cnf(c_640,plain,
    ( ~ l1_waybel_0(sK1(sK4),sK4)
    | ~ v10_waybel_0(sK1(sK4),sK4)
    | v2_struct_0(sK1(sK4))
    | ~ v4_orders_2(sK1(sK4))
    | ~ v7_waybel_0(sK1(sK4)) ),
    inference(resolution,[status(thm)],[c_594,c_609])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_640,c_542,c_532,c_522,c_512,c_502])).


%------------------------------------------------------------------------------
