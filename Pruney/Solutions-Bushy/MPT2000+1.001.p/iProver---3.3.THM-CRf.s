%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT2000+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:01 EST 2020

% Result     : Theorem 0.65s
% Output     : CNFRefutation 0.65s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 164 expanded)
%              Number of clauses        :   24 (  24 expanded)
%              Number of leaves         :    9 (  54 expanded)
%              Depth                    :   13
%              Number of atoms          :  548 (1866 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   21 (   8 average)
%              Maximal clause size      :   24 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_waybel_3(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ~ ( ~ v5_waybel_6(X1,X0)
              & ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ~ ( ~ r3_orders_2(X0,X3,X1)
                          & ~ r3_orders_2(X0,X2,X1)
                          & r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1) ) ) )
              & v5_waybel_7(k1_waybel_4(X0),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v5_waybel_6(X1,X0)
          | ? [X2] :
              ( ? [X3] :
                  ( ~ r3_orders_2(X0,X3,X1)
                  & ~ r3_orders_2(X0,X2,X1)
                  & r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v5_waybel_7(k1_waybel_4(X0),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_waybel_3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f6,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v5_waybel_6(X1,X0)
          | ? [X2] :
              ( ? [X3] :
                  ( ~ r3_orders_2(X0,X3,X1)
                  & ~ r3_orders_2(X0,X2,X1)
                  & r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v5_waybel_7(k1_waybel_4(X0),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_waybel_3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f5])).

fof(f12,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r3_orders_2(X0,X3,X1)
          & ~ r3_orders_2(X0,X2,X1)
          & r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r3_orders_2(X0,sK1(X0,X1),X1)
        & ~ r3_orders_2(X0,X2,X1)
        & r1_waybel_3(X0,k12_lattice3(X0,X2,sK1(X0,X1)),X1)
        & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r3_orders_2(X0,X3,X1)
              & ~ r3_orders_2(X0,X2,X1)
              & r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r3_orders_2(X0,X3,X1)
            & ~ r3_orders_2(X0,sK0(X0,X1),X1)
            & r1_waybel_3(X0,k12_lattice3(X0,sK0(X0,X1),X3),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v5_waybel_6(X1,X0)
          | ( ~ r3_orders_2(X0,sK1(X0,X1),X1)
            & ~ r3_orders_2(X0,sK0(X0,X1),X1)
            & r1_waybel_3(X0,k12_lattice3(X0,sK0(X0,X1),sK1(X0,X1)),X1)
            & m1_subset_1(sK1(X0,X1),u1_struct_0(X0))
            & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)) )
          | ~ v5_waybel_7(k1_waybel_4(X0),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_waybel_3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f12,f11])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v5_waybel_6(X1,X0)
      | r1_waybel_3(X0,k12_lattice3(X0,sK0(X0,X1),sK1(X0,X1)),X1)
      | ~ v5_waybel_7(k1_waybel_4(X0),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_waybel_3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_waybel_3(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ( v5_waybel_7(k1_waybel_4(X0),X0)
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( v4_waybel_7(X1,X0)
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ~ ( ~ r3_orders_2(X0,X3,X1)
                          & ~ r3_orders_2(X0,X2,X1)
                          & r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_waybel_7(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r3_orders_2(X0,X3,X1)
                    | r3_orders_2(X0,X2,X1)
                    | ~ r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v5_waybel_7(k1_waybel_4(X0),X0)
      | ~ l1_orders_2(X0)
      | ~ v3_waybel_3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_waybel_7(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r3_orders_2(X0,X3,X1)
                    | r3_orders_2(X0,X2,X1)
                    | ~ r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v5_waybel_7(k1_waybel_4(X0),X0)
      | ~ l1_orders_2(X0)
      | ~ v3_waybel_3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f7])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_waybel_7(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r3_orders_2(X0,X3,X1)
                      & ~ r3_orders_2(X0,X2,X1)
                      & r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ! [X3] :
                      ( r3_orders_2(X0,X3,X1)
                      | r3_orders_2(X0,X2,X1)
                      | ~ r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v4_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v5_waybel_7(k1_waybel_4(X0),X0)
      | ~ l1_orders_2(X0)
      | ~ v3_waybel_3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_waybel_7(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r3_orders_2(X0,X3,X1)
                      & ~ r3_orders_2(X0,X2,X1)
                      & r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r3_orders_2(X0,X5,X1)
                      | r3_orders_2(X0,X4,X1)
                      | ~ r1_waybel_3(X0,k12_lattice3(X0,X4,X5),X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v4_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v5_waybel_7(k1_waybel_4(X0),X0)
      | ~ l1_orders_2(X0)
      | ~ v3_waybel_3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(rectify,[],[f14])).

fof(f17,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r3_orders_2(X0,X3,X1)
          & ~ r3_orders_2(X0,X2,X1)
          & r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r3_orders_2(X0,sK3(X0,X1),X1)
        & ~ r3_orders_2(X0,X2,X1)
        & r1_waybel_3(X0,k12_lattice3(X0,X2,sK3(X0,X1)),X1)
        & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r3_orders_2(X0,X3,X1)
              & ~ r3_orders_2(X0,X2,X1)
              & r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r3_orders_2(X0,X3,X1)
            & ~ r3_orders_2(X0,sK2(X0,X1),X1)
            & r1_waybel_3(X0,k12_lattice3(X0,sK2(X0,X1),X3),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_waybel_7(X1,X0)
              | ( ~ r3_orders_2(X0,sK3(X0,X1),X1)
                & ~ r3_orders_2(X0,sK2(X0,X1),X1)
                & r1_waybel_3(X0,k12_lattice3(X0,sK2(X0,X1),sK3(X0,X1)),X1)
                & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r3_orders_2(X0,X5,X1)
                      | r3_orders_2(X0,X4,X1)
                      | ~ r1_waybel_3(X0,k12_lattice3(X0,X4,X5),X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v4_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v5_waybel_7(k1_waybel_4(X0),X0)
      | ~ l1_orders_2(X0)
      | ~ v3_waybel_3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f15,f17,f16])).

fof(f27,plain,(
    ! [X4,X0,X5,X1] :
      ( r3_orders_2(X0,X5,X1)
      | r3_orders_2(X0,X4,X1)
      | ~ r1_waybel_3(X0,k12_lattice3(X0,X4,X5),X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v4_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_waybel_7(k1_waybel_4(X0),X0)
      | ~ l1_orders_2(X0)
      | ~ v3_waybel_3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v5_waybel_6(X1,X0)
      | ~ r3_orders_2(X0,sK0(X0,X1),X1)
      | ~ v5_waybel_7(k1_waybel_4(X0),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_waybel_3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v5_waybel_6(X1,X0)
      | ~ r3_orders_2(X0,sK1(X0,X1),X1)
      | ~ v5_waybel_7(k1_waybel_4(X0),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_waybel_3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v5_waybel_6(X1,X0)
      | m1_subset_1(sK0(X0,X1),u1_struct_0(X0))
      | ~ v5_waybel_7(k1_waybel_4(X0),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_waybel_3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v5_waybel_6(X1,X0)
      | m1_subset_1(sK1(X0,X1),u1_struct_0(X0))
      | ~ v5_waybel_7(k1_waybel_4(X0),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_waybel_3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f3,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_waybel_3(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ( v5_waybel_7(k1_waybel_4(X0),X0)
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( v4_waybel_7(X1,X0)
             => v5_waybel_6(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v3_waybel_3(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ( v5_waybel_7(k1_waybel_4(X0),X0)
         => ! [X1] :
              ( m1_subset_1(X1,u1_struct_0(X0))
             => ( v4_waybel_7(X1,X0)
               => v5_waybel_6(X1,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v5_waybel_6(X1,X0)
          & v4_waybel_7(X1,X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & v5_waybel_7(k1_waybel_4(X0),X0)
      & l1_orders_2(X0)
      & v3_waybel_3(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v5_waybel_6(X1,X0)
          & v4_waybel_7(X1,X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & v5_waybel_7(k1_waybel_4(X0),X0)
      & l1_orders_2(X0)
      & v3_waybel_3(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f9])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v5_waybel_6(X1,X0)
          & v4_waybel_7(X1,X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ~ v5_waybel_6(sK5,X0)
        & v4_waybel_7(sK5,X0)
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v5_waybel_6(X1,X0)
            & v4_waybel_7(X1,X0)
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & v5_waybel_7(k1_waybel_4(X0),X0)
        & l1_orders_2(X0)
        & v3_waybel_3(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X1] :
          ( ~ v5_waybel_6(X1,sK4)
          & v4_waybel_7(X1,sK4)
          & m1_subset_1(X1,u1_struct_0(sK4)) )
      & v5_waybel_7(k1_waybel_4(sK4),sK4)
      & l1_orders_2(sK4)
      & v3_waybel_3(sK4)
      & v2_lattice3(sK4)
      & v1_lattice3(sK4)
      & v1_yellow_0(sK4)
      & v5_orders_2(sK4)
      & v4_orders_2(sK4)
      & v3_orders_2(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ~ v5_waybel_6(sK5,sK4)
    & v4_waybel_7(sK5,sK4)
    & m1_subset_1(sK5,u1_struct_0(sK4))
    & v5_waybel_7(k1_waybel_4(sK4),sK4)
    & l1_orders_2(sK4)
    & v3_waybel_3(sK4)
    & v2_lattice3(sK4)
    & v1_lattice3(sK4)
    & v1_yellow_0(sK4)
    & v5_orders_2(sK4)
    & v4_orders_2(sK4)
    & v3_orders_2(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f10,f20,f19])).

fof(f44,plain,(
    ~ v5_waybel_6(sK5,sK4) ),
    inference(cnf_transformation,[],[f21])).

fof(f43,plain,(
    v4_waybel_7(sK5,sK4) ),
    inference(cnf_transformation,[],[f21])).

fof(f42,plain,(
    m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f21])).

fof(f41,plain,(
    v5_waybel_7(k1_waybel_4(sK4),sK4) ),
    inference(cnf_transformation,[],[f21])).

fof(f40,plain,(
    l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f21])).

fof(f39,plain,(
    v3_waybel_3(sK4) ),
    inference(cnf_transformation,[],[f21])).

fof(f38,plain,(
    v2_lattice3(sK4) ),
    inference(cnf_transformation,[],[f21])).

fof(f37,plain,(
    v1_lattice3(sK4) ),
    inference(cnf_transformation,[],[f21])).

fof(f36,plain,(
    v1_yellow_0(sK4) ),
    inference(cnf_transformation,[],[f21])).

fof(f35,plain,(
    v5_orders_2(sK4) ),
    inference(cnf_transformation,[],[f21])).

fof(f34,plain,(
    v4_orders_2(sK4) ),
    inference(cnf_transformation,[],[f21])).

fof(f33,plain,(
    v3_orders_2(sK4) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_2,plain,
    ( r1_waybel_3(X0,k12_lattice3(X0,sK0(X0,X1),sK1(X0,X1)),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_waybel_7(k1_waybel_4(X0),X0)
    | v5_waybel_6(X1,X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_yellow_0(X0)
    | ~ v1_lattice3(X0)
    | ~ v2_lattice3(X0)
    | ~ v3_waybel_3(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_10,plain,
    ( ~ r1_waybel_3(X0,k12_lattice3(X0,X1,X2),X3)
    | r3_orders_2(X0,X1,X3)
    | r3_orders_2(X0,X2,X3)
    | ~ v4_waybel_7(X3,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_waybel_7(k1_waybel_4(X0),X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_yellow_0(X0)
    | ~ v1_lattice3(X0)
    | ~ v2_lattice3(X0)
    | ~ v3_waybel_3(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_229,plain,
    ( r3_orders_2(X0,sK0(X0,X1),X1)
    | r3_orders_2(X0,sK1(X0,X1),X1)
    | ~ v4_waybel_7(X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(sK0(X0,X1),u1_struct_0(X0))
    | ~ m1_subset_1(sK1(X0,X1),u1_struct_0(X0))
    | ~ v5_waybel_7(k1_waybel_4(X0),X0)
    | v5_waybel_6(X1,X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_yellow_0(X0)
    | ~ v1_lattice3(X0)
    | ~ v2_lattice3(X0)
    | ~ v3_waybel_3(X0)
    | ~ l1_orders_2(X0) ),
    inference(resolution,[status(thm)],[c_2,c_10])).

cnf(c_1,plain,
    ( ~ r3_orders_2(X0,sK0(X0,X1),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_waybel_7(k1_waybel_4(X0),X0)
    | v5_waybel_6(X1,X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_yellow_0(X0)
    | ~ v1_lattice3(X0)
    | ~ v2_lattice3(X0)
    | ~ v3_waybel_3(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_0,plain,
    ( ~ r3_orders_2(X0,sK1(X0,X1),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_waybel_7(k1_waybel_4(X0),X0)
    | v5_waybel_6(X1,X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_yellow_0(X0)
    | ~ v1_lattice3(X0)
    | ~ v2_lattice3(X0)
    | ~ v3_waybel_3(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_233,plain,
    ( ~ v4_waybel_7(X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(sK0(X0,X1),u1_struct_0(X0))
    | ~ m1_subset_1(sK1(X0,X1),u1_struct_0(X0))
    | ~ v5_waybel_7(k1_waybel_4(X0),X0)
    | v5_waybel_6(X1,X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_yellow_0(X0)
    | ~ v1_lattice3(X0)
    | ~ v2_lattice3(X0)
    | ~ v3_waybel_3(X0)
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_229,c_1,c_0])).

cnf(c_234,plain,
    ( ~ v4_waybel_7(X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(sK0(X1,X0),u1_struct_0(X1))
    | ~ m1_subset_1(sK1(X1,X0),u1_struct_0(X1))
    | ~ v5_waybel_7(k1_waybel_4(X1),X1)
    | v5_waybel_6(X0,X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_yellow_0(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ v3_waybel_3(X1)
    | ~ l1_orders_2(X1) ),
    inference(renaming,[status(thm)],[c_233])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(sK0(X1,X0),u1_struct_0(X1))
    | ~ v5_waybel_7(k1_waybel_4(X1),X1)
    | v5_waybel_6(X0,X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_yellow_0(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ v3_waybel_3(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(sK1(X1,X0),u1_struct_0(X1))
    | ~ v5_waybel_7(k1_waybel_4(X1),X1)
    | v5_waybel_6(X0,X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_yellow_0(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ v3_waybel_3(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_239,plain,
    ( ~ v4_waybel_7(X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v5_waybel_7(k1_waybel_4(X1),X1)
    | v5_waybel_6(X0,X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_yellow_0(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ v3_waybel_3(X1)
    | ~ l1_orders_2(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_234,c_4,c_3])).

cnf(c_11,negated_conjecture,
    ( ~ v5_waybel_6(sK5,sK4) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_284,plain,
    ( ~ v4_waybel_7(sK5,sK4)
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ v5_waybel_7(k1_waybel_4(sK4),sK4)
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v5_orders_2(sK4)
    | ~ v1_yellow_0(sK4)
    | ~ v1_lattice3(sK4)
    | ~ v2_lattice3(sK4)
    | ~ v3_waybel_3(sK4)
    | ~ l1_orders_2(sK4) ),
    inference(resolution,[status(thm)],[c_239,c_11])).

cnf(c_12,negated_conjecture,
    ( v4_waybel_7(sK5,sK4) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_14,negated_conjecture,
    ( v5_waybel_7(k1_waybel_4(sK4),sK4) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_15,negated_conjecture,
    ( l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_16,negated_conjecture,
    ( v3_waybel_3(sK4) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_17,negated_conjecture,
    ( v2_lattice3(sK4) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_18,negated_conjecture,
    ( v1_lattice3(sK4) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_19,negated_conjecture,
    ( v1_yellow_0(sK4) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_20,negated_conjecture,
    ( v5_orders_2(sK4) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_21,negated_conjecture,
    ( v4_orders_2(sK4) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_22,negated_conjecture,
    ( v3_orders_2(sK4) ),
    inference(cnf_transformation,[],[f33])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_284,c_12,c_13,c_14,c_15,c_16,c_17,c_18,c_19,c_20,c_21,c_22])).


%------------------------------------------------------------------------------
