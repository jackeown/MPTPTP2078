%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:04 EST 2020

% Result     : CounterSatisfiable 1.75s
% Output     : Saturation 1.75s
% Verified   : 
% Statistics : Number of formulae       :  199 (2912 expanded)
%              Number of clauses        :  149 ( 757 expanded)
%              Number of leaves         :   15 ( 686 expanded)
%              Depth                    :   23
%              Number of atoms          :  944 (18530 expanded)
%              Number of equality atoms :  250 (2471 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal clause size      :   15 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r3_orders_2(X0,X1,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( k2_yellow_0(X0,k6_waybel_0(X0,X1)) = X1
            & r2_yellow_0(X0,k6_waybel_0(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( k2_yellow_0(X0,k6_waybel_0(X0,X1)) = X1
              & r2_yellow_0(X0,k6_waybel_0(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f8,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( k2_yellow_0(X0,k6_waybel_0(X0,X1)) = X1
              & r2_yellow_0(X0,k6_waybel_0(X0,X1)) ) ) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_yellow_0(X0,k6_waybel_0(X0,X1)) != X1
            | ~ r2_yellow_0(X0,k6_waybel_0(X0,X1)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_yellow_0(X0,k6_waybel_0(X0,X1)) != X1
            | ~ r2_yellow_0(X0,k6_waybel_0(X0,X1)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( k2_yellow_0(X0,k6_waybel_0(X0,X1)) != X1
            | ~ r2_yellow_0(X0,k6_waybel_0(X0,X1)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ( k2_yellow_0(X0,k6_waybel_0(X0,sK3)) != sK3
          | ~ r2_yellow_0(X0,k6_waybel_0(X0,sK3)) )
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_yellow_0(X0,k6_waybel_0(X0,X1)) != X1
              | ~ r2_yellow_0(X0,k6_waybel_0(X0,X1)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( k2_yellow_0(sK2,k6_waybel_0(sK2,X1)) != X1
            | ~ r2_yellow_0(sK2,k6_waybel_0(sK2,X1)) )
          & m1_subset_1(X1,u1_struct_0(sK2)) )
      & l1_orders_2(sK2)
      & v5_orders_2(sK2)
      & v3_orders_2(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ( k2_yellow_0(sK2,k6_waybel_0(sK2,sK3)) != sK3
      | ~ r2_yellow_0(sK2,k6_waybel_0(sK2,sK3)) )
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_orders_2(sK2)
    & v5_orders_2(sK2)
    & v3_orders_2(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f18,f27,f26])).

fof(f45,plain,(
    v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f44,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f47,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f28])).

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

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f19,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f48,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
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
    inference(rectify,[],[f4])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X1)
          & r1_lattice3(X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK1(X0,X1,X2),X1)
        & r1_lattice3(X0,X2,sK1(X0,X1,X2))
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
                | ( ~ r1_orders_2(X0,sK1(X0,X1,X2),X1)
                  & r1_lattice3(X0,X2,sK1(X0,X1,X2))
                  & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f24])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k2_yellow_0(X0,X2) = X1
      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
      | ~ r1_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f46,plain,(
    v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k2_yellow_0(X0,X2) = X1
      | r1_lattice3(X0,X2,sK1(X0,X1,X2))
      | ~ r1_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f13])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X2,X4)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f20])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
        & r2_hidden(sK0(X0,X1,X2),X1)
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
                & r2_hidden(sK0(X0,X1,X2),X1)
                & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X2,X4)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).

fof(f32,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X2,X4)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k2_yellow_0(X0,X2) = X1
      | ~ r1_orders_2(X0,sK1(X0,X1,X2),X1)
      | ~ r1_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r2_yellow_0(X0,X2)
      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
      | ~ r1_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r2_yellow_0(X0,X2)
      | r1_lattice3(X0,X2,sK1(X0,X1,X2))
      | ~ r1_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r2_yellow_0(X0,X2)
      | ~ r1_orders_2(X0,sK1(X0,X1,X2),X1)
      | ~ r1_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f37,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X1)
      | ~ r1_lattice3(X0,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X2)
      | k2_yellow_0(X0,X2) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f50,plain,(
    ! [X4,X2,X0] :
      ( r1_orders_2(X0,X4,k2_yellow_0(X0,X2))
      | ~ r1_lattice3(X0,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X2)
      | ~ m1_subset_1(k2_yellow_0(X0,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f37])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X2,X1)
      | ~ r2_yellow_0(X0,X2)
      | k2_yellow_0(X0,X2) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f51,plain,(
    ! [X2,X0] :
      ( r1_lattice3(X0,X2,k2_yellow_0(X0,X2))
      | ~ r2_yellow_0(X0,X2)
      | ~ m1_subset_1(k2_yellow_0(X0,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f49,plain,
    ( k2_yellow_0(sK2,k6_waybel_0(sK2,sK3)) != sK3
    | ~ r2_yellow_0(sK2,k6_waybel_0(sK2,sK3)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_2,plain,
    ( r3_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_19,negated_conjecture,
    ( v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_271,plain,
    ( r3_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_19])).

cnf(c_272,plain,
    ( r3_orders_2(sK2,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_271])).

cnf(c_20,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_17,negated_conjecture,
    ( l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_276,plain,
    ( r3_orders_2(sK2,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_272,c_20,c_17])).

cnf(c_277,plain,
    ( r3_orders_2(sK2,X0,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_276])).

cnf(c_1,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_292,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_19])).

cnf(c_293,plain,
    ( r1_orders_2(sK2,X0,X1)
    | ~ r3_orders_2(sK2,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_292])).

cnf(c_297,plain,
    ( r1_orders_2(sK2,X0,X1)
    | ~ r3_orders_2(sK2,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_293,c_20,c_17])).

cnf(c_298,plain,
    ( r1_orders_2(sK2,X0,X1)
    | ~ r3_orders_2(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_297])).

cnf(c_355,plain,
    ( r1_orders_2(sK2,X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X3,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | X0 != X3
    | X1 != X3
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_277,c_298])).

cnf(c_356,plain,
    ( r1_orders_2(sK2,X0,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_355])).

cnf(c_1790,plain,
    ( r1_orders_2(sK2,X0_47,X0_47)
    | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
    | ~ m1_subset_1(X0_47,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_356])).

cnf(c_1793,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(sK2))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_1790])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1822,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ sP0_iProver_split ),
    inference(instantiation,[status(thm)],[c_1793])).

cnf(c_1894,plain,
    ( ~ sP0_iProver_split ),
    inference(global_propositional_subsumption,[status(thm)],[c_1793,c_16,c_1822])).

cnf(c_1795,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_1790])).

cnf(c_1882,plain,
    ( sP1_iProver_split ),
    inference(global_propositional_subsumption,[status(thm)],[c_1795,c_16,c_1822])).

cnf(c_211,plain,
    ( ~ v5_orders_2(X0)
    | v5_orders_2(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_209,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_207,plain,
    ( ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_206,plain,
    ( ~ v3_orders_2(X0)
    | v3_orders_2(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_205,plain,
    ( ~ l1_orders_2(X0)
    | l1_orders_2(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1796,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_12,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X2,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k2_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_18,negated_conjecture,
    ( v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_422,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X2,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | k2_yellow_0(X0,X1) = X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_18])).

cnf(c_423,plain,
    ( ~ r1_lattice3(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(sK1(sK2,X1,X0),u1_struct_0(sK2))
    | ~ l1_orders_2(sK2)
    | k2_yellow_0(sK2,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_422])).

cnf(c_427,plain,
    ( m1_subset_1(sK1(sK2,X1,X0),u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ r1_lattice3(sK2,X0,X1)
    | k2_yellow_0(sK2,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_423,c_17])).

cnf(c_428,plain,
    ( ~ r1_lattice3(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(sK1(sK2,X1,X0),u1_struct_0(sK2))
    | k2_yellow_0(sK2,X0) = X1 ),
    inference(renaming,[status(thm)],[c_427])).

cnf(c_1787,plain,
    ( ~ r1_lattice3(sK2,X0_46,X0_47)
    | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
    | m1_subset_1(sK1(sK2,X0_47,X0_46),u1_struct_0(sK2))
    | k2_yellow_0(sK2,X0_46) = X0_47 ),
    inference(subtyping,[status(esa)],[c_428])).

cnf(c_2124,plain,
    ( k2_yellow_0(sK2,X0_46) = X0_47
    | r1_lattice3(sK2,X0_46,X0_47) != iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK1(sK2,X0_47,X0_46),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1787])).

cnf(c_11,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_lattice3(X0,X1,sK1(X0,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k2_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_446,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_lattice3(X0,X1,sK1(X0,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | k2_yellow_0(X0,X1) = X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_18])).

cnf(c_447,plain,
    ( ~ r1_lattice3(sK2,X0,X1)
    | r1_lattice3(sK2,X0,sK1(sK2,X1,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ l1_orders_2(sK2)
    | k2_yellow_0(sK2,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_446])).

cnf(c_451,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r1_lattice3(sK2,X0,sK1(sK2,X1,X0))
    | ~ r1_lattice3(sK2,X0,X1)
    | k2_yellow_0(sK2,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_447,c_17])).

cnf(c_452,plain,
    ( ~ r1_lattice3(sK2,X0,X1)
    | r1_lattice3(sK2,X0,sK1(sK2,X1,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k2_yellow_0(sK2,X0) = X1 ),
    inference(renaming,[status(thm)],[c_451])).

cnf(c_1786,plain,
    ( ~ r1_lattice3(sK2,X0_46,X0_47)
    | r1_lattice3(sK2,X0_46,sK1(sK2,X0_47,X0_46))
    | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
    | k2_yellow_0(sK2,X0_46) = X0_47 ),
    inference(subtyping,[status(esa)],[c_452])).

cnf(c_2125,plain,
    ( k2_yellow_0(sK2,X0_46) = X0_47
    | r1_lattice3(sK2,X0_46,X0_47) != iProver_top
    | r1_lattice3(sK2,X0_46,sK1(sK2,X0_47,X0_46)) = iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1786])).

cnf(c_6,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X2,X3)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_606,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X2,X3)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_17])).

cnf(c_607,plain,
    ( ~ r1_lattice3(sK2,X0,X1)
    | r1_orders_2(sK2,X1,X2)
    | ~ r2_hidden(X2,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_606])).

cnf(c_4,plain,
    ( r1_lattice3(X0,X1,X2)
    | r2_hidden(sK0(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_640,plain,
    ( r1_lattice3(X0,X1,X2)
    | r2_hidden(sK0(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_17])).

cnf(c_641,plain,
    ( r1_lattice3(sK2,X0,X1)
    | r2_hidden(sK0(sK2,X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_640])).

cnf(c_688,plain,
    ( ~ r1_lattice3(sK2,X0,X1)
    | r1_lattice3(sK2,X2,X3)
    | r1_orders_2(sK2,X1,X4)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X4,u1_struct_0(sK2))
    | ~ m1_subset_1(X3,u1_struct_0(sK2))
    | X2 != X0
    | sK0(sK2,X2,X3) != X4 ),
    inference(resolution_lifted,[status(thm)],[c_607,c_641])).

cnf(c_689,plain,
    ( ~ r1_lattice3(sK2,X0,X1)
    | r1_lattice3(sK2,X0,X2)
    | r1_orders_2(sK2,X1,sK0(sK2,X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(sK0(sK2,X0,X2),u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_688])).

cnf(c_5,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_625,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_17])).

cnf(c_626,plain,
    ( r1_lattice3(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(sK0(sK2,X0,X1),u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_625])).

cnf(c_703,plain,
    ( ~ r1_lattice3(sK2,X0,X1)
    | r1_lattice3(sK2,X0,X2)
    | r1_orders_2(sK2,X1,sK0(sK2,X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_689,c_626])).

cnf(c_1779,plain,
    ( ~ r1_lattice3(sK2,X0_46,X0_47)
    | r1_lattice3(sK2,X0_46,X1_47)
    | r1_orders_2(sK2,X0_47,sK0(sK2,X0_46,X1_47))
    | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
    | ~ m1_subset_1(X0_47,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_703])).

cnf(c_2132,plain,
    ( r1_lattice3(sK2,X0_46,X0_47) != iProver_top
    | r1_lattice3(sK2,X0_46,X1_47) = iProver_top
    | r1_orders_2(sK2,X0_47,sK0(sK2,X0_46,X1_47)) = iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1779])).

cnf(c_10,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK1(X0,X2,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k2_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_470,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK1(X0,X2,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | k2_yellow_0(X0,X1) = X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_18])).

cnf(c_471,plain,
    ( ~ r1_lattice3(sK2,X0,X1)
    | ~ r1_orders_2(sK2,sK1(sK2,X1,X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ l1_orders_2(sK2)
    | k2_yellow_0(sK2,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_470])).

cnf(c_475,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ r1_orders_2(sK2,sK1(sK2,X1,X0),X1)
    | ~ r1_lattice3(sK2,X0,X1)
    | k2_yellow_0(sK2,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_471,c_17])).

cnf(c_476,plain,
    ( ~ r1_lattice3(sK2,X0,X1)
    | ~ r1_orders_2(sK2,sK1(sK2,X1,X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k2_yellow_0(sK2,X0) = X1 ),
    inference(renaming,[status(thm)],[c_475])).

cnf(c_1785,plain,
    ( ~ r1_lattice3(sK2,X0_46,X0_47)
    | ~ r1_orders_2(sK2,sK1(sK2,X0_47,X0_46),X0_47)
    | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
    | k2_yellow_0(sK2,X0_46) = X0_47 ),
    inference(subtyping,[status(esa)],[c_476])).

cnf(c_2126,plain,
    ( k2_yellow_0(sK2,X0_46) = X0_47
    | r1_lattice3(sK2,X0_46,X0_47) != iProver_top
    | r1_orders_2(sK2,sK1(sK2,X0_47,X0_46),X0_47) != iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1785])).

cnf(c_2509,plain,
    ( sK0(sK2,X0_46,X0_47) = k2_yellow_0(sK2,X1_46)
    | r1_lattice3(sK2,X0_46,X0_47) = iProver_top
    | r1_lattice3(sK2,X0_46,sK1(sK2,sK0(sK2,X0_46,X0_47),X1_46)) != iProver_top
    | r1_lattice3(sK2,X1_46,sK0(sK2,X0_46,X0_47)) != iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK1(sK2,sK0(sK2,X0_46,X0_47),X1_46),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK0(sK2,X0_46,X0_47),u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2132,c_2126])).

cnf(c_1781,plain,
    ( r1_lattice3(sK2,X0_46,X0_47)
    | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
    | m1_subset_1(sK0(sK2,X0_46,X0_47),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_626])).

cnf(c_1848,plain,
    ( r1_lattice3(sK2,X0_46,X0_47) = iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK0(sK2,X0_46,X0_47),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1781])).

cnf(c_3010,plain,
    ( m1_subset_1(sK1(sK2,sK0(sK2,X0_46,X0_47),X1_46),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
    | r1_lattice3(sK2,X1_46,sK0(sK2,X0_46,X0_47)) != iProver_top
    | r1_lattice3(sK2,X0_46,sK1(sK2,sK0(sK2,X0_46,X0_47),X1_46)) != iProver_top
    | r1_lattice3(sK2,X0_46,X0_47) = iProver_top
    | sK0(sK2,X0_46,X0_47) = k2_yellow_0(sK2,X1_46) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2509,c_1848])).

cnf(c_3011,plain,
    ( sK0(sK2,X0_46,X0_47) = k2_yellow_0(sK2,X1_46)
    | r1_lattice3(sK2,X0_46,X0_47) = iProver_top
    | r1_lattice3(sK2,X0_46,sK1(sK2,sK0(sK2,X0_46,X0_47),X1_46)) != iProver_top
    | r1_lattice3(sK2,X1_46,sK0(sK2,X0_46,X0_47)) != iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK1(sK2,sK0(sK2,X0_46,X0_47),X1_46),u1_struct_0(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3010])).

cnf(c_3023,plain,
    ( sK0(sK2,X0_46,X0_47) = k2_yellow_0(sK2,X0_46)
    | r1_lattice3(sK2,X0_46,X0_47) = iProver_top
    | r1_lattice3(sK2,X0_46,sK0(sK2,X0_46,X0_47)) != iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK1(sK2,sK0(sK2,X0_46,X0_47),X0_46),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK0(sK2,X0_46,X0_47),u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2125,c_3011])).

cnf(c_3267,plain,
    ( m1_subset_1(sK1(sK2,sK0(sK2,X0_46,X0_47),X0_46),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
    | r1_lattice3(sK2,X0_46,sK0(sK2,X0_46,X0_47)) != iProver_top
    | r1_lattice3(sK2,X0_46,X0_47) = iProver_top
    | sK0(sK2,X0_46,X0_47) = k2_yellow_0(sK2,X0_46) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3023,c_1848])).

cnf(c_3268,plain,
    ( sK0(sK2,X0_46,X0_47) = k2_yellow_0(sK2,X0_46)
    | r1_lattice3(sK2,X0_46,X0_47) = iProver_top
    | r1_lattice3(sK2,X0_46,sK0(sK2,X0_46,X0_47)) != iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK1(sK2,sK0(sK2,X0_46,X0_47),X0_46),u1_struct_0(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3267])).

cnf(c_3279,plain,
    ( sK0(sK2,X0_46,X0_47) = k2_yellow_0(sK2,X0_46)
    | r1_lattice3(sK2,X0_46,X0_47) = iProver_top
    | r1_lattice3(sK2,X0_46,sK0(sK2,X0_46,X0_47)) != iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK0(sK2,X0_46,X0_47),u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2124,c_3268])).

cnf(c_3294,plain,
    ( m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
    | r1_lattice3(sK2,X0_46,sK0(sK2,X0_46,X0_47)) != iProver_top
    | r1_lattice3(sK2,X0_46,X0_47) = iProver_top
    | sK0(sK2,X0_46,X0_47) = k2_yellow_0(sK2,X0_46) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3279,c_1848])).

cnf(c_3295,plain,
    ( sK0(sK2,X0_46,X0_47) = k2_yellow_0(sK2,X0_46)
    | r1_lattice3(sK2,X0_46,X0_47) = iProver_top
    | r1_lattice3(sK2,X0_46,sK0(sK2,X0_46,X0_47)) != iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3294])).

cnf(c_9,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r2_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X2,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_494,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r2_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X2,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_18])).

cnf(c_495,plain,
    ( ~ r1_lattice3(sK2,X0,X1)
    | r2_yellow_0(sK2,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(sK1(sK2,X1,X0),u1_struct_0(sK2))
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_494])).

cnf(c_499,plain,
    ( m1_subset_1(sK1(sK2,X1,X0),u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r2_yellow_0(sK2,X0)
    | ~ r1_lattice3(sK2,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_495,c_17])).

cnf(c_500,plain,
    ( ~ r1_lattice3(sK2,X0,X1)
    | r2_yellow_0(sK2,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(sK1(sK2,X1,X0),u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_499])).

cnf(c_1784,plain,
    ( ~ r1_lattice3(sK2,X0_46,X0_47)
    | r2_yellow_0(sK2,X0_46)
    | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
    | m1_subset_1(sK1(sK2,X0_47,X0_46),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_500])).

cnf(c_2127,plain,
    ( r1_lattice3(sK2,X0_46,X0_47) != iProver_top
    | r2_yellow_0(sK2,X0_46) = iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK1(sK2,X0_47,X0_46),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1784])).

cnf(c_8,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_lattice3(X0,X1,sK1(X0,X2,X1))
    | r2_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_518,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_lattice3(X0,X1,sK1(X0,X2,X1))
    | r2_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_18])).

cnf(c_519,plain,
    ( ~ r1_lattice3(sK2,X0,X1)
    | r1_lattice3(sK2,X0,sK1(sK2,X1,X0))
    | r2_yellow_0(sK2,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_518])).

cnf(c_523,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r2_yellow_0(sK2,X0)
    | r1_lattice3(sK2,X0,sK1(sK2,X1,X0))
    | ~ r1_lattice3(sK2,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_519,c_17])).

cnf(c_524,plain,
    ( ~ r1_lattice3(sK2,X0,X1)
    | r1_lattice3(sK2,X0,sK1(sK2,X1,X0))
    | r2_yellow_0(sK2,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_523])).

cnf(c_1783,plain,
    ( ~ r1_lattice3(sK2,X0_46,X0_47)
    | r1_lattice3(sK2,X0_46,sK1(sK2,X0_47,X0_46))
    | r2_yellow_0(sK2,X0_46)
    | ~ m1_subset_1(X0_47,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_524])).

cnf(c_2128,plain,
    ( r1_lattice3(sK2,X0_46,X0_47) != iProver_top
    | r1_lattice3(sK2,X0_46,sK1(sK2,X0_47,X0_46)) = iProver_top
    | r2_yellow_0(sK2,X0_46) = iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1783])).

cnf(c_7,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK1(X0,X2,X1),X2)
    | r2_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_542,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK1(X0,X2,X1),X2)
    | r2_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_18])).

cnf(c_543,plain,
    ( ~ r1_lattice3(sK2,X0,X1)
    | ~ r1_orders_2(sK2,sK1(sK2,X1,X0),X1)
    | r2_yellow_0(sK2,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_542])).

cnf(c_547,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r2_yellow_0(sK2,X0)
    | ~ r1_orders_2(sK2,sK1(sK2,X1,X0),X1)
    | ~ r1_lattice3(sK2,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_543,c_17])).

cnf(c_548,plain,
    ( ~ r1_lattice3(sK2,X0,X1)
    | ~ r1_orders_2(sK2,sK1(sK2,X1,X0),X1)
    | r2_yellow_0(sK2,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_547])).

cnf(c_1782,plain,
    ( ~ r1_lattice3(sK2,X0_46,X0_47)
    | ~ r1_orders_2(sK2,sK1(sK2,X0_47,X0_46),X0_47)
    | r2_yellow_0(sK2,X0_46)
    | ~ m1_subset_1(X0_47,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_548])).

cnf(c_2129,plain,
    ( r1_lattice3(sK2,X0_46,X0_47) != iProver_top
    | r1_orders_2(sK2,sK1(sK2,X0_47,X0_46),X0_47) != iProver_top
    | r2_yellow_0(sK2,X0_46) = iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1782])).

cnf(c_2508,plain,
    ( r1_lattice3(sK2,X0_46,X0_47) = iProver_top
    | r1_lattice3(sK2,X0_46,sK1(sK2,sK0(sK2,X0_46,X0_47),X1_46)) != iProver_top
    | r1_lattice3(sK2,X1_46,sK0(sK2,X0_46,X0_47)) != iProver_top
    | r2_yellow_0(sK2,X1_46) = iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK1(sK2,sK0(sK2,X0_46,X0_47),X1_46),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK0(sK2,X0_46,X0_47),u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2132,c_2129])).

cnf(c_2966,plain,
    ( m1_subset_1(sK1(sK2,sK0(sK2,X0_46,X0_47),X1_46),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
    | r2_yellow_0(sK2,X1_46) = iProver_top
    | r1_lattice3(sK2,X1_46,sK0(sK2,X0_46,X0_47)) != iProver_top
    | r1_lattice3(sK2,X0_46,sK1(sK2,sK0(sK2,X0_46,X0_47),X1_46)) != iProver_top
    | r1_lattice3(sK2,X0_46,X0_47) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2508,c_1848])).

cnf(c_2967,plain,
    ( r1_lattice3(sK2,X0_46,X0_47) = iProver_top
    | r1_lattice3(sK2,X0_46,sK1(sK2,sK0(sK2,X0_46,X0_47),X1_46)) != iProver_top
    | r1_lattice3(sK2,X1_46,sK0(sK2,X0_46,X0_47)) != iProver_top
    | r2_yellow_0(sK2,X1_46) = iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK1(sK2,sK0(sK2,X0_46,X0_47),X1_46),u1_struct_0(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2966])).

cnf(c_2978,plain,
    ( r1_lattice3(sK2,X0_46,X0_47) = iProver_top
    | r1_lattice3(sK2,X0_46,sK0(sK2,X0_46,X0_47)) != iProver_top
    | r2_yellow_0(sK2,X0_46) = iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK1(sK2,sK0(sK2,X0_46,X0_47),X0_46),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK0(sK2,X0_46,X0_47),u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2128,c_2967])).

cnf(c_3104,plain,
    ( m1_subset_1(sK1(sK2,sK0(sK2,X0_46,X0_47),X0_46),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
    | r2_yellow_0(sK2,X0_46) = iProver_top
    | r1_lattice3(sK2,X0_46,sK0(sK2,X0_46,X0_47)) != iProver_top
    | r1_lattice3(sK2,X0_46,X0_47) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2978,c_1848])).

cnf(c_3105,plain,
    ( r1_lattice3(sK2,X0_46,X0_47) = iProver_top
    | r1_lattice3(sK2,X0_46,sK0(sK2,X0_46,X0_47)) != iProver_top
    | r2_yellow_0(sK2,X0_46) = iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK1(sK2,sK0(sK2,X0_46,X0_47),X0_46),u1_struct_0(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3104])).

cnf(c_3115,plain,
    ( r1_lattice3(sK2,X0_46,X0_47) = iProver_top
    | r1_lattice3(sK2,X0_46,sK0(sK2,X0_46,X0_47)) != iProver_top
    | r2_yellow_0(sK2,X0_46) = iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK0(sK2,X0_46,X0_47),u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2127,c_3105])).

cnf(c_3143,plain,
    ( m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
    | r2_yellow_0(sK2,X0_46) = iProver_top
    | r1_lattice3(sK2,X0_46,sK0(sK2,X0_46,X0_47)) != iProver_top
    | r1_lattice3(sK2,X0_46,X0_47) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3115,c_1848])).

cnf(c_3144,plain,
    ( r1_lattice3(sK2,X0_46,X0_47) = iProver_top
    | r1_lattice3(sK2,X0_46,sK0(sK2,X0_46,X0_47)) != iProver_top
    | r2_yellow_0(sK2,X0_46) = iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3143])).

cnf(c_1794,plain,
    ( r1_orders_2(sK2,X0_47,X0_47)
    | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_1790])).

cnf(c_2120,plain,
    ( r1_orders_2(sK2,X0_47,X0_47) = iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1794])).

cnf(c_1887,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(sK2))
    | r1_orders_2(sK2,X0_47,X0_47) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1794,c_16,c_1795,c_1822])).

cnf(c_1888,plain,
    ( r1_orders_2(sK2,X0_47,X0_47)
    | ~ m1_subset_1(X0_47,u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_1887])).

cnf(c_1889,plain,
    ( r1_orders_2(sK2,X0_47,X0_47) = iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1888])).

cnf(c_2449,plain,
    ( m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
    | r1_orders_2(sK2,X0_47,X0_47) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2120,c_1889])).

cnf(c_2450,plain,
    ( r1_orders_2(sK2,X0_47,X0_47) = iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2449])).

cnf(c_2684,plain,
    ( r1_lattice3(sK2,X0_46,X0_47) != iProver_top
    | r1_orders_2(sK2,sK1(sK2,X0_47,X0_46),sK1(sK2,X0_47,X0_46)) = iProver_top
    | r2_yellow_0(sK2,X0_46) = iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2127,c_2450])).

cnf(c_2647,plain,
    ( k2_yellow_0(sK2,X0_46) = X0_47
    | r1_lattice3(sK2,X0_46,X0_47) != iProver_top
    | r1_orders_2(sK2,sK1(sK2,X0_47,X0_46),sK1(sK2,X0_47,X0_46)) = iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2124,c_2450])).

cnf(c_2130,plain,
    ( r1_lattice3(sK2,X0_46,X0_47) = iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK0(sK2,X0_46,X0_47),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1781])).

cnf(c_2456,plain,
    ( r1_lattice3(sK2,X0_46,X0_47) = iProver_top
    | r1_orders_2(sK2,sK0(sK2,X0_46,X0_47),sK0(sK2,X0_46,X0_47)) = iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2130,c_2450])).

cnf(c_1791,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_2118,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1791])).

cnf(c_2455,plain,
    ( r1_orders_2(sK2,sK3,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2118,c_2450])).

cnf(c_2121,plain,
    ( m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1793])).

cnf(c_25,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1821,plain,
    ( m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1793])).

cnf(c_1823,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(instantiation,[status(thm)],[c_1821])).

cnf(c_2801,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2121,c_25,c_1823])).

cnf(c_2119,plain,
    ( sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1795])).

cnf(c_1817,plain,
    ( sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1795])).

cnf(c_2807,plain,
    ( sP1_iProver_split = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2119,c_25,c_1817,c_1823])).

cnf(c_3,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_655,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_17])).

cnf(c_656,plain,
    ( r1_lattice3(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X1,sK0(sK2,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_655])).

cnf(c_1780,plain,
    ( r1_lattice3(sK2,X0_46,X0_47)
    | ~ r1_orders_2(sK2,X0_47,sK0(sK2,X0_46,X0_47))
    | ~ m1_subset_1(X0_47,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_656])).

cnf(c_2131,plain,
    ( r1_lattice3(sK2,X0_46,X0_47) = iProver_top
    | r1_orders_2(sK2,X0_47,sK0(sK2,X0_46,X0_47)) != iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1780])).

cnf(c_13,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X2,k2_yellow_0(X0,X1))
    | ~ r2_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_395,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X2,k2_yellow_0(X0,X1))
    | ~ r2_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_18])).

cnf(c_396,plain,
    ( ~ r1_lattice3(sK2,X0,X1)
    | r1_orders_2(sK2,X1,k2_yellow_0(sK2,X0))
    | ~ r2_yellow_0(sK2,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(k2_yellow_0(sK2,X0),u1_struct_0(sK2))
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_395])).

cnf(c_400,plain,
    ( ~ m1_subset_1(k2_yellow_0(sK2,X0),u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ r2_yellow_0(sK2,X0)
    | r1_orders_2(sK2,X1,k2_yellow_0(sK2,X0))
    | ~ r1_lattice3(sK2,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_396,c_17])).

cnf(c_401,plain,
    ( ~ r1_lattice3(sK2,X0,X1)
    | r1_orders_2(sK2,X1,k2_yellow_0(sK2,X0))
    | ~ r2_yellow_0(sK2,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(k2_yellow_0(sK2,X0),u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_400])).

cnf(c_1788,plain,
    ( ~ r1_lattice3(sK2,X0_46,X0_47)
    | r1_orders_2(sK2,X0_47,k2_yellow_0(sK2,X0_46))
    | ~ r2_yellow_0(sK2,X0_46)
    | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
    | ~ m1_subset_1(k2_yellow_0(sK2,X0_46),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_401])).

cnf(c_2123,plain,
    ( r1_lattice3(sK2,X0_46,X0_47) != iProver_top
    | r1_orders_2(sK2,X0_47,k2_yellow_0(sK2,X0_46)) = iProver_top
    | r2_yellow_0(sK2,X0_46) != iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k2_yellow_0(sK2,X0_46),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1788])).

cnf(c_14,plain,
    ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
    | ~ r2_yellow_0(X0,X1)
    | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_374,plain,
    ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
    | ~ r2_yellow_0(X0,X1)
    | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_18])).

cnf(c_375,plain,
    ( r1_lattice3(sK2,X0,k2_yellow_0(sK2,X0))
    | ~ r2_yellow_0(sK2,X0)
    | ~ m1_subset_1(k2_yellow_0(sK2,X0),u1_struct_0(sK2))
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_374])).

cnf(c_379,plain,
    ( ~ m1_subset_1(k2_yellow_0(sK2,X0),u1_struct_0(sK2))
    | ~ r2_yellow_0(sK2,X0)
    | r1_lattice3(sK2,X0,k2_yellow_0(sK2,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_375,c_17])).

cnf(c_380,plain,
    ( r1_lattice3(sK2,X0,k2_yellow_0(sK2,X0))
    | ~ r2_yellow_0(sK2,X0)
    | ~ m1_subset_1(k2_yellow_0(sK2,X0),u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_379])).

cnf(c_1789,plain,
    ( r1_lattice3(sK2,X0_46,k2_yellow_0(sK2,X0_46))
    | ~ r2_yellow_0(sK2,X0_46)
    | ~ m1_subset_1(k2_yellow_0(sK2,X0_46),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_380])).

cnf(c_2122,plain,
    ( r1_lattice3(sK2,X0_46,k2_yellow_0(sK2,X0_46)) = iProver_top
    | r2_yellow_0(sK2,X0_46) != iProver_top
    | m1_subset_1(k2_yellow_0(sK2,X0_46),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1789])).

cnf(c_15,negated_conjecture,
    ( ~ r2_yellow_0(sK2,k6_waybel_0(sK2,sK3))
    | k2_yellow_0(sK2,k6_waybel_0(sK2,sK3)) != sK3 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1792,negated_conjecture,
    ( ~ r2_yellow_0(sK2,k6_waybel_0(sK2,sK3))
    | k2_yellow_0(sK2,k6_waybel_0(sK2,sK3)) != sK3 ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_2117,plain,
    ( k2_yellow_0(sK2,k6_waybel_0(sK2,sK3)) != sK3
    | r2_yellow_0(sK2,k6_waybel_0(sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1792])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:40:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.75/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.75/1.00  
% 1.75/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.75/1.00  
% 1.75/1.00  ------  iProver source info
% 1.75/1.00  
% 1.75/1.00  git: date: 2020-06-30 10:37:57 +0100
% 1.75/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.75/1.00  git: non_committed_changes: false
% 1.75/1.00  git: last_make_outside_of_git: false
% 1.75/1.00  
% 1.75/1.00  ------ 
% 1.75/1.00  
% 1.75/1.00  ------ Input Options
% 1.75/1.00  
% 1.75/1.00  --out_options                           all
% 1.75/1.00  --tptp_safe_out                         true
% 1.75/1.00  --problem_path                          ""
% 1.75/1.00  --include_path                          ""
% 1.75/1.00  --clausifier                            res/vclausify_rel
% 1.75/1.00  --clausifier_options                    --mode clausify
% 1.75/1.00  --stdin                                 false
% 1.75/1.00  --stats_out                             all
% 1.75/1.00  
% 1.75/1.00  ------ General Options
% 1.75/1.00  
% 1.75/1.00  --fof                                   false
% 1.75/1.00  --time_out_real                         305.
% 1.75/1.00  --time_out_virtual                      -1.
% 1.75/1.00  --symbol_type_check                     false
% 1.75/1.00  --clausify_out                          false
% 1.75/1.00  --sig_cnt_out                           false
% 1.75/1.00  --trig_cnt_out                          false
% 1.75/1.00  --trig_cnt_out_tolerance                1.
% 1.75/1.00  --trig_cnt_out_sk_spl                   false
% 1.75/1.00  --abstr_cl_out                          false
% 1.75/1.00  
% 1.75/1.00  ------ Global Options
% 1.75/1.00  
% 1.75/1.00  --schedule                              default
% 1.75/1.00  --add_important_lit                     false
% 1.75/1.00  --prop_solver_per_cl                    1000
% 1.75/1.00  --min_unsat_core                        false
% 1.75/1.00  --soft_assumptions                      false
% 1.75/1.00  --soft_lemma_size                       3
% 1.75/1.00  --prop_impl_unit_size                   0
% 1.75/1.00  --prop_impl_unit                        []
% 1.75/1.00  --share_sel_clauses                     true
% 1.75/1.00  --reset_solvers                         false
% 1.75/1.00  --bc_imp_inh                            [conj_cone]
% 1.75/1.00  --conj_cone_tolerance                   3.
% 1.75/1.00  --extra_neg_conj                        none
% 1.75/1.00  --large_theory_mode                     true
% 1.75/1.00  --prolific_symb_bound                   200
% 1.75/1.00  --lt_threshold                          2000
% 1.75/1.00  --clause_weak_htbl                      true
% 1.75/1.00  --gc_record_bc_elim                     false
% 1.75/1.00  
% 1.75/1.00  ------ Preprocessing Options
% 1.75/1.00  
% 1.75/1.00  --preprocessing_flag                    true
% 1.75/1.00  --time_out_prep_mult                    0.1
% 1.75/1.00  --splitting_mode                        input
% 1.75/1.00  --splitting_grd                         true
% 1.75/1.00  --splitting_cvd                         false
% 1.75/1.00  --splitting_cvd_svl                     false
% 1.75/1.00  --splitting_nvd                         32
% 1.75/1.00  --sub_typing                            true
% 1.75/1.00  --prep_gs_sim                           true
% 1.75/1.00  --prep_unflatten                        true
% 1.75/1.00  --prep_res_sim                          true
% 1.75/1.00  --prep_upred                            true
% 1.75/1.00  --prep_sem_filter                       exhaustive
% 1.75/1.00  --prep_sem_filter_out                   false
% 1.75/1.00  --pred_elim                             true
% 1.75/1.00  --res_sim_input                         true
% 1.75/1.00  --eq_ax_congr_red                       true
% 1.75/1.00  --pure_diseq_elim                       true
% 1.75/1.00  --brand_transform                       false
% 1.75/1.00  --non_eq_to_eq                          false
% 1.75/1.00  --prep_def_merge                        true
% 1.75/1.00  --prep_def_merge_prop_impl              false
% 1.75/1.00  --prep_def_merge_mbd                    true
% 1.75/1.00  --prep_def_merge_tr_red                 false
% 1.75/1.00  --prep_def_merge_tr_cl                  false
% 1.75/1.00  --smt_preprocessing                     true
% 1.75/1.00  --smt_ac_axioms                         fast
% 1.75/1.00  --preprocessed_out                      false
% 1.75/1.00  --preprocessed_stats                    false
% 1.75/1.00  
% 1.75/1.00  ------ Abstraction refinement Options
% 1.75/1.00  
% 1.75/1.00  --abstr_ref                             []
% 1.75/1.00  --abstr_ref_prep                        false
% 1.75/1.00  --abstr_ref_until_sat                   false
% 1.75/1.00  --abstr_ref_sig_restrict                funpre
% 1.75/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.75/1.00  --abstr_ref_under                       []
% 1.75/1.00  
% 1.75/1.00  ------ SAT Options
% 1.75/1.00  
% 1.75/1.00  --sat_mode                              false
% 1.75/1.00  --sat_fm_restart_options                ""
% 1.75/1.00  --sat_gr_def                            false
% 1.75/1.00  --sat_epr_types                         true
% 1.75/1.00  --sat_non_cyclic_types                  false
% 1.75/1.00  --sat_finite_models                     false
% 1.75/1.00  --sat_fm_lemmas                         false
% 1.75/1.00  --sat_fm_prep                           false
% 1.75/1.00  --sat_fm_uc_incr                        true
% 1.75/1.00  --sat_out_model                         small
% 1.75/1.00  --sat_out_clauses                       false
% 1.75/1.00  
% 1.75/1.00  ------ QBF Options
% 1.75/1.00  
% 1.75/1.00  --qbf_mode                              false
% 1.75/1.00  --qbf_elim_univ                         false
% 1.75/1.00  --qbf_dom_inst                          none
% 1.75/1.00  --qbf_dom_pre_inst                      false
% 1.75/1.00  --qbf_sk_in                             false
% 1.75/1.00  --qbf_pred_elim                         true
% 1.75/1.00  --qbf_split                             512
% 1.75/1.00  
% 1.75/1.00  ------ BMC1 Options
% 1.75/1.00  
% 1.75/1.00  --bmc1_incremental                      false
% 1.75/1.00  --bmc1_axioms                           reachable_all
% 1.75/1.00  --bmc1_min_bound                        0
% 1.75/1.00  --bmc1_max_bound                        -1
% 1.75/1.00  --bmc1_max_bound_default                -1
% 1.75/1.00  --bmc1_symbol_reachability              true
% 1.75/1.00  --bmc1_property_lemmas                  false
% 1.75/1.00  --bmc1_k_induction                      false
% 1.75/1.00  --bmc1_non_equiv_states                 false
% 1.75/1.00  --bmc1_deadlock                         false
% 1.75/1.00  --bmc1_ucm                              false
% 1.75/1.00  --bmc1_add_unsat_core                   none
% 1.75/1.00  --bmc1_unsat_core_children              false
% 1.75/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.75/1.00  --bmc1_out_stat                         full
% 1.75/1.00  --bmc1_ground_init                      false
% 1.75/1.00  --bmc1_pre_inst_next_state              false
% 1.75/1.00  --bmc1_pre_inst_state                   false
% 1.75/1.00  --bmc1_pre_inst_reach_state             false
% 1.75/1.00  --bmc1_out_unsat_core                   false
% 1.75/1.00  --bmc1_aig_witness_out                  false
% 1.75/1.00  --bmc1_verbose                          false
% 1.75/1.00  --bmc1_dump_clauses_tptp                false
% 1.75/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.75/1.00  --bmc1_dump_file                        -
% 1.75/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.75/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.75/1.00  --bmc1_ucm_extend_mode                  1
% 1.75/1.00  --bmc1_ucm_init_mode                    2
% 1.75/1.00  --bmc1_ucm_cone_mode                    none
% 1.75/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.75/1.00  --bmc1_ucm_relax_model                  4
% 1.75/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.75/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.75/1.00  --bmc1_ucm_layered_model                none
% 1.75/1.00  --bmc1_ucm_max_lemma_size               10
% 1.75/1.00  
% 1.75/1.00  ------ AIG Options
% 1.75/1.00  
% 1.75/1.00  --aig_mode                              false
% 1.75/1.00  
% 1.75/1.00  ------ Instantiation Options
% 1.75/1.00  
% 1.75/1.00  --instantiation_flag                    true
% 1.75/1.00  --inst_sos_flag                         false
% 1.75/1.00  --inst_sos_phase                        true
% 1.75/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.75/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.75/1.00  --inst_lit_sel_side                     num_symb
% 1.75/1.00  --inst_solver_per_active                1400
% 1.75/1.00  --inst_solver_calls_frac                1.
% 1.75/1.00  --inst_passive_queue_type               priority_queues
% 1.75/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.75/1.00  --inst_passive_queues_freq              [25;2]
% 1.75/1.00  --inst_dismatching                      true
% 1.75/1.00  --inst_eager_unprocessed_to_passive     true
% 1.75/1.00  --inst_prop_sim_given                   true
% 1.75/1.00  --inst_prop_sim_new                     false
% 1.75/1.00  --inst_subs_new                         false
% 1.75/1.00  --inst_eq_res_simp                      false
% 1.75/1.00  --inst_subs_given                       false
% 1.75/1.00  --inst_orphan_elimination               true
% 1.75/1.00  --inst_learning_loop_flag               true
% 1.75/1.00  --inst_learning_start                   3000
% 1.75/1.00  --inst_learning_factor                  2
% 1.75/1.00  --inst_start_prop_sim_after_learn       3
% 1.75/1.00  --inst_sel_renew                        solver
% 1.75/1.00  --inst_lit_activity_flag                true
% 1.75/1.00  --inst_restr_to_given                   false
% 1.75/1.00  --inst_activity_threshold               500
% 1.75/1.00  --inst_out_proof                        true
% 1.75/1.00  
% 1.75/1.00  ------ Resolution Options
% 1.75/1.00  
% 1.75/1.00  --resolution_flag                       true
% 1.75/1.00  --res_lit_sel                           adaptive
% 1.75/1.00  --res_lit_sel_side                      none
% 1.75/1.00  --res_ordering                          kbo
% 1.75/1.00  --res_to_prop_solver                    active
% 1.75/1.00  --res_prop_simpl_new                    false
% 1.75/1.00  --res_prop_simpl_given                  true
% 1.75/1.00  --res_passive_queue_type                priority_queues
% 1.75/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.75/1.00  --res_passive_queues_freq               [15;5]
% 1.75/1.00  --res_forward_subs                      full
% 1.75/1.00  --res_backward_subs                     full
% 1.75/1.00  --res_forward_subs_resolution           true
% 1.75/1.00  --res_backward_subs_resolution          true
% 1.75/1.00  --res_orphan_elimination                true
% 1.75/1.00  --res_time_limit                        2.
% 1.75/1.00  --res_out_proof                         true
% 1.75/1.00  
% 1.75/1.00  ------ Superposition Options
% 1.75/1.00  
% 1.75/1.00  --superposition_flag                    true
% 1.75/1.00  --sup_passive_queue_type                priority_queues
% 1.75/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.75/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.75/1.00  --demod_completeness_check              fast
% 1.75/1.00  --demod_use_ground                      true
% 1.75/1.00  --sup_to_prop_solver                    passive
% 1.75/1.00  --sup_prop_simpl_new                    true
% 1.75/1.00  --sup_prop_simpl_given                  true
% 1.75/1.00  --sup_fun_splitting                     false
% 1.75/1.00  --sup_smt_interval                      50000
% 1.75/1.00  
% 1.75/1.00  ------ Superposition Simplification Setup
% 1.75/1.00  
% 1.75/1.00  --sup_indices_passive                   []
% 1.75/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.75/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.75/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.75/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.75/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.75/1.00  --sup_full_bw                           [BwDemod]
% 1.75/1.00  --sup_immed_triv                        [TrivRules]
% 1.75/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.75/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.75/1.00  --sup_immed_bw_main                     []
% 1.75/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.75/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.75/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.75/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.75/1.00  
% 1.75/1.00  ------ Combination Options
% 1.75/1.00  
% 1.75/1.00  --comb_res_mult                         3
% 1.75/1.00  --comb_sup_mult                         2
% 1.75/1.00  --comb_inst_mult                        10
% 1.75/1.00  
% 1.75/1.00  ------ Debug Options
% 1.75/1.00  
% 1.75/1.00  --dbg_backtrace                         false
% 1.75/1.00  --dbg_dump_prop_clauses                 false
% 1.75/1.00  --dbg_dump_prop_clauses_file            -
% 1.75/1.00  --dbg_out_stat                          false
% 1.75/1.00  ------ Parsing...
% 1.75/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.75/1.00  
% 1.75/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 1.75/1.00  
% 1.75/1.00  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.75/1.00  
% 1.75/1.00  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.75/1.00  ------ Proving...
% 1.75/1.00  ------ Problem Properties 
% 1.75/1.00  
% 1.75/1.00  
% 1.75/1.00  clauses                                 16
% 1.75/1.00  conjectures                             2
% 1.75/1.00  EPR                                     1
% 1.75/1.00  Horn                                    9
% 1.75/1.00  unary                                   1
% 1.75/1.00  binary                                  3
% 1.75/1.00  lits                                    53
% 1.75/1.00  lits eq                                 4
% 1.75/1.00  fd_pure                                 0
% 1.75/1.00  fd_pseudo                               0
% 1.75/1.00  fd_cond                                 0
% 1.75/1.00  fd_pseudo_cond                          3
% 1.75/1.00  AC symbols                              0
% 1.75/1.00  
% 1.75/1.00  ------ Schedule dynamic 5 is on 
% 1.75/1.00  
% 1.75/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.75/1.00  
% 1.75/1.00  
% 1.75/1.00  ------ 
% 1.75/1.00  Current options:
% 1.75/1.00  ------ 
% 1.75/1.00  
% 1.75/1.00  ------ Input Options
% 1.75/1.00  
% 1.75/1.00  --out_options                           all
% 1.75/1.00  --tptp_safe_out                         true
% 1.75/1.00  --problem_path                          ""
% 1.75/1.00  --include_path                          ""
% 1.75/1.00  --clausifier                            res/vclausify_rel
% 1.75/1.00  --clausifier_options                    --mode clausify
% 1.75/1.00  --stdin                                 false
% 1.75/1.00  --stats_out                             all
% 1.75/1.00  
% 1.75/1.00  ------ General Options
% 1.75/1.00  
% 1.75/1.00  --fof                                   false
% 1.75/1.00  --time_out_real                         305.
% 1.75/1.00  --time_out_virtual                      -1.
% 1.75/1.00  --symbol_type_check                     false
% 1.75/1.00  --clausify_out                          false
% 1.75/1.00  --sig_cnt_out                           false
% 1.75/1.00  --trig_cnt_out                          false
% 1.75/1.00  --trig_cnt_out_tolerance                1.
% 1.75/1.00  --trig_cnt_out_sk_spl                   false
% 1.75/1.00  --abstr_cl_out                          false
% 1.75/1.00  
% 1.75/1.00  ------ Global Options
% 1.75/1.00  
% 1.75/1.00  --schedule                              default
% 1.75/1.00  --add_important_lit                     false
% 1.75/1.00  --prop_solver_per_cl                    1000
% 1.75/1.00  --min_unsat_core                        false
% 1.75/1.00  --soft_assumptions                      false
% 1.75/1.00  --soft_lemma_size                       3
% 1.75/1.00  --prop_impl_unit_size                   0
% 1.75/1.00  --prop_impl_unit                        []
% 1.75/1.00  --share_sel_clauses                     true
% 1.75/1.00  --reset_solvers                         false
% 1.75/1.00  --bc_imp_inh                            [conj_cone]
% 1.75/1.00  --conj_cone_tolerance                   3.
% 1.75/1.00  --extra_neg_conj                        none
% 1.75/1.00  --large_theory_mode                     true
% 1.75/1.00  --prolific_symb_bound                   200
% 1.75/1.00  --lt_threshold                          2000
% 1.75/1.00  --clause_weak_htbl                      true
% 1.75/1.00  --gc_record_bc_elim                     false
% 1.75/1.00  
% 1.75/1.00  ------ Preprocessing Options
% 1.75/1.00  
% 1.75/1.00  --preprocessing_flag                    true
% 1.75/1.00  --time_out_prep_mult                    0.1
% 1.75/1.00  --splitting_mode                        input
% 1.75/1.00  --splitting_grd                         true
% 1.75/1.00  --splitting_cvd                         false
% 1.75/1.00  --splitting_cvd_svl                     false
% 1.75/1.00  --splitting_nvd                         32
% 1.75/1.00  --sub_typing                            true
% 1.75/1.00  --prep_gs_sim                           true
% 1.75/1.00  --prep_unflatten                        true
% 1.75/1.00  --prep_res_sim                          true
% 1.75/1.00  --prep_upred                            true
% 1.75/1.00  --prep_sem_filter                       exhaustive
% 1.75/1.00  --prep_sem_filter_out                   false
% 1.75/1.00  --pred_elim                             true
% 1.75/1.00  --res_sim_input                         true
% 1.75/1.00  --eq_ax_congr_red                       true
% 1.75/1.00  --pure_diseq_elim                       true
% 1.75/1.00  --brand_transform                       false
% 1.75/1.00  --non_eq_to_eq                          false
% 1.75/1.00  --prep_def_merge                        true
% 1.75/1.00  --prep_def_merge_prop_impl              false
% 1.75/1.00  --prep_def_merge_mbd                    true
% 1.75/1.00  --prep_def_merge_tr_red                 false
% 1.75/1.00  --prep_def_merge_tr_cl                  false
% 1.75/1.00  --smt_preprocessing                     true
% 1.75/1.00  --smt_ac_axioms                         fast
% 1.75/1.00  --preprocessed_out                      false
% 1.75/1.00  --preprocessed_stats                    false
% 1.75/1.00  
% 1.75/1.00  ------ Abstraction refinement Options
% 1.75/1.00  
% 1.75/1.00  --abstr_ref                             []
% 1.75/1.00  --abstr_ref_prep                        false
% 1.75/1.00  --abstr_ref_until_sat                   false
% 1.75/1.00  --abstr_ref_sig_restrict                funpre
% 1.75/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.75/1.00  --abstr_ref_under                       []
% 1.75/1.00  
% 1.75/1.00  ------ SAT Options
% 1.75/1.00  
% 1.75/1.00  --sat_mode                              false
% 1.75/1.00  --sat_fm_restart_options                ""
% 1.75/1.00  --sat_gr_def                            false
% 1.75/1.00  --sat_epr_types                         true
% 1.75/1.00  --sat_non_cyclic_types                  false
% 1.75/1.00  --sat_finite_models                     false
% 1.75/1.00  --sat_fm_lemmas                         false
% 1.75/1.00  --sat_fm_prep                           false
% 1.75/1.00  --sat_fm_uc_incr                        true
% 1.75/1.00  --sat_out_model                         small
% 1.75/1.00  --sat_out_clauses                       false
% 1.75/1.00  
% 1.75/1.00  ------ QBF Options
% 1.75/1.00  
% 1.75/1.00  --qbf_mode                              false
% 1.75/1.00  --qbf_elim_univ                         false
% 1.75/1.00  --qbf_dom_inst                          none
% 1.75/1.00  --qbf_dom_pre_inst                      false
% 1.75/1.00  --qbf_sk_in                             false
% 1.75/1.00  --qbf_pred_elim                         true
% 1.75/1.00  --qbf_split                             512
% 1.75/1.00  
% 1.75/1.00  ------ BMC1 Options
% 1.75/1.00  
% 1.75/1.00  --bmc1_incremental                      false
% 1.75/1.00  --bmc1_axioms                           reachable_all
% 1.75/1.00  --bmc1_min_bound                        0
% 1.75/1.00  --bmc1_max_bound                        -1
% 1.75/1.00  --bmc1_max_bound_default                -1
% 1.75/1.00  --bmc1_symbol_reachability              true
% 1.75/1.00  --bmc1_property_lemmas                  false
% 1.75/1.00  --bmc1_k_induction                      false
% 1.75/1.00  --bmc1_non_equiv_states                 false
% 1.75/1.00  --bmc1_deadlock                         false
% 1.75/1.00  --bmc1_ucm                              false
% 1.75/1.00  --bmc1_add_unsat_core                   none
% 1.75/1.00  --bmc1_unsat_core_children              false
% 1.75/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.75/1.00  --bmc1_out_stat                         full
% 1.75/1.00  --bmc1_ground_init                      false
% 1.75/1.00  --bmc1_pre_inst_next_state              false
% 1.75/1.00  --bmc1_pre_inst_state                   false
% 1.75/1.00  --bmc1_pre_inst_reach_state             false
% 1.75/1.00  --bmc1_out_unsat_core                   false
% 1.75/1.00  --bmc1_aig_witness_out                  false
% 1.75/1.00  --bmc1_verbose                          false
% 1.75/1.00  --bmc1_dump_clauses_tptp                false
% 1.75/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.75/1.00  --bmc1_dump_file                        -
% 1.75/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.75/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.75/1.00  --bmc1_ucm_extend_mode                  1
% 1.75/1.00  --bmc1_ucm_init_mode                    2
% 1.75/1.00  --bmc1_ucm_cone_mode                    none
% 1.75/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.75/1.00  --bmc1_ucm_relax_model                  4
% 1.75/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.75/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.75/1.00  --bmc1_ucm_layered_model                none
% 1.75/1.00  --bmc1_ucm_max_lemma_size               10
% 1.75/1.00  
% 1.75/1.00  ------ AIG Options
% 1.75/1.00  
% 1.75/1.00  --aig_mode                              false
% 1.75/1.00  
% 1.75/1.00  ------ Instantiation Options
% 1.75/1.00  
% 1.75/1.00  --instantiation_flag                    true
% 1.75/1.00  --inst_sos_flag                         false
% 1.75/1.00  --inst_sos_phase                        true
% 1.75/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.75/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.75/1.00  --inst_lit_sel_side                     none
% 1.75/1.00  --inst_solver_per_active                1400
% 1.75/1.00  --inst_solver_calls_frac                1.
% 1.75/1.00  --inst_passive_queue_type               priority_queues
% 1.75/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.75/1.00  --inst_passive_queues_freq              [25;2]
% 1.75/1.00  --inst_dismatching                      true
% 1.75/1.00  --inst_eager_unprocessed_to_passive     true
% 1.75/1.00  --inst_prop_sim_given                   true
% 1.75/1.00  --inst_prop_sim_new                     false
% 1.75/1.00  --inst_subs_new                         false
% 1.75/1.00  --inst_eq_res_simp                      false
% 1.75/1.00  --inst_subs_given                       false
% 1.75/1.00  --inst_orphan_elimination               true
% 1.75/1.00  --inst_learning_loop_flag               true
% 1.75/1.00  --inst_learning_start                   3000
% 1.75/1.00  --inst_learning_factor                  2
% 1.75/1.00  --inst_start_prop_sim_after_learn       3
% 1.75/1.00  --inst_sel_renew                        solver
% 1.75/1.00  --inst_lit_activity_flag                true
% 1.75/1.00  --inst_restr_to_given                   false
% 1.75/1.00  --inst_activity_threshold               500
% 1.75/1.00  --inst_out_proof                        true
% 1.75/1.00  
% 1.75/1.00  ------ Resolution Options
% 1.75/1.00  
% 1.75/1.00  --resolution_flag                       false
% 1.75/1.00  --res_lit_sel                           adaptive
% 1.75/1.00  --res_lit_sel_side                      none
% 1.75/1.00  --res_ordering                          kbo
% 1.75/1.00  --res_to_prop_solver                    active
% 1.75/1.00  --res_prop_simpl_new                    false
% 1.75/1.00  --res_prop_simpl_given                  true
% 1.75/1.00  --res_passive_queue_type                priority_queues
% 1.75/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.75/1.00  --res_passive_queues_freq               [15;5]
% 1.75/1.00  --res_forward_subs                      full
% 1.75/1.00  --res_backward_subs                     full
% 1.75/1.00  --res_forward_subs_resolution           true
% 1.75/1.00  --res_backward_subs_resolution          true
% 1.75/1.00  --res_orphan_elimination                true
% 1.75/1.00  --res_time_limit                        2.
% 1.75/1.00  --res_out_proof                         true
% 1.75/1.00  
% 1.75/1.00  ------ Superposition Options
% 1.75/1.00  
% 1.75/1.00  --superposition_flag                    true
% 1.75/1.00  --sup_passive_queue_type                priority_queues
% 1.75/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.75/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.75/1.00  --demod_completeness_check              fast
% 1.75/1.00  --demod_use_ground                      true
% 1.75/1.00  --sup_to_prop_solver                    passive
% 1.75/1.00  --sup_prop_simpl_new                    true
% 1.75/1.00  --sup_prop_simpl_given                  true
% 1.75/1.00  --sup_fun_splitting                     false
% 1.75/1.00  --sup_smt_interval                      50000
% 1.75/1.00  
% 1.75/1.00  ------ Superposition Simplification Setup
% 1.75/1.00  
% 1.75/1.00  --sup_indices_passive                   []
% 1.75/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.75/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.75/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.75/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.75/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.75/1.00  --sup_full_bw                           [BwDemod]
% 1.75/1.00  --sup_immed_triv                        [TrivRules]
% 1.75/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.75/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.75/1.00  --sup_immed_bw_main                     []
% 1.75/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.75/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.75/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.75/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.75/1.00  
% 1.75/1.00  ------ Combination Options
% 1.75/1.00  
% 1.75/1.00  --comb_res_mult                         3
% 1.75/1.00  --comb_sup_mult                         2
% 1.75/1.00  --comb_inst_mult                        10
% 1.75/1.00  
% 1.75/1.00  ------ Debug Options
% 1.75/1.00  
% 1.75/1.00  --dbg_backtrace                         false
% 1.75/1.00  --dbg_dump_prop_clauses                 false
% 1.75/1.00  --dbg_dump_prop_clauses_file            -
% 1.75/1.00  --dbg_out_stat                          false
% 1.75/1.00  
% 1.75/1.00  
% 1.75/1.00  
% 1.75/1.00  
% 1.75/1.00  ------ Proving...
% 1.75/1.00  
% 1.75/1.00  
% 1.75/1.00  % SZS status CounterSatisfiable for theBenchmark.p
% 1.75/1.00  
% 1.75/1.00  % SZS output start Saturation for theBenchmark.p
% 1.75/1.00  
% 1.75/1.00  fof(f2,axiom,(
% 1.75/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => r3_orders_2(X0,X1,X1))),
% 1.75/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.75/1.00  
% 1.75/1.00  fof(f11,plain,(
% 1.75/1.00    ! [X0,X1,X2] : (r3_orders_2(X0,X1,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.75/1.00    inference(ennf_transformation,[],[f2])).
% 1.75/1.00  
% 1.75/1.00  fof(f12,plain,(
% 1.75/1.00    ! [X0,X1,X2] : (r3_orders_2(X0,X1,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.75/1.00    inference(flattening,[],[f11])).
% 1.75/1.00  
% 1.75/1.00  fof(f31,plain,(
% 1.75/1.00    ( ! [X2,X0,X1] : (r3_orders_2(X0,X1,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.75/1.00    inference(cnf_transformation,[],[f12])).
% 1.75/1.00  
% 1.75/1.00  fof(f5,conjecture,(
% 1.75/1.00    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k2_yellow_0(X0,k6_waybel_0(X0,X1)) = X1 & r2_yellow_0(X0,k6_waybel_0(X0,X1)))))),
% 1.75/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.75/1.00  
% 1.75/1.00  fof(f6,negated_conjecture,(
% 1.75/1.00    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k2_yellow_0(X0,k6_waybel_0(X0,X1)) = X1 & r2_yellow_0(X0,k6_waybel_0(X0,X1)))))),
% 1.75/1.00    inference(negated_conjecture,[],[f5])).
% 1.75/1.00  
% 1.75/1.00  fof(f8,plain,(
% 1.75/1.00    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k2_yellow_0(X0,k6_waybel_0(X0,X1)) = X1 & r2_yellow_0(X0,k6_waybel_0(X0,X1)))))),
% 1.75/1.00    inference(pure_predicate_removal,[],[f6])).
% 1.75/1.00  
% 1.75/1.00  fof(f17,plain,(
% 1.75/1.00    ? [X0] : (? [X1] : ((k2_yellow_0(X0,k6_waybel_0(X0,X1)) != X1 | ~r2_yellow_0(X0,k6_waybel_0(X0,X1))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.75/1.00    inference(ennf_transformation,[],[f8])).
% 1.75/1.00  
% 1.75/1.00  fof(f18,plain,(
% 1.75/1.00    ? [X0] : (? [X1] : ((k2_yellow_0(X0,k6_waybel_0(X0,X1)) != X1 | ~r2_yellow_0(X0,k6_waybel_0(X0,X1))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.75/1.00    inference(flattening,[],[f17])).
% 1.75/1.00  
% 1.75/1.00  fof(f27,plain,(
% 1.75/1.00    ( ! [X0] : (? [X1] : ((k2_yellow_0(X0,k6_waybel_0(X0,X1)) != X1 | ~r2_yellow_0(X0,k6_waybel_0(X0,X1))) & m1_subset_1(X1,u1_struct_0(X0))) => ((k2_yellow_0(X0,k6_waybel_0(X0,sK3)) != sK3 | ~r2_yellow_0(X0,k6_waybel_0(X0,sK3))) & m1_subset_1(sK3,u1_struct_0(X0)))) )),
% 1.75/1.00    introduced(choice_axiom,[])).
% 1.75/1.00  
% 1.75/1.00  fof(f26,plain,(
% 1.75/1.00    ? [X0] : (? [X1] : ((k2_yellow_0(X0,k6_waybel_0(X0,X1)) != X1 | ~r2_yellow_0(X0,k6_waybel_0(X0,X1))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : ((k2_yellow_0(sK2,k6_waybel_0(sK2,X1)) != X1 | ~r2_yellow_0(sK2,k6_waybel_0(sK2,X1))) & m1_subset_1(X1,u1_struct_0(sK2))) & l1_orders_2(sK2) & v5_orders_2(sK2) & v3_orders_2(sK2) & ~v2_struct_0(sK2))),
% 1.75/1.00    introduced(choice_axiom,[])).
% 1.75/1.00  
% 1.75/1.00  fof(f28,plain,(
% 1.75/1.00    ((k2_yellow_0(sK2,k6_waybel_0(sK2,sK3)) != sK3 | ~r2_yellow_0(sK2,k6_waybel_0(sK2,sK3))) & m1_subset_1(sK3,u1_struct_0(sK2))) & l1_orders_2(sK2) & v5_orders_2(sK2) & v3_orders_2(sK2) & ~v2_struct_0(sK2)),
% 1.75/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f18,f27,f26])).
% 1.75/1.00  
% 1.75/1.00  fof(f45,plain,(
% 1.75/1.00    v3_orders_2(sK2)),
% 1.75/1.00    inference(cnf_transformation,[],[f28])).
% 1.75/1.00  
% 1.75/1.00  fof(f44,plain,(
% 1.75/1.00    ~v2_struct_0(sK2)),
% 1.75/1.00    inference(cnf_transformation,[],[f28])).
% 1.75/1.00  
% 1.75/1.00  fof(f47,plain,(
% 1.75/1.00    l1_orders_2(sK2)),
% 1.75/1.00    inference(cnf_transformation,[],[f28])).
% 1.75/1.00  
% 1.75/1.00  fof(f1,axiom,(
% 1.75/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 1.75/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.75/1.00  
% 1.75/1.00  fof(f9,plain,(
% 1.75/1.00    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.75/1.00    inference(ennf_transformation,[],[f1])).
% 1.75/1.00  
% 1.75/1.00  fof(f10,plain,(
% 1.75/1.00    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.75/1.00    inference(flattening,[],[f9])).
% 1.75/1.00  
% 1.75/1.00  fof(f19,plain,(
% 1.75/1.00    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.75/1.00    inference(nnf_transformation,[],[f10])).
% 1.75/1.00  
% 1.75/1.00  fof(f29,plain,(
% 1.75/1.00    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.75/1.00    inference(cnf_transformation,[],[f19])).
% 1.75/1.00  
% 1.75/1.00  fof(f48,plain,(
% 1.75/1.00    m1_subset_1(sK3,u1_struct_0(sK2))),
% 1.75/1.00    inference(cnf_transformation,[],[f28])).
% 1.75/1.00  
% 1.75/1.00  fof(f4,axiom,(
% 1.75/1.00    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X2,X3) => r1_orders_2(X0,X3,X1))) & r1_lattice3(X0,X2,X1)) => (r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1)) & ((r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X2,X3) => r1_orders_2(X0,X3,X1))) & r1_lattice3(X0,X2,X1))))))),
% 1.75/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.75/1.00  
% 1.75/1.00  fof(f7,plain,(
% 1.75/1.00    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X2,X3) => r1_orders_2(X0,X3,X1))) & r1_lattice3(X0,X2,X1)) => (r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1)) & ((r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1) => (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r1_lattice3(X0,X2,X4) => r1_orders_2(X0,X4,X1))) & r1_lattice3(X0,X2,X1))))))),
% 1.75/1.00    inference(rectify,[],[f4])).
% 1.75/1.00  
% 1.75/1.00  fof(f15,plain,(
% 1.75/1.00    ! [X0] : (! [X1] : (! [X2] : (((r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1) | (? [X3] : ((~r1_orders_2(X0,X3,X1) & r1_lattice3(X0,X2,X3)) & m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X2,X1))) & ((! [X4] : ((r1_orders_2(X0,X4,X1) | ~r1_lattice3(X0,X2,X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_lattice3(X0,X2,X1)) | (~r2_yellow_0(X0,X2) | k2_yellow_0(X0,X2) != X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0)))),
% 1.75/1.00    inference(ennf_transformation,[],[f7])).
% 1.75/1.00  
% 1.75/1.00  fof(f16,plain,(
% 1.75/1.00    ! [X0] : (! [X1] : (! [X2] : (((r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1) | ? [X3] : (~r1_orders_2(X0,X3,X1) & r1_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X4,X1) | ~r1_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_lattice3(X0,X2,X1)) | ~r2_yellow_0(X0,X2) | k2_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 1.75/1.00    inference(flattening,[],[f15])).
% 1.75/1.00  
% 1.75/1.00  fof(f24,plain,(
% 1.75/1.00    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X1) & r1_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK1(X0,X1,X2),X1) & r1_lattice3(X0,X2,sK1(X0,X1,X2)) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))))),
% 1.75/1.00    introduced(choice_axiom,[])).
% 1.75/1.00  
% 1.75/1.00  fof(f25,plain,(
% 1.75/1.00    ! [X0] : (! [X1] : (! [X2] : (((r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1) | (~r1_orders_2(X0,sK1(X0,X1,X2),X1) & r1_lattice3(X0,X2,sK1(X0,X1,X2)) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))) | ~r1_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X4,X1) | ~r1_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_lattice3(X0,X2,X1)) | ~r2_yellow_0(X0,X2) | k2_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 1.75/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f24])).
% 1.75/1.00  
% 1.75/1.00  fof(f38,plain,(
% 1.75/1.00    ( ! [X2,X0,X1] : (k2_yellow_0(X0,X2) = X1 | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) | ~r1_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 1.75/1.00    inference(cnf_transformation,[],[f25])).
% 1.75/1.00  
% 1.75/1.00  fof(f46,plain,(
% 1.75/1.00    v5_orders_2(sK2)),
% 1.75/1.00    inference(cnf_transformation,[],[f28])).
% 1.75/1.00  
% 1.75/1.00  fof(f39,plain,(
% 1.75/1.00    ( ! [X2,X0,X1] : (k2_yellow_0(X0,X2) = X1 | r1_lattice3(X0,X2,sK1(X0,X1,X2)) | ~r1_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 1.75/1.00    inference(cnf_transformation,[],[f25])).
% 1.75/1.00  
% 1.75/1.00  fof(f3,axiom,(
% 1.75/1.00    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X2,X3))))))),
% 1.75/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.75/1.00  
% 1.75/1.00  fof(f13,plain,(
% 1.75/1.00    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.75/1.00    inference(ennf_transformation,[],[f3])).
% 1.75/1.00  
% 1.75/1.00  fof(f14,plain,(
% 1.75/1.00    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.75/1.00    inference(flattening,[],[f13])).
% 1.75/1.00  
% 1.75/1.00  fof(f20,plain,(
% 1.75/1.00    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.75/1.00    inference(nnf_transformation,[],[f14])).
% 1.75/1.00  
% 1.75/1.00  fof(f21,plain,(
% 1.75/1.00    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.75/1.00    inference(rectify,[],[f20])).
% 1.75/1.00  
% 1.75/1.00  fof(f22,plain,(
% 1.75/1.00    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X2,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 1.75/1.00    introduced(choice_axiom,[])).
% 1.75/1.00  
% 1.75/1.00  fof(f23,plain,(
% 1.75/1.00    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | (~r1_orders_2(X0,X2,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.75/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).
% 1.75/1.00  
% 1.75/1.00  fof(f32,plain,(
% 1.75/1.00    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.75/1.00    inference(cnf_transformation,[],[f23])).
% 1.75/1.00  
% 1.75/1.00  fof(f34,plain,(
% 1.75/1.00    ( ! [X2,X0,X1] : (r1_lattice3(X0,X1,X2) | r2_hidden(sK0(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.75/1.00    inference(cnf_transformation,[],[f23])).
% 1.75/1.00  
% 1.75/1.00  fof(f33,plain,(
% 1.75/1.00    ( ! [X2,X0,X1] : (r1_lattice3(X0,X1,X2) | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.75/1.00    inference(cnf_transformation,[],[f23])).
% 1.75/1.00  
% 1.75/1.00  fof(f40,plain,(
% 1.75/1.00    ( ! [X2,X0,X1] : (k2_yellow_0(X0,X2) = X1 | ~r1_orders_2(X0,sK1(X0,X1,X2),X1) | ~r1_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 1.75/1.00    inference(cnf_transformation,[],[f25])).
% 1.75/1.00  
% 1.75/1.00  fof(f41,plain,(
% 1.75/1.00    ( ! [X2,X0,X1] : (r2_yellow_0(X0,X2) | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) | ~r1_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 1.75/1.00    inference(cnf_transformation,[],[f25])).
% 1.75/1.00  
% 1.75/1.00  fof(f42,plain,(
% 1.75/1.00    ( ! [X2,X0,X1] : (r2_yellow_0(X0,X2) | r1_lattice3(X0,X2,sK1(X0,X1,X2)) | ~r1_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 1.75/1.00    inference(cnf_transformation,[],[f25])).
% 1.75/1.00  
% 1.75/1.00  fof(f43,plain,(
% 1.75/1.00    ( ! [X2,X0,X1] : (r2_yellow_0(X0,X2) | ~r1_orders_2(X0,sK1(X0,X1,X2),X1) | ~r1_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 1.75/1.00    inference(cnf_transformation,[],[f25])).
% 1.75/1.00  
% 1.75/1.00  fof(f35,plain,(
% 1.75/1.00    ( ! [X2,X0,X1] : (r1_lattice3(X0,X1,X2) | ~r1_orders_2(X0,X2,sK0(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.75/1.00    inference(cnf_transformation,[],[f23])).
% 1.75/1.00  
% 1.75/1.00  fof(f37,plain,(
% 1.75/1.00    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X4,X1) | ~r1_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r2_yellow_0(X0,X2) | k2_yellow_0(X0,X2) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 1.75/1.00    inference(cnf_transformation,[],[f25])).
% 1.75/1.00  
% 1.75/1.00  fof(f50,plain,(
% 1.75/1.00    ( ! [X4,X2,X0] : (r1_orders_2(X0,X4,k2_yellow_0(X0,X2)) | ~r1_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r2_yellow_0(X0,X2) | ~m1_subset_1(k2_yellow_0(X0,X2),u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 1.75/1.00    inference(equality_resolution,[],[f37])).
% 1.75/1.00  
% 1.75/1.00  fof(f36,plain,(
% 1.75/1.00    ( ! [X2,X0,X1] : (r1_lattice3(X0,X2,X1) | ~r2_yellow_0(X0,X2) | k2_yellow_0(X0,X2) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 1.75/1.00    inference(cnf_transformation,[],[f25])).
% 1.75/1.00  
% 1.75/1.00  fof(f51,plain,(
% 1.75/1.00    ( ! [X2,X0] : (r1_lattice3(X0,X2,k2_yellow_0(X0,X2)) | ~r2_yellow_0(X0,X2) | ~m1_subset_1(k2_yellow_0(X0,X2),u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 1.75/1.00    inference(equality_resolution,[],[f36])).
% 1.75/1.00  
% 1.75/1.00  fof(f49,plain,(
% 1.75/1.00    k2_yellow_0(sK2,k6_waybel_0(sK2,sK3)) != sK3 | ~r2_yellow_0(sK2,k6_waybel_0(sK2,sK3))),
% 1.75/1.00    inference(cnf_transformation,[],[f28])).
% 1.75/1.00  
% 1.75/1.00  cnf(c_2,plain,
% 1.75/1.00      ( r3_orders_2(X0,X1,X1)
% 1.75/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.75/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.75/1.00      | v2_struct_0(X0)
% 1.75/1.00      | ~ v3_orders_2(X0)
% 1.75/1.00      | ~ l1_orders_2(X0) ),
% 1.75/1.00      inference(cnf_transformation,[],[f31]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_19,negated_conjecture,
% 1.75/1.00      ( v3_orders_2(sK2) ),
% 1.75/1.00      inference(cnf_transformation,[],[f45]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_271,plain,
% 1.75/1.00      ( r3_orders_2(X0,X1,X1)
% 1.75/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.75/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.75/1.00      | v2_struct_0(X0)
% 1.75/1.00      | ~ l1_orders_2(X0)
% 1.75/1.00      | sK2 != X0 ),
% 1.75/1.00      inference(resolution_lifted,[status(thm)],[c_2,c_19]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_272,plain,
% 1.75/1.00      ( r3_orders_2(sK2,X0,X0)
% 1.75/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.75/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.75/1.00      | v2_struct_0(sK2)
% 1.75/1.00      | ~ l1_orders_2(sK2) ),
% 1.75/1.00      inference(unflattening,[status(thm)],[c_271]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_20,negated_conjecture,
% 1.75/1.00      ( ~ v2_struct_0(sK2) ),
% 1.75/1.00      inference(cnf_transformation,[],[f44]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_17,negated_conjecture,
% 1.75/1.00      ( l1_orders_2(sK2) ),
% 1.75/1.00      inference(cnf_transformation,[],[f47]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_276,plain,
% 1.75/1.00      ( r3_orders_2(sK2,X0,X0)
% 1.75/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.75/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 1.75/1.00      inference(global_propositional_subsumption,
% 1.75/1.00                [status(thm)],
% 1.75/1.00                [c_272,c_20,c_17]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_277,plain,
% 1.75/1.00      ( r3_orders_2(sK2,X0,X0)
% 1.75/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.75/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 1.75/1.00      inference(renaming,[status(thm)],[c_276]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_1,plain,
% 1.75/1.00      ( r1_orders_2(X0,X1,X2)
% 1.75/1.00      | ~ r3_orders_2(X0,X1,X2)
% 1.75/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.75/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.75/1.00      | v2_struct_0(X0)
% 1.75/1.00      | ~ v3_orders_2(X0)
% 1.75/1.00      | ~ l1_orders_2(X0) ),
% 1.75/1.00      inference(cnf_transformation,[],[f29]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_292,plain,
% 1.75/1.00      ( r1_orders_2(X0,X1,X2)
% 1.75/1.00      | ~ r3_orders_2(X0,X1,X2)
% 1.75/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.75/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.75/1.00      | v2_struct_0(X0)
% 1.75/1.00      | ~ l1_orders_2(X0)
% 1.75/1.00      | sK2 != X0 ),
% 1.75/1.00      inference(resolution_lifted,[status(thm)],[c_1,c_19]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_293,plain,
% 1.75/1.00      ( r1_orders_2(sK2,X0,X1)
% 1.75/1.00      | ~ r3_orders_2(sK2,X0,X1)
% 1.75/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.75/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.75/1.00      | v2_struct_0(sK2)
% 1.75/1.00      | ~ l1_orders_2(sK2) ),
% 1.75/1.00      inference(unflattening,[status(thm)],[c_292]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_297,plain,
% 1.75/1.00      ( r1_orders_2(sK2,X0,X1)
% 1.75/1.00      | ~ r3_orders_2(sK2,X0,X1)
% 1.75/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.75/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 1.75/1.00      inference(global_propositional_subsumption,
% 1.75/1.00                [status(thm)],
% 1.75/1.00                [c_293,c_20,c_17]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_298,plain,
% 1.75/1.00      ( r1_orders_2(sK2,X0,X1)
% 1.75/1.00      | ~ r3_orders_2(sK2,X0,X1)
% 1.75/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.75/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 1.75/1.00      inference(renaming,[status(thm)],[c_297]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_355,plain,
% 1.75/1.00      ( r1_orders_2(sK2,X0,X1)
% 1.75/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 1.75/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.75/1.00      | ~ m1_subset_1(X3,u1_struct_0(sK2))
% 1.75/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.75/1.00      | X0 != X3
% 1.75/1.00      | X1 != X3
% 1.75/1.00      | sK2 != sK2 ),
% 1.75/1.00      inference(resolution_lifted,[status(thm)],[c_277,c_298]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_356,plain,
% 1.75/1.00      ( r1_orders_2(sK2,X0,X0)
% 1.75/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.75/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 1.75/1.00      inference(unflattening,[status(thm)],[c_355]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_1790,plain,
% 1.75/1.00      ( r1_orders_2(sK2,X0_47,X0_47)
% 1.75/1.00      | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
% 1.75/1.00      | ~ m1_subset_1(X0_47,u1_struct_0(sK2)) ),
% 1.75/1.00      inference(subtyping,[status(esa)],[c_356]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_1793,plain,
% 1.75/1.00      ( ~ m1_subset_1(X0_47,u1_struct_0(sK2)) | ~ sP0_iProver_split ),
% 1.75/1.00      inference(splitting,
% 1.75/1.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 1.75/1.00                [c_1790]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_16,negated_conjecture,
% 1.75/1.00      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 1.75/1.00      inference(cnf_transformation,[],[f48]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_1822,plain,
% 1.75/1.00      ( ~ m1_subset_1(sK3,u1_struct_0(sK2)) | ~ sP0_iProver_split ),
% 1.75/1.00      inference(instantiation,[status(thm)],[c_1793]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_1894,plain,
% 1.75/1.00      ( ~ sP0_iProver_split ),
% 1.75/1.00      inference(global_propositional_subsumption,
% 1.75/1.00                [status(thm)],
% 1.75/1.00                [c_1793,c_16,c_1822]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_1795,plain,
% 1.75/1.00      ( sP1_iProver_split | sP0_iProver_split ),
% 1.75/1.00      inference(splitting,
% 1.75/1.00                [splitting(split),new_symbols(definition,[])],
% 1.75/1.00                [c_1790]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_1882,plain,
% 1.75/1.00      ( sP1_iProver_split ),
% 1.75/1.00      inference(global_propositional_subsumption,
% 1.75/1.00                [status(thm)],
% 1.75/1.00                [c_1795,c_16,c_1822]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_211,plain,
% 1.75/1.00      ( ~ v5_orders_2(X0) | v5_orders_2(X1) | X1 != X0 ),
% 1.75/1.00      theory(equality) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_209,plain,
% 1.75/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X1) | X2 != X0 ),
% 1.75/1.00      theory(equality) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_207,plain,
% 1.75/1.00      ( ~ v2_struct_0(X0) | v2_struct_0(X1) | X1 != X0 ),
% 1.75/1.00      theory(equality) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_206,plain,
% 1.75/1.00      ( ~ v3_orders_2(X0) | v3_orders_2(X1) | X1 != X0 ),
% 1.75/1.00      theory(equality) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_205,plain,
% 1.75/1.00      ( ~ l1_orders_2(X0) | l1_orders_2(X1) | X1 != X0 ),
% 1.75/1.00      theory(equality) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_1796,plain,( X0_2 = X0_2 ),theory(equality) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_12,plain,
% 1.75/1.00      ( ~ r1_lattice3(X0,X1,X2)
% 1.75/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.75/1.00      | m1_subset_1(sK1(X0,X2,X1),u1_struct_0(X0))
% 1.75/1.00      | ~ v5_orders_2(X0)
% 1.75/1.00      | ~ l1_orders_2(X0)
% 1.75/1.00      | k2_yellow_0(X0,X1) = X2 ),
% 1.75/1.00      inference(cnf_transformation,[],[f38]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_18,negated_conjecture,
% 1.75/1.00      ( v5_orders_2(sK2) ),
% 1.75/1.00      inference(cnf_transformation,[],[f46]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_422,plain,
% 1.75/1.00      ( ~ r1_lattice3(X0,X1,X2)
% 1.75/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.75/1.00      | m1_subset_1(sK1(X0,X2,X1),u1_struct_0(X0))
% 1.75/1.00      | ~ l1_orders_2(X0)
% 1.75/1.00      | k2_yellow_0(X0,X1) = X2
% 1.75/1.00      | sK2 != X0 ),
% 1.75/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_18]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_423,plain,
% 1.75/1.00      ( ~ r1_lattice3(sK2,X0,X1)
% 1.75/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.75/1.00      | m1_subset_1(sK1(sK2,X1,X0),u1_struct_0(sK2))
% 1.75/1.00      | ~ l1_orders_2(sK2)
% 1.75/1.00      | k2_yellow_0(sK2,X0) = X1 ),
% 1.75/1.00      inference(unflattening,[status(thm)],[c_422]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_427,plain,
% 1.75/1.00      ( m1_subset_1(sK1(sK2,X1,X0),u1_struct_0(sK2))
% 1.75/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.75/1.00      | ~ r1_lattice3(sK2,X0,X1)
% 1.75/1.00      | k2_yellow_0(sK2,X0) = X1 ),
% 1.75/1.00      inference(global_propositional_subsumption,[status(thm)],[c_423,c_17]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_428,plain,
% 1.75/1.00      ( ~ r1_lattice3(sK2,X0,X1)
% 1.75/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.75/1.00      | m1_subset_1(sK1(sK2,X1,X0),u1_struct_0(sK2))
% 1.75/1.00      | k2_yellow_0(sK2,X0) = X1 ),
% 1.75/1.00      inference(renaming,[status(thm)],[c_427]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_1787,plain,
% 1.75/1.00      ( ~ r1_lattice3(sK2,X0_46,X0_47)
% 1.75/1.00      | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
% 1.75/1.00      | m1_subset_1(sK1(sK2,X0_47,X0_46),u1_struct_0(sK2))
% 1.75/1.00      | k2_yellow_0(sK2,X0_46) = X0_47 ),
% 1.75/1.00      inference(subtyping,[status(esa)],[c_428]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_2124,plain,
% 1.75/1.00      ( k2_yellow_0(sK2,X0_46) = X0_47
% 1.75/1.00      | r1_lattice3(sK2,X0_46,X0_47) != iProver_top
% 1.75/1.00      | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
% 1.75/1.00      | m1_subset_1(sK1(sK2,X0_47,X0_46),u1_struct_0(sK2)) = iProver_top ),
% 1.75/1.00      inference(predicate_to_equality,[status(thm)],[c_1787]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_11,plain,
% 1.75/1.00      ( ~ r1_lattice3(X0,X1,X2)
% 1.75/1.00      | r1_lattice3(X0,X1,sK1(X0,X2,X1))
% 1.75/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.75/1.00      | ~ v5_orders_2(X0)
% 1.75/1.00      | ~ l1_orders_2(X0)
% 1.75/1.00      | k2_yellow_0(X0,X1) = X2 ),
% 1.75/1.00      inference(cnf_transformation,[],[f39]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_446,plain,
% 1.75/1.00      ( ~ r1_lattice3(X0,X1,X2)
% 1.75/1.00      | r1_lattice3(X0,X1,sK1(X0,X2,X1))
% 1.75/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.75/1.00      | ~ l1_orders_2(X0)
% 1.75/1.00      | k2_yellow_0(X0,X1) = X2
% 1.75/1.00      | sK2 != X0 ),
% 1.75/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_18]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_447,plain,
% 1.75/1.00      ( ~ r1_lattice3(sK2,X0,X1)
% 1.75/1.00      | r1_lattice3(sK2,X0,sK1(sK2,X1,X0))
% 1.75/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.75/1.00      | ~ l1_orders_2(sK2)
% 1.75/1.00      | k2_yellow_0(sK2,X0) = X1 ),
% 1.75/1.00      inference(unflattening,[status(thm)],[c_446]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_451,plain,
% 1.75/1.00      ( ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.75/1.00      | r1_lattice3(sK2,X0,sK1(sK2,X1,X0))
% 1.75/1.00      | ~ r1_lattice3(sK2,X0,X1)
% 1.75/1.00      | k2_yellow_0(sK2,X0) = X1 ),
% 1.75/1.00      inference(global_propositional_subsumption,[status(thm)],[c_447,c_17]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_452,plain,
% 1.75/1.00      ( ~ r1_lattice3(sK2,X0,X1)
% 1.75/1.00      | r1_lattice3(sK2,X0,sK1(sK2,X1,X0))
% 1.75/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.75/1.00      | k2_yellow_0(sK2,X0) = X1 ),
% 1.75/1.00      inference(renaming,[status(thm)],[c_451]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_1786,plain,
% 1.75/1.00      ( ~ r1_lattice3(sK2,X0_46,X0_47)
% 1.75/1.00      | r1_lattice3(sK2,X0_46,sK1(sK2,X0_47,X0_46))
% 1.75/1.00      | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
% 1.75/1.00      | k2_yellow_0(sK2,X0_46) = X0_47 ),
% 1.75/1.00      inference(subtyping,[status(esa)],[c_452]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_2125,plain,
% 1.75/1.00      ( k2_yellow_0(sK2,X0_46) = X0_47
% 1.75/1.00      | r1_lattice3(sK2,X0_46,X0_47) != iProver_top
% 1.75/1.00      | r1_lattice3(sK2,X0_46,sK1(sK2,X0_47,X0_46)) = iProver_top
% 1.75/1.00      | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top ),
% 1.75/1.00      inference(predicate_to_equality,[status(thm)],[c_1786]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_6,plain,
% 1.75/1.00      ( ~ r1_lattice3(X0,X1,X2)
% 1.75/1.00      | r1_orders_2(X0,X2,X3)
% 1.75/1.00      | ~ r2_hidden(X3,X1)
% 1.75/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.75/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.75/1.00      | ~ l1_orders_2(X0) ),
% 1.75/1.00      inference(cnf_transformation,[],[f32]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_606,plain,
% 1.75/1.00      ( ~ r1_lattice3(X0,X1,X2)
% 1.75/1.00      | r1_orders_2(X0,X2,X3)
% 1.75/1.00      | ~ r2_hidden(X3,X1)
% 1.75/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.75/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.75/1.00      | sK2 != X0 ),
% 1.75/1.00      inference(resolution_lifted,[status(thm)],[c_6,c_17]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_607,plain,
% 1.75/1.00      ( ~ r1_lattice3(sK2,X0,X1)
% 1.75/1.00      | r1_orders_2(sK2,X1,X2)
% 1.75/1.00      | ~ r2_hidden(X2,X0)
% 1.75/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.75/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK2)) ),
% 1.75/1.00      inference(unflattening,[status(thm)],[c_606]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_4,plain,
% 1.75/1.00      ( r1_lattice3(X0,X1,X2)
% 1.75/1.00      | r2_hidden(sK0(X0,X1,X2),X1)
% 1.75/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.75/1.00      | ~ l1_orders_2(X0) ),
% 1.75/1.00      inference(cnf_transformation,[],[f34]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_640,plain,
% 1.75/1.00      ( r1_lattice3(X0,X1,X2)
% 1.75/1.00      | r2_hidden(sK0(X0,X1,X2),X1)
% 1.75/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.75/1.00      | sK2 != X0 ),
% 1.75/1.00      inference(resolution_lifted,[status(thm)],[c_4,c_17]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_641,plain,
% 1.75/1.00      ( r1_lattice3(sK2,X0,X1)
% 1.75/1.00      | r2_hidden(sK0(sK2,X0,X1),X0)
% 1.75/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 1.75/1.00      inference(unflattening,[status(thm)],[c_640]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_688,plain,
% 1.75/1.00      ( ~ r1_lattice3(sK2,X0,X1)
% 1.75/1.00      | r1_lattice3(sK2,X2,X3)
% 1.75/1.00      | r1_orders_2(sK2,X1,X4)
% 1.75/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.75/1.00      | ~ m1_subset_1(X4,u1_struct_0(sK2))
% 1.75/1.00      | ~ m1_subset_1(X3,u1_struct_0(sK2))
% 1.75/1.00      | X2 != X0
% 1.75/1.00      | sK0(sK2,X2,X3) != X4 ),
% 1.75/1.00      inference(resolution_lifted,[status(thm)],[c_607,c_641]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_689,plain,
% 1.75/1.00      ( ~ r1_lattice3(sK2,X0,X1)
% 1.75/1.00      | r1_lattice3(sK2,X0,X2)
% 1.75/1.00      | r1_orders_2(sK2,X1,sK0(sK2,X0,X2))
% 1.75/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.75/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 1.75/1.00      | ~ m1_subset_1(sK0(sK2,X0,X2),u1_struct_0(sK2)) ),
% 1.75/1.00      inference(unflattening,[status(thm)],[c_688]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_5,plain,
% 1.75/1.00      ( r1_lattice3(X0,X1,X2)
% 1.75/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.75/1.00      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 1.75/1.00      | ~ l1_orders_2(X0) ),
% 1.75/1.00      inference(cnf_transformation,[],[f33]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_625,plain,
% 1.75/1.00      ( r1_lattice3(X0,X1,X2)
% 1.75/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.75/1.00      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 1.75/1.00      | sK2 != X0 ),
% 1.75/1.00      inference(resolution_lifted,[status(thm)],[c_5,c_17]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_626,plain,
% 1.75/1.00      ( r1_lattice3(sK2,X0,X1)
% 1.75/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.75/1.00      | m1_subset_1(sK0(sK2,X0,X1),u1_struct_0(sK2)) ),
% 1.75/1.00      inference(unflattening,[status(thm)],[c_625]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_703,plain,
% 1.75/1.00      ( ~ r1_lattice3(sK2,X0,X1)
% 1.75/1.00      | r1_lattice3(sK2,X0,X2)
% 1.75/1.00      | r1_orders_2(sK2,X1,sK0(sK2,X0,X2))
% 1.75/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.75/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK2)) ),
% 1.75/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_689,c_626]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_1779,plain,
% 1.75/1.00      ( ~ r1_lattice3(sK2,X0_46,X0_47)
% 1.75/1.00      | r1_lattice3(sK2,X0_46,X1_47)
% 1.75/1.00      | r1_orders_2(sK2,X0_47,sK0(sK2,X0_46,X1_47))
% 1.75/1.00      | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
% 1.75/1.00      | ~ m1_subset_1(X0_47,u1_struct_0(sK2)) ),
% 1.75/1.00      inference(subtyping,[status(esa)],[c_703]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_2132,plain,
% 1.75/1.00      ( r1_lattice3(sK2,X0_46,X0_47) != iProver_top
% 1.75/1.00      | r1_lattice3(sK2,X0_46,X1_47) = iProver_top
% 1.75/1.00      | r1_orders_2(sK2,X0_47,sK0(sK2,X0_46,X1_47)) = iProver_top
% 1.75/1.00      | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
% 1.75/1.00      | m1_subset_1(X1_47,u1_struct_0(sK2)) != iProver_top ),
% 1.75/1.00      inference(predicate_to_equality,[status(thm)],[c_1779]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_10,plain,
% 1.75/1.00      ( ~ r1_lattice3(X0,X1,X2)
% 1.75/1.00      | ~ r1_orders_2(X0,sK1(X0,X2,X1),X2)
% 1.75/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.75/1.00      | ~ v5_orders_2(X0)
% 1.75/1.00      | ~ l1_orders_2(X0)
% 1.75/1.00      | k2_yellow_0(X0,X1) = X2 ),
% 1.75/1.00      inference(cnf_transformation,[],[f40]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_470,plain,
% 1.75/1.00      ( ~ r1_lattice3(X0,X1,X2)
% 1.75/1.00      | ~ r1_orders_2(X0,sK1(X0,X2,X1),X2)
% 1.75/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.75/1.00      | ~ l1_orders_2(X0)
% 1.75/1.00      | k2_yellow_0(X0,X1) = X2
% 1.75/1.00      | sK2 != X0 ),
% 1.75/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_18]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_471,plain,
% 1.75/1.00      ( ~ r1_lattice3(sK2,X0,X1)
% 1.75/1.00      | ~ r1_orders_2(sK2,sK1(sK2,X1,X0),X1)
% 1.75/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.75/1.00      | ~ l1_orders_2(sK2)
% 1.75/1.00      | k2_yellow_0(sK2,X0) = X1 ),
% 1.75/1.00      inference(unflattening,[status(thm)],[c_470]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_475,plain,
% 1.75/1.00      ( ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.75/1.00      | ~ r1_orders_2(sK2,sK1(sK2,X1,X0),X1)
% 1.75/1.00      | ~ r1_lattice3(sK2,X0,X1)
% 1.75/1.00      | k2_yellow_0(sK2,X0) = X1 ),
% 1.75/1.00      inference(global_propositional_subsumption,[status(thm)],[c_471,c_17]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_476,plain,
% 1.75/1.00      ( ~ r1_lattice3(sK2,X0,X1)
% 1.75/1.00      | ~ r1_orders_2(sK2,sK1(sK2,X1,X0),X1)
% 1.75/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.75/1.00      | k2_yellow_0(sK2,X0) = X1 ),
% 1.75/1.00      inference(renaming,[status(thm)],[c_475]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_1785,plain,
% 1.75/1.00      ( ~ r1_lattice3(sK2,X0_46,X0_47)
% 1.75/1.00      | ~ r1_orders_2(sK2,sK1(sK2,X0_47,X0_46),X0_47)
% 1.75/1.00      | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
% 1.75/1.00      | k2_yellow_0(sK2,X0_46) = X0_47 ),
% 1.75/1.00      inference(subtyping,[status(esa)],[c_476]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_2126,plain,
% 1.75/1.00      ( k2_yellow_0(sK2,X0_46) = X0_47
% 1.75/1.00      | r1_lattice3(sK2,X0_46,X0_47) != iProver_top
% 1.75/1.00      | r1_orders_2(sK2,sK1(sK2,X0_47,X0_46),X0_47) != iProver_top
% 1.75/1.00      | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top ),
% 1.75/1.00      inference(predicate_to_equality,[status(thm)],[c_1785]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_2509,plain,
% 1.75/1.00      ( sK0(sK2,X0_46,X0_47) = k2_yellow_0(sK2,X1_46)
% 1.75/1.00      | r1_lattice3(sK2,X0_46,X0_47) = iProver_top
% 1.75/1.00      | r1_lattice3(sK2,X0_46,sK1(sK2,sK0(sK2,X0_46,X0_47),X1_46)) != iProver_top
% 1.75/1.00      | r1_lattice3(sK2,X1_46,sK0(sK2,X0_46,X0_47)) != iProver_top
% 1.75/1.00      | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
% 1.75/1.00      | m1_subset_1(sK1(sK2,sK0(sK2,X0_46,X0_47),X1_46),u1_struct_0(sK2)) != iProver_top
% 1.75/1.00      | m1_subset_1(sK0(sK2,X0_46,X0_47),u1_struct_0(sK2)) != iProver_top ),
% 1.75/1.00      inference(superposition,[status(thm)],[c_2132,c_2126]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_1781,plain,
% 1.75/1.00      ( r1_lattice3(sK2,X0_46,X0_47)
% 1.75/1.00      | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
% 1.75/1.00      | m1_subset_1(sK0(sK2,X0_46,X0_47),u1_struct_0(sK2)) ),
% 1.75/1.00      inference(subtyping,[status(esa)],[c_626]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_1848,plain,
% 1.75/1.00      ( r1_lattice3(sK2,X0_46,X0_47) = iProver_top
% 1.75/1.00      | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
% 1.75/1.00      | m1_subset_1(sK0(sK2,X0_46,X0_47),u1_struct_0(sK2)) = iProver_top ),
% 1.75/1.00      inference(predicate_to_equality,[status(thm)],[c_1781]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_3010,plain,
% 1.75/1.00      ( m1_subset_1(sK1(sK2,sK0(sK2,X0_46,X0_47),X1_46),u1_struct_0(sK2)) != iProver_top
% 1.75/1.00      | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
% 1.75/1.00      | r1_lattice3(sK2,X1_46,sK0(sK2,X0_46,X0_47)) != iProver_top
% 1.75/1.00      | r1_lattice3(sK2,X0_46,sK1(sK2,sK0(sK2,X0_46,X0_47),X1_46)) != iProver_top
% 1.75/1.00      | r1_lattice3(sK2,X0_46,X0_47) = iProver_top
% 1.75/1.00      | sK0(sK2,X0_46,X0_47) = k2_yellow_0(sK2,X1_46) ),
% 1.75/1.00      inference(global_propositional_subsumption,[status(thm)],[c_2509,c_1848]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_3011,plain,
% 1.75/1.00      ( sK0(sK2,X0_46,X0_47) = k2_yellow_0(sK2,X1_46)
% 1.75/1.00      | r1_lattice3(sK2,X0_46,X0_47) = iProver_top
% 1.75/1.00      | r1_lattice3(sK2,X0_46,sK1(sK2,sK0(sK2,X0_46,X0_47),X1_46)) != iProver_top
% 1.75/1.00      | r1_lattice3(sK2,X1_46,sK0(sK2,X0_46,X0_47)) != iProver_top
% 1.75/1.00      | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
% 1.75/1.00      | m1_subset_1(sK1(sK2,sK0(sK2,X0_46,X0_47),X1_46),u1_struct_0(sK2)) != iProver_top ),
% 1.75/1.00      inference(renaming,[status(thm)],[c_3010]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_3023,plain,
% 1.75/1.00      ( sK0(sK2,X0_46,X0_47) = k2_yellow_0(sK2,X0_46)
% 1.75/1.00      | r1_lattice3(sK2,X0_46,X0_47) = iProver_top
% 1.75/1.00      | r1_lattice3(sK2,X0_46,sK0(sK2,X0_46,X0_47)) != iProver_top
% 1.75/1.00      | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
% 1.75/1.00      | m1_subset_1(sK1(sK2,sK0(sK2,X0_46,X0_47),X0_46),u1_struct_0(sK2)) != iProver_top
% 1.75/1.00      | m1_subset_1(sK0(sK2,X0_46,X0_47),u1_struct_0(sK2)) != iProver_top ),
% 1.75/1.00      inference(superposition,[status(thm)],[c_2125,c_3011]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_3267,plain,
% 1.75/1.00      ( m1_subset_1(sK1(sK2,sK0(sK2,X0_46,X0_47),X0_46),u1_struct_0(sK2)) != iProver_top
% 1.75/1.00      | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
% 1.75/1.00      | r1_lattice3(sK2,X0_46,sK0(sK2,X0_46,X0_47)) != iProver_top
% 1.75/1.00      | r1_lattice3(sK2,X0_46,X0_47) = iProver_top
% 1.75/1.00      | sK0(sK2,X0_46,X0_47) = k2_yellow_0(sK2,X0_46) ),
% 1.75/1.00      inference(global_propositional_subsumption,[status(thm)],[c_3023,c_1848]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_3268,plain,
% 1.75/1.00      ( sK0(sK2,X0_46,X0_47) = k2_yellow_0(sK2,X0_46)
% 1.75/1.00      | r1_lattice3(sK2,X0_46,X0_47) = iProver_top
% 1.75/1.00      | r1_lattice3(sK2,X0_46,sK0(sK2,X0_46,X0_47)) != iProver_top
% 1.75/1.00      | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
% 1.75/1.00      | m1_subset_1(sK1(sK2,sK0(sK2,X0_46,X0_47),X0_46),u1_struct_0(sK2)) != iProver_top ),
% 1.75/1.00      inference(renaming,[status(thm)],[c_3267]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_3279,plain,
% 1.75/1.00      ( sK0(sK2,X0_46,X0_47) = k2_yellow_0(sK2,X0_46)
% 1.75/1.00      | r1_lattice3(sK2,X0_46,X0_47) = iProver_top
% 1.75/1.00      | r1_lattice3(sK2,X0_46,sK0(sK2,X0_46,X0_47)) != iProver_top
% 1.75/1.00      | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
% 1.75/1.00      | m1_subset_1(sK0(sK2,X0_46,X0_47),u1_struct_0(sK2)) != iProver_top ),
% 1.75/1.00      inference(superposition,[status(thm)],[c_2124,c_3268]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_3294,plain,
% 1.75/1.00      ( m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
% 1.75/1.00      | r1_lattice3(sK2,X0_46,sK0(sK2,X0_46,X0_47)) != iProver_top
% 1.75/1.00      | r1_lattice3(sK2,X0_46,X0_47) = iProver_top
% 1.75/1.00      | sK0(sK2,X0_46,X0_47) = k2_yellow_0(sK2,X0_46) ),
% 1.75/1.00      inference(global_propositional_subsumption,[status(thm)],[c_3279,c_1848]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_3295,plain,
% 1.75/1.00      ( sK0(sK2,X0_46,X0_47) = k2_yellow_0(sK2,X0_46)
% 1.75/1.00      | r1_lattice3(sK2,X0_46,X0_47) = iProver_top
% 1.75/1.00      | r1_lattice3(sK2,X0_46,sK0(sK2,X0_46,X0_47)) != iProver_top
% 1.75/1.00      | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top ),
% 1.75/1.00      inference(renaming,[status(thm)],[c_3294]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_9,plain,
% 1.75/1.00      ( ~ r1_lattice3(X0,X1,X2)
% 1.75/1.00      | r2_yellow_0(X0,X1)
% 1.75/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.75/1.00      | m1_subset_1(sK1(X0,X2,X1),u1_struct_0(X0))
% 1.75/1.00      | ~ v5_orders_2(X0)
% 1.75/1.00      | ~ l1_orders_2(X0) ),
% 1.75/1.00      inference(cnf_transformation,[],[f41]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_494,plain,
% 1.75/1.00      ( ~ r1_lattice3(X0,X1,X2)
% 1.75/1.00      | r2_yellow_0(X0,X1)
% 1.75/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.75/1.00      | m1_subset_1(sK1(X0,X2,X1),u1_struct_0(X0))
% 1.75/1.00      | ~ l1_orders_2(X0)
% 1.75/1.00      | sK2 != X0 ),
% 1.75/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_18]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_495,plain,
% 1.75/1.00      ( ~ r1_lattice3(sK2,X0,X1)
% 1.75/1.00      | r2_yellow_0(sK2,X0)
% 1.75/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.75/1.00      | m1_subset_1(sK1(sK2,X1,X0),u1_struct_0(sK2))
% 1.75/1.00      | ~ l1_orders_2(sK2) ),
% 1.75/1.00      inference(unflattening,[status(thm)],[c_494]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_499,plain,
% 1.75/1.00      ( m1_subset_1(sK1(sK2,X1,X0),u1_struct_0(sK2))
% 1.75/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.75/1.00      | r2_yellow_0(sK2,X0)
% 1.75/1.00      | ~ r1_lattice3(sK2,X0,X1) ),
% 1.75/1.00      inference(global_propositional_subsumption,[status(thm)],[c_495,c_17]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_500,plain,
% 1.75/1.00      ( ~ r1_lattice3(sK2,X0,X1)
% 1.75/1.00      | r2_yellow_0(sK2,X0)
% 1.75/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.75/1.00      | m1_subset_1(sK1(sK2,X1,X0),u1_struct_0(sK2)) ),
% 1.75/1.00      inference(renaming,[status(thm)],[c_499]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_1784,plain,
% 1.75/1.00      ( ~ r1_lattice3(sK2,X0_46,X0_47)
% 1.75/1.00      | r2_yellow_0(sK2,X0_46)
% 1.75/1.00      | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
% 1.75/1.00      | m1_subset_1(sK1(sK2,X0_47,X0_46),u1_struct_0(sK2)) ),
% 1.75/1.00      inference(subtyping,[status(esa)],[c_500]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_2127,plain,
% 1.75/1.00      ( r1_lattice3(sK2,X0_46,X0_47) != iProver_top
% 1.75/1.00      | r2_yellow_0(sK2,X0_46) = iProver_top
% 1.75/1.00      | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
% 1.75/1.00      | m1_subset_1(sK1(sK2,X0_47,X0_46),u1_struct_0(sK2)) = iProver_top ),
% 1.75/1.00      inference(predicate_to_equality,[status(thm)],[c_1784]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_8,plain,
% 1.75/1.00      ( ~ r1_lattice3(X0,X1,X2)
% 1.75/1.00      | r1_lattice3(X0,X1,sK1(X0,X2,X1))
% 1.75/1.00      | r2_yellow_0(X0,X1)
% 1.75/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.75/1.00      | ~ v5_orders_2(X0)
% 1.75/1.00      | ~ l1_orders_2(X0) ),
% 1.75/1.00      inference(cnf_transformation,[],[f42]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_518,plain,
% 1.75/1.00      ( ~ r1_lattice3(X0,X1,X2)
% 1.75/1.00      | r1_lattice3(X0,X1,sK1(X0,X2,X1))
% 1.75/1.00      | r2_yellow_0(X0,X1)
% 1.75/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.75/1.00      | ~ l1_orders_2(X0)
% 1.75/1.00      | sK2 != X0 ),
% 1.75/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_18]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_519,plain,
% 1.75/1.00      ( ~ r1_lattice3(sK2,X0,X1)
% 1.75/1.00      | r1_lattice3(sK2,X0,sK1(sK2,X1,X0))
% 1.75/1.00      | r2_yellow_0(sK2,X0)
% 1.75/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.75/1.00      | ~ l1_orders_2(sK2) ),
% 1.75/1.00      inference(unflattening,[status(thm)],[c_518]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_523,plain,
% 1.75/1.00      ( ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.75/1.00      | r2_yellow_0(sK2,X0)
% 1.75/1.00      | r1_lattice3(sK2,X0,sK1(sK2,X1,X0))
% 1.75/1.00      | ~ r1_lattice3(sK2,X0,X1) ),
% 1.75/1.00      inference(global_propositional_subsumption,[status(thm)],[c_519,c_17]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_524,plain,
% 1.75/1.00      ( ~ r1_lattice3(sK2,X0,X1)
% 1.75/1.00      | r1_lattice3(sK2,X0,sK1(sK2,X1,X0))
% 1.75/1.00      | r2_yellow_0(sK2,X0)
% 1.75/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 1.75/1.00      inference(renaming,[status(thm)],[c_523]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_1783,plain,
% 1.75/1.00      ( ~ r1_lattice3(sK2,X0_46,X0_47)
% 1.75/1.00      | r1_lattice3(sK2,X0_46,sK1(sK2,X0_47,X0_46))
% 1.75/1.00      | r2_yellow_0(sK2,X0_46)
% 1.75/1.00      | ~ m1_subset_1(X0_47,u1_struct_0(sK2)) ),
% 1.75/1.00      inference(subtyping,[status(esa)],[c_524]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_2128,plain,
% 1.75/1.00      ( r1_lattice3(sK2,X0_46,X0_47) != iProver_top
% 1.75/1.00      | r1_lattice3(sK2,X0_46,sK1(sK2,X0_47,X0_46)) = iProver_top
% 1.75/1.00      | r2_yellow_0(sK2,X0_46) = iProver_top
% 1.75/1.00      | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top ),
% 1.75/1.00      inference(predicate_to_equality,[status(thm)],[c_1783]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_7,plain,
% 1.75/1.00      ( ~ r1_lattice3(X0,X1,X2)
% 1.75/1.00      | ~ r1_orders_2(X0,sK1(X0,X2,X1),X2)
% 1.75/1.00      | r2_yellow_0(X0,X1)
% 1.75/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.75/1.00      | ~ v5_orders_2(X0)
% 1.75/1.00      | ~ l1_orders_2(X0) ),
% 1.75/1.00      inference(cnf_transformation,[],[f43]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_542,plain,
% 1.75/1.00      ( ~ r1_lattice3(X0,X1,X2)
% 1.75/1.00      | ~ r1_orders_2(X0,sK1(X0,X2,X1),X2)
% 1.75/1.00      | r2_yellow_0(X0,X1)
% 1.75/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.75/1.00      | ~ l1_orders_2(X0)
% 1.75/1.00      | sK2 != X0 ),
% 1.75/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_18]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_543,plain,
% 1.75/1.00      ( ~ r1_lattice3(sK2,X0,X1)
% 1.75/1.00      | ~ r1_orders_2(sK2,sK1(sK2,X1,X0),X1)
% 1.75/1.00      | r2_yellow_0(sK2,X0)
% 1.75/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.75/1.00      | ~ l1_orders_2(sK2) ),
% 1.75/1.00      inference(unflattening,[status(thm)],[c_542]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_547,plain,
% 1.75/1.00      ( ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.75/1.00      | r2_yellow_0(sK2,X0)
% 1.75/1.00      | ~ r1_orders_2(sK2,sK1(sK2,X1,X0),X1)
% 1.75/1.00      | ~ r1_lattice3(sK2,X0,X1) ),
% 1.75/1.00      inference(global_propositional_subsumption,[status(thm)],[c_543,c_17]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_548,plain,
% 1.75/1.00      ( ~ r1_lattice3(sK2,X0,X1)
% 1.75/1.00      | ~ r1_orders_2(sK2,sK1(sK2,X1,X0),X1)
% 1.75/1.00      | r2_yellow_0(sK2,X0)
% 1.75/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 1.75/1.00      inference(renaming,[status(thm)],[c_547]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_1782,plain,
% 1.75/1.00      ( ~ r1_lattice3(sK2,X0_46,X0_47)
% 1.75/1.00      | ~ r1_orders_2(sK2,sK1(sK2,X0_47,X0_46),X0_47)
% 1.75/1.00      | r2_yellow_0(sK2,X0_46)
% 1.75/1.00      | ~ m1_subset_1(X0_47,u1_struct_0(sK2)) ),
% 1.75/1.00      inference(subtyping,[status(esa)],[c_548]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_2129,plain,
% 1.75/1.00      ( r1_lattice3(sK2,X0_46,X0_47) != iProver_top
% 1.75/1.00      | r1_orders_2(sK2,sK1(sK2,X0_47,X0_46),X0_47) != iProver_top
% 1.75/1.00      | r2_yellow_0(sK2,X0_46) = iProver_top
% 1.75/1.00      | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top ),
% 1.75/1.00      inference(predicate_to_equality,[status(thm)],[c_1782]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_2508,plain,
% 1.75/1.00      ( r1_lattice3(sK2,X0_46,X0_47) = iProver_top
% 1.75/1.00      | r1_lattice3(sK2,X0_46,sK1(sK2,sK0(sK2,X0_46,X0_47),X1_46)) != iProver_top
% 1.75/1.00      | r1_lattice3(sK2,X1_46,sK0(sK2,X0_46,X0_47)) != iProver_top
% 1.75/1.00      | r2_yellow_0(sK2,X1_46) = iProver_top
% 1.75/1.00      | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
% 1.75/1.00      | m1_subset_1(sK1(sK2,sK0(sK2,X0_46,X0_47),X1_46),u1_struct_0(sK2)) != iProver_top
% 1.75/1.00      | m1_subset_1(sK0(sK2,X0_46,X0_47),u1_struct_0(sK2)) != iProver_top ),
% 1.75/1.00      inference(superposition,[status(thm)],[c_2132,c_2129]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_2966,plain,
% 1.75/1.00      ( m1_subset_1(sK1(sK2,sK0(sK2,X0_46,X0_47),X1_46),u1_struct_0(sK2)) != iProver_top
% 1.75/1.00      | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
% 1.75/1.00      | r2_yellow_0(sK2,X1_46) = iProver_top
% 1.75/1.00      | r1_lattice3(sK2,X1_46,sK0(sK2,X0_46,X0_47)) != iProver_top
% 1.75/1.00      | r1_lattice3(sK2,X0_46,sK1(sK2,sK0(sK2,X0_46,X0_47),X1_46)) != iProver_top
% 1.75/1.00      | r1_lattice3(sK2,X0_46,X0_47) = iProver_top ),
% 1.75/1.00      inference(global_propositional_subsumption,[status(thm)],[c_2508,c_1848]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_2967,plain,
% 1.75/1.00      ( r1_lattice3(sK2,X0_46,X0_47) = iProver_top
% 1.75/1.00      | r1_lattice3(sK2,X0_46,sK1(sK2,sK0(sK2,X0_46,X0_47),X1_46)) != iProver_top
% 1.75/1.00      | r1_lattice3(sK2,X1_46,sK0(sK2,X0_46,X0_47)) != iProver_top
% 1.75/1.00      | r2_yellow_0(sK2,X1_46) = iProver_top
% 1.75/1.00      | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
% 1.75/1.00      | m1_subset_1(sK1(sK2,sK0(sK2,X0_46,X0_47),X1_46),u1_struct_0(sK2)) != iProver_top ),
% 1.75/1.00      inference(renaming,[status(thm)],[c_2966]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_2978,plain,
% 1.75/1.00      ( r1_lattice3(sK2,X0_46,X0_47) = iProver_top
% 1.75/1.00      | r1_lattice3(sK2,X0_46,sK0(sK2,X0_46,X0_47)) != iProver_top
% 1.75/1.00      | r2_yellow_0(sK2,X0_46) = iProver_top
% 1.75/1.00      | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
% 1.75/1.00      | m1_subset_1(sK1(sK2,sK0(sK2,X0_46,X0_47),X0_46),u1_struct_0(sK2)) != iProver_top
% 1.75/1.00      | m1_subset_1(sK0(sK2,X0_46,X0_47),u1_struct_0(sK2)) != iProver_top ),
% 1.75/1.00      inference(superposition,[status(thm)],[c_2128,c_2967]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_3104,plain,
% 1.75/1.00      ( m1_subset_1(sK1(sK2,sK0(sK2,X0_46,X0_47),X0_46),u1_struct_0(sK2)) != iProver_top
% 1.75/1.00      | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
% 1.75/1.00      | r2_yellow_0(sK2,X0_46) = iProver_top
% 1.75/1.00      | r1_lattice3(sK2,X0_46,sK0(sK2,X0_46,X0_47)) != iProver_top
% 1.75/1.00      | r1_lattice3(sK2,X0_46,X0_47) = iProver_top ),
% 1.75/1.00      inference(global_propositional_subsumption,[status(thm)],[c_2978,c_1848]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_3105,plain,
% 1.75/1.00      ( r1_lattice3(sK2,X0_46,X0_47) = iProver_top
% 1.75/1.00      | r1_lattice3(sK2,X0_46,sK0(sK2,X0_46,X0_47)) != iProver_top
% 1.75/1.00      | r2_yellow_0(sK2,X0_46) = iProver_top
% 1.75/1.00      | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
% 1.75/1.00      | m1_subset_1(sK1(sK2,sK0(sK2,X0_46,X0_47),X0_46),u1_struct_0(sK2)) != iProver_top ),
% 1.75/1.00      inference(renaming,[status(thm)],[c_3104]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_3115,plain,
% 1.75/1.00      ( r1_lattice3(sK2,X0_46,X0_47) = iProver_top
% 1.75/1.00      | r1_lattice3(sK2,X0_46,sK0(sK2,X0_46,X0_47)) != iProver_top
% 1.75/1.00      | r2_yellow_0(sK2,X0_46) = iProver_top
% 1.75/1.00      | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
% 1.75/1.00      | m1_subset_1(sK0(sK2,X0_46,X0_47),u1_struct_0(sK2)) != iProver_top ),
% 1.75/1.00      inference(superposition,[status(thm)],[c_2127,c_3105]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_3143,plain,
% 1.75/1.00      ( m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
% 1.75/1.00      | r2_yellow_0(sK2,X0_46) = iProver_top
% 1.75/1.00      | r1_lattice3(sK2,X0_46,sK0(sK2,X0_46,X0_47)) != iProver_top
% 1.75/1.00      | r1_lattice3(sK2,X0_46,X0_47) = iProver_top ),
% 1.75/1.00      inference(global_propositional_subsumption,[status(thm)],[c_3115,c_1848]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_3144,plain,
% 1.75/1.00      ( r1_lattice3(sK2,X0_46,X0_47) = iProver_top
% 1.75/1.00      | r1_lattice3(sK2,X0_46,sK0(sK2,X0_46,X0_47)) != iProver_top
% 1.75/1.00      | r2_yellow_0(sK2,X0_46) = iProver_top
% 1.75/1.00      | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top ),
% 1.75/1.00      inference(renaming,[status(thm)],[c_3143]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_1794,plain,
% 1.75/1.00      ( r1_orders_2(sK2,X0_47,X0_47)
% 1.75/1.00      | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
% 1.75/1.00      | ~ sP1_iProver_split ),
% 1.75/1.00      inference(splitting,
% 1.75/1.00                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 1.75/1.00                [c_1790]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_2120,plain,
% 1.75/1.00      ( r1_orders_2(sK2,X0_47,X0_47) = iProver_top
% 1.75/1.00      | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
% 1.75/1.00      | sP1_iProver_split != iProver_top ),
% 1.75/1.00      inference(predicate_to_equality,[status(thm)],[c_1794]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_1887,plain,
% 1.75/1.00      ( ~ m1_subset_1(X0_47,u1_struct_0(sK2)) | r1_orders_2(sK2,X0_47,X0_47) ),
% 1.75/1.00      inference(global_propositional_subsumption,
% 1.75/1.00                [status(thm)],
% 1.75/1.00                [c_1794,c_16,c_1795,c_1822]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_1888,plain,
% 1.75/1.00      ( r1_orders_2(sK2,X0_47,X0_47) | ~ m1_subset_1(X0_47,u1_struct_0(sK2)) ),
% 1.75/1.00      inference(renaming,[status(thm)],[c_1887]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_1889,plain,
% 1.75/1.00      ( r1_orders_2(sK2,X0_47,X0_47) = iProver_top
% 1.75/1.00      | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top ),
% 1.75/1.00      inference(predicate_to_equality,[status(thm)],[c_1888]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_2449,plain,
% 1.75/1.00      ( m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
% 1.75/1.00      | r1_orders_2(sK2,X0_47,X0_47) = iProver_top ),
% 1.75/1.00      inference(global_propositional_subsumption,[status(thm)],[c_2120,c_1889]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_2450,plain,
% 1.75/1.00      ( r1_orders_2(sK2,X0_47,X0_47) = iProver_top
% 1.75/1.00      | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top ),
% 1.75/1.00      inference(renaming,[status(thm)],[c_2449]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_2684,plain,
% 1.75/1.00      ( r1_lattice3(sK2,X0_46,X0_47) != iProver_top
% 1.75/1.00      | r1_orders_2(sK2,sK1(sK2,X0_47,X0_46),sK1(sK2,X0_47,X0_46)) = iProver_top
% 1.75/1.00      | r2_yellow_0(sK2,X0_46) = iProver_top
% 1.75/1.00      | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top ),
% 1.75/1.00      inference(superposition,[status(thm)],[c_2127,c_2450]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_2647,plain,
% 1.75/1.00      ( k2_yellow_0(sK2,X0_46) = X0_47
% 1.75/1.00      | r1_lattice3(sK2,X0_46,X0_47) != iProver_top
% 1.75/1.00      | r1_orders_2(sK2,sK1(sK2,X0_47,X0_46),sK1(sK2,X0_47,X0_46)) = iProver_top
% 1.75/1.00      | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top ),
% 1.75/1.00      inference(superposition,[status(thm)],[c_2124,c_2450]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_2130,plain,
% 1.75/1.00      ( r1_lattice3(sK2,X0_46,X0_47) = iProver_top
% 1.75/1.00      | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
% 1.75/1.00      | m1_subset_1(sK0(sK2,X0_46,X0_47),u1_struct_0(sK2)) = iProver_top ),
% 1.75/1.00      inference(predicate_to_equality,[status(thm)],[c_1781]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_2456,plain,
% 1.75/1.00      ( r1_lattice3(sK2,X0_46,X0_47) = iProver_top
% 1.75/1.00      | r1_orders_2(sK2,sK0(sK2,X0_46,X0_47),sK0(sK2,X0_46,X0_47)) = iProver_top
% 1.75/1.00      | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top ),
% 1.75/1.00      inference(superposition,[status(thm)],[c_2130,c_2450]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_1791,negated_conjecture,
% 1.75/1.00      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 1.75/1.00      inference(subtyping,[status(esa)],[c_16]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_2118,plain,
% 1.75/1.00      ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
% 1.75/1.00      inference(predicate_to_equality,[status(thm)],[c_1791]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_2455,plain,
% 1.75/1.00      ( r1_orders_2(sK2,sK3,sK3) = iProver_top ),
% 1.75/1.00      inference(superposition,[status(thm)],[c_2118,c_2450]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_2121,plain,
% 1.75/1.00      ( m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
% 1.75/1.00      | sP0_iProver_split != iProver_top ),
% 1.75/1.00      inference(predicate_to_equality,[status(thm)],[c_1793]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_25,plain,
% 1.75/1.00      ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
% 1.75/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_1821,plain,
% 1.75/1.00      ( m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
% 1.75/1.00      | sP0_iProver_split != iProver_top ),
% 1.75/1.00      inference(predicate_to_equality,[status(thm)],[c_1793]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_1823,plain,
% 1.75/1.00      ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 1.75/1.00      | sP0_iProver_split != iProver_top ),
% 1.75/1.00      inference(instantiation,[status(thm)],[c_1821]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_2801,plain,
% 1.75/1.00      ( sP0_iProver_split != iProver_top ),
% 1.75/1.00      inference(global_propositional_subsumption,
% 1.75/1.00                [status(thm)],
% 1.75/1.00                [c_2121,c_25,c_1823]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_2119,plain,
% 1.75/1.00      ( sP1_iProver_split = iProver_top | sP0_iProver_split = iProver_top ),
% 1.75/1.00      inference(predicate_to_equality,[status(thm)],[c_1795]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_1817,plain,
% 1.75/1.00      ( sP1_iProver_split = iProver_top | sP0_iProver_split = iProver_top ),
% 1.75/1.00      inference(predicate_to_equality,[status(thm)],[c_1795]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_2807,plain,
% 1.75/1.00      ( sP1_iProver_split = iProver_top ),
% 1.75/1.00      inference(global_propositional_subsumption,
% 1.75/1.00                [status(thm)],
% 1.75/1.00                [c_2119,c_25,c_1817,c_1823]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_3,plain,
% 1.75/1.00      ( r1_lattice3(X0,X1,X2)
% 1.75/1.00      | ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
% 1.75/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.75/1.00      | ~ l1_orders_2(X0) ),
% 1.75/1.00      inference(cnf_transformation,[],[f35]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_655,plain,
% 1.75/1.00      ( r1_lattice3(X0,X1,X2)
% 1.75/1.00      | ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
% 1.75/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.75/1.00      | sK2 != X0 ),
% 1.75/1.00      inference(resolution_lifted,[status(thm)],[c_3,c_17]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_656,plain,
% 1.75/1.00      ( r1_lattice3(sK2,X0,X1)
% 1.75/1.00      | ~ r1_orders_2(sK2,X1,sK0(sK2,X0,X1))
% 1.75/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 1.75/1.00      inference(unflattening,[status(thm)],[c_655]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_1780,plain,
% 1.75/1.00      ( r1_lattice3(sK2,X0_46,X0_47)
% 1.75/1.00      | ~ r1_orders_2(sK2,X0_47,sK0(sK2,X0_46,X0_47))
% 1.75/1.00      | ~ m1_subset_1(X0_47,u1_struct_0(sK2)) ),
% 1.75/1.00      inference(subtyping,[status(esa)],[c_656]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_2131,plain,
% 1.75/1.00      ( r1_lattice3(sK2,X0_46,X0_47) = iProver_top
% 1.75/1.00      | r1_orders_2(sK2,X0_47,sK0(sK2,X0_46,X0_47)) != iProver_top
% 1.75/1.00      | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top ),
% 1.75/1.00      inference(predicate_to_equality,[status(thm)],[c_1780]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_13,plain,
% 1.75/1.00      ( ~ r1_lattice3(X0,X1,X2)
% 1.75/1.00      | r1_orders_2(X0,X2,k2_yellow_0(X0,X1))
% 1.75/1.00      | ~ r2_yellow_0(X0,X1)
% 1.75/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.75/1.00      | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
% 1.75/1.00      | ~ v5_orders_2(X0)
% 1.75/1.00      | ~ l1_orders_2(X0) ),
% 1.75/1.00      inference(cnf_transformation,[],[f50]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_395,plain,
% 1.75/1.00      ( ~ r1_lattice3(X0,X1,X2)
% 1.75/1.00      | r1_orders_2(X0,X2,k2_yellow_0(X0,X1))
% 1.75/1.00      | ~ r2_yellow_0(X0,X1)
% 1.75/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.75/1.00      | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
% 1.75/1.00      | ~ l1_orders_2(X0)
% 1.75/1.00      | sK2 != X0 ),
% 1.75/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_18]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_396,plain,
% 1.75/1.00      ( ~ r1_lattice3(sK2,X0,X1)
% 1.75/1.00      | r1_orders_2(sK2,X1,k2_yellow_0(sK2,X0))
% 1.75/1.00      | ~ r2_yellow_0(sK2,X0)
% 1.75/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.75/1.00      | ~ m1_subset_1(k2_yellow_0(sK2,X0),u1_struct_0(sK2))
% 1.75/1.00      | ~ l1_orders_2(sK2) ),
% 1.75/1.00      inference(unflattening,[status(thm)],[c_395]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_400,plain,
% 1.75/1.00      ( ~ m1_subset_1(k2_yellow_0(sK2,X0),u1_struct_0(sK2))
% 1.75/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.75/1.00      | ~ r2_yellow_0(sK2,X0)
% 1.75/1.00      | r1_orders_2(sK2,X1,k2_yellow_0(sK2,X0))
% 1.75/1.00      | ~ r1_lattice3(sK2,X0,X1) ),
% 1.75/1.00      inference(global_propositional_subsumption,[status(thm)],[c_396,c_17]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_401,plain,
% 1.75/1.00      ( ~ r1_lattice3(sK2,X0,X1)
% 1.75/1.00      | r1_orders_2(sK2,X1,k2_yellow_0(sK2,X0))
% 1.75/1.00      | ~ r2_yellow_0(sK2,X0)
% 1.75/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.75/1.00      | ~ m1_subset_1(k2_yellow_0(sK2,X0),u1_struct_0(sK2)) ),
% 1.75/1.00      inference(renaming,[status(thm)],[c_400]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_1788,plain,
% 1.75/1.00      ( ~ r1_lattice3(sK2,X0_46,X0_47)
% 1.75/1.00      | r1_orders_2(sK2,X0_47,k2_yellow_0(sK2,X0_46))
% 1.75/1.00      | ~ r2_yellow_0(sK2,X0_46)
% 1.75/1.00      | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
% 1.75/1.00      | ~ m1_subset_1(k2_yellow_0(sK2,X0_46),u1_struct_0(sK2)) ),
% 1.75/1.00      inference(subtyping,[status(esa)],[c_401]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_2123,plain,
% 1.75/1.00      ( r1_lattice3(sK2,X0_46,X0_47) != iProver_top
% 1.75/1.00      | r1_orders_2(sK2,X0_47,k2_yellow_0(sK2,X0_46)) = iProver_top
% 1.75/1.00      | r2_yellow_0(sK2,X0_46) != iProver_top
% 1.75/1.00      | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
% 1.75/1.00      | m1_subset_1(k2_yellow_0(sK2,X0_46),u1_struct_0(sK2)) != iProver_top ),
% 1.75/1.00      inference(predicate_to_equality,[status(thm)],[c_1788]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_14,plain,
% 1.75/1.00      ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
% 1.75/1.00      | ~ r2_yellow_0(X0,X1)
% 1.75/1.00      | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
% 1.75/1.00      | ~ v5_orders_2(X0)
% 1.75/1.00      | ~ l1_orders_2(X0) ),
% 1.75/1.00      inference(cnf_transformation,[],[f51]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_374,plain,
% 1.75/1.00      ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
% 1.75/1.00      | ~ r2_yellow_0(X0,X1)
% 1.75/1.00      | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
% 1.75/1.00      | ~ l1_orders_2(X0)
% 1.75/1.00      | sK2 != X0 ),
% 1.75/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_18]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_375,plain,
% 1.75/1.00      ( r1_lattice3(sK2,X0,k2_yellow_0(sK2,X0))
% 1.75/1.00      | ~ r2_yellow_0(sK2,X0)
% 1.75/1.00      | ~ m1_subset_1(k2_yellow_0(sK2,X0),u1_struct_0(sK2))
% 1.75/1.00      | ~ l1_orders_2(sK2) ),
% 1.75/1.00      inference(unflattening,[status(thm)],[c_374]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_379,plain,
% 1.75/1.00      ( ~ m1_subset_1(k2_yellow_0(sK2,X0),u1_struct_0(sK2))
% 1.75/1.00      | ~ r2_yellow_0(sK2,X0)
% 1.75/1.00      | r1_lattice3(sK2,X0,k2_yellow_0(sK2,X0)) ),
% 1.75/1.00      inference(global_propositional_subsumption,[status(thm)],[c_375,c_17]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_380,plain,
% 1.75/1.00      ( r1_lattice3(sK2,X0,k2_yellow_0(sK2,X0))
% 1.75/1.00      | ~ r2_yellow_0(sK2,X0)
% 1.75/1.00      | ~ m1_subset_1(k2_yellow_0(sK2,X0),u1_struct_0(sK2)) ),
% 1.75/1.00      inference(renaming,[status(thm)],[c_379]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_1789,plain,
% 1.75/1.00      ( r1_lattice3(sK2,X0_46,k2_yellow_0(sK2,X0_46))
% 1.75/1.00      | ~ r2_yellow_0(sK2,X0_46)
% 1.75/1.00      | ~ m1_subset_1(k2_yellow_0(sK2,X0_46),u1_struct_0(sK2)) ),
% 1.75/1.00      inference(subtyping,[status(esa)],[c_380]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_2122,plain,
% 1.75/1.00      ( r1_lattice3(sK2,X0_46,k2_yellow_0(sK2,X0_46)) = iProver_top
% 1.75/1.00      | r2_yellow_0(sK2,X0_46) != iProver_top
% 1.75/1.00      | m1_subset_1(k2_yellow_0(sK2,X0_46),u1_struct_0(sK2)) != iProver_top ),
% 1.75/1.00      inference(predicate_to_equality,[status(thm)],[c_1789]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_15,negated_conjecture,
% 1.75/1.00      ( ~ r2_yellow_0(sK2,k6_waybel_0(sK2,sK3))
% 1.75/1.00      | k2_yellow_0(sK2,k6_waybel_0(sK2,sK3)) != sK3 ),
% 1.75/1.00      inference(cnf_transformation,[],[f49]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_1792,negated_conjecture,
% 1.75/1.00      ( ~ r2_yellow_0(sK2,k6_waybel_0(sK2,sK3))
% 1.75/1.00      | k2_yellow_0(sK2,k6_waybel_0(sK2,sK3)) != sK3 ),
% 1.75/1.00      inference(subtyping,[status(esa)],[c_15]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_2117,plain,
% 1.75/1.00      ( k2_yellow_0(sK2,k6_waybel_0(sK2,sK3)) != sK3
% 1.75/1.00      | r2_yellow_0(sK2,k6_waybel_0(sK2,sK3)) != iProver_top ),
% 1.75/1.00      inference(predicate_to_equality,[status(thm)],[c_1792]) ).
% 1.75/1.00  
% 1.75/1.00  
% 1.75/1.00  % SZS output end Saturation for theBenchmark.p
% 1.75/1.00  
% 1.75/1.00  ------                               Statistics
% 1.75/1.00  
% 1.75/1.00  ------ General
% 1.75/1.00  
% 1.75/1.00  abstr_ref_over_cycles:                  0
% 1.75/1.00  abstr_ref_under_cycles:                 0
% 1.75/1.00  gc_basic_clause_elim:                   0
% 1.75/1.00  forced_gc_time:                         0
% 1.75/1.00  parsing_time:                           0.008
% 1.75/1.00  unif_index_cands_time:                  0.
% 1.75/1.00  unif_index_add_time:                    0.
% 1.75/1.00  orderings_time:                         0.
% 1.75/1.00  out_proof_time:                         0.
% 1.75/1.00  total_time:                             0.164
% 1.75/1.00  num_of_symbols:                         51
% 1.75/1.00  num_of_terms:                           2230
% 1.75/1.00  
% 1.75/1.00  ------ Preprocessing
% 1.75/1.00  
% 1.75/1.00  num_of_splits:                          2
% 1.75/1.00  num_of_split_atoms:                     2
% 1.75/1.00  num_of_reused_defs:                     0
% 1.75/1.00  num_eq_ax_congr_red:                    32
% 1.75/1.00  num_of_sem_filtered_clauses:            3
% 1.75/1.00  num_of_subtypes:                        4
% 1.75/1.00  monotx_restored_types:                  0
% 1.75/1.00  sat_num_of_epr_types:                   0
% 1.75/1.00  sat_num_of_non_cyclic_types:            0
% 1.75/1.00  sat_guarded_non_collapsed_types:        1
% 1.75/1.00  num_pure_diseq_elim:                    0
% 1.75/1.00  simp_replaced_by:                       0
% 1.75/1.00  res_preprocessed:                       84
% 1.75/1.00  prep_upred:                             0
% 1.75/1.00  prep_unflattend:                        53
% 1.75/1.00  smt_new_axioms:                         0
% 1.75/1.00  pred_elim_cands:                        4
% 1.75/1.00  pred_elim:                              6
% 1.75/1.00  pred_elim_cl:                           7
% 1.75/1.00  pred_elim_cycles:                       11
% 1.75/1.01  merged_defs:                            0
% 1.75/1.01  merged_defs_ncl:                        0
% 1.75/1.01  bin_hyper_res:                          0
% 1.75/1.01  prep_cycles:                            4
% 1.75/1.01  pred_elim_time:                         0.037
% 1.75/1.01  splitting_time:                         0.
% 1.75/1.01  sem_filter_time:                        0.
% 1.75/1.01  monotx_time:                            0.
% 1.75/1.01  subtype_inf_time:                       0.
% 1.75/1.01  
% 1.75/1.01  ------ Problem properties
% 1.75/1.01  
% 1.75/1.01  clauses:                                16
% 1.75/1.01  conjectures:                            2
% 1.75/1.01  epr:                                    1
% 1.75/1.01  horn:                                   9
% 1.75/1.01  ground:                                 3
% 1.75/1.01  unary:                                  1
% 1.75/1.01  binary:                                 3
% 1.75/1.01  lits:                                   53
% 1.75/1.01  lits_eq:                                4
% 1.75/1.01  fd_pure:                                0
% 1.75/1.01  fd_pseudo:                              0
% 1.75/1.01  fd_cond:                                0
% 1.75/1.01  fd_pseudo_cond:                         3
% 1.75/1.01  ac_symbols:                             0
% 1.75/1.01  
% 1.75/1.01  ------ Propositional Solver
% 1.75/1.01  
% 1.75/1.01  prop_solver_calls:                      29
% 1.75/1.01  prop_fast_solver_calls:                 1077
% 1.75/1.01  smt_solver_calls:                       0
% 1.75/1.01  smt_fast_solver_calls:                  0
% 1.75/1.01  prop_num_of_clauses:                    753
% 1.75/1.01  prop_preprocess_simplified:             3303
% 1.75/1.01  prop_fo_subsumed:                       32
% 1.75/1.01  prop_solver_time:                       0.
% 1.75/1.01  smt_solver_time:                        0.
% 1.75/1.01  smt_fast_solver_time:                   0.
% 1.75/1.01  prop_fast_solver_time:                  0.
% 1.75/1.01  prop_unsat_core_time:                   0.
% 1.75/1.01  
% 1.75/1.01  ------ QBF
% 1.75/1.01  
% 1.75/1.01  qbf_q_res:                              0
% 1.75/1.01  qbf_num_tautologies:                    0
% 1.75/1.01  qbf_prep_cycles:                        0
% 1.75/1.01  
% 1.75/1.01  ------ BMC1
% 1.75/1.01  
% 1.75/1.01  bmc1_current_bound:                     -1
% 1.75/1.01  bmc1_last_solved_bound:                 -1
% 1.75/1.01  bmc1_unsat_core_size:                   -1
% 1.75/1.01  bmc1_unsat_core_parents_size:           -1
% 1.75/1.01  bmc1_merge_next_fun:                    0
% 1.75/1.01  bmc1_unsat_core_clauses_time:           0.
% 1.75/1.01  
% 1.75/1.01  ------ Instantiation
% 1.75/1.01  
% 1.75/1.01  inst_num_of_clauses:                    152
% 1.75/1.01  inst_num_in_passive:                    42
% 1.75/1.01  inst_num_in_active:                     104
% 1.75/1.01  inst_num_in_unprocessed:                6
% 1.75/1.01  inst_num_of_loops:                      140
% 1.75/1.01  inst_num_of_learning_restarts:          0
% 1.75/1.01  inst_num_moves_active_passive:          31
% 1.75/1.01  inst_lit_activity:                      0
% 1.75/1.01  inst_lit_activity_moves:                0
% 1.75/1.01  inst_num_tautologies:                   0
% 1.75/1.01  inst_num_prop_implied:                  0
% 1.75/1.01  inst_num_existing_simplified:           0
% 1.75/1.01  inst_num_eq_res_simplified:             0
% 1.75/1.01  inst_num_child_elim:                    0
% 1.75/1.01  inst_num_of_dismatching_blockings:      129
% 1.75/1.01  inst_num_of_non_proper_insts:           218
% 1.75/1.01  inst_num_of_duplicates:                 0
% 1.75/1.01  inst_inst_num_from_inst_to_res:         0
% 1.75/1.01  inst_dismatching_checking_time:         0.
% 1.75/1.01  
% 1.75/1.01  ------ Resolution
% 1.75/1.01  
% 1.75/1.01  res_num_of_clauses:                     0
% 1.75/1.01  res_num_in_passive:                     0
% 1.75/1.01  res_num_in_active:                      0
% 1.75/1.01  res_num_of_loops:                       88
% 1.75/1.01  res_forward_subset_subsumed:            0
% 1.75/1.01  res_backward_subset_subsumed:           0
% 1.75/1.01  res_forward_subsumed:                   0
% 1.75/1.01  res_backward_subsumed:                  0
% 1.75/1.01  res_forward_subsumption_resolution:     3
% 1.75/1.01  res_backward_subsumption_resolution:    0
% 1.75/1.01  res_clause_to_clause_subsumption:       191
% 1.75/1.01  res_orphan_elimination:                 0
% 1.75/1.01  res_tautology_del:                      12
% 1.75/1.01  res_num_eq_res_simplified:              0
% 1.75/1.01  res_num_sel_changes:                    0
% 1.75/1.01  res_moves_from_active_to_pass:          0
% 1.75/1.01  
% 1.75/1.01  ------ Superposition
% 1.75/1.01  
% 1.75/1.01  sup_time_total:                         0.
% 1.75/1.01  sup_time_generating:                    0.
% 1.75/1.01  sup_time_sim_full:                      0.
% 1.75/1.01  sup_time_sim_immed:                     0.
% 1.75/1.01  
% 1.75/1.01  sup_num_of_clauses:                     24
% 1.75/1.01  sup_num_in_active:                      24
% 1.75/1.01  sup_num_in_passive:                     0
% 1.75/1.01  sup_num_of_loops:                       26
% 1.75/1.01  sup_fw_superposition:                   10
% 1.75/1.01  sup_bw_superposition:                   5
% 1.75/1.01  sup_immediate_simplified:               2
% 1.75/1.01  sup_given_eliminated:                   0
% 1.75/1.01  comparisons_done:                       0
% 1.75/1.01  comparisons_avoided:                    0
% 1.75/1.01  
% 1.75/1.01  ------ Simplifications
% 1.75/1.01  
% 1.75/1.01  
% 1.75/1.01  sim_fw_subset_subsumed:                 0
% 1.75/1.01  sim_bw_subset_subsumed:                 2
% 1.75/1.01  sim_fw_subsumed:                        0
% 1.75/1.01  sim_bw_subsumed:                        2
% 1.75/1.01  sim_fw_subsumption_res:                 0
% 1.75/1.01  sim_bw_subsumption_res:                 0
% 1.75/1.01  sim_tautology_del:                      1
% 1.75/1.01  sim_eq_tautology_del:                   0
% 1.75/1.01  sim_eq_res_simp:                        0
% 1.75/1.01  sim_fw_demodulated:                     0
% 1.75/1.01  sim_bw_demodulated:                     0
% 1.75/1.01  sim_light_normalised:                   0
% 1.75/1.01  sim_joinable_taut:                      0
% 1.75/1.01  sim_joinable_simp:                      0
% 1.75/1.01  sim_ac_normalised:                      0
% 1.75/1.01  sim_smt_subsumption:                    0
% 1.75/1.01  
%------------------------------------------------------------------------------
