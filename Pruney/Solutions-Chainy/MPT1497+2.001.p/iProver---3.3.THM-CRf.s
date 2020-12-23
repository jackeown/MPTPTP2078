%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:19:07 EST 2020

% Result     : Theorem 1.01s
% Output     : CNFRefutation 1.01s
% Verified   : 
% Statistics : Number of formulae       :  299 (4971 expanded)
%              Number of clauses        :  204 (1232 expanded)
%              Number of leaves         :   21 (1044 expanded)
%              Depth                    :   31
%              Number of atoms          : 1463 (31299 expanded)
%              Number of equality atoms :  252 (1103 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   16 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
    ! [X0,X1] :
      ( ( l3_lattices(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( r4_lattice3(X1,X2,X0)
          <=> r2_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( l3_lattices(X1)
          & v10_lattices(X1)
          & ~ v2_struct_0(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ( r4_lattice3(X1,X2,X0)
            <=> r2_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f48,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r4_lattice3(X1,X2,X0)
          <~> r2_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2)) )
          & m1_subset_1(X2,u1_struct_0(X1)) )
      & l3_lattices(X1)
      & v10_lattices(X1)
      & ~ v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f49,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r4_lattice3(X1,X2,X0)
          <~> r2_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2)) )
          & m1_subset_1(X2,u1_struct_0(X1)) )
      & l3_lattices(X1)
      & v10_lattices(X1)
      & ~ v2_struct_0(X1) ) ),
    inference(flattening,[],[f48])).

fof(f61,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r2_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2))
            | ~ r4_lattice3(X1,X2,X0) )
          & ( r2_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2))
            | r4_lattice3(X1,X2,X0) )
          & m1_subset_1(X2,u1_struct_0(X1)) )
      & l3_lattices(X1)
      & v10_lattices(X1)
      & ~ v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f49])).

fof(f62,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r2_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2))
            | ~ r4_lattice3(X1,X2,X0) )
          & ( r2_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2))
            | r4_lattice3(X1,X2,X0) )
          & m1_subset_1(X2,u1_struct_0(X1)) )
      & l3_lattices(X1)
      & v10_lattices(X1)
      & ~ v2_struct_0(X1) ) ),
    inference(flattening,[],[f61])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ r2_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2))
            | ~ r4_lattice3(X1,X2,X0) )
          & ( r2_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2))
            | r4_lattice3(X1,X2,X0) )
          & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ( ~ r2_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,sK4))
          | ~ r4_lattice3(X1,sK4,X0) )
        & ( r2_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,sK4))
          | r4_lattice3(X1,sK4,X0) )
        & m1_subset_1(sK4,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r2_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2))
              | ~ r4_lattice3(X1,X2,X0) )
            & ( r2_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2))
              | r4_lattice3(X1,X2,X0) )
            & m1_subset_1(X2,u1_struct_0(X1)) )
        & l3_lattices(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ( ~ r2_lattice3(k3_lattice3(sK3),sK2,k4_lattice3(sK3,X2))
            | ~ r4_lattice3(sK3,X2,sK2) )
          & ( r2_lattice3(k3_lattice3(sK3),sK2,k4_lattice3(sK3,X2))
            | r4_lattice3(sK3,X2,sK2) )
          & m1_subset_1(X2,u1_struct_0(sK3)) )
      & l3_lattices(sK3)
      & v10_lattices(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,
    ( ( ~ r2_lattice3(k3_lattice3(sK3),sK2,k4_lattice3(sK3,sK4))
      | ~ r4_lattice3(sK3,sK4,sK2) )
    & ( r2_lattice3(k3_lattice3(sK3),sK2,k4_lattice3(sK3,sK4))
      | r4_lattice3(sK3,sK4,sK2) )
    & m1_subset_1(sK4,u1_struct_0(sK3))
    & l3_lattices(sK3)
    & v10_lattices(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f62,f64,f63])).

fof(f95,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f65])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k4_lattice3(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattice3(X0,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattice3(X0,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k4_lattice3(X0,X1) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f93,plain,(
    v10_lattices(sK3) ),
    inference(cnf_transformation,[],[f65])).

fof(f92,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f65])).

fof(f94,plain,(
    l3_lattices(sK3) ),
    inference(cnf_transformation,[],[f65])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k4_lattice3(X0,X1),u1_struct_0(k3_lattice3(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_lattice3(X0,X1),u1_struct_0(k3_lattice3(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_lattice3(X0,X1),u1_struct_0(k3_lattice3(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f86,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_lattice3(X0,X1),u1_struct_0(k3_lattice3(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f36])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f56])).

fof(f58,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK1(X0,X1,X2),X2)
        & r2_hidden(sK1(X0,X1,X2),X1)
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,sK1(X0,X1,X2),X2)
                & r2_hidden(sK1(X0,X1,X2),X1)
                & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f57,f58])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_orders_2(k3_lattice3(X0))
        & v5_orders_2(k3_lattice3(X0))
        & v4_orders_2(k3_lattice3(X0))
        & v3_orders_2(k3_lattice3(X0))
        & v1_orders_2(k3_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_orders_2(k3_lattice3(X0))
        & v4_orders_2(k3_lattice3(X0))
        & v3_orders_2(k3_lattice3(X0))
        & v1_orders_2(k3_lattice3(X0)) ) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f17,plain,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_orders_2(k3_lattice3(X0))
        & v3_orders_2(k3_lattice3(X0))
        & v1_orders_2(k3_lattice3(X0)) ) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f19,plain,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_orders_2(k3_lattice3(X0))
        & v3_orders_2(k3_lattice3(X0)) ) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f38,plain,(
    ! [X0] :
      ( ( l1_orders_2(k3_lattice3(X0))
        & v3_orders_2(k3_lattice3(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f39,plain,(
    ! [X0] :
      ( ( l1_orders_2(k3_lattice3(X0))
        & v3_orders_2(k3_lattice3(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f85,plain,(
    ! [X0] :
      ( l1_orders_2(k3_lattice3(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k3_lattice3(X0)))
         => k5_lattice3(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_lattice3(X0,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(X0))) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_lattice3(X0,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(X0))) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k5_lattice3(X0,X1) = X1
      | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(X0)))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f97,plain,
    ( ~ r2_lattice3(k3_lattice3(sK3),sK2,k4_lattice3(sK3,sK4))
    | ~ r4_lattice3(sK3,sK4,sK2) ),
    inference(cnf_transformation,[],[f65])).

fof(f96,plain,
    ( r2_lattice3(k3_lattice3(sK3),sK2,k4_lattice3(sK3,sK4))
    | r4_lattice3(sK3,sK4,sK2) ),
    inference(cnf_transformation,[],[f65])).

fof(f80,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f59])).

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

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X2)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f84,plain,(
    ! [X0] :
      ( v3_orders_2(k3_lattice3(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v5_orders_2(k3_lattice3(X0))
        & v4_orders_2(k3_lattice3(X0))
        & v3_orders_2(k3_lattice3(X0))
        & v1_orders_2(k3_lattice3(X0))
        & ~ v2_struct_0(k3_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v4_orders_2(k3_lattice3(X0))
        & v3_orders_2(k3_lattice3(X0))
        & v1_orders_2(k3_lattice3(X0))
        & ~ v2_struct_0(k3_lattice3(X0)) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f18,plain,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v3_orders_2(k3_lattice3(X0))
        & v1_orders_2(k3_lattice3(X0))
        & ~ v2_struct_0(k3_lattice3(X0)) ) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f20,plain,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v3_orders_2(k3_lattice3(X0))
        & ~ v2_struct_0(k3_lattice3(X0)) ) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f44,plain,(
    ! [X0] :
      ( ( v3_orders_2(k3_lattice3(X0))
        & ~ v2_struct_0(k3_lattice3(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f45,plain,(
    ! [X0] :
      ( ( v3_orders_2(k3_lattice3(X0))
        & ~ v2_struct_0(k3_lattice3(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f88,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k3_lattice3(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r4_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r2_hidden(X3,X2)
                   => r1_lattices(X0,X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X3,X1)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X3,X1)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r4_lattice3(X0,X1,X2)
                | ? [X3] :
                    ( ~ r1_lattices(X0,X3,X1)
                    & r2_hidden(X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) )
              & ( ! [X3] :
                    ( r1_lattices(X0,X3,X1)
                    | ~ r2_hidden(X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r4_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r4_lattice3(X0,X1,X2)
                | ? [X3] :
                    ( ~ r1_lattices(X0,X3,X1)
                    & r2_hidden(X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) )
              & ( ! [X4] :
                    ( r1_lattices(X0,X4,X1)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r4_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f52])).

fof(f54,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X3,X1)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,sK0(X0,X1,X2),X1)
        & r2_hidden(sK0(X0,X1,X2),X2)
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r4_lattice3(X0,X1,X2)
                | ( ~ r1_lattices(X0,sK0(X0,X1,X2),X1)
                  & r2_hidden(sK0(X0,X1,X2),X2)
                  & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) )
              & ( ! [X4] :
                    ( r1_lattices(X0,X4,X1)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r4_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f53,f54])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X1,X2)
      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X1,X2)
      | r2_hidden(sK0(X0,X1,X2),X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r3_lattices(X0,X1,X2)
              <=> r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattices(X0,X1,X2)
              <=> r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattices(X0,X1,X2)
              <=> r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_lattices(X0,X1,X2)
                  | ~ r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2)) )
                & ( r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2))
                  | ~ r3_lattices(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,X1,X2)
      | ~ r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f2,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v7_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f22,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f21])).

fof(f23,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f22])).

fof(f26,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f27,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f26])).

fof(f71,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_lattices(X0,X1,X2)
          | ~ r1_lattices(X0,X1,X2) )
        & ( r1_lattices(X0,X1,X2)
          | ~ r3_lattices(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,X1,X2)
      | ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f69,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f70,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X1,X2)
      | ~ r1_lattices(X0,sK0(X0,X1,X2),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(k3_lattice3(X0)))
        & l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_lattice3(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(X0)))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_lattice3(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(X0)))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f87,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_lattice3(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(X0)))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2))
      | ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,X1,X2)
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f74,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_lattices(X0,X4,X1)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r4_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | r2_hidden(sK1(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,sK1(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_2586,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_3056,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2586])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1)
    | v2_struct_0(X1)
    | k4_lattice3(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_30,negated_conjecture,
    ( v10_lattices(sK3) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1566,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k4_lattice3(X1,X0) = X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_30])).

cnf(c_1567,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ l3_lattices(sK3)
    | v2_struct_0(sK3)
    | k4_lattice3(sK3,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_1566])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_29,negated_conjecture,
    ( l3_lattices(sK3) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1571,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | k4_lattice3(sK3,X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1567,c_31,c_29])).

cnf(c_2578,plain,
    ( ~ m1_subset_1(X0_54,u1_struct_0(sK3))
    | k4_lattice3(sK3,X0_54) = X0_54 ),
    inference(subtyping,[status(esa)],[c_1571])).

cnf(c_3064,plain,
    ( k4_lattice3(sK3,X0_54) = X0_54
    | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2578])).

cnf(c_3262,plain,
    ( k4_lattice3(sK3,sK4) = sK4 ),
    inference(superposition,[status(thm)],[c_3056,c_3064])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k4_lattice3(X1,X0),u1_struct_0(k3_lattice3(X1)))
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1530,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k4_lattice3(X1,X0),u1_struct_0(k3_lattice3(X1)))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_30])).

cnf(c_1531,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(k4_lattice3(sK3,X0),u1_struct_0(k3_lattice3(sK3)))
    | ~ l3_lattices(sK3)
    | v2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_1530])).

cnf(c_1535,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(k4_lattice3(sK3,X0),u1_struct_0(k3_lattice3(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1531,c_31,c_29])).

cnf(c_2580,plain,
    ( ~ m1_subset_1(X0_54,u1_struct_0(sK3))
    | m1_subset_1(k4_lattice3(sK3,X0_54),u1_struct_0(k3_lattice3(sK3))) ),
    inference(subtyping,[status(esa)],[c_1535])).

cnf(c_3062,plain,
    ( m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k4_lattice3(sK3,X0_54),u1_struct_0(k3_lattice3(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2580])).

cnf(c_3455,plain,
    ( m1_subset_1(sK4,u1_struct_0(k3_lattice3(sK3))) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3262,c_3062])).

cnf(c_35,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_2590,plain,
    ( X0_54 = X0_54 ),
    theory(equality)).

cnf(c_2605,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_2590])).

cnf(c_2624,plain,
    ( m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k4_lattice3(sK3,X0_54),u1_struct_0(k3_lattice3(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2580])).

cnf(c_2626,plain,
    ( m1_subset_1(k4_lattice3(sK3,sK4),u1_struct_0(k3_lattice3(sK3))) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2624])).

cnf(c_2631,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | k4_lattice3(sK3,sK4) = sK4 ),
    inference(instantiation,[status(thm)],[c_2578])).

cnf(c_2593,plain,
    ( ~ m1_subset_1(X0_54,X0_56)
    | m1_subset_1(X1_54,X0_56)
    | X1_54 != X0_54 ),
    theory(equality)).

cnf(c_3249,plain,
    ( m1_subset_1(X0_54,u1_struct_0(k3_lattice3(sK3)))
    | ~ m1_subset_1(k4_lattice3(sK3,X1_54),u1_struct_0(k3_lattice3(sK3)))
    | X0_54 != k4_lattice3(sK3,X1_54) ),
    inference(instantiation,[status(thm)],[c_2593])).

cnf(c_3250,plain,
    ( X0_54 != k4_lattice3(sK3,X1_54)
    | m1_subset_1(X0_54,u1_struct_0(k3_lattice3(sK3))) = iProver_top
    | m1_subset_1(k4_lattice3(sK3,X1_54),u1_struct_0(k3_lattice3(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3249])).

cnf(c_3252,plain,
    ( sK4 != k4_lattice3(sK3,sK4)
    | m1_subset_1(k4_lattice3(sK3,sK4),u1_struct_0(k3_lattice3(sK3))) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(k3_lattice3(sK3))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3250])).

cnf(c_2591,plain,
    ( X0_54 != X1_54
    | X2_54 != X1_54
    | X2_54 = X0_54 ),
    theory(equality)).

cnf(c_3278,plain,
    ( X0_54 != X1_54
    | X0_54 = k4_lattice3(sK3,X2_54)
    | k4_lattice3(sK3,X2_54) != X1_54 ),
    inference(instantiation,[status(thm)],[c_2591])).

cnf(c_3279,plain,
    ( k4_lattice3(sK3,sK4) != sK4
    | sK4 = k4_lattice3(sK3,sK4)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_3278])).

cnf(c_3595,plain,
    ( m1_subset_1(sK4,u1_struct_0(k3_lattice3(sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3455,c_28,c_35,c_2605,c_2626,c_2631,c_3252,c_3279])).

cnf(c_16,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_18,plain,
    ( ~ l3_lattices(X0)
    | ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | l1_orders_2(k3_lattice3(X0)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1501,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | l1_orders_2(k3_lattice3(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_30])).

cnf(c_1502,plain,
    ( ~ l3_lattices(sK3)
    | v2_struct_0(sK3)
    | l1_orders_2(k3_lattice3(sK3)) ),
    inference(unflattening,[status(thm)],[c_1501])).

cnf(c_58,plain,
    ( ~ l3_lattices(sK3)
    | ~ v10_lattices(sK3)
    | v2_struct_0(sK3)
    | l1_orders_2(k3_lattice3(sK3)) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1504,plain,
    ( l1_orders_2(k3_lattice3(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1502,c_31,c_30,c_29,c_58])).

cnf(c_1636,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
    | k3_lattice3(sK3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_1504])).

cnf(c_1637,plain,
    ( r2_lattice3(k3_lattice3(sK3),X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(sK3)))
    | m1_subset_1(sK1(k3_lattice3(sK3),X0,X1),u1_struct_0(k3_lattice3(sK3))) ),
    inference(unflattening,[status(thm)],[c_1636])).

cnf(c_2576,plain,
    ( r2_lattice3(k3_lattice3(sK3),X0_55,X0_54)
    | ~ m1_subset_1(X0_54,u1_struct_0(k3_lattice3(sK3)))
    | m1_subset_1(sK1(k3_lattice3(sK3),X0_55,X0_54),u1_struct_0(k3_lattice3(sK3))) ),
    inference(subtyping,[status(esa)],[c_1637])).

cnf(c_3066,plain,
    ( r2_lattice3(k3_lattice3(sK3),X0_55,X0_54) = iProver_top
    | m1_subset_1(X0_54,u1_struct_0(k3_lattice3(sK3))) != iProver_top
    | m1_subset_1(sK1(k3_lattice3(sK3),X0_55,X0_54),u1_struct_0(k3_lattice3(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2576])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(X1)))
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1)
    | v2_struct_0(X1)
    | k5_lattice3(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1548,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(X1)))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k5_lattice3(X1,X0) = X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_30])).

cnf(c_1549,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(sK3)))
    | ~ l3_lattices(sK3)
    | v2_struct_0(sK3)
    | k5_lattice3(sK3,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_1548])).

cnf(c_1553,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(sK3)))
    | k5_lattice3(sK3,X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1549,c_31,c_29])).

cnf(c_2579,plain,
    ( ~ m1_subset_1(X0_54,u1_struct_0(k3_lattice3(sK3)))
    | k5_lattice3(sK3,X0_54) = X0_54 ),
    inference(subtyping,[status(esa)],[c_1553])).

cnf(c_3063,plain,
    ( k5_lattice3(sK3,X0_54) = X0_54
    | m1_subset_1(X0_54,u1_struct_0(k3_lattice3(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2579])).

cnf(c_3432,plain,
    ( k5_lattice3(sK3,sK1(k3_lattice3(sK3),X0_55,X0_54)) = sK1(k3_lattice3(sK3),X0_55,X0_54)
    | r2_lattice3(k3_lattice3(sK3),X0_55,X0_54) = iProver_top
    | m1_subset_1(X0_54,u1_struct_0(k3_lattice3(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3066,c_3063])).

cnf(c_3776,plain,
    ( k5_lattice3(sK3,sK1(k3_lattice3(sK3),X0_55,sK4)) = sK1(k3_lattice3(sK3),X0_55,sK4)
    | r2_lattice3(k3_lattice3(sK3),X0_55,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3595,c_3432])).

cnf(c_26,negated_conjecture,
    ( ~ r2_lattice3(k3_lattice3(sK3),sK2,k4_lattice3(sK3,sK4))
    | ~ r4_lattice3(sK3,sK4,sK2) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_2588,negated_conjecture,
    ( ~ r2_lattice3(k3_lattice3(sK3),sK2,k4_lattice3(sK3,sK4))
    | ~ r4_lattice3(sK3,sK4,sK2) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_3054,plain,
    ( r2_lattice3(k3_lattice3(sK3),sK2,k4_lattice3(sK3,sK4)) != iProver_top
    | r4_lattice3(sK3,sK4,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2588])).

cnf(c_3291,plain,
    ( r2_lattice3(k3_lattice3(sK3),sK2,sK4) != iProver_top
    | r4_lattice3(sK3,sK4,sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3262,c_3054])).

cnf(c_7946,plain,
    ( k5_lattice3(sK3,sK1(k3_lattice3(sK3),sK2,sK4)) = sK1(k3_lattice3(sK3),sK2,sK4)
    | r4_lattice3(sK3,sK4,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3776,c_3291])).

cnf(c_3434,plain,
    ( k5_lattice3(sK3,sK1(k3_lattice3(sK3),sK2,sK4)) = sK1(k3_lattice3(sK3),sK2,sK4)
    | r2_lattice3(k3_lattice3(sK3),sK2,sK4) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(k3_lattice3(sK3))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3432])).

cnf(c_27,negated_conjecture,
    ( r2_lattice3(k3_lattice3(sK3),sK2,k4_lattice3(sK3,sK4))
    | r4_lattice3(sK3,sK4,sK2) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_2587,negated_conjecture,
    ( r2_lattice3(k3_lattice3(sK3),sK2,k4_lattice3(sK3,sK4))
    | r4_lattice3(sK3,sK4,sK2) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_3055,plain,
    ( r2_lattice3(k3_lattice3(sK3),sK2,k4_lattice3(sK3,sK4)) = iProver_top
    | r4_lattice3(sK3,sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2587])).

cnf(c_3290,plain,
    ( r2_lattice3(k3_lattice3(sK3),sK2,sK4) = iProver_top
    | r4_lattice3(sK3,sK4,sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3262,c_3055])).

cnf(c_17,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X3,X2)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_0,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_19,plain,
    ( ~ l3_lattices(X0)
    | ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | v3_orders_2(k3_lattice3(X0)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_444,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X3)
    | ~ v10_lattices(X3)
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | ~ l1_orders_2(X0)
    | k3_lattice3(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_19])).

cnf(c_445,plain,
    ( ~ r1_orders_2(k3_lattice3(X0),X1,X2)
    | r3_orders_2(k3_lattice3(X0),X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(X0)))
    | ~ l3_lattices(X0)
    | ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | v2_struct_0(k3_lattice3(X0))
    | ~ l1_orders_2(k3_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_444])).

cnf(c_23,plain,
    ( ~ l3_lattices(X0)
    | ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | ~ v2_struct_0(k3_lattice3(X0)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_449,plain,
    ( ~ r1_orders_2(k3_lattice3(X0),X1,X2)
    | r3_orders_2(k3_lattice3(X0),X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(X0)))
    | ~ l3_lattices(X0)
    | ~ v10_lattices(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_445,c_23,c_18])).

cnf(c_918,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r3_orders_2(k3_lattice3(X3),X4,X5)
    | ~ r2_hidden(X6,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X6,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(k3_lattice3(X3)))
    | ~ m1_subset_1(X5,u1_struct_0(k3_lattice3(X3)))
    | ~ l3_lattices(X3)
    | ~ v10_lattices(X3)
    | v2_struct_0(X3)
    | ~ l1_orders_2(X0)
    | X5 != X2
    | X4 != X6
    | k3_lattice3(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_449])).

cnf(c_919,plain,
    ( ~ r2_lattice3(k3_lattice3(X0),X1,X2)
    | r3_orders_2(k3_lattice3(X0),X3,X2)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(k3_lattice3(X0)))
    | ~ l3_lattices(X0)
    | ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(k3_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_918])).

cnf(c_923,plain,
    ( v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | ~ l3_lattices(X0)
    | ~ m1_subset_1(X3,u1_struct_0(k3_lattice3(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(X0)))
    | ~ r2_hidden(X3,X1)
    | r3_orders_2(k3_lattice3(X0),X3,X2)
    | ~ r2_lattice3(k3_lattice3(X0),X1,X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_919,c_18])).

cnf(c_924,plain,
    ( ~ r2_lattice3(k3_lattice3(X0),X1,X2)
    | r3_orders_2(k3_lattice3(X0),X3,X2)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(k3_lattice3(X0)))
    | ~ l3_lattices(X0)
    | ~ v10_lattices(X0)
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_923])).

cnf(c_1442,plain,
    ( ~ r2_lattice3(k3_lattice3(X0),X1,X2)
    | r3_orders_2(k3_lattice3(X0),X3,X2)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(k3_lattice3(X0)))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_924,c_30])).

cnf(c_1443,plain,
    ( ~ r2_lattice3(k3_lattice3(sK3),X0,X1)
    | r3_orders_2(k3_lattice3(sK3),X2,X1)
    | ~ r2_hidden(X2,X0)
    | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(sK3)))
    | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(sK3)))
    | ~ l3_lattices(sK3)
    | v2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_1442])).

cnf(c_1447,plain,
    ( ~ r2_lattice3(k3_lattice3(sK3),X0,X1)
    | r3_orders_2(k3_lattice3(sK3),X2,X1)
    | ~ r2_hidden(X2,X0)
    | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(sK3)))
    | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1443,c_31,c_29])).

cnf(c_2583,plain,
    ( ~ r2_lattice3(k3_lattice3(sK3),X0_55,X0_54)
    | r3_orders_2(k3_lattice3(sK3),X1_54,X0_54)
    | ~ r2_hidden(X1_54,X0_55)
    | ~ m1_subset_1(X1_54,u1_struct_0(k3_lattice3(sK3)))
    | ~ m1_subset_1(X0_54,u1_struct_0(k3_lattice3(sK3))) ),
    inference(subtyping,[status(esa)],[c_1447])).

cnf(c_3059,plain,
    ( r2_lattice3(k3_lattice3(sK3),X0_55,X0_54) != iProver_top
    | r3_orders_2(k3_lattice3(sK3),X1_54,X0_54) = iProver_top
    | r2_hidden(X1_54,X0_55) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(k3_lattice3(sK3))) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(k3_lattice3(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2583])).

cnf(c_3516,plain,
    ( r2_lattice3(k3_lattice3(sK3),X0_55,X0_54) != iProver_top
    | r3_orders_2(k3_lattice3(sK3),k4_lattice3(sK3,X1_54),X0_54) = iProver_top
    | r2_hidden(k4_lattice3(sK3,X1_54),X0_55) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(k3_lattice3(sK3))) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3062,c_3059])).

cnf(c_4951,plain,
    ( r4_lattice3(sK3,sK4,sK2) = iProver_top
    | r3_orders_2(k3_lattice3(sK3),k4_lattice3(sK3,X0_54),sK4) = iProver_top
    | r2_hidden(k4_lattice3(sK3,X0_54),sK2) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(k3_lattice3(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3290,c_3516])).

cnf(c_10,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1699,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | v2_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_29])).

cnf(c_1700,plain,
    ( r4_lattice3(sK3,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(sK0(sK3,X0,X1),u1_struct_0(sK3))
    | v2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_1699])).

cnf(c_1704,plain,
    ( m1_subset_1(sK0(sK3,X0,X1),u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r4_lattice3(sK3,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1700,c_31])).

cnf(c_1705,plain,
    ( r4_lattice3(sK3,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(sK0(sK3,X0,X1),u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_1704])).

cnf(c_2573,plain,
    ( r4_lattice3(sK3,X0_54,X0_55)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
    | m1_subset_1(sK0(sK3,X0_54,X0_55),u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_1705])).

cnf(c_2641,plain,
    ( r4_lattice3(sK3,X0_54,X0_55) = iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK0(sK3,X0_54,X0_55),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2573])).

cnf(c_2643,plain,
    ( r4_lattice3(sK3,sK4,sK2) = iProver_top
    | m1_subset_1(sK0(sK3,sK4,sK2),u1_struct_0(sK3)) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2641])).

cnf(c_9,plain,
    ( r4_lattice3(X0,X1,X2)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1720,plain,
    ( r4_lattice3(X0,X1,X2)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_29])).

cnf(c_1721,plain,
    ( r4_lattice3(sK3,X0,X1)
    | r2_hidden(sK0(sK3,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | v2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_1720])).

cnf(c_1725,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r2_hidden(sK0(sK3,X0,X1),X1)
    | r4_lattice3(sK3,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1721,c_31])).

cnf(c_1726,plain,
    ( r4_lattice3(sK3,X0,X1)
    | r2_hidden(sK0(sK3,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_1725])).

cnf(c_2572,plain,
    ( r4_lattice3(sK3,X0_54,X0_55)
    | r2_hidden(sK0(sK3,X0_54,X0_55),X0_55)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_1726])).

cnf(c_2644,plain,
    ( r4_lattice3(sK3,X0_54,X0_55) = iProver_top
    | r2_hidden(sK0(sK3,X0_54,X0_55),X0_55) = iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2572])).

cnf(c_2646,plain,
    ( r4_lattice3(sK3,sK4,sK2) = iProver_top
    | r2_hidden(sK0(sK3,sK4,sK2),sK2) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2644])).

cnf(c_2595,plain,
    ( ~ r2_hidden(X0_54,X0_55)
    | r2_hidden(X1_54,X0_55)
    | X1_54 != X0_54 ),
    theory(equality)).

cnf(c_3317,plain,
    ( r2_hidden(X0_54,X0_55)
    | ~ r2_hidden(sK0(sK3,X1_54,X0_55),X0_55)
    | X0_54 != sK0(sK3,X1_54,X0_55) ),
    inference(instantiation,[status(thm)],[c_2595])).

cnf(c_3350,plain,
    ( ~ r2_hidden(sK0(sK3,X0_54,X0_55),X0_55)
    | r2_hidden(k4_lattice3(sK3,sK0(sK3,X0_54,X0_55)),X0_55)
    | k4_lattice3(sK3,sK0(sK3,X0_54,X0_55)) != sK0(sK3,X0_54,X0_55) ),
    inference(instantiation,[status(thm)],[c_3317])).

cnf(c_3352,plain,
    ( k4_lattice3(sK3,sK0(sK3,X0_54,X0_55)) != sK0(sK3,X0_54,X0_55)
    | r2_hidden(sK0(sK3,X0_54,X0_55),X0_55) != iProver_top
    | r2_hidden(k4_lattice3(sK3,sK0(sK3,X0_54,X0_55)),X0_55) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3350])).

cnf(c_3354,plain,
    ( k4_lattice3(sK3,sK0(sK3,sK4,sK2)) != sK0(sK3,sK4,sK2)
    | r2_hidden(sK0(sK3,sK4,sK2),sK2) != iProver_top
    | r2_hidden(k4_lattice3(sK3,sK0(sK3,sK4,sK2)),sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3352])).

cnf(c_24,plain,
    ( r3_lattices(X0,X1,X2)
    | ~ r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | ~ v10_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_2,plain,
    ( ~ l3_lattices(X0)
    | ~ v10_lattices(X0)
    | v9_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_7,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | ~ v9_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_493,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | ~ v10_lattices(X0)
    | v2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_2,c_7])).

cnf(c_4,plain,
    ( v6_lattices(X0)
    | ~ l3_lattices(X0)
    | ~ v10_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_3,plain,
    ( v8_lattices(X0)
    | ~ l3_lattices(X0)
    | ~ v10_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_497,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | ~ v10_lattices(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_493,c_7,c_4,c_3,c_2])).

cnf(c_8,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,sK0(X0,X1,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1065,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ r3_lattices(X3,X4,X5)
    | ~ m1_subset_1(X5,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X3)
    | ~ l3_lattices(X0)
    | ~ v10_lattices(X3)
    | v2_struct_0(X3)
    | v2_struct_0(X0)
    | X0 != X3
    | X1 != X5
    | sK0(X0,X1,X2) != X4 ),
    inference(resolution_lifted,[status(thm)],[c_497,c_8])).

cnf(c_1066,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ r3_lattices(X0,sK0(X0,X1,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | ~ v10_lattices(X0)
    | v2_struct_0(X0) ),
    inference(unflattening,[status(thm)],[c_1065])).

cnf(c_1070,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r3_lattices(X0,sK0(X0,X1,X2),X1)
    | r4_lattice3(X0,X1,X2)
    | ~ l3_lattices(X0)
    | ~ v10_lattices(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1066,c_10])).

cnf(c_1071,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ r3_lattices(X0,sK0(X0,X1,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | ~ v10_lattices(X0)
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_1070])).

cnf(c_1311,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ r3_orders_2(k3_lattice3(X3),k4_lattice3(X3,X4),k4_lattice3(X3,X5))
    | ~ m1_subset_1(X5,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X3)
    | ~ l3_lattices(X0)
    | ~ v10_lattices(X3)
    | ~ v10_lattices(X0)
    | v2_struct_0(X3)
    | v2_struct_0(X0)
    | X0 != X3
    | X1 != X5
    | sK0(X0,X1,X2) != X4 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_1071])).

cnf(c_1312,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,sK0(X0,X1,X2)),k4_lattice3(X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | ~ v10_lattices(X0)
    | v2_struct_0(X0) ),
    inference(unflattening,[status(thm)],[c_1311])).

cnf(c_1316,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,sK0(X0,X1,X2)),k4_lattice3(X0,X1))
    | r4_lattice3(X0,X1,X2)
    | ~ l3_lattices(X0)
    | ~ v10_lattices(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1312,c_10])).

cnf(c_1317,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,sK0(X0,X1,X2)),k4_lattice3(X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | ~ v10_lattices(X0)
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_1316])).

cnf(c_1421,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,sK0(X0,X1,X2)),k4_lattice3(X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1317,c_30])).

cnf(c_1422,plain,
    ( r4_lattice3(sK3,X0,X1)
    | ~ r3_orders_2(k3_lattice3(sK3),k4_lattice3(sK3,sK0(sK3,X0,X1)),k4_lattice3(sK3,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ l3_lattices(sK3)
    | v2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_1421])).

cnf(c_1426,plain,
    ( r4_lattice3(sK3,X0,X1)
    | ~ r3_orders_2(k3_lattice3(sK3),k4_lattice3(sK3,sK0(sK3,X0,X1)),k4_lattice3(sK3,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1422,c_31,c_29])).

cnf(c_2584,plain,
    ( r4_lattice3(sK3,X0_54,X0_55)
    | ~ r3_orders_2(k3_lattice3(sK3),k4_lattice3(sK3,sK0(sK3,X0_54,X0_55)),k4_lattice3(sK3,X0_54))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_1426])).

cnf(c_3058,plain,
    ( r4_lattice3(sK3,X0_54,X0_55) = iProver_top
    | r3_orders_2(k3_lattice3(sK3),k4_lattice3(sK3,sK0(sK3,X0_54,X0_55)),k4_lattice3(sK3,X0_54)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2584])).

cnf(c_3490,plain,
    ( r4_lattice3(sK3,sK4,X0_55) = iProver_top
    | r3_orders_2(k3_lattice3(sK3),k4_lattice3(sK3,sK0(sK3,sK4,X0_55)),sK4) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3262,c_3058])).

cnf(c_3492,plain,
    ( r4_lattice3(sK3,sK4,sK2) = iProver_top
    | r3_orders_2(k3_lattice3(sK3),k4_lattice3(sK3,sK0(sK3,sK4,sK2)),sK4) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3490])).

cnf(c_3228,plain,
    ( ~ r2_lattice3(k3_lattice3(sK3),X0_55,X0_54)
    | r3_orders_2(k3_lattice3(sK3),k4_lattice3(sK3,X1_54),X0_54)
    | ~ r2_hidden(k4_lattice3(sK3,X1_54),X0_55)
    | ~ m1_subset_1(X0_54,u1_struct_0(k3_lattice3(sK3)))
    | ~ m1_subset_1(k4_lattice3(sK3,X1_54),u1_struct_0(k3_lattice3(sK3))) ),
    inference(instantiation,[status(thm)],[c_2583])).

cnf(c_3563,plain,
    ( ~ r2_lattice3(k3_lattice3(sK3),X0_55,X0_54)
    | r3_orders_2(k3_lattice3(sK3),k4_lattice3(sK3,sK0(sK3,X1_54,X0_55)),X0_54)
    | ~ r2_hidden(k4_lattice3(sK3,sK0(sK3,X1_54,X0_55)),X0_55)
    | ~ m1_subset_1(X0_54,u1_struct_0(k3_lattice3(sK3)))
    | ~ m1_subset_1(k4_lattice3(sK3,sK0(sK3,X1_54,X0_55)),u1_struct_0(k3_lattice3(sK3))) ),
    inference(instantiation,[status(thm)],[c_3228])).

cnf(c_3569,plain,
    ( r2_lattice3(k3_lattice3(sK3),X0_55,X0_54) != iProver_top
    | r3_orders_2(k3_lattice3(sK3),k4_lattice3(sK3,sK0(sK3,X1_54,X0_55)),X0_54) = iProver_top
    | r2_hidden(k4_lattice3(sK3,sK0(sK3,X1_54,X0_55)),X0_55) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(k3_lattice3(sK3))) != iProver_top
    | m1_subset_1(k4_lattice3(sK3,sK0(sK3,X1_54,X0_55)),u1_struct_0(k3_lattice3(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3563])).

cnf(c_3571,plain,
    ( r2_lattice3(k3_lattice3(sK3),sK2,sK4) != iProver_top
    | r3_orders_2(k3_lattice3(sK3),k4_lattice3(sK3,sK0(sK3,sK4,sK2)),sK4) = iProver_top
    | r2_hidden(k4_lattice3(sK3,sK0(sK3,sK4,sK2)),sK2) != iProver_top
    | m1_subset_1(k4_lattice3(sK3,sK0(sK3,sK4,sK2)),u1_struct_0(k3_lattice3(sK3))) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(k3_lattice3(sK3))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3569])).

cnf(c_3069,plain,
    ( r4_lattice3(sK3,X0_54,X0_55) = iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK0(sK3,X0_54,X0_55),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2573])).

cnf(c_3590,plain,
    ( k4_lattice3(sK3,sK0(sK3,X0_54,X0_55)) = sK0(sK3,X0_54,X0_55)
    | r4_lattice3(sK3,X0_54,X0_55) = iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3069,c_3064])).

cnf(c_3592,plain,
    ( k4_lattice3(sK3,sK0(sK3,sK4,sK2)) = sK0(sK3,sK4,sK2)
    | r4_lattice3(sK3,sK4,sK2) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3590])).

cnf(c_3749,plain,
    ( ~ m1_subset_1(sK0(sK3,X0_54,X0_55),u1_struct_0(sK3))
    | m1_subset_1(k4_lattice3(sK3,sK0(sK3,X0_54,X0_55)),u1_struct_0(k3_lattice3(sK3))) ),
    inference(instantiation,[status(thm)],[c_2580])).

cnf(c_3750,plain,
    ( m1_subset_1(sK0(sK3,X0_54,X0_55),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k4_lattice3(sK3,sK0(sK3,X0_54,X0_55)),u1_struct_0(k3_lattice3(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3749])).

cnf(c_3752,plain,
    ( m1_subset_1(sK0(sK3,sK4,sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k4_lattice3(sK3,sK0(sK3,sK4,sK2)),u1_struct_0(k3_lattice3(sK3))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3750])).

cnf(c_4984,plain,
    ( r4_lattice3(sK3,sK4,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4951,c_28,c_35,c_2605,c_2626,c_2631,c_2643,c_2646,c_3252,c_3279,c_3290,c_3354,c_3492,c_3571,c_3592,c_3752])).

cnf(c_8099,plain,
    ( k5_lattice3(sK3,sK1(k3_lattice3(sK3),sK2,sK4)) = sK1(k3_lattice3(sK3),sK2,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7946,c_28,c_35,c_2605,c_2626,c_2631,c_2643,c_2646,c_3252,c_3279,c_3290,c_3291,c_3354,c_3434,c_3492,c_3571,c_3592,c_3752])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(X1)))
    | m1_subset_1(k5_lattice3(X1,X0),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1512,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(X1)))
    | m1_subset_1(k5_lattice3(X1,X0),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_30])).

cnf(c_1513,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(sK3)))
    | m1_subset_1(k5_lattice3(sK3,X0),u1_struct_0(sK3))
    | ~ l3_lattices(sK3)
    | v2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_1512])).

cnf(c_1517,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(sK3)))
    | m1_subset_1(k5_lattice3(sK3,X0),u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1513,c_31,c_29])).

cnf(c_2581,plain,
    ( ~ m1_subset_1(X0_54,u1_struct_0(k3_lattice3(sK3)))
    | m1_subset_1(k5_lattice3(sK3,X0_54),u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_1517])).

cnf(c_3061,plain,
    ( m1_subset_1(X0_54,u1_struct_0(k3_lattice3(sK3))) != iProver_top
    | m1_subset_1(k5_lattice3(sK3,X0_54),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2581])).

cnf(c_8102,plain,
    ( m1_subset_1(sK1(k3_lattice3(sK3),sK2,sK4),u1_struct_0(k3_lattice3(sK3))) != iProver_top
    | m1_subset_1(sK1(k3_lattice3(sK3),sK2,sK4),u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8099,c_3061])).

cnf(c_2634,plain,
    ( r2_lattice3(k3_lattice3(sK3),X0_55,X0_54) = iProver_top
    | m1_subset_1(X0_54,u1_struct_0(k3_lattice3(sK3))) != iProver_top
    | m1_subset_1(sK1(k3_lattice3(sK3),X0_55,X0_54),u1_struct_0(k3_lattice3(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2576])).

cnf(c_2636,plain,
    ( r2_lattice3(k3_lattice3(sK3),sK2,sK4) = iProver_top
    | m1_subset_1(sK1(k3_lattice3(sK3),sK2,sK4),u1_struct_0(k3_lattice3(sK3))) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(k3_lattice3(sK3))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2634])).

cnf(c_4417,plain,
    ( ~ m1_subset_1(sK1(k3_lattice3(sK3),X0_55,X0_54),u1_struct_0(k3_lattice3(sK3)))
    | m1_subset_1(k5_lattice3(sK3,sK1(k3_lattice3(sK3),X0_55,X0_54)),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_2581])).

cnf(c_4418,plain,
    ( m1_subset_1(sK1(k3_lattice3(sK3),X0_55,X0_54),u1_struct_0(k3_lattice3(sK3))) != iProver_top
    | m1_subset_1(k5_lattice3(sK3,sK1(k3_lattice3(sK3),X0_55,X0_54)),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4417])).

cnf(c_4420,plain,
    ( m1_subset_1(sK1(k3_lattice3(sK3),sK2,sK4),u1_struct_0(k3_lattice3(sK3))) != iProver_top
    | m1_subset_1(k5_lattice3(sK3,sK1(k3_lattice3(sK3),sK2,sK4)),u1_struct_0(sK3)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4418])).

cnf(c_4434,plain,
    ( sK1(k3_lattice3(sK3),X0_55,X0_54) = sK1(k3_lattice3(sK3),X0_55,X0_54) ),
    inference(instantiation,[status(thm)],[c_2590])).

cnf(c_4436,plain,
    ( sK1(k3_lattice3(sK3),sK2,sK4) = sK1(k3_lattice3(sK3),sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_4434])).

cnf(c_4557,plain,
    ( X0_54 != X1_54
    | X0_54 = k5_lattice3(sK3,sK1(k3_lattice3(sK3),X0_55,X2_54))
    | k5_lattice3(sK3,sK1(k3_lattice3(sK3),X0_55,X2_54)) != X1_54 ),
    inference(instantiation,[status(thm)],[c_2591])).

cnf(c_5141,plain,
    ( X0_54 != sK1(k3_lattice3(sK3),X0_55,X1_54)
    | X0_54 = k5_lattice3(sK3,sK1(k3_lattice3(sK3),X0_55,X1_54))
    | k5_lattice3(sK3,sK1(k3_lattice3(sK3),X0_55,X1_54)) != sK1(k3_lattice3(sK3),X0_55,X1_54) ),
    inference(instantiation,[status(thm)],[c_4557])).

cnf(c_5503,plain,
    ( sK1(k3_lattice3(sK3),X0_55,X0_54) != sK1(k3_lattice3(sK3),X0_55,X0_54)
    | sK1(k3_lattice3(sK3),X0_55,X0_54) = k5_lattice3(sK3,sK1(k3_lattice3(sK3),X0_55,X0_54))
    | k5_lattice3(sK3,sK1(k3_lattice3(sK3),X0_55,X0_54)) != sK1(k3_lattice3(sK3),X0_55,X0_54) ),
    inference(instantiation,[status(thm)],[c_5141])).

cnf(c_5504,plain,
    ( sK1(k3_lattice3(sK3),sK2,sK4) != sK1(k3_lattice3(sK3),sK2,sK4)
    | sK1(k3_lattice3(sK3),sK2,sK4) = k5_lattice3(sK3,sK1(k3_lattice3(sK3),sK2,sK4))
    | k5_lattice3(sK3,sK1(k3_lattice3(sK3),sK2,sK4)) != sK1(k3_lattice3(sK3),sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_5503])).

cnf(c_3263,plain,
    ( ~ m1_subset_1(X0_54,u1_struct_0(sK3))
    | m1_subset_1(X1_54,u1_struct_0(sK3))
    | X1_54 != X0_54 ),
    inference(instantiation,[status(thm)],[c_2593])).

cnf(c_3959,plain,
    ( ~ m1_subset_1(X0_54,u1_struct_0(sK3))
    | m1_subset_1(sK1(k3_lattice3(sK3),X0_55,X1_54),u1_struct_0(sK3))
    | sK1(k3_lattice3(sK3),X0_55,X1_54) != X0_54 ),
    inference(instantiation,[status(thm)],[c_3263])).

cnf(c_6560,plain,
    ( m1_subset_1(sK1(k3_lattice3(sK3),X0_55,X0_54),u1_struct_0(sK3))
    | ~ m1_subset_1(k5_lattice3(sK3,sK1(k3_lattice3(sK3),X0_55,X0_54)),u1_struct_0(sK3))
    | sK1(k3_lattice3(sK3),X0_55,X0_54) != k5_lattice3(sK3,sK1(k3_lattice3(sK3),X0_55,X0_54)) ),
    inference(instantiation,[status(thm)],[c_3959])).

cnf(c_6561,plain,
    ( sK1(k3_lattice3(sK3),X0_55,X0_54) != k5_lattice3(sK3,sK1(k3_lattice3(sK3),X0_55,X0_54))
    | m1_subset_1(sK1(k3_lattice3(sK3),X0_55,X0_54),u1_struct_0(sK3)) = iProver_top
    | m1_subset_1(k5_lattice3(sK3,sK1(k3_lattice3(sK3),X0_55,X0_54)),u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6560])).

cnf(c_6563,plain,
    ( sK1(k3_lattice3(sK3),sK2,sK4) != k5_lattice3(sK3,sK1(k3_lattice3(sK3),sK2,sK4))
    | m1_subset_1(sK1(k3_lattice3(sK3),sK2,sK4),u1_struct_0(sK3)) = iProver_top
    | m1_subset_1(k5_lattice3(sK3,sK1(k3_lattice3(sK3),sK2,sK4)),u1_struct_0(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6561])).

cnf(c_8500,plain,
    ( m1_subset_1(sK1(k3_lattice3(sK3),sK2,sK4),u1_struct_0(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8102,c_28,c_35,c_2605,c_2626,c_2631,c_2636,c_2643,c_2646,c_3252,c_3279,c_3290,c_3291,c_3354,c_3434,c_3492,c_3571,c_3592,c_3752,c_4420,c_4436,c_5504,c_6563])).

cnf(c_8524,plain,
    ( k4_lattice3(sK3,sK1(k3_lattice3(sK3),sK2,sK4)) = sK1(k3_lattice3(sK3),sK2,sK4) ),
    inference(superposition,[status(thm)],[c_8500,c_3064])).

cnf(c_25,plain,
    ( ~ r3_lattices(X0,X1,X2)
    | r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | ~ v10_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_6,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | ~ v9_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_525,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | ~ v10_lattices(X0)
    | v2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_2,c_6])).

cnf(c_529,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | ~ v10_lattices(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_525,c_6,c_4,c_3,c_2])).

cnf(c_11,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r1_lattices(X0,X3,X1)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1095,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r3_lattices(X3,X4,X5)
    | ~ r2_hidden(X6,X2)
    | ~ m1_subset_1(X5,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X6,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X3)
    | ~ l3_lattices(X0)
    | ~ v10_lattices(X3)
    | v2_struct_0(X3)
    | v2_struct_0(X0)
    | X0 != X3
    | X6 != X4
    | X1 != X5 ),
    inference(resolution_lifted,[status(thm)],[c_529,c_11])).

cnf(c_1096,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r3_lattices(X0,X3,X1)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | ~ v10_lattices(X0)
    | v2_struct_0(X0) ),
    inference(unflattening,[status(thm)],[c_1095])).

cnf(c_1341,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r3_orders_2(k3_lattice3(X3),k4_lattice3(X3,X4),k4_lattice3(X3,X5))
    | ~ r2_hidden(X6,X2)
    | ~ m1_subset_1(X5,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X6,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X3)
    | ~ l3_lattices(X0)
    | ~ v10_lattices(X3)
    | ~ v10_lattices(X0)
    | v2_struct_0(X3)
    | v2_struct_0(X0)
    | X0 != X3
    | X6 != X4
    | X1 != X5 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_1096])).

cnf(c_1342,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X3),k4_lattice3(X0,X1))
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | ~ v10_lattices(X0)
    | v2_struct_0(X0) ),
    inference(unflattening,[status(thm)],[c_1341])).

cnf(c_1394,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X3),k4_lattice3(X0,X1))
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1342,c_30])).

cnf(c_1395,plain,
    ( ~ r4_lattice3(sK3,X0,X1)
    | r3_orders_2(k3_lattice3(sK3),k4_lattice3(sK3,X2),k4_lattice3(sK3,X0))
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ l3_lattices(sK3)
    | v2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_1394])).

cnf(c_1399,plain,
    ( ~ r4_lattice3(sK3,X0,X1)
    | r3_orders_2(k3_lattice3(sK3),k4_lattice3(sK3,X2),k4_lattice3(sK3,X0))
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1395,c_31,c_29])).

cnf(c_2585,plain,
    ( ~ r4_lattice3(sK3,X0_54,X0_55)
    | r3_orders_2(k3_lattice3(sK3),k4_lattice3(sK3,X1_54),k4_lattice3(sK3,X0_54))
    | ~ r2_hidden(X1_54,X0_55)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
    | ~ m1_subset_1(X1_54,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_1399])).

cnf(c_3057,plain,
    ( r4_lattice3(sK3,X0_54,X0_55) != iProver_top
    | r3_orders_2(k3_lattice3(sK3),k4_lattice3(sK3,X1_54),k4_lattice3(sK3,X0_54)) = iProver_top
    | r2_hidden(X1_54,X0_55) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2585])).

cnf(c_4989,plain,
    ( r3_orders_2(k3_lattice3(sK3),k4_lattice3(sK3,X0_54),k4_lattice3(sK3,sK4)) = iProver_top
    | r2_hidden(X0_54,sK2) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4984,c_3057])).

cnf(c_4990,plain,
    ( r3_orders_2(k3_lattice3(sK3),k4_lattice3(sK3,X0_54),sK4) = iProver_top
    | r2_hidden(X0_54,sK2) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4989,c_3262])).

cnf(c_5089,plain,
    ( m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0_54,sK2) != iProver_top
    | r3_orders_2(k3_lattice3(sK3),k4_lattice3(sK3,X0_54),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4990,c_35])).

cnf(c_5090,plain,
    ( r3_orders_2(k3_lattice3(sK3),k4_lattice3(sK3,X0_54),sK4) = iProver_top
    | r2_hidden(X0_54,sK2) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5089])).

cnf(c_8589,plain,
    ( r3_orders_2(k3_lattice3(sK3),sK1(k3_lattice3(sK3),sK2,sK4),sK4) = iProver_top
    | r2_hidden(sK1(k3_lattice3(sK3),sK2,sK4),sK2) != iProver_top
    | m1_subset_1(sK1(k3_lattice3(sK3),sK2,sK4),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8524,c_5090])).

cnf(c_15,plain,
    ( r2_lattice3(X0,X1,X2)
    | r2_hidden(sK1(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1651,plain,
    ( r2_lattice3(X0,X1,X2)
    | r2_hidden(sK1(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | k3_lattice3(sK3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_1504])).

cnf(c_1652,plain,
    ( r2_lattice3(k3_lattice3(sK3),X0,X1)
    | r2_hidden(sK1(k3_lattice3(sK3),X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(sK3))) ),
    inference(unflattening,[status(thm)],[c_1651])).

cnf(c_2575,plain,
    ( r2_lattice3(k3_lattice3(sK3),X0_55,X0_54)
    | r2_hidden(sK1(k3_lattice3(sK3),X0_55,X0_54),X0_55)
    | ~ m1_subset_1(X0_54,u1_struct_0(k3_lattice3(sK3))) ),
    inference(subtyping,[status(esa)],[c_1652])).

cnf(c_2637,plain,
    ( r2_lattice3(k3_lattice3(sK3),X0_55,X0_54) = iProver_top
    | r2_hidden(sK1(k3_lattice3(sK3),X0_55,X0_54),X0_55) = iProver_top
    | m1_subset_1(X0_54,u1_struct_0(k3_lattice3(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2575])).

cnf(c_2639,plain,
    ( r2_lattice3(k3_lattice3(sK3),sK2,sK4) = iProver_top
    | r2_hidden(sK1(k3_lattice3(sK3),sK2,sK4),sK2) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(k3_lattice3(sK3))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2637])).

cnf(c_14,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK1(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_411,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X3)
    | ~ v10_lattices(X3)
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | ~ l1_orders_2(X0)
    | k3_lattice3(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_19])).

cnf(c_412,plain,
    ( r1_orders_2(k3_lattice3(X0),X1,X2)
    | ~ r3_orders_2(k3_lattice3(X0),X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(X0)))
    | ~ l3_lattices(X0)
    | ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | v2_struct_0(k3_lattice3(X0))
    | ~ l1_orders_2(k3_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_411])).

cnf(c_416,plain,
    ( r1_orders_2(k3_lattice3(X0),X1,X2)
    | ~ r3_orders_2(k3_lattice3(X0),X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(X0)))
    | ~ l3_lattices(X0)
    | ~ v10_lattices(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_412,c_23,c_18])).

cnf(c_888,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ r3_orders_2(k3_lattice3(X3),X4,X5)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(k3_lattice3(X3)))
    | ~ m1_subset_1(X5,u1_struct_0(k3_lattice3(X3)))
    | ~ l3_lattices(X3)
    | ~ v10_lattices(X3)
    | v2_struct_0(X3)
    | ~ l1_orders_2(X0)
    | X5 != X2
    | sK1(X0,X1,X2) != X4
    | k3_lattice3(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_416])).

cnf(c_889,plain,
    ( r2_lattice3(k3_lattice3(X0),X1,X2)
    | ~ r3_orders_2(k3_lattice3(X0),sK1(k3_lattice3(X0),X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(X0)))
    | ~ m1_subset_1(sK1(k3_lattice3(X0),X1,X2),u1_struct_0(k3_lattice3(X0)))
    | ~ l3_lattices(X0)
    | ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(k3_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_888])).

cnf(c_603,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
    | ~ l3_lattices(X3)
    | ~ v10_lattices(X3)
    | v2_struct_0(X3)
    | k3_lattice3(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_18])).

cnf(c_604,plain,
    ( r2_lattice3(k3_lattice3(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(X0)))
    | m1_subset_1(sK1(k3_lattice3(X0),X1,X2),u1_struct_0(k3_lattice3(X0)))
    | ~ l3_lattices(X0)
    | ~ v10_lattices(X0)
    | v2_struct_0(X0) ),
    inference(unflattening,[status(thm)],[c_603])).

cnf(c_893,plain,
    ( v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | ~ l3_lattices(X0)
    | r2_lattice3(k3_lattice3(X0),X1,X2)
    | ~ r3_orders_2(k3_lattice3(X0),sK1(k3_lattice3(X0),X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_889,c_18,c_604])).

cnf(c_894,plain,
    ( r2_lattice3(k3_lattice3(X0),X1,X2)
    | ~ r3_orders_2(k3_lattice3(X0),sK1(k3_lattice3(X0),X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(X0)))
    | ~ l3_lattices(X0)
    | ~ v10_lattices(X0)
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_893])).

cnf(c_1469,plain,
    ( r2_lattice3(k3_lattice3(X0),X1,X2)
    | ~ r3_orders_2(k3_lattice3(X0),sK1(k3_lattice3(X0),X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(X0)))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_894,c_30])).

cnf(c_1470,plain,
    ( r2_lattice3(k3_lattice3(sK3),X0,X1)
    | ~ r3_orders_2(k3_lattice3(sK3),sK1(k3_lattice3(sK3),X0,X1),X1)
    | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(sK3)))
    | ~ l3_lattices(sK3)
    | v2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_1469])).

cnf(c_1474,plain,
    ( r2_lattice3(k3_lattice3(sK3),X0,X1)
    | ~ r3_orders_2(k3_lattice3(sK3),sK1(k3_lattice3(sK3),X0,X1),X1)
    | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1470,c_31,c_29])).

cnf(c_2582,plain,
    ( r2_lattice3(k3_lattice3(sK3),X0_55,X0_54)
    | ~ r3_orders_2(k3_lattice3(sK3),sK1(k3_lattice3(sK3),X0_55,X0_54),X0_54)
    | ~ m1_subset_1(X0_54,u1_struct_0(k3_lattice3(sK3))) ),
    inference(subtyping,[status(esa)],[c_1474])).

cnf(c_2618,plain,
    ( r2_lattice3(k3_lattice3(sK3),X0_55,X0_54) = iProver_top
    | r3_orders_2(k3_lattice3(sK3),sK1(k3_lattice3(sK3),X0_55,X0_54),X0_54) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(k3_lattice3(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2582])).

cnf(c_2620,plain,
    ( r2_lattice3(k3_lattice3(sK3),sK2,sK4) = iProver_top
    | r3_orders_2(k3_lattice3(sK3),sK1(k3_lattice3(sK3),sK2,sK4),sK4) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(k3_lattice3(sK3))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2618])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8589,c_6563,c_5504,c_4984,c_4436,c_4420,c_3434,c_3291,c_3279,c_3252,c_2639,c_2636,c_2631,c_2626,c_2620,c_2605,c_35,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:13:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.01/1.04  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.01/1.04  
% 1.01/1.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.01/1.04  
% 1.01/1.04  ------  iProver source info
% 1.01/1.04  
% 1.01/1.04  git: date: 2020-06-30 10:37:57 +0100
% 1.01/1.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.01/1.04  git: non_committed_changes: false
% 1.01/1.04  git: last_make_outside_of_git: false
% 1.01/1.04  
% 1.01/1.04  ------ 
% 1.01/1.04  
% 1.01/1.04  ------ Input Options
% 1.01/1.04  
% 1.01/1.04  --out_options                           all
% 1.01/1.04  --tptp_safe_out                         true
% 1.01/1.04  --problem_path                          ""
% 1.01/1.04  --include_path                          ""
% 1.01/1.04  --clausifier                            res/vclausify_rel
% 1.01/1.04  --clausifier_options                    --mode clausify
% 1.01/1.04  --stdin                                 false
% 1.01/1.04  --stats_out                             all
% 1.01/1.04  
% 1.01/1.04  ------ General Options
% 1.01/1.04  
% 1.01/1.04  --fof                                   false
% 1.01/1.04  --time_out_real                         305.
% 1.01/1.04  --time_out_virtual                      -1.
% 1.01/1.04  --symbol_type_check                     false
% 1.01/1.04  --clausify_out                          false
% 1.01/1.04  --sig_cnt_out                           false
% 1.01/1.04  --trig_cnt_out                          false
% 1.01/1.04  --trig_cnt_out_tolerance                1.
% 1.01/1.04  --trig_cnt_out_sk_spl                   false
% 1.01/1.04  --abstr_cl_out                          false
% 1.01/1.04  
% 1.01/1.04  ------ Global Options
% 1.01/1.04  
% 1.01/1.04  --schedule                              default
% 1.01/1.04  --add_important_lit                     false
% 1.01/1.04  --prop_solver_per_cl                    1000
% 1.01/1.04  --min_unsat_core                        false
% 1.01/1.04  --soft_assumptions                      false
% 1.01/1.04  --soft_lemma_size                       3
% 1.01/1.04  --prop_impl_unit_size                   0
% 1.01/1.04  --prop_impl_unit                        []
% 1.01/1.04  --share_sel_clauses                     true
% 1.01/1.04  --reset_solvers                         false
% 1.01/1.04  --bc_imp_inh                            [conj_cone]
% 1.01/1.04  --conj_cone_tolerance                   3.
% 1.01/1.04  --extra_neg_conj                        none
% 1.01/1.04  --large_theory_mode                     true
% 1.01/1.04  --prolific_symb_bound                   200
% 1.01/1.04  --lt_threshold                          2000
% 1.01/1.04  --clause_weak_htbl                      true
% 1.01/1.04  --gc_record_bc_elim                     false
% 1.01/1.04  
% 1.01/1.04  ------ Preprocessing Options
% 1.01/1.04  
% 1.01/1.04  --preprocessing_flag                    true
% 1.01/1.04  --time_out_prep_mult                    0.1
% 1.01/1.04  --splitting_mode                        input
% 1.01/1.04  --splitting_grd                         true
% 1.01/1.04  --splitting_cvd                         false
% 1.01/1.04  --splitting_cvd_svl                     false
% 1.01/1.04  --splitting_nvd                         32
% 1.01/1.04  --sub_typing                            true
% 1.01/1.04  --prep_gs_sim                           true
% 1.01/1.04  --prep_unflatten                        true
% 1.01/1.04  --prep_res_sim                          true
% 1.01/1.04  --prep_upred                            true
% 1.01/1.04  --prep_sem_filter                       exhaustive
% 1.01/1.04  --prep_sem_filter_out                   false
% 1.01/1.04  --pred_elim                             true
% 1.01/1.04  --res_sim_input                         true
% 1.01/1.04  --eq_ax_congr_red                       true
% 1.01/1.04  --pure_diseq_elim                       true
% 1.01/1.04  --brand_transform                       false
% 1.01/1.04  --non_eq_to_eq                          false
% 1.01/1.04  --prep_def_merge                        true
% 1.01/1.04  --prep_def_merge_prop_impl              false
% 1.01/1.04  --prep_def_merge_mbd                    true
% 1.01/1.04  --prep_def_merge_tr_red                 false
% 1.01/1.04  --prep_def_merge_tr_cl                  false
% 1.01/1.04  --smt_preprocessing                     true
% 1.01/1.04  --smt_ac_axioms                         fast
% 1.01/1.04  --preprocessed_out                      false
% 1.01/1.04  --preprocessed_stats                    false
% 1.01/1.04  
% 1.01/1.04  ------ Abstraction refinement Options
% 1.01/1.04  
% 1.01/1.04  --abstr_ref                             []
% 1.01/1.04  --abstr_ref_prep                        false
% 1.01/1.04  --abstr_ref_until_sat                   false
% 1.01/1.04  --abstr_ref_sig_restrict                funpre
% 1.01/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 1.01/1.04  --abstr_ref_under                       []
% 1.01/1.04  
% 1.01/1.04  ------ SAT Options
% 1.01/1.04  
% 1.01/1.04  --sat_mode                              false
% 1.01/1.04  --sat_fm_restart_options                ""
% 1.01/1.04  --sat_gr_def                            false
% 1.01/1.04  --sat_epr_types                         true
% 1.01/1.04  --sat_non_cyclic_types                  false
% 1.01/1.04  --sat_finite_models                     false
% 1.01/1.04  --sat_fm_lemmas                         false
% 1.01/1.04  --sat_fm_prep                           false
% 1.01/1.04  --sat_fm_uc_incr                        true
% 1.01/1.04  --sat_out_model                         small
% 1.01/1.04  --sat_out_clauses                       false
% 1.01/1.04  
% 1.01/1.04  ------ QBF Options
% 1.01/1.04  
% 1.01/1.04  --qbf_mode                              false
% 1.01/1.04  --qbf_elim_univ                         false
% 1.01/1.04  --qbf_dom_inst                          none
% 1.01/1.04  --qbf_dom_pre_inst                      false
% 1.01/1.04  --qbf_sk_in                             false
% 1.01/1.04  --qbf_pred_elim                         true
% 1.01/1.04  --qbf_split                             512
% 1.01/1.04  
% 1.01/1.04  ------ BMC1 Options
% 1.01/1.04  
% 1.01/1.04  --bmc1_incremental                      false
% 1.01/1.04  --bmc1_axioms                           reachable_all
% 1.01/1.04  --bmc1_min_bound                        0
% 1.01/1.04  --bmc1_max_bound                        -1
% 1.01/1.04  --bmc1_max_bound_default                -1
% 1.01/1.04  --bmc1_symbol_reachability              true
% 1.01/1.04  --bmc1_property_lemmas                  false
% 1.01/1.04  --bmc1_k_induction                      false
% 1.01/1.04  --bmc1_non_equiv_states                 false
% 1.01/1.04  --bmc1_deadlock                         false
% 1.01/1.04  --bmc1_ucm                              false
% 1.01/1.04  --bmc1_add_unsat_core                   none
% 1.01/1.04  --bmc1_unsat_core_children              false
% 1.01/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 1.01/1.04  --bmc1_out_stat                         full
% 1.01/1.04  --bmc1_ground_init                      false
% 1.01/1.04  --bmc1_pre_inst_next_state              false
% 1.01/1.04  --bmc1_pre_inst_state                   false
% 1.01/1.04  --bmc1_pre_inst_reach_state             false
% 1.01/1.04  --bmc1_out_unsat_core                   false
% 1.01/1.04  --bmc1_aig_witness_out                  false
% 1.01/1.04  --bmc1_verbose                          false
% 1.01/1.04  --bmc1_dump_clauses_tptp                false
% 1.01/1.04  --bmc1_dump_unsat_core_tptp             false
% 1.01/1.04  --bmc1_dump_file                        -
% 1.01/1.04  --bmc1_ucm_expand_uc_limit              128
% 1.01/1.04  --bmc1_ucm_n_expand_iterations          6
% 1.01/1.04  --bmc1_ucm_extend_mode                  1
% 1.01/1.04  --bmc1_ucm_init_mode                    2
% 1.01/1.04  --bmc1_ucm_cone_mode                    none
% 1.01/1.04  --bmc1_ucm_reduced_relation_type        0
% 1.01/1.04  --bmc1_ucm_relax_model                  4
% 1.01/1.04  --bmc1_ucm_full_tr_after_sat            true
% 1.01/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 1.01/1.04  --bmc1_ucm_layered_model                none
% 1.01/1.04  --bmc1_ucm_max_lemma_size               10
% 1.01/1.04  
% 1.01/1.04  ------ AIG Options
% 1.01/1.04  
% 1.01/1.04  --aig_mode                              false
% 1.01/1.04  
% 1.01/1.04  ------ Instantiation Options
% 1.01/1.04  
% 1.01/1.04  --instantiation_flag                    true
% 1.01/1.04  --inst_sos_flag                         false
% 1.01/1.04  --inst_sos_phase                        true
% 1.01/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.01/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.01/1.04  --inst_lit_sel_side                     num_symb
% 1.01/1.04  --inst_solver_per_active                1400
% 1.01/1.04  --inst_solver_calls_frac                1.
% 1.01/1.04  --inst_passive_queue_type               priority_queues
% 1.01/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.01/1.04  --inst_passive_queues_freq              [25;2]
% 1.01/1.04  --inst_dismatching                      true
% 1.01/1.04  --inst_eager_unprocessed_to_passive     true
% 1.01/1.04  --inst_prop_sim_given                   true
% 1.01/1.04  --inst_prop_sim_new                     false
% 1.01/1.04  --inst_subs_new                         false
% 1.01/1.04  --inst_eq_res_simp                      false
% 1.01/1.04  --inst_subs_given                       false
% 1.01/1.04  --inst_orphan_elimination               true
% 1.01/1.04  --inst_learning_loop_flag               true
% 1.01/1.04  --inst_learning_start                   3000
% 1.01/1.04  --inst_learning_factor                  2
% 1.01/1.04  --inst_start_prop_sim_after_learn       3
% 1.01/1.04  --inst_sel_renew                        solver
% 1.01/1.04  --inst_lit_activity_flag                true
% 1.01/1.04  --inst_restr_to_given                   false
% 1.01/1.04  --inst_activity_threshold               500
% 1.01/1.04  --inst_out_proof                        true
% 1.01/1.04  
% 1.01/1.04  ------ Resolution Options
% 1.01/1.04  
% 1.01/1.04  --resolution_flag                       true
% 1.01/1.04  --res_lit_sel                           adaptive
% 1.01/1.04  --res_lit_sel_side                      none
% 1.01/1.04  --res_ordering                          kbo
% 1.01/1.04  --res_to_prop_solver                    active
% 1.01/1.04  --res_prop_simpl_new                    false
% 1.01/1.04  --res_prop_simpl_given                  true
% 1.01/1.04  --res_passive_queue_type                priority_queues
% 1.01/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.01/1.04  --res_passive_queues_freq               [15;5]
% 1.01/1.04  --res_forward_subs                      full
% 1.01/1.04  --res_backward_subs                     full
% 1.01/1.04  --res_forward_subs_resolution           true
% 1.01/1.04  --res_backward_subs_resolution          true
% 1.01/1.04  --res_orphan_elimination                true
% 1.01/1.04  --res_time_limit                        2.
% 1.01/1.04  --res_out_proof                         true
% 1.01/1.04  
% 1.01/1.04  ------ Superposition Options
% 1.01/1.04  
% 1.01/1.04  --superposition_flag                    true
% 1.01/1.04  --sup_passive_queue_type                priority_queues
% 1.01/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.01/1.04  --sup_passive_queues_freq               [8;1;4]
% 1.01/1.04  --demod_completeness_check              fast
% 1.01/1.04  --demod_use_ground                      true
% 1.01/1.04  --sup_to_prop_solver                    passive
% 1.01/1.04  --sup_prop_simpl_new                    true
% 1.01/1.04  --sup_prop_simpl_given                  true
% 1.01/1.04  --sup_fun_splitting                     false
% 1.01/1.04  --sup_smt_interval                      50000
% 1.01/1.04  
% 1.01/1.04  ------ Superposition Simplification Setup
% 1.01/1.04  
% 1.01/1.04  --sup_indices_passive                   []
% 1.01/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.01/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.01/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.01/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 1.01/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.01/1.04  --sup_full_bw                           [BwDemod]
% 1.01/1.04  --sup_immed_triv                        [TrivRules]
% 1.01/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.01/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.01/1.04  --sup_immed_bw_main                     []
% 1.01/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.01/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 1.01/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.01/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.01/1.04  
% 1.01/1.04  ------ Combination Options
% 1.01/1.04  
% 1.01/1.04  --comb_res_mult                         3
% 1.01/1.04  --comb_sup_mult                         2
% 1.01/1.04  --comb_inst_mult                        10
% 1.01/1.04  
% 1.01/1.04  ------ Debug Options
% 1.01/1.04  
% 1.01/1.04  --dbg_backtrace                         false
% 1.01/1.04  --dbg_dump_prop_clauses                 false
% 1.01/1.04  --dbg_dump_prop_clauses_file            -
% 1.01/1.04  --dbg_out_stat                          false
% 1.01/1.04  ------ Parsing...
% 1.01/1.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.01/1.04  
% 1.01/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 1.01/1.04  
% 1.01/1.04  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.01/1.04  
% 1.01/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.01/1.04  ------ Proving...
% 1.01/1.04  ------ Problem Properties 
% 1.01/1.04  
% 1.01/1.04  
% 1.01/1.04  clauses                                 17
% 1.01/1.04  conjectures                             3
% 1.01/1.04  EPR                                     0
% 1.01/1.04  Horn                                    12
% 1.01/1.04  unary                                   1
% 1.01/1.04  binary                                  6
% 1.01/1.04  lits                                    49
% 1.01/1.04  lits eq                                 2
% 1.01/1.04  fd_pure                                 0
% 1.01/1.04  fd_pseudo                               0
% 1.01/1.04  fd_cond                                 0
% 1.01/1.04  fd_pseudo_cond                          0
% 1.01/1.04  AC symbols                              0
% 1.01/1.04  
% 1.01/1.04  ------ Schedule dynamic 5 is on 
% 1.01/1.04  
% 1.01/1.04  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.01/1.04  
% 1.01/1.04  
% 1.01/1.04  ------ 
% 1.01/1.04  Current options:
% 1.01/1.04  ------ 
% 1.01/1.04  
% 1.01/1.04  ------ Input Options
% 1.01/1.04  
% 1.01/1.04  --out_options                           all
% 1.01/1.04  --tptp_safe_out                         true
% 1.01/1.04  --problem_path                          ""
% 1.01/1.04  --include_path                          ""
% 1.01/1.04  --clausifier                            res/vclausify_rel
% 1.01/1.04  --clausifier_options                    --mode clausify
% 1.01/1.04  --stdin                                 false
% 1.01/1.04  --stats_out                             all
% 1.01/1.04  
% 1.01/1.04  ------ General Options
% 1.01/1.04  
% 1.01/1.04  --fof                                   false
% 1.01/1.04  --time_out_real                         305.
% 1.01/1.04  --time_out_virtual                      -1.
% 1.01/1.04  --symbol_type_check                     false
% 1.01/1.04  --clausify_out                          false
% 1.01/1.04  --sig_cnt_out                           false
% 1.01/1.04  --trig_cnt_out                          false
% 1.01/1.04  --trig_cnt_out_tolerance                1.
% 1.01/1.04  --trig_cnt_out_sk_spl                   false
% 1.01/1.04  --abstr_cl_out                          false
% 1.01/1.04  
% 1.01/1.04  ------ Global Options
% 1.01/1.04  
% 1.01/1.04  --schedule                              default
% 1.01/1.04  --add_important_lit                     false
% 1.01/1.04  --prop_solver_per_cl                    1000
% 1.01/1.04  --min_unsat_core                        false
% 1.01/1.04  --soft_assumptions                      false
% 1.01/1.04  --soft_lemma_size                       3
% 1.01/1.04  --prop_impl_unit_size                   0
% 1.01/1.04  --prop_impl_unit                        []
% 1.01/1.04  --share_sel_clauses                     true
% 1.01/1.04  --reset_solvers                         false
% 1.01/1.04  --bc_imp_inh                            [conj_cone]
% 1.01/1.04  --conj_cone_tolerance                   3.
% 1.01/1.04  --extra_neg_conj                        none
% 1.01/1.04  --large_theory_mode                     true
% 1.01/1.04  --prolific_symb_bound                   200
% 1.01/1.04  --lt_threshold                          2000
% 1.01/1.04  --clause_weak_htbl                      true
% 1.01/1.04  --gc_record_bc_elim                     false
% 1.01/1.04  
% 1.01/1.04  ------ Preprocessing Options
% 1.01/1.04  
% 1.01/1.04  --preprocessing_flag                    true
% 1.01/1.04  --time_out_prep_mult                    0.1
% 1.01/1.04  --splitting_mode                        input
% 1.01/1.04  --splitting_grd                         true
% 1.01/1.04  --splitting_cvd                         false
% 1.01/1.04  --splitting_cvd_svl                     false
% 1.01/1.04  --splitting_nvd                         32
% 1.01/1.04  --sub_typing                            true
% 1.01/1.04  --prep_gs_sim                           true
% 1.01/1.04  --prep_unflatten                        true
% 1.01/1.04  --prep_res_sim                          true
% 1.01/1.04  --prep_upred                            true
% 1.01/1.04  --prep_sem_filter                       exhaustive
% 1.01/1.04  --prep_sem_filter_out                   false
% 1.01/1.04  --pred_elim                             true
% 1.01/1.04  --res_sim_input                         true
% 1.01/1.04  --eq_ax_congr_red                       true
% 1.01/1.04  --pure_diseq_elim                       true
% 1.01/1.04  --brand_transform                       false
% 1.01/1.04  --non_eq_to_eq                          false
% 1.01/1.04  --prep_def_merge                        true
% 1.01/1.04  --prep_def_merge_prop_impl              false
% 1.01/1.04  --prep_def_merge_mbd                    true
% 1.01/1.04  --prep_def_merge_tr_red                 false
% 1.01/1.04  --prep_def_merge_tr_cl                  false
% 1.01/1.04  --smt_preprocessing                     true
% 1.01/1.04  --smt_ac_axioms                         fast
% 1.01/1.04  --preprocessed_out                      false
% 1.01/1.04  --preprocessed_stats                    false
% 1.01/1.04  
% 1.01/1.04  ------ Abstraction refinement Options
% 1.01/1.04  
% 1.01/1.04  --abstr_ref                             []
% 1.01/1.04  --abstr_ref_prep                        false
% 1.01/1.04  --abstr_ref_until_sat                   false
% 1.01/1.04  --abstr_ref_sig_restrict                funpre
% 1.01/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 1.01/1.04  --abstr_ref_under                       []
% 1.01/1.04  
% 1.01/1.04  ------ SAT Options
% 1.01/1.04  
% 1.01/1.04  --sat_mode                              false
% 1.01/1.04  --sat_fm_restart_options                ""
% 1.01/1.04  --sat_gr_def                            false
% 1.01/1.04  --sat_epr_types                         true
% 1.01/1.04  --sat_non_cyclic_types                  false
% 1.01/1.04  --sat_finite_models                     false
% 1.01/1.04  --sat_fm_lemmas                         false
% 1.01/1.04  --sat_fm_prep                           false
% 1.01/1.04  --sat_fm_uc_incr                        true
% 1.01/1.04  --sat_out_model                         small
% 1.01/1.04  --sat_out_clauses                       false
% 1.01/1.04  
% 1.01/1.04  ------ QBF Options
% 1.01/1.04  
% 1.01/1.04  --qbf_mode                              false
% 1.01/1.04  --qbf_elim_univ                         false
% 1.01/1.04  --qbf_dom_inst                          none
% 1.01/1.04  --qbf_dom_pre_inst                      false
% 1.01/1.04  --qbf_sk_in                             false
% 1.01/1.04  --qbf_pred_elim                         true
% 1.01/1.04  --qbf_split                             512
% 1.01/1.04  
% 1.01/1.04  ------ BMC1 Options
% 1.01/1.04  
% 1.01/1.04  --bmc1_incremental                      false
% 1.01/1.04  --bmc1_axioms                           reachable_all
% 1.01/1.04  --bmc1_min_bound                        0
% 1.01/1.04  --bmc1_max_bound                        -1
% 1.01/1.04  --bmc1_max_bound_default                -1
% 1.01/1.04  --bmc1_symbol_reachability              true
% 1.01/1.04  --bmc1_property_lemmas                  false
% 1.01/1.04  --bmc1_k_induction                      false
% 1.01/1.04  --bmc1_non_equiv_states                 false
% 1.01/1.04  --bmc1_deadlock                         false
% 1.01/1.04  --bmc1_ucm                              false
% 1.01/1.04  --bmc1_add_unsat_core                   none
% 1.01/1.04  --bmc1_unsat_core_children              false
% 1.01/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 1.01/1.04  --bmc1_out_stat                         full
% 1.01/1.04  --bmc1_ground_init                      false
% 1.01/1.04  --bmc1_pre_inst_next_state              false
% 1.01/1.04  --bmc1_pre_inst_state                   false
% 1.01/1.04  --bmc1_pre_inst_reach_state             false
% 1.01/1.04  --bmc1_out_unsat_core                   false
% 1.01/1.04  --bmc1_aig_witness_out                  false
% 1.01/1.04  --bmc1_verbose                          false
% 1.01/1.04  --bmc1_dump_clauses_tptp                false
% 1.01/1.04  --bmc1_dump_unsat_core_tptp             false
% 1.01/1.04  --bmc1_dump_file                        -
% 1.01/1.04  --bmc1_ucm_expand_uc_limit              128
% 1.01/1.04  --bmc1_ucm_n_expand_iterations          6
% 1.01/1.04  --bmc1_ucm_extend_mode                  1
% 1.01/1.04  --bmc1_ucm_init_mode                    2
% 1.01/1.04  --bmc1_ucm_cone_mode                    none
% 1.01/1.04  --bmc1_ucm_reduced_relation_type        0
% 1.01/1.04  --bmc1_ucm_relax_model                  4
% 1.01/1.04  --bmc1_ucm_full_tr_after_sat            true
% 1.01/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 1.01/1.04  --bmc1_ucm_layered_model                none
% 1.01/1.04  --bmc1_ucm_max_lemma_size               10
% 1.01/1.04  
% 1.01/1.04  ------ AIG Options
% 1.01/1.04  
% 1.01/1.04  --aig_mode                              false
% 1.01/1.04  
% 1.01/1.04  ------ Instantiation Options
% 1.01/1.04  
% 1.01/1.04  --instantiation_flag                    true
% 1.01/1.04  --inst_sos_flag                         false
% 1.01/1.04  --inst_sos_phase                        true
% 1.01/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.01/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.01/1.04  --inst_lit_sel_side                     none
% 1.01/1.04  --inst_solver_per_active                1400
% 1.01/1.04  --inst_solver_calls_frac                1.
% 1.01/1.04  --inst_passive_queue_type               priority_queues
% 1.01/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.01/1.04  --inst_passive_queues_freq              [25;2]
% 1.01/1.04  --inst_dismatching                      true
% 1.01/1.04  --inst_eager_unprocessed_to_passive     true
% 1.01/1.04  --inst_prop_sim_given                   true
% 1.01/1.04  --inst_prop_sim_new                     false
% 1.01/1.04  --inst_subs_new                         false
% 1.01/1.04  --inst_eq_res_simp                      false
% 1.01/1.04  --inst_subs_given                       false
% 1.01/1.04  --inst_orphan_elimination               true
% 1.01/1.04  --inst_learning_loop_flag               true
% 1.01/1.04  --inst_learning_start                   3000
% 1.01/1.04  --inst_learning_factor                  2
% 1.01/1.04  --inst_start_prop_sim_after_learn       3
% 1.01/1.04  --inst_sel_renew                        solver
% 1.01/1.04  --inst_lit_activity_flag                true
% 1.01/1.04  --inst_restr_to_given                   false
% 1.01/1.04  --inst_activity_threshold               500
% 1.01/1.04  --inst_out_proof                        true
% 1.01/1.04  
% 1.01/1.04  ------ Resolution Options
% 1.01/1.04  
% 1.01/1.04  --resolution_flag                       false
% 1.01/1.04  --res_lit_sel                           adaptive
% 1.01/1.04  --res_lit_sel_side                      none
% 1.01/1.04  --res_ordering                          kbo
% 1.01/1.04  --res_to_prop_solver                    active
% 1.01/1.04  --res_prop_simpl_new                    false
% 1.01/1.04  --res_prop_simpl_given                  true
% 1.01/1.04  --res_passive_queue_type                priority_queues
% 1.01/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.01/1.04  --res_passive_queues_freq               [15;5]
% 1.01/1.04  --res_forward_subs                      full
% 1.01/1.04  --res_backward_subs                     full
% 1.01/1.04  --res_forward_subs_resolution           true
% 1.01/1.04  --res_backward_subs_resolution          true
% 1.01/1.04  --res_orphan_elimination                true
% 1.01/1.04  --res_time_limit                        2.
% 1.01/1.04  --res_out_proof                         true
% 1.01/1.04  
% 1.01/1.04  ------ Superposition Options
% 1.01/1.04  
% 1.01/1.04  --superposition_flag                    true
% 1.01/1.04  --sup_passive_queue_type                priority_queues
% 1.01/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.01/1.04  --sup_passive_queues_freq               [8;1;4]
% 1.01/1.04  --demod_completeness_check              fast
% 1.01/1.04  --demod_use_ground                      true
% 1.01/1.04  --sup_to_prop_solver                    passive
% 1.01/1.04  --sup_prop_simpl_new                    true
% 1.01/1.04  --sup_prop_simpl_given                  true
% 1.01/1.04  --sup_fun_splitting                     false
% 1.01/1.04  --sup_smt_interval                      50000
% 1.01/1.04  
% 1.01/1.04  ------ Superposition Simplification Setup
% 1.01/1.04  
% 1.01/1.04  --sup_indices_passive                   []
% 1.01/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.01/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.01/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.01/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 1.01/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.01/1.04  --sup_full_bw                           [BwDemod]
% 1.01/1.04  --sup_immed_triv                        [TrivRules]
% 1.01/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.01/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.01/1.05  --sup_immed_bw_main                     []
% 1.01/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.01/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 1.01/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.01/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.01/1.05  
% 1.01/1.05  ------ Combination Options
% 1.01/1.05  
% 1.01/1.05  --comb_res_mult                         3
% 1.01/1.05  --comb_sup_mult                         2
% 1.01/1.05  --comb_inst_mult                        10
% 1.01/1.05  
% 1.01/1.05  ------ Debug Options
% 1.01/1.05  
% 1.01/1.05  --dbg_backtrace                         false
% 1.01/1.05  --dbg_dump_prop_clauses                 false
% 1.01/1.05  --dbg_dump_prop_clauses_file            -
% 1.01/1.05  --dbg_out_stat                          false
% 1.01/1.05  
% 1.01/1.05  
% 1.01/1.05  
% 1.01/1.05  
% 1.01/1.05  ------ Proving...
% 1.01/1.05  
% 1.01/1.05  
% 1.01/1.05  % SZS status Theorem for theBenchmark.p
% 1.01/1.05  
% 1.01/1.05  % SZS output start CNFRefutation for theBenchmark.p
% 1.01/1.05  
% 1.01/1.05  fof(f13,conjecture,(
% 1.01/1.05    ! [X0,X1] : ((l3_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => (r4_lattice3(X1,X2,X0) <=> r2_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2)))))),
% 1.01/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.01/1.05  
% 1.01/1.05  fof(f14,negated_conjecture,(
% 1.01/1.05    ~! [X0,X1] : ((l3_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => (r4_lattice3(X1,X2,X0) <=> r2_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2)))))),
% 1.01/1.05    inference(negated_conjecture,[],[f13])).
% 1.01/1.05  
% 1.01/1.05  fof(f48,plain,(
% 1.01/1.05    ? [X0,X1] : (? [X2] : ((r4_lattice3(X1,X2,X0) <~> r2_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2))) & m1_subset_1(X2,u1_struct_0(X1))) & (l3_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1)))),
% 1.01/1.05    inference(ennf_transformation,[],[f14])).
% 1.01/1.05  
% 1.01/1.05  fof(f49,plain,(
% 1.01/1.05    ? [X0,X1] : (? [X2] : ((r4_lattice3(X1,X2,X0) <~> r2_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2))) & m1_subset_1(X2,u1_struct_0(X1))) & l3_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1))),
% 1.01/1.05    inference(flattening,[],[f48])).
% 1.01/1.05  
% 1.01/1.05  fof(f61,plain,(
% 1.01/1.05    ? [X0,X1] : (? [X2] : (((~r2_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2)) | ~r4_lattice3(X1,X2,X0)) & (r2_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2)) | r4_lattice3(X1,X2,X0))) & m1_subset_1(X2,u1_struct_0(X1))) & l3_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1))),
% 1.01/1.05    inference(nnf_transformation,[],[f49])).
% 1.01/1.05  
% 1.01/1.05  fof(f62,plain,(
% 1.01/1.05    ? [X0,X1] : (? [X2] : ((~r2_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2)) | ~r4_lattice3(X1,X2,X0)) & (r2_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2)) | r4_lattice3(X1,X2,X0)) & m1_subset_1(X2,u1_struct_0(X1))) & l3_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1))),
% 1.01/1.05    inference(flattening,[],[f61])).
% 1.01/1.05  
% 1.01/1.05  fof(f64,plain,(
% 1.01/1.05    ( ! [X0,X1] : (? [X2] : ((~r2_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2)) | ~r4_lattice3(X1,X2,X0)) & (r2_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2)) | r4_lattice3(X1,X2,X0)) & m1_subset_1(X2,u1_struct_0(X1))) => ((~r2_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,sK4)) | ~r4_lattice3(X1,sK4,X0)) & (r2_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,sK4)) | r4_lattice3(X1,sK4,X0)) & m1_subset_1(sK4,u1_struct_0(X1)))) )),
% 1.01/1.05    introduced(choice_axiom,[])).
% 1.01/1.05  
% 1.01/1.05  fof(f63,plain,(
% 1.01/1.05    ? [X0,X1] : (? [X2] : ((~r2_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2)) | ~r4_lattice3(X1,X2,X0)) & (r2_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2)) | r4_lattice3(X1,X2,X0)) & m1_subset_1(X2,u1_struct_0(X1))) & l3_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => (? [X2] : ((~r2_lattice3(k3_lattice3(sK3),sK2,k4_lattice3(sK3,X2)) | ~r4_lattice3(sK3,X2,sK2)) & (r2_lattice3(k3_lattice3(sK3),sK2,k4_lattice3(sK3,X2)) | r4_lattice3(sK3,X2,sK2)) & m1_subset_1(X2,u1_struct_0(sK3))) & l3_lattices(sK3) & v10_lattices(sK3) & ~v2_struct_0(sK3))),
% 1.01/1.05    introduced(choice_axiom,[])).
% 1.01/1.05  
% 1.01/1.05  fof(f65,plain,(
% 1.01/1.05    ((~r2_lattice3(k3_lattice3(sK3),sK2,k4_lattice3(sK3,sK4)) | ~r4_lattice3(sK3,sK4,sK2)) & (r2_lattice3(k3_lattice3(sK3),sK2,k4_lattice3(sK3,sK4)) | r4_lattice3(sK3,sK4,sK2)) & m1_subset_1(sK4,u1_struct_0(sK3))) & l3_lattices(sK3) & v10_lattices(sK3) & ~v2_struct_0(sK3)),
% 1.01/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f62,f64,f63])).
% 1.01/1.05  
% 1.01/1.05  fof(f95,plain,(
% 1.01/1.05    m1_subset_1(sK4,u1_struct_0(sK3))),
% 1.01/1.05    inference(cnf_transformation,[],[f65])).
% 1.01/1.05  
% 1.01/1.05  fof(f5,axiom,(
% 1.01/1.05    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k4_lattice3(X0,X1) = X1))),
% 1.01/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.01/1.05  
% 1.01/1.05  fof(f32,plain,(
% 1.01/1.05    ! [X0] : (! [X1] : (k4_lattice3(X0,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 1.01/1.05    inference(ennf_transformation,[],[f5])).
% 1.01/1.05  
% 1.01/1.05  fof(f33,plain,(
% 1.01/1.05    ! [X0] : (! [X1] : (k4_lattice3(X0,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.01/1.05    inference(flattening,[],[f32])).
% 1.01/1.05  
% 1.01/1.05  fof(f78,plain,(
% 1.01/1.05    ( ! [X0,X1] : (k4_lattice3(X0,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 1.01/1.05    inference(cnf_transformation,[],[f33])).
% 1.01/1.05  
% 1.01/1.05  fof(f93,plain,(
% 1.01/1.05    v10_lattices(sK3)),
% 1.01/1.05    inference(cnf_transformation,[],[f65])).
% 1.01/1.05  
% 1.01/1.05  fof(f92,plain,(
% 1.01/1.05    ~v2_struct_0(sK3)),
% 1.01/1.05    inference(cnf_transformation,[],[f65])).
% 1.01/1.05  
% 1.01/1.05  fof(f94,plain,(
% 1.01/1.05    l3_lattices(sK3)),
% 1.01/1.05    inference(cnf_transformation,[],[f65])).
% 1.01/1.05  
% 1.01/1.05  fof(f9,axiom,(
% 1.01/1.05    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k4_lattice3(X0,X1),u1_struct_0(k3_lattice3(X0))))),
% 1.01/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.01/1.05  
% 1.01/1.05  fof(f40,plain,(
% 1.01/1.05    ! [X0,X1] : (m1_subset_1(k4_lattice3(X0,X1),u1_struct_0(k3_lattice3(X0))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 1.01/1.05    inference(ennf_transformation,[],[f9])).
% 1.01/1.05  
% 1.01/1.05  fof(f41,plain,(
% 1.01/1.05    ! [X0,X1] : (m1_subset_1(k4_lattice3(X0,X1),u1_struct_0(k3_lattice3(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.01/1.05    inference(flattening,[],[f40])).
% 1.01/1.05  
% 1.01/1.05  fof(f86,plain,(
% 1.01/1.05    ( ! [X0,X1] : (m1_subset_1(k4_lattice3(X0,X1),u1_struct_0(k3_lattice3(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 1.01/1.05    inference(cnf_transformation,[],[f41])).
% 1.01/1.05  
% 1.01/1.05  fof(f7,axiom,(
% 1.01/1.05    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X3,X2))))))),
% 1.01/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.01/1.05  
% 1.01/1.05  fof(f36,plain,(
% 1.01/1.05    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.01/1.05    inference(ennf_transformation,[],[f7])).
% 1.01/1.05  
% 1.01/1.05  fof(f37,plain,(
% 1.01/1.05    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.01/1.05    inference(flattening,[],[f36])).
% 1.01/1.05  
% 1.01/1.05  fof(f56,plain,(
% 1.01/1.05    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.01/1.05    inference(nnf_transformation,[],[f37])).
% 1.01/1.05  
% 1.01/1.05  fof(f57,plain,(
% 1.01/1.05    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.01/1.05    inference(rectify,[],[f56])).
% 1.01/1.05  
% 1.01/1.05  fof(f58,plain,(
% 1.01/1.05    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK1(X0,X1,X2),X2) & r2_hidden(sK1(X0,X1,X2),X1) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))))),
% 1.01/1.05    introduced(choice_axiom,[])).
% 1.01/1.05  
% 1.01/1.05  fof(f59,plain,(
% 1.01/1.05    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | (~r1_orders_2(X0,sK1(X0,X1,X2),X2) & r2_hidden(sK1(X0,X1,X2),X1) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.01/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f57,f58])).
% 1.01/1.05  
% 1.01/1.05  fof(f81,plain,(
% 1.01/1.05    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.01/1.05    inference(cnf_transformation,[],[f59])).
% 1.01/1.05  
% 1.01/1.05  fof(f8,axiom,(
% 1.01/1.05    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (l1_orders_2(k3_lattice3(X0)) & v5_orders_2(k3_lattice3(X0)) & v4_orders_2(k3_lattice3(X0)) & v3_orders_2(k3_lattice3(X0)) & v1_orders_2(k3_lattice3(X0))))),
% 1.01/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.01/1.05  
% 1.01/1.05  fof(f15,plain,(
% 1.01/1.05    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (l1_orders_2(k3_lattice3(X0)) & v4_orders_2(k3_lattice3(X0)) & v3_orders_2(k3_lattice3(X0)) & v1_orders_2(k3_lattice3(X0))))),
% 1.01/1.05    inference(pure_predicate_removal,[],[f8])).
% 1.01/1.05  
% 1.01/1.05  fof(f17,plain,(
% 1.01/1.05    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (l1_orders_2(k3_lattice3(X0)) & v3_orders_2(k3_lattice3(X0)) & v1_orders_2(k3_lattice3(X0))))),
% 1.01/1.05    inference(pure_predicate_removal,[],[f15])).
% 1.01/1.05  
% 1.01/1.05  fof(f19,plain,(
% 1.01/1.05    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (l1_orders_2(k3_lattice3(X0)) & v3_orders_2(k3_lattice3(X0))))),
% 1.01/1.05    inference(pure_predicate_removal,[],[f17])).
% 1.01/1.05  
% 1.01/1.05  fof(f38,plain,(
% 1.01/1.05    ! [X0] : ((l1_orders_2(k3_lattice3(X0)) & v3_orders_2(k3_lattice3(X0))) | (~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 1.01/1.05    inference(ennf_transformation,[],[f19])).
% 1.01/1.05  
% 1.01/1.05  fof(f39,plain,(
% 1.01/1.05    ! [X0] : ((l1_orders_2(k3_lattice3(X0)) & v3_orders_2(k3_lattice3(X0))) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.01/1.05    inference(flattening,[],[f38])).
% 1.01/1.05  
% 1.01/1.05  fof(f85,plain,(
% 1.01/1.05    ( ! [X0] : (l1_orders_2(k3_lattice3(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 1.01/1.05    inference(cnf_transformation,[],[f39])).
% 1.01/1.05  
% 1.01/1.05  fof(f6,axiom,(
% 1.01/1.05    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k3_lattice3(X0))) => k5_lattice3(X0,X1) = X1))),
% 1.01/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.01/1.05  
% 1.01/1.05  fof(f34,plain,(
% 1.01/1.05    ! [X0] : (! [X1] : (k5_lattice3(X0,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(k3_lattice3(X0)))) | (~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 1.01/1.05    inference(ennf_transformation,[],[f6])).
% 1.01/1.05  
% 1.01/1.05  fof(f35,plain,(
% 1.01/1.05    ! [X0] : (! [X1] : (k5_lattice3(X0,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(k3_lattice3(X0)))) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.01/1.05    inference(flattening,[],[f34])).
% 1.01/1.05  
% 1.01/1.05  fof(f79,plain,(
% 1.01/1.05    ( ! [X0,X1] : (k5_lattice3(X0,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(k3_lattice3(X0))) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 1.01/1.05    inference(cnf_transformation,[],[f35])).
% 1.01/1.05  
% 1.01/1.05  fof(f97,plain,(
% 1.01/1.05    ~r2_lattice3(k3_lattice3(sK3),sK2,k4_lattice3(sK3,sK4)) | ~r4_lattice3(sK3,sK4,sK2)),
% 1.01/1.05    inference(cnf_transformation,[],[f65])).
% 1.01/1.05  
% 1.01/1.05  fof(f96,plain,(
% 1.01/1.05    r2_lattice3(k3_lattice3(sK3),sK2,k4_lattice3(sK3,sK4)) | r4_lattice3(sK3,sK4,sK2)),
% 1.01/1.05    inference(cnf_transformation,[],[f65])).
% 1.01/1.05  
% 1.01/1.05  fof(f80,plain,(
% 1.01/1.05    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.01/1.05    inference(cnf_transformation,[],[f59])).
% 1.01/1.05  
% 1.01/1.05  fof(f1,axiom,(
% 1.01/1.05    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 1.01/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.01/1.05  
% 1.01/1.05  fof(f24,plain,(
% 1.01/1.05    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.01/1.05    inference(ennf_transformation,[],[f1])).
% 1.01/1.05  
% 1.01/1.05  fof(f25,plain,(
% 1.01/1.05    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.01/1.05    inference(flattening,[],[f24])).
% 1.01/1.05  
% 1.01/1.05  fof(f50,plain,(
% 1.01/1.05    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.01/1.05    inference(nnf_transformation,[],[f25])).
% 1.01/1.05  
% 1.01/1.05  fof(f67,plain,(
% 1.01/1.05    ( ! [X2,X0,X1] : (r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.01/1.05    inference(cnf_transformation,[],[f50])).
% 1.01/1.05  
% 1.01/1.05  fof(f84,plain,(
% 1.01/1.05    ( ! [X0] : (v3_orders_2(k3_lattice3(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 1.01/1.05    inference(cnf_transformation,[],[f39])).
% 1.01/1.05  
% 1.01/1.05  fof(f11,axiom,(
% 1.01/1.05    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (v5_orders_2(k3_lattice3(X0)) & v4_orders_2(k3_lattice3(X0)) & v3_orders_2(k3_lattice3(X0)) & v1_orders_2(k3_lattice3(X0)) & ~v2_struct_0(k3_lattice3(X0))))),
% 1.01/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.01/1.05  
% 1.01/1.05  fof(f16,plain,(
% 1.01/1.05    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (v4_orders_2(k3_lattice3(X0)) & v3_orders_2(k3_lattice3(X0)) & v1_orders_2(k3_lattice3(X0)) & ~v2_struct_0(k3_lattice3(X0))))),
% 1.01/1.05    inference(pure_predicate_removal,[],[f11])).
% 1.01/1.05  
% 1.01/1.05  fof(f18,plain,(
% 1.01/1.05    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (v3_orders_2(k3_lattice3(X0)) & v1_orders_2(k3_lattice3(X0)) & ~v2_struct_0(k3_lattice3(X0))))),
% 1.01/1.05    inference(pure_predicate_removal,[],[f16])).
% 1.01/1.05  
% 1.01/1.05  fof(f20,plain,(
% 1.01/1.05    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (v3_orders_2(k3_lattice3(X0)) & ~v2_struct_0(k3_lattice3(X0))))),
% 1.01/1.05    inference(pure_predicate_removal,[],[f18])).
% 1.01/1.05  
% 1.01/1.05  fof(f44,plain,(
% 1.01/1.05    ! [X0] : ((v3_orders_2(k3_lattice3(X0)) & ~v2_struct_0(k3_lattice3(X0))) | (~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 1.01/1.05    inference(ennf_transformation,[],[f20])).
% 1.01/1.05  
% 1.01/1.05  fof(f45,plain,(
% 1.01/1.05    ! [X0] : ((v3_orders_2(k3_lattice3(X0)) & ~v2_struct_0(k3_lattice3(X0))) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.01/1.05    inference(flattening,[],[f44])).
% 1.01/1.05  
% 1.01/1.05  fof(f88,plain,(
% 1.01/1.05    ( ! [X0] : (~v2_struct_0(k3_lattice3(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 1.01/1.05    inference(cnf_transformation,[],[f45])).
% 1.01/1.05  
% 1.01/1.05  fof(f4,axiom,(
% 1.01/1.05    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X3,X1))))))),
% 1.01/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.01/1.05  
% 1.01/1.05  fof(f30,plain,(
% 1.01/1.05    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.01/1.05    inference(ennf_transformation,[],[f4])).
% 1.01/1.05  
% 1.01/1.05  fof(f31,plain,(
% 1.01/1.05    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.01/1.05    inference(flattening,[],[f30])).
% 1.01/1.05  
% 1.01/1.05  fof(f52,plain,(
% 1.01/1.05    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.01/1.05    inference(nnf_transformation,[],[f31])).
% 1.01/1.05  
% 1.01/1.05  fof(f53,plain,(
% 1.01/1.05    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.01/1.05    inference(rectify,[],[f52])).
% 1.01/1.05  
% 1.01/1.05  fof(f54,plain,(
% 1.01/1.05    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X2) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 1.01/1.05    introduced(choice_axiom,[])).
% 1.01/1.05  
% 1.01/1.05  fof(f55,plain,(
% 1.01/1.05    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | (~r1_lattices(X0,sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X2) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.01/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f53,f54])).
% 1.01/1.05  
% 1.01/1.05  fof(f75,plain,(
% 1.01/1.05    ( ! [X2,X0,X1] : (r4_lattice3(X0,X1,X2) | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.01/1.05    inference(cnf_transformation,[],[f55])).
% 1.01/1.05  
% 1.01/1.05  fof(f76,plain,(
% 1.01/1.05    ( ! [X2,X0,X1] : (r4_lattice3(X0,X1,X2) | r2_hidden(sK0(X0,X1,X2),X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.01/1.05    inference(cnf_transformation,[],[f55])).
% 1.01/1.05  
% 1.01/1.05  fof(f12,axiom,(
% 1.01/1.05    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2))))))),
% 1.01/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.01/1.05  
% 1.01/1.05  fof(f46,plain,(
% 1.01/1.05    ! [X0] : (! [X1] : (! [X2] : ((r3_lattices(X0,X1,X2) <=> r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 1.01/1.05    inference(ennf_transformation,[],[f12])).
% 1.01/1.05  
% 1.01/1.05  fof(f47,plain,(
% 1.01/1.05    ! [X0] : (! [X1] : (! [X2] : ((r3_lattices(X0,X1,X2) <=> r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.01/1.05    inference(flattening,[],[f46])).
% 1.01/1.05  
% 1.01/1.05  fof(f60,plain,(
% 1.01/1.05    ! [X0] : (! [X1] : (! [X2] : (((r3_lattices(X0,X1,X2) | ~r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2))) & (r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2)) | ~r3_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.01/1.05    inference(nnf_transformation,[],[f47])).
% 1.01/1.05  
% 1.01/1.05  fof(f91,plain,(
% 1.01/1.05    ( ! [X2,X0,X1] : (r3_lattices(X0,X1,X2) | ~r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 1.01/1.05    inference(cnf_transformation,[],[f60])).
% 1.01/1.05  
% 1.01/1.05  fof(f2,axiom,(
% 1.01/1.05    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 1.01/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.01/1.05  
% 1.01/1.05  fof(f21,plain,(
% 1.01/1.05    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 1.01/1.05    inference(pure_predicate_removal,[],[f2])).
% 1.01/1.05  
% 1.01/1.05  fof(f22,plain,(
% 1.01/1.05    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 1.01/1.05    inference(pure_predicate_removal,[],[f21])).
% 1.01/1.05  
% 1.01/1.05  fof(f23,plain,(
% 1.01/1.05    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0))))),
% 1.01/1.05    inference(pure_predicate_removal,[],[f22])).
% 1.01/1.05  
% 1.01/1.05  fof(f26,plain,(
% 1.01/1.05    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 1.01/1.05    inference(ennf_transformation,[],[f23])).
% 1.01/1.05  
% 1.01/1.05  fof(f27,plain,(
% 1.01/1.05    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 1.01/1.05    inference(flattening,[],[f26])).
% 1.01/1.05  
% 1.01/1.05  fof(f71,plain,(
% 1.01/1.05    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.01/1.05    inference(cnf_transformation,[],[f27])).
% 1.01/1.05  
% 1.01/1.05  fof(f3,axiom,(
% 1.01/1.05    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 1.01/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.01/1.05  
% 1.01/1.05  fof(f28,plain,(
% 1.01/1.05    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 1.01/1.05    inference(ennf_transformation,[],[f3])).
% 1.01/1.05  
% 1.01/1.05  fof(f29,plain,(
% 1.01/1.05    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 1.01/1.05    inference(flattening,[],[f28])).
% 1.01/1.05  
% 1.01/1.05  fof(f51,plain,(
% 1.01/1.05    ! [X0,X1,X2] : (((r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2)) & (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 1.01/1.05    inference(nnf_transformation,[],[f29])).
% 1.01/1.05  
% 1.01/1.05  fof(f72,plain,(
% 1.01/1.05    ( ! [X2,X0,X1] : (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 1.01/1.05    inference(cnf_transformation,[],[f51])).
% 1.01/1.05  
% 1.01/1.05  fof(f69,plain,(
% 1.01/1.05    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.01/1.05    inference(cnf_transformation,[],[f27])).
% 1.01/1.05  
% 1.01/1.05  fof(f70,plain,(
% 1.01/1.05    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.01/1.05    inference(cnf_transformation,[],[f27])).
% 1.01/1.05  
% 1.01/1.05  fof(f77,plain,(
% 1.01/1.05    ( ! [X2,X0,X1] : (r4_lattice3(X0,X1,X2) | ~r1_lattices(X0,sK0(X0,X1,X2),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.01/1.05    inference(cnf_transformation,[],[f55])).
% 1.01/1.05  
% 1.01/1.05  fof(f10,axiom,(
% 1.01/1.05    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(k3_lattice3(X0))) & l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k5_lattice3(X0,X1),u1_struct_0(X0)))),
% 1.01/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.01/1.05  
% 1.01/1.05  fof(f42,plain,(
% 1.01/1.05    ! [X0,X1] : (m1_subset_1(k5_lattice3(X0,X1),u1_struct_0(X0)) | (~m1_subset_1(X1,u1_struct_0(k3_lattice3(X0))) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 1.01/1.05    inference(ennf_transformation,[],[f10])).
% 1.01/1.05  
% 1.01/1.05  fof(f43,plain,(
% 1.01/1.05    ! [X0,X1] : (m1_subset_1(k5_lattice3(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(k3_lattice3(X0))) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.01/1.05    inference(flattening,[],[f42])).
% 1.01/1.05  
% 1.01/1.05  fof(f87,plain,(
% 1.01/1.05    ( ! [X0,X1] : (m1_subset_1(k5_lattice3(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(k3_lattice3(X0))) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 1.01/1.05    inference(cnf_transformation,[],[f43])).
% 1.01/1.05  
% 1.01/1.05  fof(f90,plain,(
% 1.01/1.05    ( ! [X2,X0,X1] : (r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2)) | ~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 1.01/1.05    inference(cnf_transformation,[],[f60])).
% 1.01/1.05  
% 1.01/1.05  fof(f73,plain,(
% 1.01/1.05    ( ! [X2,X0,X1] : (r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 1.01/1.05    inference(cnf_transformation,[],[f51])).
% 1.01/1.05  
% 1.01/1.05  fof(f74,plain,(
% 1.01/1.05    ( ! [X4,X2,X0,X1] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r4_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.01/1.05    inference(cnf_transformation,[],[f55])).
% 1.01/1.05  
% 1.01/1.05  fof(f82,plain,(
% 1.01/1.05    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | r2_hidden(sK1(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.01/1.05    inference(cnf_transformation,[],[f59])).
% 1.01/1.05  
% 1.01/1.05  fof(f83,plain,(
% 1.01/1.05    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | ~r1_orders_2(X0,sK1(X0,X1,X2),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.01/1.05    inference(cnf_transformation,[],[f59])).
% 1.01/1.05  
% 1.01/1.05  fof(f66,plain,(
% 1.01/1.05    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.01/1.05    inference(cnf_transformation,[],[f50])).
% 1.01/1.05  
% 1.01/1.05  cnf(c_28,negated_conjecture,
% 1.01/1.05      ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 1.01/1.05      inference(cnf_transformation,[],[f95]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_2586,negated_conjecture,
% 1.01/1.05      ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 1.01/1.05      inference(subtyping,[status(esa)],[c_28]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_3056,plain,
% 1.01/1.05      ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
% 1.01/1.05      inference(predicate_to_equality,[status(thm)],[c_2586]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_12,plain,
% 1.01/1.05      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.01/1.05      | ~ l3_lattices(X1)
% 1.01/1.05      | ~ v10_lattices(X1)
% 1.01/1.05      | v2_struct_0(X1)
% 1.01/1.05      | k4_lattice3(X1,X0) = X0 ),
% 1.01/1.05      inference(cnf_transformation,[],[f78]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_30,negated_conjecture,
% 1.01/1.05      ( v10_lattices(sK3) ),
% 1.01/1.05      inference(cnf_transformation,[],[f93]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_1566,plain,
% 1.01/1.05      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.01/1.05      | ~ l3_lattices(X1)
% 1.01/1.05      | v2_struct_0(X1)
% 1.01/1.05      | k4_lattice3(X1,X0) = X0
% 1.01/1.05      | sK3 != X1 ),
% 1.01/1.05      inference(resolution_lifted,[status(thm)],[c_12,c_30]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_1567,plain,
% 1.01/1.05      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.01/1.05      | ~ l3_lattices(sK3)
% 1.01/1.05      | v2_struct_0(sK3)
% 1.01/1.05      | k4_lattice3(sK3,X0) = X0 ),
% 1.01/1.05      inference(unflattening,[status(thm)],[c_1566]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_31,negated_conjecture,
% 1.01/1.05      ( ~ v2_struct_0(sK3) ),
% 1.01/1.05      inference(cnf_transformation,[],[f92]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_29,negated_conjecture,
% 1.01/1.05      ( l3_lattices(sK3) ),
% 1.01/1.05      inference(cnf_transformation,[],[f94]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_1571,plain,
% 1.01/1.05      ( ~ m1_subset_1(X0,u1_struct_0(sK3)) | k4_lattice3(sK3,X0) = X0 ),
% 1.01/1.05      inference(global_propositional_subsumption,
% 1.01/1.05                [status(thm)],
% 1.01/1.05                [c_1567,c_31,c_29]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_2578,plain,
% 1.01/1.05      ( ~ m1_subset_1(X0_54,u1_struct_0(sK3))
% 1.01/1.05      | k4_lattice3(sK3,X0_54) = X0_54 ),
% 1.01/1.05      inference(subtyping,[status(esa)],[c_1571]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_3064,plain,
% 1.01/1.05      ( k4_lattice3(sK3,X0_54) = X0_54
% 1.01/1.05      | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top ),
% 1.01/1.05      inference(predicate_to_equality,[status(thm)],[c_2578]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_3262,plain,
% 1.01/1.05      ( k4_lattice3(sK3,sK4) = sK4 ),
% 1.01/1.05      inference(superposition,[status(thm)],[c_3056,c_3064]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_20,plain,
% 1.01/1.05      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.01/1.05      | m1_subset_1(k4_lattice3(X1,X0),u1_struct_0(k3_lattice3(X1)))
% 1.01/1.05      | ~ l3_lattices(X1)
% 1.01/1.05      | ~ v10_lattices(X1)
% 1.01/1.05      | v2_struct_0(X1) ),
% 1.01/1.05      inference(cnf_transformation,[],[f86]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_1530,plain,
% 1.01/1.05      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.01/1.05      | m1_subset_1(k4_lattice3(X1,X0),u1_struct_0(k3_lattice3(X1)))
% 1.01/1.05      | ~ l3_lattices(X1)
% 1.01/1.05      | v2_struct_0(X1)
% 1.01/1.05      | sK3 != X1 ),
% 1.01/1.05      inference(resolution_lifted,[status(thm)],[c_20,c_30]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_1531,plain,
% 1.01/1.05      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.01/1.05      | m1_subset_1(k4_lattice3(sK3,X0),u1_struct_0(k3_lattice3(sK3)))
% 1.01/1.05      | ~ l3_lattices(sK3)
% 1.01/1.05      | v2_struct_0(sK3) ),
% 1.01/1.05      inference(unflattening,[status(thm)],[c_1530]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_1535,plain,
% 1.01/1.05      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.01/1.05      | m1_subset_1(k4_lattice3(sK3,X0),u1_struct_0(k3_lattice3(sK3))) ),
% 1.01/1.05      inference(global_propositional_subsumption,
% 1.01/1.05                [status(thm)],
% 1.01/1.05                [c_1531,c_31,c_29]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_2580,plain,
% 1.01/1.05      ( ~ m1_subset_1(X0_54,u1_struct_0(sK3))
% 1.01/1.05      | m1_subset_1(k4_lattice3(sK3,X0_54),u1_struct_0(k3_lattice3(sK3))) ),
% 1.01/1.05      inference(subtyping,[status(esa)],[c_1535]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_3062,plain,
% 1.01/1.05      ( m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top
% 1.01/1.05      | m1_subset_1(k4_lattice3(sK3,X0_54),u1_struct_0(k3_lattice3(sK3))) = iProver_top ),
% 1.01/1.05      inference(predicate_to_equality,[status(thm)],[c_2580]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_3455,plain,
% 1.01/1.05      ( m1_subset_1(sK4,u1_struct_0(k3_lattice3(sK3))) = iProver_top
% 1.01/1.05      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
% 1.01/1.05      inference(superposition,[status(thm)],[c_3262,c_3062]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_35,plain,
% 1.01/1.05      ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
% 1.01/1.05      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_2590,plain,( X0_54 = X0_54 ),theory(equality) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_2605,plain,
% 1.01/1.05      ( sK4 = sK4 ),
% 1.01/1.05      inference(instantiation,[status(thm)],[c_2590]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_2624,plain,
% 1.01/1.05      ( m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top
% 1.01/1.05      | m1_subset_1(k4_lattice3(sK3,X0_54),u1_struct_0(k3_lattice3(sK3))) = iProver_top ),
% 1.01/1.05      inference(predicate_to_equality,[status(thm)],[c_2580]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_2626,plain,
% 1.01/1.05      ( m1_subset_1(k4_lattice3(sK3,sK4),u1_struct_0(k3_lattice3(sK3))) = iProver_top
% 1.01/1.05      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
% 1.01/1.05      inference(instantiation,[status(thm)],[c_2624]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_2631,plain,
% 1.01/1.05      ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 1.01/1.05      | k4_lattice3(sK3,sK4) = sK4 ),
% 1.01/1.05      inference(instantiation,[status(thm)],[c_2578]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_2593,plain,
% 1.01/1.05      ( ~ m1_subset_1(X0_54,X0_56)
% 1.01/1.05      | m1_subset_1(X1_54,X0_56)
% 1.01/1.05      | X1_54 != X0_54 ),
% 1.01/1.05      theory(equality) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_3249,plain,
% 1.01/1.05      ( m1_subset_1(X0_54,u1_struct_0(k3_lattice3(sK3)))
% 1.01/1.05      | ~ m1_subset_1(k4_lattice3(sK3,X1_54),u1_struct_0(k3_lattice3(sK3)))
% 1.01/1.05      | X0_54 != k4_lattice3(sK3,X1_54) ),
% 1.01/1.05      inference(instantiation,[status(thm)],[c_2593]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_3250,plain,
% 1.01/1.05      ( X0_54 != k4_lattice3(sK3,X1_54)
% 1.01/1.05      | m1_subset_1(X0_54,u1_struct_0(k3_lattice3(sK3))) = iProver_top
% 1.01/1.05      | m1_subset_1(k4_lattice3(sK3,X1_54),u1_struct_0(k3_lattice3(sK3))) != iProver_top ),
% 1.01/1.05      inference(predicate_to_equality,[status(thm)],[c_3249]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_3252,plain,
% 1.01/1.05      ( sK4 != k4_lattice3(sK3,sK4)
% 1.01/1.05      | m1_subset_1(k4_lattice3(sK3,sK4),u1_struct_0(k3_lattice3(sK3))) != iProver_top
% 1.01/1.05      | m1_subset_1(sK4,u1_struct_0(k3_lattice3(sK3))) = iProver_top ),
% 1.01/1.05      inference(instantiation,[status(thm)],[c_3250]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_2591,plain,
% 1.01/1.05      ( X0_54 != X1_54 | X2_54 != X1_54 | X2_54 = X0_54 ),
% 1.01/1.05      theory(equality) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_3278,plain,
% 1.01/1.05      ( X0_54 != X1_54
% 1.01/1.05      | X0_54 = k4_lattice3(sK3,X2_54)
% 1.01/1.05      | k4_lattice3(sK3,X2_54) != X1_54 ),
% 1.01/1.05      inference(instantiation,[status(thm)],[c_2591]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_3279,plain,
% 1.01/1.05      ( k4_lattice3(sK3,sK4) != sK4
% 1.01/1.05      | sK4 = k4_lattice3(sK3,sK4)
% 1.01/1.05      | sK4 != sK4 ),
% 1.01/1.05      inference(instantiation,[status(thm)],[c_3278]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_3595,plain,
% 1.01/1.05      ( m1_subset_1(sK4,u1_struct_0(k3_lattice3(sK3))) = iProver_top ),
% 1.01/1.05      inference(global_propositional_subsumption,
% 1.01/1.05                [status(thm)],
% 1.01/1.05                [c_3455,c_28,c_35,c_2605,c_2626,c_2631,c_3252,c_3279]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_16,plain,
% 1.01/1.05      ( r2_lattice3(X0,X1,X2)
% 1.01/1.05      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.01/1.05      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
% 1.01/1.05      | ~ l1_orders_2(X0) ),
% 1.01/1.05      inference(cnf_transformation,[],[f81]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_18,plain,
% 1.01/1.05      ( ~ l3_lattices(X0)
% 1.01/1.05      | ~ v10_lattices(X0)
% 1.01/1.05      | v2_struct_0(X0)
% 1.01/1.05      | l1_orders_2(k3_lattice3(X0)) ),
% 1.01/1.05      inference(cnf_transformation,[],[f85]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_1501,plain,
% 1.01/1.05      ( ~ l3_lattices(X0)
% 1.01/1.05      | v2_struct_0(X0)
% 1.01/1.05      | l1_orders_2(k3_lattice3(X0))
% 1.01/1.05      | sK3 != X0 ),
% 1.01/1.05      inference(resolution_lifted,[status(thm)],[c_18,c_30]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_1502,plain,
% 1.01/1.05      ( ~ l3_lattices(sK3)
% 1.01/1.05      | v2_struct_0(sK3)
% 1.01/1.05      | l1_orders_2(k3_lattice3(sK3)) ),
% 1.01/1.05      inference(unflattening,[status(thm)],[c_1501]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_58,plain,
% 1.01/1.05      ( ~ l3_lattices(sK3)
% 1.01/1.05      | ~ v10_lattices(sK3)
% 1.01/1.05      | v2_struct_0(sK3)
% 1.01/1.05      | l1_orders_2(k3_lattice3(sK3)) ),
% 1.01/1.05      inference(instantiation,[status(thm)],[c_18]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_1504,plain,
% 1.01/1.05      ( l1_orders_2(k3_lattice3(sK3)) ),
% 1.01/1.05      inference(global_propositional_subsumption,
% 1.01/1.05                [status(thm)],
% 1.01/1.05                [c_1502,c_31,c_30,c_29,c_58]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_1636,plain,
% 1.01/1.05      ( r2_lattice3(X0,X1,X2)
% 1.01/1.05      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.01/1.05      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
% 1.01/1.05      | k3_lattice3(sK3) != X0 ),
% 1.01/1.05      inference(resolution_lifted,[status(thm)],[c_16,c_1504]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_1637,plain,
% 1.01/1.05      ( r2_lattice3(k3_lattice3(sK3),X0,X1)
% 1.01/1.05      | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(sK3)))
% 1.01/1.05      | m1_subset_1(sK1(k3_lattice3(sK3),X0,X1),u1_struct_0(k3_lattice3(sK3))) ),
% 1.01/1.05      inference(unflattening,[status(thm)],[c_1636]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_2576,plain,
% 1.01/1.05      ( r2_lattice3(k3_lattice3(sK3),X0_55,X0_54)
% 1.01/1.05      | ~ m1_subset_1(X0_54,u1_struct_0(k3_lattice3(sK3)))
% 1.01/1.05      | m1_subset_1(sK1(k3_lattice3(sK3),X0_55,X0_54),u1_struct_0(k3_lattice3(sK3))) ),
% 1.01/1.05      inference(subtyping,[status(esa)],[c_1637]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_3066,plain,
% 1.01/1.05      ( r2_lattice3(k3_lattice3(sK3),X0_55,X0_54) = iProver_top
% 1.01/1.05      | m1_subset_1(X0_54,u1_struct_0(k3_lattice3(sK3))) != iProver_top
% 1.01/1.05      | m1_subset_1(sK1(k3_lattice3(sK3),X0_55,X0_54),u1_struct_0(k3_lattice3(sK3))) = iProver_top ),
% 1.01/1.05      inference(predicate_to_equality,[status(thm)],[c_2576]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_13,plain,
% 1.01/1.05      ( ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(X1)))
% 1.01/1.05      | ~ l3_lattices(X1)
% 1.01/1.05      | ~ v10_lattices(X1)
% 1.01/1.05      | v2_struct_0(X1)
% 1.01/1.05      | k5_lattice3(X1,X0) = X0 ),
% 1.01/1.05      inference(cnf_transformation,[],[f79]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_1548,plain,
% 1.01/1.05      ( ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(X1)))
% 1.01/1.05      | ~ l3_lattices(X1)
% 1.01/1.05      | v2_struct_0(X1)
% 1.01/1.05      | k5_lattice3(X1,X0) = X0
% 1.01/1.05      | sK3 != X1 ),
% 1.01/1.05      inference(resolution_lifted,[status(thm)],[c_13,c_30]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_1549,plain,
% 1.01/1.05      ( ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(sK3)))
% 1.01/1.05      | ~ l3_lattices(sK3)
% 1.01/1.05      | v2_struct_0(sK3)
% 1.01/1.05      | k5_lattice3(sK3,X0) = X0 ),
% 1.01/1.05      inference(unflattening,[status(thm)],[c_1548]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_1553,plain,
% 1.01/1.05      ( ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(sK3)))
% 1.01/1.05      | k5_lattice3(sK3,X0) = X0 ),
% 1.01/1.05      inference(global_propositional_subsumption,
% 1.01/1.05                [status(thm)],
% 1.01/1.05                [c_1549,c_31,c_29]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_2579,plain,
% 1.01/1.05      ( ~ m1_subset_1(X0_54,u1_struct_0(k3_lattice3(sK3)))
% 1.01/1.05      | k5_lattice3(sK3,X0_54) = X0_54 ),
% 1.01/1.05      inference(subtyping,[status(esa)],[c_1553]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_3063,plain,
% 1.01/1.05      ( k5_lattice3(sK3,X0_54) = X0_54
% 1.01/1.05      | m1_subset_1(X0_54,u1_struct_0(k3_lattice3(sK3))) != iProver_top ),
% 1.01/1.05      inference(predicate_to_equality,[status(thm)],[c_2579]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_3432,plain,
% 1.01/1.05      ( k5_lattice3(sK3,sK1(k3_lattice3(sK3),X0_55,X0_54)) = sK1(k3_lattice3(sK3),X0_55,X0_54)
% 1.01/1.05      | r2_lattice3(k3_lattice3(sK3),X0_55,X0_54) = iProver_top
% 1.01/1.05      | m1_subset_1(X0_54,u1_struct_0(k3_lattice3(sK3))) != iProver_top ),
% 1.01/1.05      inference(superposition,[status(thm)],[c_3066,c_3063]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_3776,plain,
% 1.01/1.05      ( k5_lattice3(sK3,sK1(k3_lattice3(sK3),X0_55,sK4)) = sK1(k3_lattice3(sK3),X0_55,sK4)
% 1.01/1.05      | r2_lattice3(k3_lattice3(sK3),X0_55,sK4) = iProver_top ),
% 1.01/1.05      inference(superposition,[status(thm)],[c_3595,c_3432]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_26,negated_conjecture,
% 1.01/1.05      ( ~ r2_lattice3(k3_lattice3(sK3),sK2,k4_lattice3(sK3,sK4))
% 1.01/1.05      | ~ r4_lattice3(sK3,sK4,sK2) ),
% 1.01/1.05      inference(cnf_transformation,[],[f97]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_2588,negated_conjecture,
% 1.01/1.05      ( ~ r2_lattice3(k3_lattice3(sK3),sK2,k4_lattice3(sK3,sK4))
% 1.01/1.05      | ~ r4_lattice3(sK3,sK4,sK2) ),
% 1.01/1.05      inference(subtyping,[status(esa)],[c_26]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_3054,plain,
% 1.01/1.05      ( r2_lattice3(k3_lattice3(sK3),sK2,k4_lattice3(sK3,sK4)) != iProver_top
% 1.01/1.05      | r4_lattice3(sK3,sK4,sK2) != iProver_top ),
% 1.01/1.05      inference(predicate_to_equality,[status(thm)],[c_2588]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_3291,plain,
% 1.01/1.05      ( r2_lattice3(k3_lattice3(sK3),sK2,sK4) != iProver_top
% 1.01/1.05      | r4_lattice3(sK3,sK4,sK2) != iProver_top ),
% 1.01/1.05      inference(demodulation,[status(thm)],[c_3262,c_3054]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_7946,plain,
% 1.01/1.05      ( k5_lattice3(sK3,sK1(k3_lattice3(sK3),sK2,sK4)) = sK1(k3_lattice3(sK3),sK2,sK4)
% 1.01/1.05      | r4_lattice3(sK3,sK4,sK2) != iProver_top ),
% 1.01/1.05      inference(superposition,[status(thm)],[c_3776,c_3291]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_3434,plain,
% 1.01/1.05      ( k5_lattice3(sK3,sK1(k3_lattice3(sK3),sK2,sK4)) = sK1(k3_lattice3(sK3),sK2,sK4)
% 1.01/1.05      | r2_lattice3(k3_lattice3(sK3),sK2,sK4) = iProver_top
% 1.01/1.05      | m1_subset_1(sK4,u1_struct_0(k3_lattice3(sK3))) != iProver_top ),
% 1.01/1.05      inference(instantiation,[status(thm)],[c_3432]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_27,negated_conjecture,
% 1.01/1.05      ( r2_lattice3(k3_lattice3(sK3),sK2,k4_lattice3(sK3,sK4))
% 1.01/1.05      | r4_lattice3(sK3,sK4,sK2) ),
% 1.01/1.05      inference(cnf_transformation,[],[f96]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_2587,negated_conjecture,
% 1.01/1.05      ( r2_lattice3(k3_lattice3(sK3),sK2,k4_lattice3(sK3,sK4))
% 1.01/1.05      | r4_lattice3(sK3,sK4,sK2) ),
% 1.01/1.05      inference(subtyping,[status(esa)],[c_27]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_3055,plain,
% 1.01/1.05      ( r2_lattice3(k3_lattice3(sK3),sK2,k4_lattice3(sK3,sK4)) = iProver_top
% 1.01/1.05      | r4_lattice3(sK3,sK4,sK2) = iProver_top ),
% 1.01/1.05      inference(predicate_to_equality,[status(thm)],[c_2587]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_3290,plain,
% 1.01/1.05      ( r2_lattice3(k3_lattice3(sK3),sK2,sK4) = iProver_top
% 1.01/1.05      | r4_lattice3(sK3,sK4,sK2) = iProver_top ),
% 1.01/1.05      inference(demodulation,[status(thm)],[c_3262,c_3055]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_17,plain,
% 1.01/1.05      ( ~ r2_lattice3(X0,X1,X2)
% 1.01/1.05      | r1_orders_2(X0,X3,X2)
% 1.01/1.05      | ~ r2_hidden(X3,X1)
% 1.01/1.05      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.01/1.05      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.01/1.05      | ~ l1_orders_2(X0) ),
% 1.01/1.05      inference(cnf_transformation,[],[f80]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_0,plain,
% 1.01/1.05      ( ~ r1_orders_2(X0,X1,X2)
% 1.01/1.05      | r3_orders_2(X0,X1,X2)
% 1.01/1.05      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.01/1.05      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.01/1.05      | v2_struct_0(X0)
% 1.01/1.05      | ~ v3_orders_2(X0)
% 1.01/1.05      | ~ l1_orders_2(X0) ),
% 1.01/1.05      inference(cnf_transformation,[],[f67]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_19,plain,
% 1.01/1.05      ( ~ l3_lattices(X0)
% 1.01/1.05      | ~ v10_lattices(X0)
% 1.01/1.05      | v2_struct_0(X0)
% 1.01/1.05      | v3_orders_2(k3_lattice3(X0)) ),
% 1.01/1.05      inference(cnf_transformation,[],[f84]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_444,plain,
% 1.01/1.05      ( ~ r1_orders_2(X0,X1,X2)
% 1.01/1.05      | r3_orders_2(X0,X1,X2)
% 1.01/1.05      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.01/1.05      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.01/1.05      | ~ l3_lattices(X3)
% 1.01/1.05      | ~ v10_lattices(X3)
% 1.01/1.05      | v2_struct_0(X0)
% 1.01/1.05      | v2_struct_0(X3)
% 1.01/1.05      | ~ l1_orders_2(X0)
% 1.01/1.05      | k3_lattice3(X3) != X0 ),
% 1.01/1.05      inference(resolution_lifted,[status(thm)],[c_0,c_19]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_445,plain,
% 1.01/1.05      ( ~ r1_orders_2(k3_lattice3(X0),X1,X2)
% 1.01/1.05      | r3_orders_2(k3_lattice3(X0),X1,X2)
% 1.01/1.05      | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(X0)))
% 1.01/1.05      | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(X0)))
% 1.01/1.05      | ~ l3_lattices(X0)
% 1.01/1.05      | ~ v10_lattices(X0)
% 1.01/1.05      | v2_struct_0(X0)
% 1.01/1.05      | v2_struct_0(k3_lattice3(X0))
% 1.01/1.05      | ~ l1_orders_2(k3_lattice3(X0)) ),
% 1.01/1.05      inference(unflattening,[status(thm)],[c_444]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_23,plain,
% 1.01/1.05      ( ~ l3_lattices(X0)
% 1.01/1.05      | ~ v10_lattices(X0)
% 1.01/1.05      | v2_struct_0(X0)
% 1.01/1.05      | ~ v2_struct_0(k3_lattice3(X0)) ),
% 1.01/1.05      inference(cnf_transformation,[],[f88]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_449,plain,
% 1.01/1.05      ( ~ r1_orders_2(k3_lattice3(X0),X1,X2)
% 1.01/1.05      | r3_orders_2(k3_lattice3(X0),X1,X2)
% 1.01/1.05      | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(X0)))
% 1.01/1.05      | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(X0)))
% 1.01/1.05      | ~ l3_lattices(X0)
% 1.01/1.05      | ~ v10_lattices(X0)
% 1.01/1.05      | v2_struct_0(X0) ),
% 1.01/1.05      inference(global_propositional_subsumption,
% 1.01/1.05                [status(thm)],
% 1.01/1.05                [c_445,c_23,c_18]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_918,plain,
% 1.01/1.05      ( ~ r2_lattice3(X0,X1,X2)
% 1.01/1.05      | r3_orders_2(k3_lattice3(X3),X4,X5)
% 1.01/1.05      | ~ r2_hidden(X6,X1)
% 1.01/1.05      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.01/1.05      | ~ m1_subset_1(X6,u1_struct_0(X0))
% 1.01/1.05      | ~ m1_subset_1(X4,u1_struct_0(k3_lattice3(X3)))
% 1.01/1.05      | ~ m1_subset_1(X5,u1_struct_0(k3_lattice3(X3)))
% 1.01/1.05      | ~ l3_lattices(X3)
% 1.01/1.05      | ~ v10_lattices(X3)
% 1.01/1.05      | v2_struct_0(X3)
% 1.01/1.05      | ~ l1_orders_2(X0)
% 1.01/1.05      | X5 != X2
% 1.01/1.05      | X4 != X6
% 1.01/1.05      | k3_lattice3(X3) != X0 ),
% 1.01/1.05      inference(resolution_lifted,[status(thm)],[c_17,c_449]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_919,plain,
% 1.01/1.05      ( ~ r2_lattice3(k3_lattice3(X0),X1,X2)
% 1.01/1.05      | r3_orders_2(k3_lattice3(X0),X3,X2)
% 1.01/1.05      | ~ r2_hidden(X3,X1)
% 1.01/1.05      | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(X0)))
% 1.01/1.05      | ~ m1_subset_1(X3,u1_struct_0(k3_lattice3(X0)))
% 1.01/1.05      | ~ l3_lattices(X0)
% 1.01/1.05      | ~ v10_lattices(X0)
% 1.01/1.05      | v2_struct_0(X0)
% 1.01/1.05      | ~ l1_orders_2(k3_lattice3(X0)) ),
% 1.01/1.05      inference(unflattening,[status(thm)],[c_918]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_923,plain,
% 1.01/1.05      ( v2_struct_0(X0)
% 1.01/1.05      | ~ v10_lattices(X0)
% 1.01/1.05      | ~ l3_lattices(X0)
% 1.01/1.05      | ~ m1_subset_1(X3,u1_struct_0(k3_lattice3(X0)))
% 1.01/1.05      | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(X0)))
% 1.01/1.05      | ~ r2_hidden(X3,X1)
% 1.01/1.05      | r3_orders_2(k3_lattice3(X0),X3,X2)
% 1.01/1.05      | ~ r2_lattice3(k3_lattice3(X0),X1,X2) ),
% 1.01/1.05      inference(global_propositional_subsumption,
% 1.01/1.05                [status(thm)],
% 1.01/1.05                [c_919,c_18]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_924,plain,
% 1.01/1.05      ( ~ r2_lattice3(k3_lattice3(X0),X1,X2)
% 1.01/1.05      | r3_orders_2(k3_lattice3(X0),X3,X2)
% 1.01/1.05      | ~ r2_hidden(X3,X1)
% 1.01/1.05      | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(X0)))
% 1.01/1.05      | ~ m1_subset_1(X3,u1_struct_0(k3_lattice3(X0)))
% 1.01/1.05      | ~ l3_lattices(X0)
% 1.01/1.05      | ~ v10_lattices(X0)
% 1.01/1.05      | v2_struct_0(X0) ),
% 1.01/1.05      inference(renaming,[status(thm)],[c_923]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_1442,plain,
% 1.01/1.05      ( ~ r2_lattice3(k3_lattice3(X0),X1,X2)
% 1.01/1.05      | r3_orders_2(k3_lattice3(X0),X3,X2)
% 1.01/1.05      | ~ r2_hidden(X3,X1)
% 1.01/1.05      | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(X0)))
% 1.01/1.05      | ~ m1_subset_1(X3,u1_struct_0(k3_lattice3(X0)))
% 1.01/1.05      | ~ l3_lattices(X0)
% 1.01/1.05      | v2_struct_0(X0)
% 1.01/1.05      | sK3 != X0 ),
% 1.01/1.05      inference(resolution_lifted,[status(thm)],[c_924,c_30]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_1443,plain,
% 1.01/1.05      ( ~ r2_lattice3(k3_lattice3(sK3),X0,X1)
% 1.01/1.05      | r3_orders_2(k3_lattice3(sK3),X2,X1)
% 1.01/1.05      | ~ r2_hidden(X2,X0)
% 1.01/1.05      | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(sK3)))
% 1.01/1.05      | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(sK3)))
% 1.01/1.05      | ~ l3_lattices(sK3)
% 1.01/1.05      | v2_struct_0(sK3) ),
% 1.01/1.05      inference(unflattening,[status(thm)],[c_1442]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_1447,plain,
% 1.01/1.05      ( ~ r2_lattice3(k3_lattice3(sK3),X0,X1)
% 1.01/1.05      | r3_orders_2(k3_lattice3(sK3),X2,X1)
% 1.01/1.05      | ~ r2_hidden(X2,X0)
% 1.01/1.05      | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(sK3)))
% 1.01/1.05      | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(sK3))) ),
% 1.01/1.05      inference(global_propositional_subsumption,
% 1.01/1.05                [status(thm)],
% 1.01/1.05                [c_1443,c_31,c_29]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_2583,plain,
% 1.01/1.05      ( ~ r2_lattice3(k3_lattice3(sK3),X0_55,X0_54)
% 1.01/1.05      | r3_orders_2(k3_lattice3(sK3),X1_54,X0_54)
% 1.01/1.05      | ~ r2_hidden(X1_54,X0_55)
% 1.01/1.05      | ~ m1_subset_1(X1_54,u1_struct_0(k3_lattice3(sK3)))
% 1.01/1.05      | ~ m1_subset_1(X0_54,u1_struct_0(k3_lattice3(sK3))) ),
% 1.01/1.05      inference(subtyping,[status(esa)],[c_1447]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_3059,plain,
% 1.01/1.05      ( r2_lattice3(k3_lattice3(sK3),X0_55,X0_54) != iProver_top
% 1.01/1.05      | r3_orders_2(k3_lattice3(sK3),X1_54,X0_54) = iProver_top
% 1.01/1.05      | r2_hidden(X1_54,X0_55) != iProver_top
% 1.01/1.05      | m1_subset_1(X1_54,u1_struct_0(k3_lattice3(sK3))) != iProver_top
% 1.01/1.05      | m1_subset_1(X0_54,u1_struct_0(k3_lattice3(sK3))) != iProver_top ),
% 1.01/1.05      inference(predicate_to_equality,[status(thm)],[c_2583]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_3516,plain,
% 1.01/1.05      ( r2_lattice3(k3_lattice3(sK3),X0_55,X0_54) != iProver_top
% 1.01/1.05      | r3_orders_2(k3_lattice3(sK3),k4_lattice3(sK3,X1_54),X0_54) = iProver_top
% 1.01/1.05      | r2_hidden(k4_lattice3(sK3,X1_54),X0_55) != iProver_top
% 1.01/1.05      | m1_subset_1(X0_54,u1_struct_0(k3_lattice3(sK3))) != iProver_top
% 1.01/1.05      | m1_subset_1(X1_54,u1_struct_0(sK3)) != iProver_top ),
% 1.01/1.05      inference(superposition,[status(thm)],[c_3062,c_3059]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_4951,plain,
% 1.01/1.05      ( r4_lattice3(sK3,sK4,sK2) = iProver_top
% 1.01/1.05      | r3_orders_2(k3_lattice3(sK3),k4_lattice3(sK3,X0_54),sK4) = iProver_top
% 1.01/1.05      | r2_hidden(k4_lattice3(sK3,X0_54),sK2) != iProver_top
% 1.01/1.05      | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top
% 1.01/1.05      | m1_subset_1(sK4,u1_struct_0(k3_lattice3(sK3))) != iProver_top ),
% 1.01/1.05      inference(superposition,[status(thm)],[c_3290,c_3516]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_10,plain,
% 1.01/1.05      ( r4_lattice3(X0,X1,X2)
% 1.01/1.05      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.01/1.05      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 1.01/1.05      | ~ l3_lattices(X0)
% 1.01/1.05      | v2_struct_0(X0) ),
% 1.01/1.05      inference(cnf_transformation,[],[f75]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_1699,plain,
% 1.01/1.05      ( r4_lattice3(X0,X1,X2)
% 1.01/1.05      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.01/1.05      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 1.01/1.05      | v2_struct_0(X0)
% 1.01/1.05      | sK3 != X0 ),
% 1.01/1.05      inference(resolution_lifted,[status(thm)],[c_10,c_29]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_1700,plain,
% 1.01/1.05      ( r4_lattice3(sK3,X0,X1)
% 1.01/1.05      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.01/1.05      | m1_subset_1(sK0(sK3,X0,X1),u1_struct_0(sK3))
% 1.01/1.05      | v2_struct_0(sK3) ),
% 1.01/1.05      inference(unflattening,[status(thm)],[c_1699]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_1704,plain,
% 1.01/1.05      ( m1_subset_1(sK0(sK3,X0,X1),u1_struct_0(sK3))
% 1.01/1.05      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.01/1.05      | r4_lattice3(sK3,X0,X1) ),
% 1.01/1.05      inference(global_propositional_subsumption,
% 1.01/1.05                [status(thm)],
% 1.01/1.05                [c_1700,c_31]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_1705,plain,
% 1.01/1.05      ( r4_lattice3(sK3,X0,X1)
% 1.01/1.05      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.01/1.05      | m1_subset_1(sK0(sK3,X0,X1),u1_struct_0(sK3)) ),
% 1.01/1.05      inference(renaming,[status(thm)],[c_1704]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_2573,plain,
% 1.01/1.05      ( r4_lattice3(sK3,X0_54,X0_55)
% 1.01/1.05      | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
% 1.01/1.05      | m1_subset_1(sK0(sK3,X0_54,X0_55),u1_struct_0(sK3)) ),
% 1.01/1.05      inference(subtyping,[status(esa)],[c_1705]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_2641,plain,
% 1.01/1.05      ( r4_lattice3(sK3,X0_54,X0_55) = iProver_top
% 1.01/1.05      | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top
% 1.01/1.05      | m1_subset_1(sK0(sK3,X0_54,X0_55),u1_struct_0(sK3)) = iProver_top ),
% 1.01/1.05      inference(predicate_to_equality,[status(thm)],[c_2573]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_2643,plain,
% 1.01/1.05      ( r4_lattice3(sK3,sK4,sK2) = iProver_top
% 1.01/1.05      | m1_subset_1(sK0(sK3,sK4,sK2),u1_struct_0(sK3)) = iProver_top
% 1.01/1.05      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
% 1.01/1.05      inference(instantiation,[status(thm)],[c_2641]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_9,plain,
% 1.01/1.05      ( r4_lattice3(X0,X1,X2)
% 1.01/1.05      | r2_hidden(sK0(X0,X1,X2),X2)
% 1.01/1.05      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.01/1.05      | ~ l3_lattices(X0)
% 1.01/1.05      | v2_struct_0(X0) ),
% 1.01/1.05      inference(cnf_transformation,[],[f76]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_1720,plain,
% 1.01/1.05      ( r4_lattice3(X0,X1,X2)
% 1.01/1.05      | r2_hidden(sK0(X0,X1,X2),X2)
% 1.01/1.05      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.01/1.05      | v2_struct_0(X0)
% 1.01/1.05      | sK3 != X0 ),
% 1.01/1.05      inference(resolution_lifted,[status(thm)],[c_9,c_29]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_1721,plain,
% 1.01/1.05      ( r4_lattice3(sK3,X0,X1)
% 1.01/1.05      | r2_hidden(sK0(sK3,X0,X1),X1)
% 1.01/1.05      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.01/1.05      | v2_struct_0(sK3) ),
% 1.01/1.05      inference(unflattening,[status(thm)],[c_1720]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_1725,plain,
% 1.01/1.05      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.01/1.05      | r2_hidden(sK0(sK3,X0,X1),X1)
% 1.01/1.05      | r4_lattice3(sK3,X0,X1) ),
% 1.01/1.05      inference(global_propositional_subsumption,
% 1.01/1.05                [status(thm)],
% 1.01/1.05                [c_1721,c_31]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_1726,plain,
% 1.01/1.05      ( r4_lattice3(sK3,X0,X1)
% 1.01/1.05      | r2_hidden(sK0(sK3,X0,X1),X1)
% 1.01/1.05      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 1.01/1.05      inference(renaming,[status(thm)],[c_1725]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_2572,plain,
% 1.01/1.05      ( r4_lattice3(sK3,X0_54,X0_55)
% 1.01/1.05      | r2_hidden(sK0(sK3,X0_54,X0_55),X0_55)
% 1.01/1.05      | ~ m1_subset_1(X0_54,u1_struct_0(sK3)) ),
% 1.01/1.05      inference(subtyping,[status(esa)],[c_1726]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_2644,plain,
% 1.01/1.05      ( r4_lattice3(sK3,X0_54,X0_55) = iProver_top
% 1.01/1.05      | r2_hidden(sK0(sK3,X0_54,X0_55),X0_55) = iProver_top
% 1.01/1.05      | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top ),
% 1.01/1.05      inference(predicate_to_equality,[status(thm)],[c_2572]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_2646,plain,
% 1.01/1.05      ( r4_lattice3(sK3,sK4,sK2) = iProver_top
% 1.01/1.05      | r2_hidden(sK0(sK3,sK4,sK2),sK2) = iProver_top
% 1.01/1.05      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
% 1.01/1.05      inference(instantiation,[status(thm)],[c_2644]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_2595,plain,
% 1.01/1.05      ( ~ r2_hidden(X0_54,X0_55)
% 1.01/1.05      | r2_hidden(X1_54,X0_55)
% 1.01/1.05      | X1_54 != X0_54 ),
% 1.01/1.05      theory(equality) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_3317,plain,
% 1.01/1.05      ( r2_hidden(X0_54,X0_55)
% 1.01/1.05      | ~ r2_hidden(sK0(sK3,X1_54,X0_55),X0_55)
% 1.01/1.05      | X0_54 != sK0(sK3,X1_54,X0_55) ),
% 1.01/1.05      inference(instantiation,[status(thm)],[c_2595]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_3350,plain,
% 1.01/1.05      ( ~ r2_hidden(sK0(sK3,X0_54,X0_55),X0_55)
% 1.01/1.05      | r2_hidden(k4_lattice3(sK3,sK0(sK3,X0_54,X0_55)),X0_55)
% 1.01/1.05      | k4_lattice3(sK3,sK0(sK3,X0_54,X0_55)) != sK0(sK3,X0_54,X0_55) ),
% 1.01/1.05      inference(instantiation,[status(thm)],[c_3317]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_3352,plain,
% 1.01/1.05      ( k4_lattice3(sK3,sK0(sK3,X0_54,X0_55)) != sK0(sK3,X0_54,X0_55)
% 1.01/1.05      | r2_hidden(sK0(sK3,X0_54,X0_55),X0_55) != iProver_top
% 1.01/1.05      | r2_hidden(k4_lattice3(sK3,sK0(sK3,X0_54,X0_55)),X0_55) = iProver_top ),
% 1.01/1.05      inference(predicate_to_equality,[status(thm)],[c_3350]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_3354,plain,
% 1.01/1.05      ( k4_lattice3(sK3,sK0(sK3,sK4,sK2)) != sK0(sK3,sK4,sK2)
% 1.01/1.05      | r2_hidden(sK0(sK3,sK4,sK2),sK2) != iProver_top
% 1.01/1.05      | r2_hidden(k4_lattice3(sK3,sK0(sK3,sK4,sK2)),sK2) = iProver_top ),
% 1.01/1.05      inference(instantiation,[status(thm)],[c_3352]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_24,plain,
% 1.01/1.05      ( r3_lattices(X0,X1,X2)
% 1.01/1.05      | ~ r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2))
% 1.01/1.05      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.01/1.05      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.01/1.05      | ~ l3_lattices(X0)
% 1.01/1.05      | ~ v10_lattices(X0)
% 1.01/1.05      | v2_struct_0(X0) ),
% 1.01/1.05      inference(cnf_transformation,[],[f91]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_2,plain,
% 1.01/1.05      ( ~ l3_lattices(X0)
% 1.01/1.05      | ~ v10_lattices(X0)
% 1.01/1.05      | v9_lattices(X0)
% 1.01/1.05      | v2_struct_0(X0) ),
% 1.01/1.05      inference(cnf_transformation,[],[f71]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_7,plain,
% 1.01/1.05      ( r1_lattices(X0,X1,X2)
% 1.01/1.05      | ~ r3_lattices(X0,X1,X2)
% 1.01/1.05      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.01/1.05      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.01/1.05      | ~ v6_lattices(X0)
% 1.01/1.05      | ~ v8_lattices(X0)
% 1.01/1.05      | ~ l3_lattices(X0)
% 1.01/1.05      | ~ v9_lattices(X0)
% 1.01/1.05      | v2_struct_0(X0) ),
% 1.01/1.05      inference(cnf_transformation,[],[f72]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_493,plain,
% 1.01/1.05      ( r1_lattices(X0,X1,X2)
% 1.01/1.05      | ~ r3_lattices(X0,X1,X2)
% 1.01/1.05      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.01/1.05      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.01/1.05      | ~ v6_lattices(X0)
% 1.01/1.05      | ~ v8_lattices(X0)
% 1.01/1.05      | ~ l3_lattices(X0)
% 1.01/1.05      | ~ v10_lattices(X0)
% 1.01/1.05      | v2_struct_0(X0) ),
% 1.01/1.05      inference(resolution,[status(thm)],[c_2,c_7]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_4,plain,
% 1.01/1.05      ( v6_lattices(X0)
% 1.01/1.05      | ~ l3_lattices(X0)
% 1.01/1.05      | ~ v10_lattices(X0)
% 1.01/1.05      | v2_struct_0(X0) ),
% 1.01/1.05      inference(cnf_transformation,[],[f69]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_3,plain,
% 1.01/1.05      ( v8_lattices(X0)
% 1.01/1.05      | ~ l3_lattices(X0)
% 1.01/1.05      | ~ v10_lattices(X0)
% 1.01/1.05      | v2_struct_0(X0) ),
% 1.01/1.05      inference(cnf_transformation,[],[f70]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_497,plain,
% 1.01/1.05      ( r1_lattices(X0,X1,X2)
% 1.01/1.05      | ~ r3_lattices(X0,X1,X2)
% 1.01/1.05      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.01/1.05      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.01/1.05      | ~ l3_lattices(X0)
% 1.01/1.05      | ~ v10_lattices(X0)
% 1.01/1.05      | v2_struct_0(X0) ),
% 1.01/1.05      inference(global_propositional_subsumption,
% 1.01/1.05                [status(thm)],
% 1.01/1.05                [c_493,c_7,c_4,c_3,c_2]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_8,plain,
% 1.01/1.05      ( r4_lattice3(X0,X1,X2)
% 1.01/1.05      | ~ r1_lattices(X0,sK0(X0,X1,X2),X1)
% 1.01/1.05      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.01/1.05      | ~ l3_lattices(X0)
% 1.01/1.05      | v2_struct_0(X0) ),
% 1.01/1.05      inference(cnf_transformation,[],[f77]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_1065,plain,
% 1.01/1.05      ( r4_lattice3(X0,X1,X2)
% 1.01/1.05      | ~ r3_lattices(X3,X4,X5)
% 1.01/1.05      | ~ m1_subset_1(X5,u1_struct_0(X3))
% 1.01/1.05      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 1.01/1.05      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.01/1.05      | ~ l3_lattices(X3)
% 1.01/1.05      | ~ l3_lattices(X0)
% 1.01/1.05      | ~ v10_lattices(X3)
% 1.01/1.05      | v2_struct_0(X3)
% 1.01/1.05      | v2_struct_0(X0)
% 1.01/1.05      | X0 != X3
% 1.01/1.05      | X1 != X5
% 1.01/1.05      | sK0(X0,X1,X2) != X4 ),
% 1.01/1.05      inference(resolution_lifted,[status(thm)],[c_497,c_8]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_1066,plain,
% 1.01/1.05      ( r4_lattice3(X0,X1,X2)
% 1.01/1.05      | ~ r3_lattices(X0,sK0(X0,X1,X2),X1)
% 1.01/1.05      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.01/1.05      | ~ m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 1.01/1.05      | ~ l3_lattices(X0)
% 1.01/1.05      | ~ v10_lattices(X0)
% 1.01/1.05      | v2_struct_0(X0) ),
% 1.01/1.05      inference(unflattening,[status(thm)],[c_1065]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_1070,plain,
% 1.01/1.05      ( ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.01/1.05      | ~ r3_lattices(X0,sK0(X0,X1,X2),X1)
% 1.01/1.05      | r4_lattice3(X0,X1,X2)
% 1.01/1.05      | ~ l3_lattices(X0)
% 1.01/1.05      | ~ v10_lattices(X0)
% 1.01/1.05      | v2_struct_0(X0) ),
% 1.01/1.05      inference(global_propositional_subsumption,
% 1.01/1.05                [status(thm)],
% 1.01/1.05                [c_1066,c_10]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_1071,plain,
% 1.01/1.05      ( r4_lattice3(X0,X1,X2)
% 1.01/1.05      | ~ r3_lattices(X0,sK0(X0,X1,X2),X1)
% 1.01/1.05      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.01/1.05      | ~ l3_lattices(X0)
% 1.01/1.05      | ~ v10_lattices(X0)
% 1.01/1.05      | v2_struct_0(X0) ),
% 1.01/1.05      inference(renaming,[status(thm)],[c_1070]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_1311,plain,
% 1.01/1.05      ( r4_lattice3(X0,X1,X2)
% 1.01/1.05      | ~ r3_orders_2(k3_lattice3(X3),k4_lattice3(X3,X4),k4_lattice3(X3,X5))
% 1.01/1.05      | ~ m1_subset_1(X5,u1_struct_0(X3))
% 1.01/1.05      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 1.01/1.05      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.01/1.05      | ~ l3_lattices(X3)
% 1.01/1.05      | ~ l3_lattices(X0)
% 1.01/1.05      | ~ v10_lattices(X3)
% 1.01/1.05      | ~ v10_lattices(X0)
% 1.01/1.05      | v2_struct_0(X3)
% 1.01/1.05      | v2_struct_0(X0)
% 1.01/1.05      | X0 != X3
% 1.01/1.05      | X1 != X5
% 1.01/1.05      | sK0(X0,X1,X2) != X4 ),
% 1.01/1.05      inference(resolution_lifted,[status(thm)],[c_24,c_1071]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_1312,plain,
% 1.01/1.05      ( r4_lattice3(X0,X1,X2)
% 1.01/1.05      | ~ r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,sK0(X0,X1,X2)),k4_lattice3(X0,X1))
% 1.01/1.05      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.01/1.05      | ~ m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 1.01/1.05      | ~ l3_lattices(X0)
% 1.01/1.05      | ~ v10_lattices(X0)
% 1.01/1.05      | v2_struct_0(X0) ),
% 1.01/1.05      inference(unflattening,[status(thm)],[c_1311]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_1316,plain,
% 1.01/1.05      ( ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.01/1.05      | ~ r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,sK0(X0,X1,X2)),k4_lattice3(X0,X1))
% 1.01/1.05      | r4_lattice3(X0,X1,X2)
% 1.01/1.05      | ~ l3_lattices(X0)
% 1.01/1.05      | ~ v10_lattices(X0)
% 1.01/1.05      | v2_struct_0(X0) ),
% 1.01/1.05      inference(global_propositional_subsumption,
% 1.01/1.05                [status(thm)],
% 1.01/1.05                [c_1312,c_10]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_1317,plain,
% 1.01/1.05      ( r4_lattice3(X0,X1,X2)
% 1.01/1.05      | ~ r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,sK0(X0,X1,X2)),k4_lattice3(X0,X1))
% 1.01/1.05      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.01/1.05      | ~ l3_lattices(X0)
% 1.01/1.05      | ~ v10_lattices(X0)
% 1.01/1.05      | v2_struct_0(X0) ),
% 1.01/1.05      inference(renaming,[status(thm)],[c_1316]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_1421,plain,
% 1.01/1.05      ( r4_lattice3(X0,X1,X2)
% 1.01/1.05      | ~ r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,sK0(X0,X1,X2)),k4_lattice3(X0,X1))
% 1.01/1.05      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.01/1.05      | ~ l3_lattices(X0)
% 1.01/1.05      | v2_struct_0(X0)
% 1.01/1.05      | sK3 != X0 ),
% 1.01/1.05      inference(resolution_lifted,[status(thm)],[c_1317,c_30]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_1422,plain,
% 1.01/1.05      ( r4_lattice3(sK3,X0,X1)
% 1.01/1.05      | ~ r3_orders_2(k3_lattice3(sK3),k4_lattice3(sK3,sK0(sK3,X0,X1)),k4_lattice3(sK3,X0))
% 1.01/1.05      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.01/1.05      | ~ l3_lattices(sK3)
% 1.01/1.05      | v2_struct_0(sK3) ),
% 1.01/1.05      inference(unflattening,[status(thm)],[c_1421]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_1426,plain,
% 1.01/1.05      ( r4_lattice3(sK3,X0,X1)
% 1.01/1.05      | ~ r3_orders_2(k3_lattice3(sK3),k4_lattice3(sK3,sK0(sK3,X0,X1)),k4_lattice3(sK3,X0))
% 1.01/1.05      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 1.01/1.05      inference(global_propositional_subsumption,
% 1.01/1.05                [status(thm)],
% 1.01/1.05                [c_1422,c_31,c_29]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_2584,plain,
% 1.01/1.05      ( r4_lattice3(sK3,X0_54,X0_55)
% 1.01/1.05      | ~ r3_orders_2(k3_lattice3(sK3),k4_lattice3(sK3,sK0(sK3,X0_54,X0_55)),k4_lattice3(sK3,X0_54))
% 1.01/1.05      | ~ m1_subset_1(X0_54,u1_struct_0(sK3)) ),
% 1.01/1.05      inference(subtyping,[status(esa)],[c_1426]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_3058,plain,
% 1.01/1.05      ( r4_lattice3(sK3,X0_54,X0_55) = iProver_top
% 1.01/1.05      | r3_orders_2(k3_lattice3(sK3),k4_lattice3(sK3,sK0(sK3,X0_54,X0_55)),k4_lattice3(sK3,X0_54)) != iProver_top
% 1.01/1.05      | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top ),
% 1.01/1.05      inference(predicate_to_equality,[status(thm)],[c_2584]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_3490,plain,
% 1.01/1.05      ( r4_lattice3(sK3,sK4,X0_55) = iProver_top
% 1.01/1.05      | r3_orders_2(k3_lattice3(sK3),k4_lattice3(sK3,sK0(sK3,sK4,X0_55)),sK4) != iProver_top
% 1.01/1.05      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
% 1.01/1.05      inference(superposition,[status(thm)],[c_3262,c_3058]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_3492,plain,
% 1.01/1.05      ( r4_lattice3(sK3,sK4,sK2) = iProver_top
% 1.01/1.05      | r3_orders_2(k3_lattice3(sK3),k4_lattice3(sK3,sK0(sK3,sK4,sK2)),sK4) != iProver_top
% 1.01/1.05      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
% 1.01/1.05      inference(instantiation,[status(thm)],[c_3490]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_3228,plain,
% 1.01/1.05      ( ~ r2_lattice3(k3_lattice3(sK3),X0_55,X0_54)
% 1.01/1.05      | r3_orders_2(k3_lattice3(sK3),k4_lattice3(sK3,X1_54),X0_54)
% 1.01/1.05      | ~ r2_hidden(k4_lattice3(sK3,X1_54),X0_55)
% 1.01/1.05      | ~ m1_subset_1(X0_54,u1_struct_0(k3_lattice3(sK3)))
% 1.01/1.05      | ~ m1_subset_1(k4_lattice3(sK3,X1_54),u1_struct_0(k3_lattice3(sK3))) ),
% 1.01/1.05      inference(instantiation,[status(thm)],[c_2583]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_3563,plain,
% 1.01/1.05      ( ~ r2_lattice3(k3_lattice3(sK3),X0_55,X0_54)
% 1.01/1.05      | r3_orders_2(k3_lattice3(sK3),k4_lattice3(sK3,sK0(sK3,X1_54,X0_55)),X0_54)
% 1.01/1.05      | ~ r2_hidden(k4_lattice3(sK3,sK0(sK3,X1_54,X0_55)),X0_55)
% 1.01/1.05      | ~ m1_subset_1(X0_54,u1_struct_0(k3_lattice3(sK3)))
% 1.01/1.05      | ~ m1_subset_1(k4_lattice3(sK3,sK0(sK3,X1_54,X0_55)),u1_struct_0(k3_lattice3(sK3))) ),
% 1.01/1.05      inference(instantiation,[status(thm)],[c_3228]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_3569,plain,
% 1.01/1.05      ( r2_lattice3(k3_lattice3(sK3),X0_55,X0_54) != iProver_top
% 1.01/1.05      | r3_orders_2(k3_lattice3(sK3),k4_lattice3(sK3,sK0(sK3,X1_54,X0_55)),X0_54) = iProver_top
% 1.01/1.05      | r2_hidden(k4_lattice3(sK3,sK0(sK3,X1_54,X0_55)),X0_55) != iProver_top
% 1.01/1.05      | m1_subset_1(X0_54,u1_struct_0(k3_lattice3(sK3))) != iProver_top
% 1.01/1.05      | m1_subset_1(k4_lattice3(sK3,sK0(sK3,X1_54,X0_55)),u1_struct_0(k3_lattice3(sK3))) != iProver_top ),
% 1.01/1.05      inference(predicate_to_equality,[status(thm)],[c_3563]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_3571,plain,
% 1.01/1.05      ( r2_lattice3(k3_lattice3(sK3),sK2,sK4) != iProver_top
% 1.01/1.05      | r3_orders_2(k3_lattice3(sK3),k4_lattice3(sK3,sK0(sK3,sK4,sK2)),sK4) = iProver_top
% 1.01/1.05      | r2_hidden(k4_lattice3(sK3,sK0(sK3,sK4,sK2)),sK2) != iProver_top
% 1.01/1.05      | m1_subset_1(k4_lattice3(sK3,sK0(sK3,sK4,sK2)),u1_struct_0(k3_lattice3(sK3))) != iProver_top
% 1.01/1.05      | m1_subset_1(sK4,u1_struct_0(k3_lattice3(sK3))) != iProver_top ),
% 1.01/1.05      inference(instantiation,[status(thm)],[c_3569]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_3069,plain,
% 1.01/1.05      ( r4_lattice3(sK3,X0_54,X0_55) = iProver_top
% 1.01/1.05      | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top
% 1.01/1.05      | m1_subset_1(sK0(sK3,X0_54,X0_55),u1_struct_0(sK3)) = iProver_top ),
% 1.01/1.05      inference(predicate_to_equality,[status(thm)],[c_2573]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_3590,plain,
% 1.01/1.05      ( k4_lattice3(sK3,sK0(sK3,X0_54,X0_55)) = sK0(sK3,X0_54,X0_55)
% 1.01/1.05      | r4_lattice3(sK3,X0_54,X0_55) = iProver_top
% 1.01/1.05      | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top ),
% 1.01/1.05      inference(superposition,[status(thm)],[c_3069,c_3064]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_3592,plain,
% 1.01/1.05      ( k4_lattice3(sK3,sK0(sK3,sK4,sK2)) = sK0(sK3,sK4,sK2)
% 1.01/1.05      | r4_lattice3(sK3,sK4,sK2) = iProver_top
% 1.01/1.05      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
% 1.01/1.05      inference(instantiation,[status(thm)],[c_3590]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_3749,plain,
% 1.01/1.05      ( ~ m1_subset_1(sK0(sK3,X0_54,X0_55),u1_struct_0(sK3))
% 1.01/1.05      | m1_subset_1(k4_lattice3(sK3,sK0(sK3,X0_54,X0_55)),u1_struct_0(k3_lattice3(sK3))) ),
% 1.01/1.05      inference(instantiation,[status(thm)],[c_2580]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_3750,plain,
% 1.01/1.05      ( m1_subset_1(sK0(sK3,X0_54,X0_55),u1_struct_0(sK3)) != iProver_top
% 1.01/1.05      | m1_subset_1(k4_lattice3(sK3,sK0(sK3,X0_54,X0_55)),u1_struct_0(k3_lattice3(sK3))) = iProver_top ),
% 1.01/1.05      inference(predicate_to_equality,[status(thm)],[c_3749]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_3752,plain,
% 1.01/1.05      ( m1_subset_1(sK0(sK3,sK4,sK2),u1_struct_0(sK3)) != iProver_top
% 1.01/1.05      | m1_subset_1(k4_lattice3(sK3,sK0(sK3,sK4,sK2)),u1_struct_0(k3_lattice3(sK3))) = iProver_top ),
% 1.01/1.05      inference(instantiation,[status(thm)],[c_3750]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_4984,plain,
% 1.01/1.05      ( r4_lattice3(sK3,sK4,sK2) = iProver_top ),
% 1.01/1.05      inference(global_propositional_subsumption,
% 1.01/1.05                [status(thm)],
% 1.01/1.05                [c_4951,c_28,c_35,c_2605,c_2626,c_2631,c_2643,c_2646,
% 1.01/1.05                 c_3252,c_3279,c_3290,c_3354,c_3492,c_3571,c_3592,c_3752]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_8099,plain,
% 1.01/1.05      ( k5_lattice3(sK3,sK1(k3_lattice3(sK3),sK2,sK4)) = sK1(k3_lattice3(sK3),sK2,sK4) ),
% 1.01/1.05      inference(global_propositional_subsumption,
% 1.01/1.05                [status(thm)],
% 1.01/1.05                [c_7946,c_28,c_35,c_2605,c_2626,c_2631,c_2643,c_2646,
% 1.01/1.05                 c_3252,c_3279,c_3290,c_3291,c_3354,c_3434,c_3492,c_3571,
% 1.01/1.05                 c_3592,c_3752]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_21,plain,
% 1.01/1.05      ( ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(X1)))
% 1.01/1.05      | m1_subset_1(k5_lattice3(X1,X0),u1_struct_0(X1))
% 1.01/1.05      | ~ l3_lattices(X1)
% 1.01/1.05      | ~ v10_lattices(X1)
% 1.01/1.05      | v2_struct_0(X1) ),
% 1.01/1.05      inference(cnf_transformation,[],[f87]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_1512,plain,
% 1.01/1.05      ( ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(X1)))
% 1.01/1.05      | m1_subset_1(k5_lattice3(X1,X0),u1_struct_0(X1))
% 1.01/1.05      | ~ l3_lattices(X1)
% 1.01/1.05      | v2_struct_0(X1)
% 1.01/1.05      | sK3 != X1 ),
% 1.01/1.05      inference(resolution_lifted,[status(thm)],[c_21,c_30]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_1513,plain,
% 1.01/1.05      ( ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(sK3)))
% 1.01/1.05      | m1_subset_1(k5_lattice3(sK3,X0),u1_struct_0(sK3))
% 1.01/1.05      | ~ l3_lattices(sK3)
% 1.01/1.05      | v2_struct_0(sK3) ),
% 1.01/1.05      inference(unflattening,[status(thm)],[c_1512]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_1517,plain,
% 1.01/1.05      ( ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(sK3)))
% 1.01/1.05      | m1_subset_1(k5_lattice3(sK3,X0),u1_struct_0(sK3)) ),
% 1.01/1.05      inference(global_propositional_subsumption,
% 1.01/1.05                [status(thm)],
% 1.01/1.05                [c_1513,c_31,c_29]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_2581,plain,
% 1.01/1.05      ( ~ m1_subset_1(X0_54,u1_struct_0(k3_lattice3(sK3)))
% 1.01/1.05      | m1_subset_1(k5_lattice3(sK3,X0_54),u1_struct_0(sK3)) ),
% 1.01/1.05      inference(subtyping,[status(esa)],[c_1517]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_3061,plain,
% 1.01/1.05      ( m1_subset_1(X0_54,u1_struct_0(k3_lattice3(sK3))) != iProver_top
% 1.01/1.05      | m1_subset_1(k5_lattice3(sK3,X0_54),u1_struct_0(sK3)) = iProver_top ),
% 1.01/1.05      inference(predicate_to_equality,[status(thm)],[c_2581]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_8102,plain,
% 1.01/1.05      ( m1_subset_1(sK1(k3_lattice3(sK3),sK2,sK4),u1_struct_0(k3_lattice3(sK3))) != iProver_top
% 1.01/1.05      | m1_subset_1(sK1(k3_lattice3(sK3),sK2,sK4),u1_struct_0(sK3)) = iProver_top ),
% 1.01/1.05      inference(superposition,[status(thm)],[c_8099,c_3061]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_2634,plain,
% 1.01/1.05      ( r2_lattice3(k3_lattice3(sK3),X0_55,X0_54) = iProver_top
% 1.01/1.05      | m1_subset_1(X0_54,u1_struct_0(k3_lattice3(sK3))) != iProver_top
% 1.01/1.05      | m1_subset_1(sK1(k3_lattice3(sK3),X0_55,X0_54),u1_struct_0(k3_lattice3(sK3))) = iProver_top ),
% 1.01/1.05      inference(predicate_to_equality,[status(thm)],[c_2576]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_2636,plain,
% 1.01/1.05      ( r2_lattice3(k3_lattice3(sK3),sK2,sK4) = iProver_top
% 1.01/1.05      | m1_subset_1(sK1(k3_lattice3(sK3),sK2,sK4),u1_struct_0(k3_lattice3(sK3))) = iProver_top
% 1.01/1.05      | m1_subset_1(sK4,u1_struct_0(k3_lattice3(sK3))) != iProver_top ),
% 1.01/1.05      inference(instantiation,[status(thm)],[c_2634]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_4417,plain,
% 1.01/1.05      ( ~ m1_subset_1(sK1(k3_lattice3(sK3),X0_55,X0_54),u1_struct_0(k3_lattice3(sK3)))
% 1.01/1.05      | m1_subset_1(k5_lattice3(sK3,sK1(k3_lattice3(sK3),X0_55,X0_54)),u1_struct_0(sK3)) ),
% 1.01/1.05      inference(instantiation,[status(thm)],[c_2581]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_4418,plain,
% 1.01/1.05      ( m1_subset_1(sK1(k3_lattice3(sK3),X0_55,X0_54),u1_struct_0(k3_lattice3(sK3))) != iProver_top
% 1.01/1.05      | m1_subset_1(k5_lattice3(sK3,sK1(k3_lattice3(sK3),X0_55,X0_54)),u1_struct_0(sK3)) = iProver_top ),
% 1.01/1.05      inference(predicate_to_equality,[status(thm)],[c_4417]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_4420,plain,
% 1.01/1.05      ( m1_subset_1(sK1(k3_lattice3(sK3),sK2,sK4),u1_struct_0(k3_lattice3(sK3))) != iProver_top
% 1.01/1.05      | m1_subset_1(k5_lattice3(sK3,sK1(k3_lattice3(sK3),sK2,sK4)),u1_struct_0(sK3)) = iProver_top ),
% 1.01/1.05      inference(instantiation,[status(thm)],[c_4418]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_4434,plain,
% 1.01/1.05      ( sK1(k3_lattice3(sK3),X0_55,X0_54) = sK1(k3_lattice3(sK3),X0_55,X0_54) ),
% 1.01/1.05      inference(instantiation,[status(thm)],[c_2590]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_4436,plain,
% 1.01/1.05      ( sK1(k3_lattice3(sK3),sK2,sK4) = sK1(k3_lattice3(sK3),sK2,sK4) ),
% 1.01/1.05      inference(instantiation,[status(thm)],[c_4434]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_4557,plain,
% 1.01/1.05      ( X0_54 != X1_54
% 1.01/1.05      | X0_54 = k5_lattice3(sK3,sK1(k3_lattice3(sK3),X0_55,X2_54))
% 1.01/1.05      | k5_lattice3(sK3,sK1(k3_lattice3(sK3),X0_55,X2_54)) != X1_54 ),
% 1.01/1.05      inference(instantiation,[status(thm)],[c_2591]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_5141,plain,
% 1.01/1.05      ( X0_54 != sK1(k3_lattice3(sK3),X0_55,X1_54)
% 1.01/1.05      | X0_54 = k5_lattice3(sK3,sK1(k3_lattice3(sK3),X0_55,X1_54))
% 1.01/1.05      | k5_lattice3(sK3,sK1(k3_lattice3(sK3),X0_55,X1_54)) != sK1(k3_lattice3(sK3),X0_55,X1_54) ),
% 1.01/1.05      inference(instantiation,[status(thm)],[c_4557]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_5503,plain,
% 1.01/1.05      ( sK1(k3_lattice3(sK3),X0_55,X0_54) != sK1(k3_lattice3(sK3),X0_55,X0_54)
% 1.01/1.05      | sK1(k3_lattice3(sK3),X0_55,X0_54) = k5_lattice3(sK3,sK1(k3_lattice3(sK3),X0_55,X0_54))
% 1.01/1.05      | k5_lattice3(sK3,sK1(k3_lattice3(sK3),X0_55,X0_54)) != sK1(k3_lattice3(sK3),X0_55,X0_54) ),
% 1.01/1.05      inference(instantiation,[status(thm)],[c_5141]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_5504,plain,
% 1.01/1.05      ( sK1(k3_lattice3(sK3),sK2,sK4) != sK1(k3_lattice3(sK3),sK2,sK4)
% 1.01/1.05      | sK1(k3_lattice3(sK3),sK2,sK4) = k5_lattice3(sK3,sK1(k3_lattice3(sK3),sK2,sK4))
% 1.01/1.05      | k5_lattice3(sK3,sK1(k3_lattice3(sK3),sK2,sK4)) != sK1(k3_lattice3(sK3),sK2,sK4) ),
% 1.01/1.05      inference(instantiation,[status(thm)],[c_5503]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_3263,plain,
% 1.01/1.05      ( ~ m1_subset_1(X0_54,u1_struct_0(sK3))
% 1.01/1.05      | m1_subset_1(X1_54,u1_struct_0(sK3))
% 1.01/1.05      | X1_54 != X0_54 ),
% 1.01/1.05      inference(instantiation,[status(thm)],[c_2593]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_3959,plain,
% 1.01/1.05      ( ~ m1_subset_1(X0_54,u1_struct_0(sK3))
% 1.01/1.05      | m1_subset_1(sK1(k3_lattice3(sK3),X0_55,X1_54),u1_struct_0(sK3))
% 1.01/1.05      | sK1(k3_lattice3(sK3),X0_55,X1_54) != X0_54 ),
% 1.01/1.05      inference(instantiation,[status(thm)],[c_3263]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_6560,plain,
% 1.01/1.05      ( m1_subset_1(sK1(k3_lattice3(sK3),X0_55,X0_54),u1_struct_0(sK3))
% 1.01/1.05      | ~ m1_subset_1(k5_lattice3(sK3,sK1(k3_lattice3(sK3),X0_55,X0_54)),u1_struct_0(sK3))
% 1.01/1.05      | sK1(k3_lattice3(sK3),X0_55,X0_54) != k5_lattice3(sK3,sK1(k3_lattice3(sK3),X0_55,X0_54)) ),
% 1.01/1.05      inference(instantiation,[status(thm)],[c_3959]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_6561,plain,
% 1.01/1.05      ( sK1(k3_lattice3(sK3),X0_55,X0_54) != k5_lattice3(sK3,sK1(k3_lattice3(sK3),X0_55,X0_54))
% 1.01/1.05      | m1_subset_1(sK1(k3_lattice3(sK3),X0_55,X0_54),u1_struct_0(sK3)) = iProver_top
% 1.01/1.05      | m1_subset_1(k5_lattice3(sK3,sK1(k3_lattice3(sK3),X0_55,X0_54)),u1_struct_0(sK3)) != iProver_top ),
% 1.01/1.05      inference(predicate_to_equality,[status(thm)],[c_6560]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_6563,plain,
% 1.01/1.05      ( sK1(k3_lattice3(sK3),sK2,sK4) != k5_lattice3(sK3,sK1(k3_lattice3(sK3),sK2,sK4))
% 1.01/1.05      | m1_subset_1(sK1(k3_lattice3(sK3),sK2,sK4),u1_struct_0(sK3)) = iProver_top
% 1.01/1.05      | m1_subset_1(k5_lattice3(sK3,sK1(k3_lattice3(sK3),sK2,sK4)),u1_struct_0(sK3)) != iProver_top ),
% 1.01/1.05      inference(instantiation,[status(thm)],[c_6561]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_8500,plain,
% 1.01/1.05      ( m1_subset_1(sK1(k3_lattice3(sK3),sK2,sK4),u1_struct_0(sK3)) = iProver_top ),
% 1.01/1.05      inference(global_propositional_subsumption,
% 1.01/1.05                [status(thm)],
% 1.01/1.05                [c_8102,c_28,c_35,c_2605,c_2626,c_2631,c_2636,c_2643,
% 1.01/1.05                 c_2646,c_3252,c_3279,c_3290,c_3291,c_3354,c_3434,c_3492,
% 1.01/1.05                 c_3571,c_3592,c_3752,c_4420,c_4436,c_5504,c_6563]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_8524,plain,
% 1.01/1.05      ( k4_lattice3(sK3,sK1(k3_lattice3(sK3),sK2,sK4)) = sK1(k3_lattice3(sK3),sK2,sK4) ),
% 1.01/1.05      inference(superposition,[status(thm)],[c_8500,c_3064]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_25,plain,
% 1.01/1.05      ( ~ r3_lattices(X0,X1,X2)
% 1.01/1.05      | r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2))
% 1.01/1.05      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.01/1.05      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.01/1.05      | ~ l3_lattices(X0)
% 1.01/1.05      | ~ v10_lattices(X0)
% 1.01/1.05      | v2_struct_0(X0) ),
% 1.01/1.05      inference(cnf_transformation,[],[f90]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_6,plain,
% 1.01/1.05      ( ~ r1_lattices(X0,X1,X2)
% 1.01/1.05      | r3_lattices(X0,X1,X2)
% 1.01/1.05      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.01/1.05      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.01/1.05      | ~ v6_lattices(X0)
% 1.01/1.05      | ~ v8_lattices(X0)
% 1.01/1.05      | ~ l3_lattices(X0)
% 1.01/1.05      | ~ v9_lattices(X0)
% 1.01/1.05      | v2_struct_0(X0) ),
% 1.01/1.05      inference(cnf_transformation,[],[f73]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_525,plain,
% 1.01/1.05      ( ~ r1_lattices(X0,X1,X2)
% 1.01/1.05      | r3_lattices(X0,X1,X2)
% 1.01/1.05      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.01/1.05      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.01/1.05      | ~ v6_lattices(X0)
% 1.01/1.05      | ~ v8_lattices(X0)
% 1.01/1.05      | ~ l3_lattices(X0)
% 1.01/1.05      | ~ v10_lattices(X0)
% 1.01/1.05      | v2_struct_0(X0) ),
% 1.01/1.05      inference(resolution,[status(thm)],[c_2,c_6]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_529,plain,
% 1.01/1.05      ( ~ r1_lattices(X0,X1,X2)
% 1.01/1.05      | r3_lattices(X0,X1,X2)
% 1.01/1.05      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.01/1.05      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.01/1.05      | ~ l3_lattices(X0)
% 1.01/1.05      | ~ v10_lattices(X0)
% 1.01/1.05      | v2_struct_0(X0) ),
% 1.01/1.05      inference(global_propositional_subsumption,
% 1.01/1.05                [status(thm)],
% 1.01/1.05                [c_525,c_6,c_4,c_3,c_2]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_11,plain,
% 1.01/1.05      ( ~ r4_lattice3(X0,X1,X2)
% 1.01/1.05      | r1_lattices(X0,X3,X1)
% 1.01/1.05      | ~ r2_hidden(X3,X2)
% 1.01/1.05      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.01/1.05      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.01/1.05      | ~ l3_lattices(X0)
% 1.01/1.05      | v2_struct_0(X0) ),
% 1.01/1.05      inference(cnf_transformation,[],[f74]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_1095,plain,
% 1.01/1.05      ( ~ r4_lattice3(X0,X1,X2)
% 1.01/1.05      | r3_lattices(X3,X4,X5)
% 1.01/1.05      | ~ r2_hidden(X6,X2)
% 1.01/1.05      | ~ m1_subset_1(X5,u1_struct_0(X3))
% 1.01/1.05      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 1.01/1.05      | ~ m1_subset_1(X6,u1_struct_0(X0))
% 1.01/1.05      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.01/1.05      | ~ l3_lattices(X3)
% 1.01/1.05      | ~ l3_lattices(X0)
% 1.01/1.05      | ~ v10_lattices(X3)
% 1.01/1.05      | v2_struct_0(X3)
% 1.01/1.05      | v2_struct_0(X0)
% 1.01/1.05      | X0 != X3
% 1.01/1.05      | X6 != X4
% 1.01/1.05      | X1 != X5 ),
% 1.01/1.05      inference(resolution_lifted,[status(thm)],[c_529,c_11]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_1096,plain,
% 1.01/1.05      ( ~ r4_lattice3(X0,X1,X2)
% 1.01/1.05      | r3_lattices(X0,X3,X1)
% 1.01/1.05      | ~ r2_hidden(X3,X2)
% 1.01/1.05      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.01/1.05      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.01/1.05      | ~ l3_lattices(X0)
% 1.01/1.05      | ~ v10_lattices(X0)
% 1.01/1.05      | v2_struct_0(X0) ),
% 1.01/1.05      inference(unflattening,[status(thm)],[c_1095]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_1341,plain,
% 1.01/1.05      ( ~ r4_lattice3(X0,X1,X2)
% 1.01/1.05      | r3_orders_2(k3_lattice3(X3),k4_lattice3(X3,X4),k4_lattice3(X3,X5))
% 1.01/1.05      | ~ r2_hidden(X6,X2)
% 1.01/1.05      | ~ m1_subset_1(X5,u1_struct_0(X3))
% 1.01/1.05      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 1.01/1.05      | ~ m1_subset_1(X6,u1_struct_0(X0))
% 1.01/1.05      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.01/1.05      | ~ l3_lattices(X3)
% 1.01/1.05      | ~ l3_lattices(X0)
% 1.01/1.05      | ~ v10_lattices(X3)
% 1.01/1.05      | ~ v10_lattices(X0)
% 1.01/1.05      | v2_struct_0(X3)
% 1.01/1.05      | v2_struct_0(X0)
% 1.01/1.05      | X0 != X3
% 1.01/1.05      | X6 != X4
% 1.01/1.05      | X1 != X5 ),
% 1.01/1.05      inference(resolution_lifted,[status(thm)],[c_25,c_1096]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_1342,plain,
% 1.01/1.05      ( ~ r4_lattice3(X0,X1,X2)
% 1.01/1.05      | r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X3),k4_lattice3(X0,X1))
% 1.01/1.05      | ~ r2_hidden(X3,X2)
% 1.01/1.05      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.01/1.05      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.01/1.05      | ~ l3_lattices(X0)
% 1.01/1.05      | ~ v10_lattices(X0)
% 1.01/1.05      | v2_struct_0(X0) ),
% 1.01/1.05      inference(unflattening,[status(thm)],[c_1341]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_1394,plain,
% 1.01/1.05      ( ~ r4_lattice3(X0,X1,X2)
% 1.01/1.05      | r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X3),k4_lattice3(X0,X1))
% 1.01/1.05      | ~ r2_hidden(X3,X2)
% 1.01/1.05      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.01/1.05      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.01/1.05      | ~ l3_lattices(X0)
% 1.01/1.05      | v2_struct_0(X0)
% 1.01/1.05      | sK3 != X0 ),
% 1.01/1.05      inference(resolution_lifted,[status(thm)],[c_1342,c_30]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_1395,plain,
% 1.01/1.05      ( ~ r4_lattice3(sK3,X0,X1)
% 1.01/1.05      | r3_orders_2(k3_lattice3(sK3),k4_lattice3(sK3,X2),k4_lattice3(sK3,X0))
% 1.01/1.05      | ~ r2_hidden(X2,X1)
% 1.01/1.05      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.01/1.05      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.01/1.05      | ~ l3_lattices(sK3)
% 1.01/1.05      | v2_struct_0(sK3) ),
% 1.01/1.05      inference(unflattening,[status(thm)],[c_1394]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_1399,plain,
% 1.01/1.05      ( ~ r4_lattice3(sK3,X0,X1)
% 1.01/1.05      | r3_orders_2(k3_lattice3(sK3),k4_lattice3(sK3,X2),k4_lattice3(sK3,X0))
% 1.01/1.05      | ~ r2_hidden(X2,X1)
% 1.01/1.05      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.01/1.05      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 1.01/1.05      inference(global_propositional_subsumption,
% 1.01/1.05                [status(thm)],
% 1.01/1.05                [c_1395,c_31,c_29]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_2585,plain,
% 1.01/1.05      ( ~ r4_lattice3(sK3,X0_54,X0_55)
% 1.01/1.05      | r3_orders_2(k3_lattice3(sK3),k4_lattice3(sK3,X1_54),k4_lattice3(sK3,X0_54))
% 1.01/1.05      | ~ r2_hidden(X1_54,X0_55)
% 1.01/1.05      | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
% 1.01/1.05      | ~ m1_subset_1(X1_54,u1_struct_0(sK3)) ),
% 1.01/1.05      inference(subtyping,[status(esa)],[c_1399]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_3057,plain,
% 1.01/1.05      ( r4_lattice3(sK3,X0_54,X0_55) != iProver_top
% 1.01/1.05      | r3_orders_2(k3_lattice3(sK3),k4_lattice3(sK3,X1_54),k4_lattice3(sK3,X0_54)) = iProver_top
% 1.01/1.05      | r2_hidden(X1_54,X0_55) != iProver_top
% 1.01/1.05      | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top
% 1.01/1.05      | m1_subset_1(X1_54,u1_struct_0(sK3)) != iProver_top ),
% 1.01/1.05      inference(predicate_to_equality,[status(thm)],[c_2585]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_4989,plain,
% 1.01/1.05      ( r3_orders_2(k3_lattice3(sK3),k4_lattice3(sK3,X0_54),k4_lattice3(sK3,sK4)) = iProver_top
% 1.01/1.05      | r2_hidden(X0_54,sK2) != iProver_top
% 1.01/1.05      | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top
% 1.01/1.05      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
% 1.01/1.05      inference(superposition,[status(thm)],[c_4984,c_3057]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_4990,plain,
% 1.01/1.05      ( r3_orders_2(k3_lattice3(sK3),k4_lattice3(sK3,X0_54),sK4) = iProver_top
% 1.01/1.05      | r2_hidden(X0_54,sK2) != iProver_top
% 1.01/1.05      | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top
% 1.01/1.05      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
% 1.01/1.05      inference(light_normalisation,[status(thm)],[c_4989,c_3262]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_5089,plain,
% 1.01/1.05      ( m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top
% 1.01/1.05      | r2_hidden(X0_54,sK2) != iProver_top
% 1.01/1.05      | r3_orders_2(k3_lattice3(sK3),k4_lattice3(sK3,X0_54),sK4) = iProver_top ),
% 1.01/1.05      inference(global_propositional_subsumption,
% 1.01/1.05                [status(thm)],
% 1.01/1.05                [c_4990,c_35]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_5090,plain,
% 1.01/1.05      ( r3_orders_2(k3_lattice3(sK3),k4_lattice3(sK3,X0_54),sK4) = iProver_top
% 1.01/1.05      | r2_hidden(X0_54,sK2) != iProver_top
% 1.01/1.05      | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top ),
% 1.01/1.05      inference(renaming,[status(thm)],[c_5089]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_8589,plain,
% 1.01/1.05      ( r3_orders_2(k3_lattice3(sK3),sK1(k3_lattice3(sK3),sK2,sK4),sK4) = iProver_top
% 1.01/1.05      | r2_hidden(sK1(k3_lattice3(sK3),sK2,sK4),sK2) != iProver_top
% 1.01/1.05      | m1_subset_1(sK1(k3_lattice3(sK3),sK2,sK4),u1_struct_0(sK3)) != iProver_top ),
% 1.01/1.05      inference(superposition,[status(thm)],[c_8524,c_5090]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_15,plain,
% 1.01/1.05      ( r2_lattice3(X0,X1,X2)
% 1.01/1.05      | r2_hidden(sK1(X0,X1,X2),X1)
% 1.01/1.05      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.01/1.05      | ~ l1_orders_2(X0) ),
% 1.01/1.05      inference(cnf_transformation,[],[f82]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_1651,plain,
% 1.01/1.05      ( r2_lattice3(X0,X1,X2)
% 1.01/1.05      | r2_hidden(sK1(X0,X1,X2),X1)
% 1.01/1.05      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.01/1.05      | k3_lattice3(sK3) != X0 ),
% 1.01/1.05      inference(resolution_lifted,[status(thm)],[c_15,c_1504]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_1652,plain,
% 1.01/1.05      ( r2_lattice3(k3_lattice3(sK3),X0,X1)
% 1.01/1.05      | r2_hidden(sK1(k3_lattice3(sK3),X0,X1),X0)
% 1.01/1.05      | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(sK3))) ),
% 1.01/1.05      inference(unflattening,[status(thm)],[c_1651]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_2575,plain,
% 1.01/1.05      ( r2_lattice3(k3_lattice3(sK3),X0_55,X0_54)
% 1.01/1.05      | r2_hidden(sK1(k3_lattice3(sK3),X0_55,X0_54),X0_55)
% 1.01/1.05      | ~ m1_subset_1(X0_54,u1_struct_0(k3_lattice3(sK3))) ),
% 1.01/1.05      inference(subtyping,[status(esa)],[c_1652]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_2637,plain,
% 1.01/1.05      ( r2_lattice3(k3_lattice3(sK3),X0_55,X0_54) = iProver_top
% 1.01/1.05      | r2_hidden(sK1(k3_lattice3(sK3),X0_55,X0_54),X0_55) = iProver_top
% 1.01/1.05      | m1_subset_1(X0_54,u1_struct_0(k3_lattice3(sK3))) != iProver_top ),
% 1.01/1.05      inference(predicate_to_equality,[status(thm)],[c_2575]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_2639,plain,
% 1.01/1.05      ( r2_lattice3(k3_lattice3(sK3),sK2,sK4) = iProver_top
% 1.01/1.05      | r2_hidden(sK1(k3_lattice3(sK3),sK2,sK4),sK2) = iProver_top
% 1.01/1.05      | m1_subset_1(sK4,u1_struct_0(k3_lattice3(sK3))) != iProver_top ),
% 1.01/1.05      inference(instantiation,[status(thm)],[c_2637]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_14,plain,
% 1.01/1.05      ( r2_lattice3(X0,X1,X2)
% 1.01/1.05      | ~ r1_orders_2(X0,sK1(X0,X1,X2),X2)
% 1.01/1.05      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.01/1.05      | ~ l1_orders_2(X0) ),
% 1.01/1.05      inference(cnf_transformation,[],[f83]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_1,plain,
% 1.01/1.05      ( r1_orders_2(X0,X1,X2)
% 1.01/1.05      | ~ r3_orders_2(X0,X1,X2)
% 1.01/1.05      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.01/1.05      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.01/1.05      | v2_struct_0(X0)
% 1.01/1.05      | ~ v3_orders_2(X0)
% 1.01/1.05      | ~ l1_orders_2(X0) ),
% 1.01/1.05      inference(cnf_transformation,[],[f66]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_411,plain,
% 1.01/1.05      ( r1_orders_2(X0,X1,X2)
% 1.01/1.05      | ~ r3_orders_2(X0,X1,X2)
% 1.01/1.05      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.01/1.05      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.01/1.05      | ~ l3_lattices(X3)
% 1.01/1.05      | ~ v10_lattices(X3)
% 1.01/1.05      | v2_struct_0(X0)
% 1.01/1.05      | v2_struct_0(X3)
% 1.01/1.05      | ~ l1_orders_2(X0)
% 1.01/1.05      | k3_lattice3(X3) != X0 ),
% 1.01/1.05      inference(resolution_lifted,[status(thm)],[c_1,c_19]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_412,plain,
% 1.01/1.05      ( r1_orders_2(k3_lattice3(X0),X1,X2)
% 1.01/1.05      | ~ r3_orders_2(k3_lattice3(X0),X1,X2)
% 1.01/1.05      | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(X0)))
% 1.01/1.05      | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(X0)))
% 1.01/1.05      | ~ l3_lattices(X0)
% 1.01/1.05      | ~ v10_lattices(X0)
% 1.01/1.05      | v2_struct_0(X0)
% 1.01/1.05      | v2_struct_0(k3_lattice3(X0))
% 1.01/1.05      | ~ l1_orders_2(k3_lattice3(X0)) ),
% 1.01/1.05      inference(unflattening,[status(thm)],[c_411]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_416,plain,
% 1.01/1.05      ( r1_orders_2(k3_lattice3(X0),X1,X2)
% 1.01/1.05      | ~ r3_orders_2(k3_lattice3(X0),X1,X2)
% 1.01/1.05      | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(X0)))
% 1.01/1.05      | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(X0)))
% 1.01/1.05      | ~ l3_lattices(X0)
% 1.01/1.05      | ~ v10_lattices(X0)
% 1.01/1.05      | v2_struct_0(X0) ),
% 1.01/1.05      inference(global_propositional_subsumption,
% 1.01/1.05                [status(thm)],
% 1.01/1.05                [c_412,c_23,c_18]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_888,plain,
% 1.01/1.05      ( r2_lattice3(X0,X1,X2)
% 1.01/1.05      | ~ r3_orders_2(k3_lattice3(X3),X4,X5)
% 1.01/1.05      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.01/1.05      | ~ m1_subset_1(X4,u1_struct_0(k3_lattice3(X3)))
% 1.01/1.05      | ~ m1_subset_1(X5,u1_struct_0(k3_lattice3(X3)))
% 1.01/1.05      | ~ l3_lattices(X3)
% 1.01/1.05      | ~ v10_lattices(X3)
% 1.01/1.05      | v2_struct_0(X3)
% 1.01/1.05      | ~ l1_orders_2(X0)
% 1.01/1.05      | X5 != X2
% 1.01/1.05      | sK1(X0,X1,X2) != X4
% 1.01/1.05      | k3_lattice3(X3) != X0 ),
% 1.01/1.05      inference(resolution_lifted,[status(thm)],[c_14,c_416]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_889,plain,
% 1.01/1.05      ( r2_lattice3(k3_lattice3(X0),X1,X2)
% 1.01/1.05      | ~ r3_orders_2(k3_lattice3(X0),sK1(k3_lattice3(X0),X1,X2),X2)
% 1.01/1.05      | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(X0)))
% 1.01/1.05      | ~ m1_subset_1(sK1(k3_lattice3(X0),X1,X2),u1_struct_0(k3_lattice3(X0)))
% 1.01/1.05      | ~ l3_lattices(X0)
% 1.01/1.05      | ~ v10_lattices(X0)
% 1.01/1.05      | v2_struct_0(X0)
% 1.01/1.05      | ~ l1_orders_2(k3_lattice3(X0)) ),
% 1.01/1.05      inference(unflattening,[status(thm)],[c_888]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_603,plain,
% 1.01/1.05      ( r2_lattice3(X0,X1,X2)
% 1.01/1.05      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.01/1.05      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
% 1.01/1.05      | ~ l3_lattices(X3)
% 1.01/1.05      | ~ v10_lattices(X3)
% 1.01/1.05      | v2_struct_0(X3)
% 1.01/1.05      | k3_lattice3(X3) != X0 ),
% 1.01/1.05      inference(resolution_lifted,[status(thm)],[c_16,c_18]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_604,plain,
% 1.01/1.05      ( r2_lattice3(k3_lattice3(X0),X1,X2)
% 1.01/1.05      | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(X0)))
% 1.01/1.05      | m1_subset_1(sK1(k3_lattice3(X0),X1,X2),u1_struct_0(k3_lattice3(X0)))
% 1.01/1.05      | ~ l3_lattices(X0)
% 1.01/1.05      | ~ v10_lattices(X0)
% 1.01/1.05      | v2_struct_0(X0) ),
% 1.01/1.05      inference(unflattening,[status(thm)],[c_603]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_893,plain,
% 1.01/1.05      ( v2_struct_0(X0)
% 1.01/1.05      | ~ v10_lattices(X0)
% 1.01/1.05      | ~ l3_lattices(X0)
% 1.01/1.05      | r2_lattice3(k3_lattice3(X0),X1,X2)
% 1.01/1.05      | ~ r3_orders_2(k3_lattice3(X0),sK1(k3_lattice3(X0),X1,X2),X2)
% 1.01/1.05      | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(X0))) ),
% 1.01/1.05      inference(global_propositional_subsumption,
% 1.01/1.05                [status(thm)],
% 1.01/1.05                [c_889,c_18,c_604]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_894,plain,
% 1.01/1.05      ( r2_lattice3(k3_lattice3(X0),X1,X2)
% 1.01/1.05      | ~ r3_orders_2(k3_lattice3(X0),sK1(k3_lattice3(X0),X1,X2),X2)
% 1.01/1.05      | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(X0)))
% 1.01/1.05      | ~ l3_lattices(X0)
% 1.01/1.05      | ~ v10_lattices(X0)
% 1.01/1.05      | v2_struct_0(X0) ),
% 1.01/1.05      inference(renaming,[status(thm)],[c_893]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_1469,plain,
% 1.01/1.05      ( r2_lattice3(k3_lattice3(X0),X1,X2)
% 1.01/1.05      | ~ r3_orders_2(k3_lattice3(X0),sK1(k3_lattice3(X0),X1,X2),X2)
% 1.01/1.05      | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(X0)))
% 1.01/1.05      | ~ l3_lattices(X0)
% 1.01/1.05      | v2_struct_0(X0)
% 1.01/1.05      | sK3 != X0 ),
% 1.01/1.05      inference(resolution_lifted,[status(thm)],[c_894,c_30]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_1470,plain,
% 1.01/1.05      ( r2_lattice3(k3_lattice3(sK3),X0,X1)
% 1.01/1.05      | ~ r3_orders_2(k3_lattice3(sK3),sK1(k3_lattice3(sK3),X0,X1),X1)
% 1.01/1.05      | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(sK3)))
% 1.01/1.05      | ~ l3_lattices(sK3)
% 1.01/1.05      | v2_struct_0(sK3) ),
% 1.01/1.05      inference(unflattening,[status(thm)],[c_1469]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_1474,plain,
% 1.01/1.05      ( r2_lattice3(k3_lattice3(sK3),X0,X1)
% 1.01/1.05      | ~ r3_orders_2(k3_lattice3(sK3),sK1(k3_lattice3(sK3),X0,X1),X1)
% 1.01/1.05      | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(sK3))) ),
% 1.01/1.05      inference(global_propositional_subsumption,
% 1.01/1.05                [status(thm)],
% 1.01/1.05                [c_1470,c_31,c_29]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_2582,plain,
% 1.01/1.05      ( r2_lattice3(k3_lattice3(sK3),X0_55,X0_54)
% 1.01/1.05      | ~ r3_orders_2(k3_lattice3(sK3),sK1(k3_lattice3(sK3),X0_55,X0_54),X0_54)
% 1.01/1.05      | ~ m1_subset_1(X0_54,u1_struct_0(k3_lattice3(sK3))) ),
% 1.01/1.05      inference(subtyping,[status(esa)],[c_1474]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_2618,plain,
% 1.01/1.05      ( r2_lattice3(k3_lattice3(sK3),X0_55,X0_54) = iProver_top
% 1.01/1.05      | r3_orders_2(k3_lattice3(sK3),sK1(k3_lattice3(sK3),X0_55,X0_54),X0_54) != iProver_top
% 1.01/1.05      | m1_subset_1(X0_54,u1_struct_0(k3_lattice3(sK3))) != iProver_top ),
% 1.01/1.05      inference(predicate_to_equality,[status(thm)],[c_2582]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(c_2620,plain,
% 1.01/1.05      ( r2_lattice3(k3_lattice3(sK3),sK2,sK4) = iProver_top
% 1.01/1.05      | r3_orders_2(k3_lattice3(sK3),sK1(k3_lattice3(sK3),sK2,sK4),sK4) != iProver_top
% 1.01/1.05      | m1_subset_1(sK4,u1_struct_0(k3_lattice3(sK3))) != iProver_top ),
% 1.01/1.05      inference(instantiation,[status(thm)],[c_2618]) ).
% 1.01/1.05  
% 1.01/1.05  cnf(contradiction,plain,
% 1.01/1.05      ( $false ),
% 1.01/1.05      inference(minisat,
% 1.01/1.05                [status(thm)],
% 1.01/1.05                [c_8589,c_6563,c_5504,c_4984,c_4436,c_4420,c_3434,c_3291,
% 1.01/1.05                 c_3279,c_3252,c_2639,c_2636,c_2631,c_2626,c_2620,c_2605,
% 1.01/1.05                 c_35,c_28]) ).
% 1.01/1.05  
% 1.01/1.05  
% 1.01/1.05  % SZS output end CNFRefutation for theBenchmark.p
% 1.01/1.05  
% 1.01/1.05  ------                               Statistics
% 1.01/1.05  
% 1.01/1.05  ------ General
% 1.01/1.05  
% 1.01/1.05  abstr_ref_over_cycles:                  0
% 1.01/1.05  abstr_ref_under_cycles:                 0
% 1.01/1.05  gc_basic_clause_elim:                   0
% 1.01/1.05  forced_gc_time:                         0
% 1.01/1.05  parsing_time:                           0.013
% 1.01/1.05  unif_index_cands_time:                  0.
% 1.01/1.05  unif_index_add_time:                    0.
% 1.01/1.05  orderings_time:                         0.
% 1.01/1.05  out_proof_time:                         0.017
% 1.01/1.05  total_time:                             0.262
% 1.01/1.05  num_of_symbols:                         57
% 1.01/1.05  num_of_terms:                           6505
% 1.01/1.05  
% 1.01/1.05  ------ Preprocessing
% 1.01/1.05  
% 1.01/1.05  num_of_splits:                          0
% 1.01/1.05  num_of_split_atoms:                     0
% 1.01/1.05  num_of_reused_defs:                     0
% 1.01/1.05  num_eq_ax_congr_red:                    43
% 1.01/1.05  num_of_sem_filtered_clauses:            1
% 1.01/1.05  num_of_subtypes:                        4
% 1.01/1.05  monotx_restored_types:                  0
% 1.01/1.05  sat_num_of_epr_types:                   0
% 1.01/1.05  sat_num_of_non_cyclic_types:            0
% 1.01/1.05  sat_guarded_non_collapsed_types:        1
% 1.01/1.05  num_pure_diseq_elim:                    0
% 1.01/1.05  simp_replaced_by:                       0
% 1.01/1.05  res_preprocessed:                       98
% 1.01/1.05  prep_upred:                             0
% 1.01/1.05  prep_unflattend:                        99
% 1.01/1.05  smt_new_axioms:                         0
% 1.01/1.05  pred_elim_cands:                        5
% 1.01/1.05  pred_elim:                              11
% 1.01/1.05  pred_elim_cl:                           13
% 1.01/1.05  pred_elim_cycles:                       19
% 1.01/1.05  merged_defs:                            8
% 1.01/1.05  merged_defs_ncl:                        0
% 1.01/1.05  bin_hyper_res:                          8
% 1.01/1.05  prep_cycles:                            4
% 1.01/1.05  pred_elim_time:                         0.038
% 1.01/1.05  splitting_time:                         0.
% 1.01/1.05  sem_filter_time:                        0.
% 1.01/1.05  monotx_time:                            0.
% 1.01/1.05  subtype_inf_time:                       0.
% 1.01/1.05  
% 1.01/1.05  ------ Problem properties
% 1.01/1.05  
% 1.01/1.05  clauses:                                17
% 1.01/1.05  conjectures:                            3
% 1.01/1.05  epr:                                    0
% 1.01/1.05  horn:                                   12
% 1.01/1.05  ground:                                 3
% 1.01/1.05  unary:                                  1
% 1.01/1.05  binary:                                 6
% 1.01/1.05  lits:                                   49
% 1.01/1.05  lits_eq:                                2
% 1.01/1.05  fd_pure:                                0
% 1.01/1.05  fd_pseudo:                              0
% 1.01/1.05  fd_cond:                                0
% 1.01/1.05  fd_pseudo_cond:                         0
% 1.01/1.05  ac_symbols:                             0
% 1.01/1.05  
% 1.01/1.05  ------ Propositional Solver
% 1.01/1.05  
% 1.01/1.05  prop_solver_calls:                      35
% 1.01/1.05  prop_fast_solver_calls:                 1475
% 1.01/1.05  smt_solver_calls:                       0
% 1.01/1.05  smt_fast_solver_calls:                  0
% 1.01/1.05  prop_num_of_clauses:                    2678
% 1.01/1.05  prop_preprocess_simplified:             5898
% 1.01/1.05  prop_fo_subsumed:                       54
% 1.01/1.05  prop_solver_time:                       0.
% 1.01/1.05  smt_solver_time:                        0.
% 1.01/1.05  smt_fast_solver_time:                   0.
% 1.01/1.05  prop_fast_solver_time:                  0.
% 1.01/1.05  prop_unsat_core_time:                   0.
% 1.01/1.05  
% 1.01/1.05  ------ QBF
% 1.01/1.05  
% 1.01/1.05  qbf_q_res:                              0
% 1.01/1.05  qbf_num_tautologies:                    0
% 1.01/1.05  qbf_prep_cycles:                        0
% 1.01/1.05  
% 1.01/1.05  ------ BMC1
% 1.01/1.05  
% 1.01/1.05  bmc1_current_bound:                     -1
% 1.01/1.05  bmc1_last_solved_bound:                 -1
% 1.01/1.05  bmc1_unsat_core_size:                   -1
% 1.01/1.05  bmc1_unsat_core_parents_size:           -1
% 1.01/1.05  bmc1_merge_next_fun:                    0
% 1.01/1.05  bmc1_unsat_core_clauses_time:           0.
% 1.01/1.05  
% 1.01/1.05  ------ Instantiation
% 1.01/1.05  
% 1.01/1.05  inst_num_of_clauses:                    572
% 1.01/1.05  inst_num_in_passive:                    84
% 1.01/1.05  inst_num_in_active:                     356
% 1.01/1.05  inst_num_in_unprocessed:                132
% 1.01/1.05  inst_num_of_loops:                      450
% 1.01/1.05  inst_num_of_learning_restarts:          0
% 1.01/1.05  inst_num_moves_active_passive:          85
% 1.01/1.05  inst_lit_activity:                      0
% 1.01/1.05  inst_lit_activity_moves:                0
% 1.01/1.05  inst_num_tautologies:                   0
% 1.01/1.05  inst_num_prop_implied:                  0
% 1.01/1.05  inst_num_existing_simplified:           0
% 1.01/1.05  inst_num_eq_res_simplified:             0
% 1.01/1.05  inst_num_child_elim:                    0
% 1.01/1.05  inst_num_of_dismatching_blockings:      249
% 1.01/1.05  inst_num_of_non_proper_insts:           827
% 1.01/1.05  inst_num_of_duplicates:                 0
% 1.01/1.05  inst_inst_num_from_inst_to_res:         0
% 1.01/1.05  inst_dismatching_checking_time:         0.
% 1.01/1.05  
% 1.01/1.05  ------ Resolution
% 1.01/1.05  
% 1.01/1.05  res_num_of_clauses:                     0
% 1.01/1.05  res_num_in_passive:                     0
% 1.01/1.05  res_num_in_active:                      0
% 1.01/1.05  res_num_of_loops:                       102
% 1.01/1.05  res_forward_subset_subsumed:            55
% 1.01/1.05  res_backward_subset_subsumed:           0
% 1.01/1.05  res_forward_subsumed:                   1
% 1.01/1.05  res_backward_subsumed:                  0
% 1.01/1.05  res_forward_subsumption_resolution:     6
% 1.01/1.05  res_backward_subsumption_resolution:    0
% 1.01/1.05  res_clause_to_clause_subsumption:       1780
% 1.01/1.05  res_orphan_elimination:                 0
% 1.01/1.05  res_tautology_del:                      140
% 1.01/1.05  res_num_eq_res_simplified:              0
% 1.01/1.05  res_num_sel_changes:                    0
% 1.01/1.05  res_moves_from_active_to_pass:          0
% 1.01/1.05  
% 1.01/1.05  ------ Superposition
% 1.01/1.05  
% 1.01/1.05  sup_time_total:                         0.
% 1.01/1.05  sup_time_generating:                    0.
% 1.01/1.05  sup_time_sim_full:                      0.
% 1.01/1.05  sup_time_sim_immed:                     0.
% 1.01/1.05  
% 1.01/1.05  sup_num_of_clauses:                     160
% 1.01/1.05  sup_num_in_active:                      88
% 1.01/1.05  sup_num_in_passive:                     72
% 1.01/1.05  sup_num_of_loops:                       89
% 1.01/1.05  sup_fw_superposition:                   156
% 1.01/1.05  sup_bw_superposition:                   51
% 1.01/1.05  sup_immediate_simplified:               80
% 1.01/1.05  sup_given_eliminated:                   0
% 1.01/1.05  comparisons_done:                       0
% 1.01/1.05  comparisons_avoided:                    0
% 1.01/1.05  
% 1.01/1.05  ------ Simplifications
% 1.01/1.05  
% 1.01/1.05  
% 1.01/1.05  sim_fw_subset_subsumed:                 3
% 1.01/1.05  sim_bw_subset_subsumed:                 0
% 1.01/1.05  sim_fw_subsumed:                        1
% 1.01/1.05  sim_bw_subsumed:                        0
% 1.01/1.05  sim_fw_subsumption_res:                 0
% 1.01/1.05  sim_bw_subsumption_res:                 0
% 1.01/1.05  sim_tautology_del:                      3
% 1.01/1.05  sim_eq_tautology_del:                   36
% 1.01/1.05  sim_eq_res_simp:                        0
% 1.01/1.05  sim_fw_demodulated:                     0
% 1.01/1.05  sim_bw_demodulated:                     2
% 1.01/1.05  sim_light_normalised:                   77
% 1.01/1.05  sim_joinable_taut:                      0
% 1.01/1.05  sim_joinable_simp:                      0
% 1.01/1.05  sim_ac_normalised:                      0
% 1.01/1.05  sim_smt_subsumption:                    0
% 1.01/1.05  
%------------------------------------------------------------------------------
