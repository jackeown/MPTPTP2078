%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:20:14 EST 2020

% Result     : Theorem 3.12s
% Output     : CNFRefutation 3.12s
% Verified   : 
% Statistics : Number of formulae       :  172 ( 317 expanded)
%              Number of clauses        :  100 ( 131 expanded)
%              Number of leaves         :   20 (  58 expanded)
%              Depth                    :   22
%              Number of atoms          :  608 (1027 expanded)
%              Number of equality atoms :  133 ( 194 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   10 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( r2_hidden(k1_xboole_0,X0)
       => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ( r2_hidden(k1_xboole_0,X0)
         => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f37,plain,(
    ? [X0] :
      ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0))
      & r2_hidden(k1_xboole_0,X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f38,plain,(
    ? [X0] :
      ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0))
      & r2_hidden(k1_xboole_0,X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f58,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0))
        & r2_hidden(k1_xboole_0,X0)
        & ~ v1_xboole_0(X0) )
   => ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK4))
      & r2_hidden(k1_xboole_0,sK4)
      & ~ v1_xboole_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
    ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK4))
    & r2_hidden(k1_xboole_0,sK4)
    & ~ v1_xboole_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f38,f58])).

fof(f92,plain,(
    r2_hidden(k1_xboole_0,sK4) ),
    inference(cnf_transformation,[],[f59])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f71,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f16,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
             => ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_orders_2(k2_yellow_1(X0),X1,X2)
                  | ~ r1_tarski(X1,X2) )
                & ( r1_tarski(X1,X2)
                  | ~ r3_orders_2(k2_yellow_1(X0),X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f48,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f13,axiom,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v4_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f22,plain,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f84,plain,(
    ! [X0] : v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f83,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f14,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_orders_2(k2_yellow_1(X0))
        & ~ v2_struct_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ~ v2_struct_0(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k2_yellow_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f86,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k2_yellow_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f15,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f87,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f8,axiom,(
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

fof(f29,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f29])).

fof(f49,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f50,plain,(
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
    inference(rectify,[],[f49])).

fof(f51,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK2(X0,X1,X2))
        & r2_hidden(sK2(X0,X1,X2),X1)
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,X2,sK2(X0,X1,X2))
                & r2_hidden(sK2(X0,X1,X2),X1)
                & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X2,X4)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f50,f51])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,X2,sK2(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_yellow_0(X0)
      <=> ? [X1] :
            ( r1_lattice3(X0,u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_yellow_0(X0)
      <=> ? [X1] :
            ( r1_lattice3(X0,u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f53,plain,(
    ! [X0] :
      ( ( ( v1_yellow_0(X0)
          | ! [X1] :
              ( ~ r1_lattice3(X0,u1_struct_0(X0),X1)
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ? [X1] :
              ( r1_lattice3(X0,u1_struct_0(X0),X1)
              & m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v1_yellow_0(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f54,plain,(
    ! [X0] :
      ( ( ( v1_yellow_0(X0)
          | ! [X1] :
              ( ~ r1_lattice3(X0,u1_struct_0(X0),X1)
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ? [X2] :
              ( r1_lattice3(X0,u1_struct_0(X0),X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v1_yellow_0(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f53])).

fof(f55,plain,(
    ! [X0] :
      ( ? [X2] :
          ( r1_lattice3(X0,u1_struct_0(X0),X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( r1_lattice3(X0,u1_struct_0(X0),sK3(X0))
        & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0] :
      ( ( ( v1_yellow_0(X0)
          | ! [X1] :
              ( ~ r1_lattice3(X0,u1_struct_0(X0),X1)
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ( r1_lattice3(X0,u1_struct_0(X0),sK3(X0))
            & m1_subset_1(sK3(X0),u1_struct_0(X0)) )
          | ~ v1_yellow_0(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f54,f55])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v1_yellow_0(X0)
      | ~ r1_lattice3(X0,u1_struct_0(X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f81,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | r2_hidden(sK2(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f39])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f40,f41])).

fof(f60,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,k3_yellow_0(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,k3_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,k3_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r1_orders_2(X0,k3_yellow_0(X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f85,plain,(
    ! [X0] : v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X2)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f4,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f66,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f93,plain,(
    k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK4)) ),
    inference(cnf_transformation,[],[f59])).

fof(f91,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_32,negated_conjecture,
    ( r2_hidden(k1_xboole_0,sK4) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_2763,plain,
    ( r2_hidden(k1_xboole_0,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_11,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2764,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3147,plain,
    ( m1_subset_1(k1_xboole_0,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2763,c_2764])).

cnf(c_5,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2769,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_29,plain,
    ( r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ r1_tarski(X1,X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_13,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_25,plain,
    ( v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_387,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | k2_yellow_1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_25])).

cnf(c_388,plain,
    ( r1_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | v2_struct_0(k2_yellow_1(X0))
    | ~ l1_orders_2(k2_yellow_1(X0)) ),
    inference(unflattening,[status(thm)],[c_387])).

cnf(c_23,plain,
    ( l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_392,plain,
    ( v2_struct_0(k2_yellow_1(X0))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
    | r1_orders_2(k2_yellow_1(X0),X1,X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_388,c_23])).

cnf(c_393,plain,
    ( r1_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | v2_struct_0(k2_yellow_1(X0)) ),
    inference(renaming,[status(thm)],[c_392])).

cnf(c_26,plain,
    ( ~ v2_struct_0(k2_yellow_1(X0))
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_473,plain,
    ( r1_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | v1_xboole_0(X0) ),
    inference(resolution,[status(thm)],[c_393,c_26])).

cnf(c_821,plain,
    ( r1_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ r1_tarski(X1,X2)
    | v1_xboole_0(X0) ),
    inference(resolution,[status(thm)],[c_29,c_473])).

cnf(c_2751,plain,
    ( r1_orders_2(k2_yellow_1(X0),X1,X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_821])).

cnf(c_28,plain,
    ( u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2885,plain,
    ( r1_orders_2(k2_yellow_1(X0),X1,X2) = iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2751,c_28])).

cnf(c_14,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK2(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_700,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK2(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | k2_yellow_1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_23])).

cnf(c_701,plain,
    ( r1_lattice3(k2_yellow_1(X0),X1,X2)
    | ~ r1_orders_2(k2_yellow_1(X0),X2,sK2(k2_yellow_1(X0),X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) ),
    inference(unflattening,[status(thm)],[c_700])).

cnf(c_2753,plain,
    ( r1_lattice3(k2_yellow_1(X0),X1,X2) = iProver_top
    | r1_orders_2(k2_yellow_1(X0),X2,sK2(k2_yellow_1(X0),X1,X2)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_701])).

cnf(c_2869,plain,
    ( r1_lattice3(k2_yellow_1(X0),X1,X2) = iProver_top
    | r1_orders_2(k2_yellow_1(X0),X2,sK2(k2_yellow_1(X0),X1,X2)) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2753,c_28])).

cnf(c_4285,plain,
    ( r1_lattice3(k2_yellow_1(X0),X1,X2) = iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(sK2(k2_yellow_1(X0),X1,X2),X0) != iProver_top
    | r1_tarski(X2,sK2(k2_yellow_1(X0),X1,X2)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2885,c_2869])).

cnf(c_16,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_670,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
    | k2_yellow_1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_23])).

cnf(c_671,plain,
    ( r1_lattice3(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | m1_subset_1(sK2(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0))) ),
    inference(unflattening,[status(thm)],[c_670])).

cnf(c_2755,plain,
    ( r1_lattice3(k2_yellow_1(X0),X1,X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | m1_subset_1(sK2(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_671])).

cnf(c_2862,plain,
    ( r1_lattice3(k2_yellow_1(X0),X1,X2) = iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(sK2(k2_yellow_1(X0),X1,X2),X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2755,c_28])).

cnf(c_11095,plain,
    ( m1_subset_1(X2,X0) != iProver_top
    | r1_lattice3(k2_yellow_1(X0),X1,X2) = iProver_top
    | r1_tarski(X2,sK2(k2_yellow_1(X0),X1,X2)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4285,c_2862])).

cnf(c_11096,plain,
    ( r1_lattice3(k2_yellow_1(X0),X1,X2) = iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | r1_tarski(X2,sK2(k2_yellow_1(X0),X1,X2)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_11095])).

cnf(c_11106,plain,
    ( r1_lattice3(k2_yellow_1(X0),X1,k1_xboole_0) = iProver_top
    | m1_subset_1(k1_xboole_0,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2769,c_11096])).

cnf(c_18,plain,
    ( ~ r1_lattice3(X0,u1_struct_0(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v1_yellow_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_634,plain,
    ( ~ r1_lattice3(X0,u1_struct_0(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v1_yellow_0(X0)
    | k2_yellow_1(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_23])).

cnf(c_635,plain,
    ( ~ r1_lattice3(k2_yellow_1(X0),u1_struct_0(k2_yellow_1(X0)),X1)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | v1_yellow_0(k2_yellow_1(X0)) ),
    inference(unflattening,[status(thm)],[c_634])).

cnf(c_2757,plain,
    ( r1_lattice3(k2_yellow_1(X0),u1_struct_0(k2_yellow_1(X0)),X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | v1_yellow_0(k2_yellow_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_635])).

cnf(c_2848,plain,
    ( r1_lattice3(k2_yellow_1(X0),X0,X1) != iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | v1_yellow_0(k2_yellow_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2757,c_28])).

cnf(c_11277,plain,
    ( m1_subset_1(k1_xboole_0,X0) != iProver_top
    | v1_yellow_0(k2_yellow_1(X0)) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_11106,c_2848])).

cnf(c_21,plain,
    ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_601,plain,
    ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
    | k2_yellow_1(X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_23])).

cnf(c_602,plain,
    ( m1_subset_1(k3_yellow_0(k2_yellow_1(X0)),u1_struct_0(k2_yellow_1(X0))) ),
    inference(unflattening,[status(thm)],[c_601])).

cnf(c_2760,plain,
    ( m1_subset_1(k3_yellow_0(k2_yellow_1(X0)),u1_struct_0(k2_yellow_1(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_602])).

cnf(c_2787,plain,
    ( m1_subset_1(k3_yellow_0(k2_yellow_1(X0)),X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2760,c_28])).

cnf(c_15,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK2(X0,X1,X2),X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_685,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK2(X0,X1,X2),X1)
    | k2_yellow_1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_23])).

cnf(c_686,plain,
    ( r1_lattice3(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | r2_hidden(sK2(k2_yellow_1(X0),X1,X2),X1) ),
    inference(unflattening,[status(thm)],[c_685])).

cnf(c_2754,plain,
    ( r1_lattice3(k2_yellow_1(X0),X1,X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | r2_hidden(sK2(k2_yellow_1(X0),X1,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_686])).

cnf(c_2855,plain,
    ( r1_lattice3(k2_yellow_1(X0),X1,X2) = iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | r2_hidden(sK2(k2_yellow_1(X0),X1,X2),X1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2754,c_28])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2773,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3701,plain,
    ( r1_lattice3(k2_yellow_1(X0),X1,X2) = iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2855,c_2773])).

cnf(c_4440,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | v1_yellow_0(k2_yellow_1(X1)) = iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3701,c_2848])).

cnf(c_4575,plain,
    ( v1_yellow_0(k2_yellow_1(X0)) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2787,c_4440])).

cnf(c_11301,plain,
    ( v1_yellow_0(k2_yellow_1(X0)) = iProver_top
    | m1_subset_1(k1_xboole_0,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11277,c_4575])).

cnf(c_11302,plain,
    ( m1_subset_1(k1_xboole_0,X0) != iProver_top
    | v1_yellow_0(k2_yellow_1(X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_11301])).

cnf(c_11310,plain,
    ( v1_yellow_0(k2_yellow_1(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3147,c_11302])).

cnf(c_3920,plain,
    ( m1_subset_1(k3_yellow_0(k2_yellow_1(sK4)),u1_struct_0(k2_yellow_1(sK4))) ),
    inference(instantiation,[status(thm)],[c_602])).

cnf(c_3925,plain,
    ( m1_subset_1(k3_yellow_0(k2_yellow_1(sK4)),u1_struct_0(k2_yellow_1(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3920])).

cnf(c_3300,plain,
    ( m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
    | ~ r2_hidden(X0,u1_struct_0(k2_yellow_1(X1))) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_3860,plain,
    ( m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK4)))
    | ~ r2_hidden(k1_xboole_0,u1_struct_0(k2_yellow_1(sK4))) ),
    inference(instantiation,[status(thm)],[c_3300])).

cnf(c_3861,plain,
    ( m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK4))) = iProver_top
    | r2_hidden(k1_xboole_0,u1_struct_0(k2_yellow_1(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3860])).

cnf(c_22,plain,
    ( r1_orders_2(X0,k3_yellow_0(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v1_yellow_0(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_24,plain,
    ( v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_358,plain,
    ( r1_orders_2(X0,k3_yellow_0(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v1_yellow_0(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | k2_yellow_1(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_24])).

cnf(c_359,plain,
    ( r1_orders_2(k2_yellow_1(X0),k3_yellow_0(k2_yellow_1(X0)),X1)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ v1_yellow_0(k2_yellow_1(X0))
    | v2_struct_0(k2_yellow_1(X0))
    | ~ l1_orders_2(k2_yellow_1(X0)) ),
    inference(unflattening,[status(thm)],[c_358])).

cnf(c_363,plain,
    ( v2_struct_0(k2_yellow_1(X0))
    | ~ v1_yellow_0(k2_yellow_1(X0))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | r1_orders_2(k2_yellow_1(X0),k3_yellow_0(k2_yellow_1(X0)),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_359,c_23])).

cnf(c_364,plain,
    ( r1_orders_2(k2_yellow_1(X0),k3_yellow_0(k2_yellow_1(X0)),X1)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ v1_yellow_0(k2_yellow_1(X0))
    | v2_struct_0(k2_yellow_1(X0)) ),
    inference(renaming,[status(thm)],[c_363])).

cnf(c_493,plain,
    ( r1_orders_2(k2_yellow_1(X0),k3_yellow_0(k2_yellow_1(X0)),X1)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ v1_yellow_0(k2_yellow_1(X0))
    | v1_xboole_0(X0) ),
    inference(resolution,[status(thm)],[c_364,c_26])).

cnf(c_3729,plain,
    ( r1_orders_2(k2_yellow_1(sK4),k3_yellow_0(k2_yellow_1(sK4)),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK4)))
    | ~ v1_yellow_0(k2_yellow_1(sK4))
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_493])).

cnf(c_3732,plain,
    ( r1_orders_2(k2_yellow_1(sK4),k3_yellow_0(k2_yellow_1(sK4)),k1_xboole_0) = iProver_top
    | m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK4))) != iProver_top
    | v1_yellow_0(k2_yellow_1(sK4)) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3729])).

cnf(c_12,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_414,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | k2_yellow_1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_25])).

cnf(c_415,plain,
    ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
    | r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | v2_struct_0(k2_yellow_1(X0))
    | ~ l1_orders_2(k2_yellow_1(X0)) ),
    inference(unflattening,[status(thm)],[c_414])).

cnf(c_419,plain,
    ( v2_struct_0(k2_yellow_1(X0))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ r1_orders_2(k2_yellow_1(X0),X1,X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_415,c_23])).

cnf(c_420,plain,
    ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
    | r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | v2_struct_0(k2_yellow_1(X0)) ),
    inference(renaming,[status(thm)],[c_419])).

cnf(c_453,plain,
    ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
    | r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | v1_xboole_0(X0) ),
    inference(resolution,[status(thm)],[c_420,c_26])).

cnf(c_30,plain,
    ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | r1_tarski(X1,X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_803,plain,
    ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | r1_tarski(X1,X2)
    | v1_xboole_0(X0) ),
    inference(resolution,[status(thm)],[c_453,c_30])).

cnf(c_3090,plain,
    ( ~ r1_orders_2(k2_yellow_1(X0),k3_yellow_0(k2_yellow_1(sK4)),k1_xboole_0)
    | ~ m1_subset_1(k3_yellow_0(k2_yellow_1(sK4)),u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(X0)))
    | r1_tarski(k3_yellow_0(k2_yellow_1(sK4)),k1_xboole_0)
    | v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_803])).

cnf(c_3727,plain,
    ( ~ r1_orders_2(k2_yellow_1(sK4),k3_yellow_0(k2_yellow_1(sK4)),k1_xboole_0)
    | ~ m1_subset_1(k3_yellow_0(k2_yellow_1(sK4)),u1_struct_0(k2_yellow_1(sK4)))
    | ~ m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK4)))
    | r1_tarski(k3_yellow_0(k2_yellow_1(sK4)),k1_xboole_0)
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_3090])).

cnf(c_3730,plain,
    ( r1_orders_2(k2_yellow_1(sK4),k3_yellow_0(k2_yellow_1(sK4)),k1_xboole_0) != iProver_top
    | m1_subset_1(k3_yellow_0(k2_yellow_1(sK4)),u1_struct_0(k2_yellow_1(sK4))) != iProver_top
    | m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK4))) != iProver_top
    | r1_tarski(k3_yellow_0(k2_yellow_1(sK4)),k1_xboole_0) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3727])).

cnf(c_3133,plain,
    ( u1_struct_0(k2_yellow_1(sK4)) = sK4 ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_2281,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3038,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k1_xboole_0,sK4)
    | X1 != sK4
    | X0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2281])).

cnf(c_3132,plain,
    ( r2_hidden(X0,u1_struct_0(k2_yellow_1(sK4)))
    | ~ r2_hidden(k1_xboole_0,sK4)
    | X0 != k1_xboole_0
    | u1_struct_0(k2_yellow_1(sK4)) != sK4 ),
    inference(instantiation,[status(thm)],[c_3038])).

cnf(c_3134,plain,
    ( X0 != k1_xboole_0
    | u1_struct_0(k2_yellow_1(sK4)) != sK4
    | r2_hidden(X0,u1_struct_0(k2_yellow_1(sK4))) = iProver_top
    | r2_hidden(k1_xboole_0,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3132])).

cnf(c_3136,plain,
    ( u1_struct_0(k2_yellow_1(sK4)) != sK4
    | k1_xboole_0 != k1_xboole_0
    | r2_hidden(k1_xboole_0,u1_struct_0(k2_yellow_1(sK4))) = iProver_top
    | r2_hidden(k1_xboole_0,sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3134])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2993,plain,
    ( ~ r1_tarski(k3_yellow_0(k2_yellow_1(sK4)),k1_xboole_0)
    | k1_xboole_0 = k3_yellow_0(k2_yellow_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2994,plain,
    ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(sK4))
    | r1_tarski(k3_yellow_0(k2_yellow_1(sK4)),k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2993])).

cnf(c_104,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_101,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_31,negated_conjecture,
    ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK4)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_35,plain,
    ( r2_hidden(k1_xboole_0,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_33,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_34,plain,
    ( v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11310,c_3925,c_3861,c_3732,c_3730,c_3133,c_3136,c_2994,c_104,c_101,c_31,c_35,c_34])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:48:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.12/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.12/0.99  
% 3.12/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.12/0.99  
% 3.12/0.99  ------  iProver source info
% 3.12/0.99  
% 3.12/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.12/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.12/0.99  git: non_committed_changes: false
% 3.12/0.99  git: last_make_outside_of_git: false
% 3.12/0.99  
% 3.12/0.99  ------ 
% 3.12/0.99  
% 3.12/0.99  ------ Input Options
% 3.12/0.99  
% 3.12/0.99  --out_options                           all
% 3.12/0.99  --tptp_safe_out                         true
% 3.12/0.99  --problem_path                          ""
% 3.12/0.99  --include_path                          ""
% 3.12/0.99  --clausifier                            res/vclausify_rel
% 3.12/0.99  --clausifier_options                    --mode clausify
% 3.12/0.99  --stdin                                 false
% 3.12/0.99  --stats_out                             all
% 3.12/0.99  
% 3.12/0.99  ------ General Options
% 3.12/0.99  
% 3.12/0.99  --fof                                   false
% 3.12/0.99  --time_out_real                         305.
% 3.12/0.99  --time_out_virtual                      -1.
% 3.12/0.99  --symbol_type_check                     false
% 3.12/0.99  --clausify_out                          false
% 3.12/0.99  --sig_cnt_out                           false
% 3.12/0.99  --trig_cnt_out                          false
% 3.12/0.99  --trig_cnt_out_tolerance                1.
% 3.12/0.99  --trig_cnt_out_sk_spl                   false
% 3.12/0.99  --abstr_cl_out                          false
% 3.12/0.99  
% 3.12/0.99  ------ Global Options
% 3.12/0.99  
% 3.12/0.99  --schedule                              default
% 3.12/0.99  --add_important_lit                     false
% 3.12/0.99  --prop_solver_per_cl                    1000
% 3.12/0.99  --min_unsat_core                        false
% 3.12/0.99  --soft_assumptions                      false
% 3.12/0.99  --soft_lemma_size                       3
% 3.12/0.99  --prop_impl_unit_size                   0
% 3.12/0.99  --prop_impl_unit                        []
% 3.12/0.99  --share_sel_clauses                     true
% 3.12/0.99  --reset_solvers                         false
% 3.12/0.99  --bc_imp_inh                            [conj_cone]
% 3.12/0.99  --conj_cone_tolerance                   3.
% 3.12/0.99  --extra_neg_conj                        none
% 3.12/0.99  --large_theory_mode                     true
% 3.12/0.99  --prolific_symb_bound                   200
% 3.12/0.99  --lt_threshold                          2000
% 3.12/0.99  --clause_weak_htbl                      true
% 3.12/0.99  --gc_record_bc_elim                     false
% 3.12/0.99  
% 3.12/0.99  ------ Preprocessing Options
% 3.12/0.99  
% 3.12/0.99  --preprocessing_flag                    true
% 3.12/0.99  --time_out_prep_mult                    0.1
% 3.12/0.99  --splitting_mode                        input
% 3.12/0.99  --splitting_grd                         true
% 3.12/0.99  --splitting_cvd                         false
% 3.12/0.99  --splitting_cvd_svl                     false
% 3.12/0.99  --splitting_nvd                         32
% 3.12/0.99  --sub_typing                            true
% 3.12/0.99  --prep_gs_sim                           true
% 3.12/0.99  --prep_unflatten                        true
% 3.12/0.99  --prep_res_sim                          true
% 3.12/0.99  --prep_upred                            true
% 3.12/0.99  --prep_sem_filter                       exhaustive
% 3.12/0.99  --prep_sem_filter_out                   false
% 3.12/0.99  --pred_elim                             true
% 3.12/0.99  --res_sim_input                         true
% 3.12/0.99  --eq_ax_congr_red                       true
% 3.12/0.99  --pure_diseq_elim                       true
% 3.12/0.99  --brand_transform                       false
% 3.12/0.99  --non_eq_to_eq                          false
% 3.12/0.99  --prep_def_merge                        true
% 3.12/0.99  --prep_def_merge_prop_impl              false
% 3.12/0.99  --prep_def_merge_mbd                    true
% 3.12/0.99  --prep_def_merge_tr_red                 false
% 3.12/0.99  --prep_def_merge_tr_cl                  false
% 3.12/0.99  --smt_preprocessing                     true
% 3.12/0.99  --smt_ac_axioms                         fast
% 3.12/0.99  --preprocessed_out                      false
% 3.12/0.99  --preprocessed_stats                    false
% 3.12/0.99  
% 3.12/0.99  ------ Abstraction refinement Options
% 3.12/0.99  
% 3.12/0.99  --abstr_ref                             []
% 3.12/0.99  --abstr_ref_prep                        false
% 3.12/0.99  --abstr_ref_until_sat                   false
% 3.12/0.99  --abstr_ref_sig_restrict                funpre
% 3.12/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.12/0.99  --abstr_ref_under                       []
% 3.12/0.99  
% 3.12/0.99  ------ SAT Options
% 3.12/0.99  
% 3.12/0.99  --sat_mode                              false
% 3.12/0.99  --sat_fm_restart_options                ""
% 3.12/0.99  --sat_gr_def                            false
% 3.12/0.99  --sat_epr_types                         true
% 3.12/0.99  --sat_non_cyclic_types                  false
% 3.12/0.99  --sat_finite_models                     false
% 3.12/0.99  --sat_fm_lemmas                         false
% 3.12/0.99  --sat_fm_prep                           false
% 3.12/0.99  --sat_fm_uc_incr                        true
% 3.12/0.99  --sat_out_model                         small
% 3.12/0.99  --sat_out_clauses                       false
% 3.12/0.99  
% 3.12/0.99  ------ QBF Options
% 3.12/0.99  
% 3.12/0.99  --qbf_mode                              false
% 3.12/0.99  --qbf_elim_univ                         false
% 3.12/0.99  --qbf_dom_inst                          none
% 3.12/0.99  --qbf_dom_pre_inst                      false
% 3.12/0.99  --qbf_sk_in                             false
% 3.12/0.99  --qbf_pred_elim                         true
% 3.12/0.99  --qbf_split                             512
% 3.12/0.99  
% 3.12/0.99  ------ BMC1 Options
% 3.12/0.99  
% 3.12/0.99  --bmc1_incremental                      false
% 3.12/0.99  --bmc1_axioms                           reachable_all
% 3.12/0.99  --bmc1_min_bound                        0
% 3.12/0.99  --bmc1_max_bound                        -1
% 3.12/0.99  --bmc1_max_bound_default                -1
% 3.12/0.99  --bmc1_symbol_reachability              true
% 3.12/0.99  --bmc1_property_lemmas                  false
% 3.12/0.99  --bmc1_k_induction                      false
% 3.12/0.99  --bmc1_non_equiv_states                 false
% 3.12/0.99  --bmc1_deadlock                         false
% 3.12/0.99  --bmc1_ucm                              false
% 3.12/0.99  --bmc1_add_unsat_core                   none
% 3.12/0.99  --bmc1_unsat_core_children              false
% 3.12/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.12/0.99  --bmc1_out_stat                         full
% 3.12/0.99  --bmc1_ground_init                      false
% 3.12/0.99  --bmc1_pre_inst_next_state              false
% 3.12/0.99  --bmc1_pre_inst_state                   false
% 3.12/0.99  --bmc1_pre_inst_reach_state             false
% 3.12/0.99  --bmc1_out_unsat_core                   false
% 3.12/0.99  --bmc1_aig_witness_out                  false
% 3.12/0.99  --bmc1_verbose                          false
% 3.12/0.99  --bmc1_dump_clauses_tptp                false
% 3.12/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.12/0.99  --bmc1_dump_file                        -
% 3.12/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.12/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.12/0.99  --bmc1_ucm_extend_mode                  1
% 3.12/0.99  --bmc1_ucm_init_mode                    2
% 3.12/0.99  --bmc1_ucm_cone_mode                    none
% 3.12/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.12/0.99  --bmc1_ucm_relax_model                  4
% 3.12/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.12/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.12/0.99  --bmc1_ucm_layered_model                none
% 3.12/0.99  --bmc1_ucm_max_lemma_size               10
% 3.12/0.99  
% 3.12/0.99  ------ AIG Options
% 3.12/0.99  
% 3.12/0.99  --aig_mode                              false
% 3.12/0.99  
% 3.12/0.99  ------ Instantiation Options
% 3.12/0.99  
% 3.12/0.99  --instantiation_flag                    true
% 3.12/0.99  --inst_sos_flag                         false
% 3.12/0.99  --inst_sos_phase                        true
% 3.12/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.12/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.12/0.99  --inst_lit_sel_side                     num_symb
% 3.12/0.99  --inst_solver_per_active                1400
% 3.12/0.99  --inst_solver_calls_frac                1.
% 3.12/0.99  --inst_passive_queue_type               priority_queues
% 3.12/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.12/0.99  --inst_passive_queues_freq              [25;2]
% 3.12/0.99  --inst_dismatching                      true
% 3.12/0.99  --inst_eager_unprocessed_to_passive     true
% 3.12/0.99  --inst_prop_sim_given                   true
% 3.12/0.99  --inst_prop_sim_new                     false
% 3.12/0.99  --inst_subs_new                         false
% 3.12/0.99  --inst_eq_res_simp                      false
% 3.12/0.99  --inst_subs_given                       false
% 3.12/0.99  --inst_orphan_elimination               true
% 3.12/0.99  --inst_learning_loop_flag               true
% 3.12/0.99  --inst_learning_start                   3000
% 3.12/0.99  --inst_learning_factor                  2
% 3.12/0.99  --inst_start_prop_sim_after_learn       3
% 3.12/0.99  --inst_sel_renew                        solver
% 3.12/0.99  --inst_lit_activity_flag                true
% 3.12/0.99  --inst_restr_to_given                   false
% 3.12/0.99  --inst_activity_threshold               500
% 3.12/0.99  --inst_out_proof                        true
% 3.12/0.99  
% 3.12/0.99  ------ Resolution Options
% 3.12/0.99  
% 3.12/0.99  --resolution_flag                       true
% 3.12/0.99  --res_lit_sel                           adaptive
% 3.12/0.99  --res_lit_sel_side                      none
% 3.12/0.99  --res_ordering                          kbo
% 3.12/0.99  --res_to_prop_solver                    active
% 3.12/0.99  --res_prop_simpl_new                    false
% 3.12/0.99  --res_prop_simpl_given                  true
% 3.12/0.99  --res_passive_queue_type                priority_queues
% 3.12/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.12/0.99  --res_passive_queues_freq               [15;5]
% 3.12/0.99  --res_forward_subs                      full
% 3.12/0.99  --res_backward_subs                     full
% 3.12/0.99  --res_forward_subs_resolution           true
% 3.12/0.99  --res_backward_subs_resolution          true
% 3.12/0.99  --res_orphan_elimination                true
% 3.12/0.99  --res_time_limit                        2.
% 3.12/0.99  --res_out_proof                         true
% 3.12/0.99  
% 3.12/0.99  ------ Superposition Options
% 3.12/0.99  
% 3.12/0.99  --superposition_flag                    true
% 3.12/0.99  --sup_passive_queue_type                priority_queues
% 3.12/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.12/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.12/0.99  --demod_completeness_check              fast
% 3.12/0.99  --demod_use_ground                      true
% 3.12/0.99  --sup_to_prop_solver                    passive
% 3.12/0.99  --sup_prop_simpl_new                    true
% 3.12/0.99  --sup_prop_simpl_given                  true
% 3.12/0.99  --sup_fun_splitting                     false
% 3.12/0.99  --sup_smt_interval                      50000
% 3.12/0.99  
% 3.12/0.99  ------ Superposition Simplification Setup
% 3.12/0.99  
% 3.12/0.99  --sup_indices_passive                   []
% 3.12/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.12/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.12/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.12/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.12/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.12/0.99  --sup_full_bw                           [BwDemod]
% 3.12/0.99  --sup_immed_triv                        [TrivRules]
% 3.12/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.12/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.12/0.99  --sup_immed_bw_main                     []
% 3.12/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.12/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.12/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.12/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.12/0.99  
% 3.12/0.99  ------ Combination Options
% 3.12/0.99  
% 3.12/0.99  --comb_res_mult                         3
% 3.12/0.99  --comb_sup_mult                         2
% 3.12/0.99  --comb_inst_mult                        10
% 3.12/0.99  
% 3.12/0.99  ------ Debug Options
% 3.12/0.99  
% 3.12/0.99  --dbg_backtrace                         false
% 3.12/0.99  --dbg_dump_prop_clauses                 false
% 3.12/0.99  --dbg_dump_prop_clauses_file            -
% 3.12/0.99  --dbg_out_stat                          false
% 3.12/0.99  ------ Parsing...
% 3.12/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.12/0.99  
% 3.12/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 3.12/0.99  
% 3.12/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.12/0.99  
% 3.12/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.12/0.99  ------ Proving...
% 3.12/0.99  ------ Problem Properties 
% 3.12/0.99  
% 3.12/0.99  
% 3.12/0.99  clauses                                 27
% 3.12/0.99  conjectures                             3
% 3.12/0.99  EPR                                     10
% 3.12/0.99  Horn                                    19
% 3.12/0.99  unary                                   7
% 3.12/0.99  binary                                  8
% 3.12/0.99  lits                                    66
% 3.12/0.99  lits eq                                 4
% 3.12/0.99  fd_pure                                 0
% 3.12/0.99  fd_pseudo                               0
% 3.12/0.99  fd_cond                                 1
% 3.12/0.99  fd_pseudo_cond                          0
% 3.12/0.99  AC symbols                              0
% 3.12/0.99  
% 3.12/0.99  ------ Schedule dynamic 5 is on 
% 3.12/0.99  
% 3.12/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.12/0.99  
% 3.12/0.99  
% 3.12/0.99  ------ 
% 3.12/0.99  Current options:
% 3.12/0.99  ------ 
% 3.12/0.99  
% 3.12/0.99  ------ Input Options
% 3.12/0.99  
% 3.12/0.99  --out_options                           all
% 3.12/0.99  --tptp_safe_out                         true
% 3.12/0.99  --problem_path                          ""
% 3.12/0.99  --include_path                          ""
% 3.12/0.99  --clausifier                            res/vclausify_rel
% 3.12/0.99  --clausifier_options                    --mode clausify
% 3.12/0.99  --stdin                                 false
% 3.12/0.99  --stats_out                             all
% 3.12/0.99  
% 3.12/0.99  ------ General Options
% 3.12/0.99  
% 3.12/0.99  --fof                                   false
% 3.12/0.99  --time_out_real                         305.
% 3.12/0.99  --time_out_virtual                      -1.
% 3.12/0.99  --symbol_type_check                     false
% 3.12/0.99  --clausify_out                          false
% 3.12/0.99  --sig_cnt_out                           false
% 3.12/0.99  --trig_cnt_out                          false
% 3.12/0.99  --trig_cnt_out_tolerance                1.
% 3.12/0.99  --trig_cnt_out_sk_spl                   false
% 3.12/0.99  --abstr_cl_out                          false
% 3.12/0.99  
% 3.12/0.99  ------ Global Options
% 3.12/0.99  
% 3.12/0.99  --schedule                              default
% 3.12/0.99  --add_important_lit                     false
% 3.12/0.99  --prop_solver_per_cl                    1000
% 3.12/0.99  --min_unsat_core                        false
% 3.12/0.99  --soft_assumptions                      false
% 3.12/0.99  --soft_lemma_size                       3
% 3.12/0.99  --prop_impl_unit_size                   0
% 3.12/0.99  --prop_impl_unit                        []
% 3.12/0.99  --share_sel_clauses                     true
% 3.12/0.99  --reset_solvers                         false
% 3.12/0.99  --bc_imp_inh                            [conj_cone]
% 3.12/0.99  --conj_cone_tolerance                   3.
% 3.12/0.99  --extra_neg_conj                        none
% 3.12/0.99  --large_theory_mode                     true
% 3.12/0.99  --prolific_symb_bound                   200
% 3.12/0.99  --lt_threshold                          2000
% 3.12/0.99  --clause_weak_htbl                      true
% 3.12/0.99  --gc_record_bc_elim                     false
% 3.12/0.99  
% 3.12/0.99  ------ Preprocessing Options
% 3.12/0.99  
% 3.12/0.99  --preprocessing_flag                    true
% 3.12/0.99  --time_out_prep_mult                    0.1
% 3.12/0.99  --splitting_mode                        input
% 3.12/0.99  --splitting_grd                         true
% 3.12/0.99  --splitting_cvd                         false
% 3.12/0.99  --splitting_cvd_svl                     false
% 3.12/0.99  --splitting_nvd                         32
% 3.12/0.99  --sub_typing                            true
% 3.12/0.99  --prep_gs_sim                           true
% 3.12/0.99  --prep_unflatten                        true
% 3.12/0.99  --prep_res_sim                          true
% 3.12/0.99  --prep_upred                            true
% 3.12/0.99  --prep_sem_filter                       exhaustive
% 3.12/0.99  --prep_sem_filter_out                   false
% 3.12/0.99  --pred_elim                             true
% 3.12/0.99  --res_sim_input                         true
% 3.12/0.99  --eq_ax_congr_red                       true
% 3.12/0.99  --pure_diseq_elim                       true
% 3.12/0.99  --brand_transform                       false
% 3.12/0.99  --non_eq_to_eq                          false
% 3.12/0.99  --prep_def_merge                        true
% 3.12/0.99  --prep_def_merge_prop_impl              false
% 3.12/0.99  --prep_def_merge_mbd                    true
% 3.12/0.99  --prep_def_merge_tr_red                 false
% 3.12/0.99  --prep_def_merge_tr_cl                  false
% 3.12/0.99  --smt_preprocessing                     true
% 3.12/0.99  --smt_ac_axioms                         fast
% 3.12/0.99  --preprocessed_out                      false
% 3.12/0.99  --preprocessed_stats                    false
% 3.12/0.99  
% 3.12/0.99  ------ Abstraction refinement Options
% 3.12/0.99  
% 3.12/0.99  --abstr_ref                             []
% 3.12/0.99  --abstr_ref_prep                        false
% 3.12/0.99  --abstr_ref_until_sat                   false
% 3.12/0.99  --abstr_ref_sig_restrict                funpre
% 3.12/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.12/0.99  --abstr_ref_under                       []
% 3.12/0.99  
% 3.12/0.99  ------ SAT Options
% 3.12/0.99  
% 3.12/0.99  --sat_mode                              false
% 3.12/0.99  --sat_fm_restart_options                ""
% 3.12/0.99  --sat_gr_def                            false
% 3.12/0.99  --sat_epr_types                         true
% 3.12/0.99  --sat_non_cyclic_types                  false
% 3.12/0.99  --sat_finite_models                     false
% 3.12/0.99  --sat_fm_lemmas                         false
% 3.12/0.99  --sat_fm_prep                           false
% 3.12/0.99  --sat_fm_uc_incr                        true
% 3.12/0.99  --sat_out_model                         small
% 3.12/0.99  --sat_out_clauses                       false
% 3.12/0.99  
% 3.12/0.99  ------ QBF Options
% 3.12/0.99  
% 3.12/0.99  --qbf_mode                              false
% 3.12/0.99  --qbf_elim_univ                         false
% 3.12/0.99  --qbf_dom_inst                          none
% 3.12/0.99  --qbf_dom_pre_inst                      false
% 3.12/0.99  --qbf_sk_in                             false
% 3.12/0.99  --qbf_pred_elim                         true
% 3.12/0.99  --qbf_split                             512
% 3.12/0.99  
% 3.12/0.99  ------ BMC1 Options
% 3.12/0.99  
% 3.12/0.99  --bmc1_incremental                      false
% 3.12/0.99  --bmc1_axioms                           reachable_all
% 3.12/0.99  --bmc1_min_bound                        0
% 3.12/0.99  --bmc1_max_bound                        -1
% 3.12/0.99  --bmc1_max_bound_default                -1
% 3.12/0.99  --bmc1_symbol_reachability              true
% 3.12/0.99  --bmc1_property_lemmas                  false
% 3.12/0.99  --bmc1_k_induction                      false
% 3.12/0.99  --bmc1_non_equiv_states                 false
% 3.12/0.99  --bmc1_deadlock                         false
% 3.12/0.99  --bmc1_ucm                              false
% 3.12/0.99  --bmc1_add_unsat_core                   none
% 3.12/0.99  --bmc1_unsat_core_children              false
% 3.12/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.12/0.99  --bmc1_out_stat                         full
% 3.12/0.99  --bmc1_ground_init                      false
% 3.12/0.99  --bmc1_pre_inst_next_state              false
% 3.12/0.99  --bmc1_pre_inst_state                   false
% 3.12/0.99  --bmc1_pre_inst_reach_state             false
% 3.12/0.99  --bmc1_out_unsat_core                   false
% 3.12/0.99  --bmc1_aig_witness_out                  false
% 3.12/0.99  --bmc1_verbose                          false
% 3.12/0.99  --bmc1_dump_clauses_tptp                false
% 3.12/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.12/0.99  --bmc1_dump_file                        -
% 3.12/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.12/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.12/0.99  --bmc1_ucm_extend_mode                  1
% 3.12/0.99  --bmc1_ucm_init_mode                    2
% 3.12/0.99  --bmc1_ucm_cone_mode                    none
% 3.12/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.12/0.99  --bmc1_ucm_relax_model                  4
% 3.12/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.12/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.12/0.99  --bmc1_ucm_layered_model                none
% 3.12/0.99  --bmc1_ucm_max_lemma_size               10
% 3.12/0.99  
% 3.12/0.99  ------ AIG Options
% 3.12/0.99  
% 3.12/0.99  --aig_mode                              false
% 3.12/0.99  
% 3.12/0.99  ------ Instantiation Options
% 3.12/0.99  
% 3.12/0.99  --instantiation_flag                    true
% 3.12/0.99  --inst_sos_flag                         false
% 3.12/0.99  --inst_sos_phase                        true
% 3.12/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.12/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.12/0.99  --inst_lit_sel_side                     none
% 3.12/0.99  --inst_solver_per_active                1400
% 3.12/0.99  --inst_solver_calls_frac                1.
% 3.12/0.99  --inst_passive_queue_type               priority_queues
% 3.12/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.12/0.99  --inst_passive_queues_freq              [25;2]
% 3.12/0.99  --inst_dismatching                      true
% 3.12/0.99  --inst_eager_unprocessed_to_passive     true
% 3.12/0.99  --inst_prop_sim_given                   true
% 3.12/0.99  --inst_prop_sim_new                     false
% 3.12/0.99  --inst_subs_new                         false
% 3.12/0.99  --inst_eq_res_simp                      false
% 3.12/0.99  --inst_subs_given                       false
% 3.12/0.99  --inst_orphan_elimination               true
% 3.12/0.99  --inst_learning_loop_flag               true
% 3.12/0.99  --inst_learning_start                   3000
% 3.12/0.99  --inst_learning_factor                  2
% 3.12/0.99  --inst_start_prop_sim_after_learn       3
% 3.12/0.99  --inst_sel_renew                        solver
% 3.12/0.99  --inst_lit_activity_flag                true
% 3.12/0.99  --inst_restr_to_given                   false
% 3.12/0.99  --inst_activity_threshold               500
% 3.12/0.99  --inst_out_proof                        true
% 3.12/0.99  
% 3.12/0.99  ------ Resolution Options
% 3.12/0.99  
% 3.12/0.99  --resolution_flag                       false
% 3.12/0.99  --res_lit_sel                           adaptive
% 3.12/0.99  --res_lit_sel_side                      none
% 3.12/0.99  --res_ordering                          kbo
% 3.12/0.99  --res_to_prop_solver                    active
% 3.12/0.99  --res_prop_simpl_new                    false
% 3.12/0.99  --res_prop_simpl_given                  true
% 3.12/0.99  --res_passive_queue_type                priority_queues
% 3.12/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.12/0.99  --res_passive_queues_freq               [15;5]
% 3.12/0.99  --res_forward_subs                      full
% 3.12/0.99  --res_backward_subs                     full
% 3.12/0.99  --res_forward_subs_resolution           true
% 3.12/0.99  --res_backward_subs_resolution          true
% 3.12/0.99  --res_orphan_elimination                true
% 3.12/0.99  --res_time_limit                        2.
% 3.12/0.99  --res_out_proof                         true
% 3.12/0.99  
% 3.12/0.99  ------ Superposition Options
% 3.12/0.99  
% 3.12/0.99  --superposition_flag                    true
% 3.12/0.99  --sup_passive_queue_type                priority_queues
% 3.12/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.12/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.12/0.99  --demod_completeness_check              fast
% 3.12/0.99  --demod_use_ground                      true
% 3.12/0.99  --sup_to_prop_solver                    passive
% 3.12/0.99  --sup_prop_simpl_new                    true
% 3.12/0.99  --sup_prop_simpl_given                  true
% 3.12/0.99  --sup_fun_splitting                     false
% 3.12/0.99  --sup_smt_interval                      50000
% 3.12/0.99  
% 3.12/0.99  ------ Superposition Simplification Setup
% 3.12/0.99  
% 3.12/0.99  --sup_indices_passive                   []
% 3.12/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.12/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.12/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.12/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.12/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.12/0.99  --sup_full_bw                           [BwDemod]
% 3.12/0.99  --sup_immed_triv                        [TrivRules]
% 3.12/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.12/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.12/0.99  --sup_immed_bw_main                     []
% 3.12/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.12/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.12/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.12/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.12/0.99  
% 3.12/0.99  ------ Combination Options
% 3.12/0.99  
% 3.12/0.99  --comb_res_mult                         3
% 3.12/0.99  --comb_sup_mult                         2
% 3.12/0.99  --comb_inst_mult                        10
% 3.12/0.99  
% 3.12/0.99  ------ Debug Options
% 3.12/0.99  
% 3.12/0.99  --dbg_backtrace                         false
% 3.12/0.99  --dbg_dump_prop_clauses                 false
% 3.12/0.99  --dbg_dump_prop_clauses_file            -
% 3.12/0.99  --dbg_out_stat                          false
% 3.12/0.99  
% 3.12/0.99  
% 3.12/0.99  
% 3.12/0.99  
% 3.12/0.99  ------ Proving...
% 3.12/0.99  
% 3.12/0.99  
% 3.12/0.99  % SZS status Theorem for theBenchmark.p
% 3.12/0.99  
% 3.12/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.12/0.99  
% 3.12/0.99  fof(f17,conjecture,(
% 3.12/0.99    ! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k1_xboole_0,X0) => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))))),
% 3.12/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.12/0.99  
% 3.12/0.99  fof(f18,negated_conjecture,(
% 3.12/0.99    ~! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k1_xboole_0,X0) => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))))),
% 3.12/0.99    inference(negated_conjecture,[],[f17])).
% 3.12/0.99  
% 3.12/0.99  fof(f37,plain,(
% 3.12/0.99    ? [X0] : ((k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0)) & r2_hidden(k1_xboole_0,X0)) & ~v1_xboole_0(X0))),
% 3.12/0.99    inference(ennf_transformation,[],[f18])).
% 3.12/0.99  
% 3.12/0.99  fof(f38,plain,(
% 3.12/0.99    ? [X0] : (k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0)) & r2_hidden(k1_xboole_0,X0) & ~v1_xboole_0(X0))),
% 3.12/0.99    inference(flattening,[],[f37])).
% 3.12/0.99  
% 3.12/0.99  fof(f58,plain,(
% 3.12/0.99    ? [X0] : (k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0)) & r2_hidden(k1_xboole_0,X0) & ~v1_xboole_0(X0)) => (k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK4)) & r2_hidden(k1_xboole_0,sK4) & ~v1_xboole_0(sK4))),
% 3.12/0.99    introduced(choice_axiom,[])).
% 3.12/0.99  
% 3.12/0.99  fof(f59,plain,(
% 3.12/0.99    k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK4)) & r2_hidden(k1_xboole_0,sK4) & ~v1_xboole_0(sK4)),
% 3.12/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f38,f58])).
% 3.12/0.99  
% 3.12/0.99  fof(f92,plain,(
% 3.12/0.99    r2_hidden(k1_xboole_0,sK4)),
% 3.12/0.99    inference(cnf_transformation,[],[f59])).
% 3.12/0.99  
% 3.12/0.99  fof(f6,axiom,(
% 3.12/0.99    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 3.12/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.12/0.99  
% 3.12/0.99  fof(f26,plain,(
% 3.12/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 3.12/0.99    inference(ennf_transformation,[],[f6])).
% 3.12/0.99  
% 3.12/0.99  fof(f71,plain,(
% 3.12/0.99    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 3.12/0.99    inference(cnf_transformation,[],[f26])).
% 3.12/0.99  
% 3.12/0.99  fof(f3,axiom,(
% 3.12/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.12/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.12/0.99  
% 3.12/0.99  fof(f65,plain,(
% 3.12/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.12/0.99    inference(cnf_transformation,[],[f3])).
% 3.12/0.99  
% 3.12/0.99  fof(f16,axiom,(
% 3.12/0.99    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)))))),
% 3.12/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.12/0.99  
% 3.12/0.99  fof(f36,plain,(
% 3.12/0.99    ! [X0] : (! [X1] : (! [X2] : ((r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 3.12/0.99    inference(ennf_transformation,[],[f16])).
% 3.12/0.99  
% 3.12/0.99  fof(f57,plain,(
% 3.12/0.99    ! [X0] : (! [X1] : (! [X2] : (((r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2)) & (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 3.12/0.99    inference(nnf_transformation,[],[f36])).
% 3.12/0.99  
% 3.12/0.99  fof(f90,plain,(
% 3.12/0.99    ( ! [X2,X0,X1] : (r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 3.12/0.99    inference(cnf_transformation,[],[f57])).
% 3.12/0.99  
% 3.12/0.99  fof(f7,axiom,(
% 3.12/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 3.12/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.12/0.99  
% 3.12/0.99  fof(f27,plain,(
% 3.12/0.99    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 3.12/0.99    inference(ennf_transformation,[],[f7])).
% 3.12/0.99  
% 3.12/0.99  fof(f28,plain,(
% 3.12/0.99    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.12/0.99    inference(flattening,[],[f27])).
% 3.12/0.99  
% 3.12/0.99  fof(f48,plain,(
% 3.12/0.99    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.12/0.99    inference(nnf_transformation,[],[f28])).
% 3.12/0.99  
% 3.12/0.99  fof(f72,plain,(
% 3.12/0.99    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.12/0.99    inference(cnf_transformation,[],[f48])).
% 3.12/0.99  
% 3.12/0.99  fof(f13,axiom,(
% 3.12/0.99    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v4_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 3.12/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.12/0.99  
% 3.12/0.99  fof(f19,plain,(
% 3.12/0.99    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 3.12/0.99    inference(pure_predicate_removal,[],[f13])).
% 3.12/0.99  
% 3.12/0.99  fof(f22,plain,(
% 3.12/0.99    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)))),
% 3.12/0.99    inference(pure_predicate_removal,[],[f19])).
% 3.12/0.99  
% 3.12/0.99  fof(f84,plain,(
% 3.12/0.99    ( ! [X0] : (v3_orders_2(k2_yellow_1(X0))) )),
% 3.12/0.99    inference(cnf_transformation,[],[f22])).
% 3.12/0.99  
% 3.12/0.99  fof(f12,axiom,(
% 3.12/0.99    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 3.12/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.12/0.99  
% 3.12/0.99  fof(f21,plain,(
% 3.12/0.99    ! [X0] : l1_orders_2(k2_yellow_1(X0))),
% 3.12/0.99    inference(pure_predicate_removal,[],[f12])).
% 3.12/0.99  
% 3.12/0.99  fof(f83,plain,(
% 3.12/0.99    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 3.12/0.99    inference(cnf_transformation,[],[f21])).
% 3.12/0.99  
% 3.12/0.99  fof(f14,axiom,(
% 3.12/0.99    ! [X0] : (~v1_xboole_0(X0) => (v1_orders_2(k2_yellow_1(X0)) & ~v2_struct_0(k2_yellow_1(X0))))),
% 3.12/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.12/0.99  
% 3.12/0.99  fof(f20,plain,(
% 3.12/0.99    ! [X0] : (~v1_xboole_0(X0) => ~v2_struct_0(k2_yellow_1(X0)))),
% 3.12/0.99    inference(pure_predicate_removal,[],[f14])).
% 3.12/0.99  
% 3.12/0.99  fof(f35,plain,(
% 3.12/0.99    ! [X0] : (~v2_struct_0(k2_yellow_1(X0)) | v1_xboole_0(X0))),
% 3.12/0.99    inference(ennf_transformation,[],[f20])).
% 3.12/0.99  
% 3.12/0.99  fof(f86,plain,(
% 3.12/0.99    ( ! [X0] : (~v2_struct_0(k2_yellow_1(X0)) | v1_xboole_0(X0)) )),
% 3.12/0.99    inference(cnf_transformation,[],[f35])).
% 3.12/0.99  
% 3.12/0.99  fof(f15,axiom,(
% 3.12/0.99    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 3.12/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.12/0.99  
% 3.12/0.99  fof(f87,plain,(
% 3.12/0.99    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 3.12/0.99    inference(cnf_transformation,[],[f15])).
% 3.12/0.99  
% 3.12/0.99  fof(f8,axiom,(
% 3.12/0.99    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X2,X3))))))),
% 3.12/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.12/0.99  
% 3.12/0.99  fof(f29,plain,(
% 3.12/0.99    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.12/0.99    inference(ennf_transformation,[],[f8])).
% 3.12/0.99  
% 3.12/0.99  fof(f30,plain,(
% 3.12/0.99    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.12/0.99    inference(flattening,[],[f29])).
% 3.12/0.99  
% 3.12/0.99  fof(f49,plain,(
% 3.12/0.99    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.12/0.99    inference(nnf_transformation,[],[f30])).
% 3.12/0.99  
% 3.12/0.99  fof(f50,plain,(
% 3.12/0.99    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.12/0.99    inference(rectify,[],[f49])).
% 3.12/0.99  
% 3.12/0.99  fof(f51,plain,(
% 3.12/0.99    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X2,sK2(X0,X1,X2)) & r2_hidden(sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))))),
% 3.12/0.99    introduced(choice_axiom,[])).
% 3.12/0.99  
% 3.12/0.99  fof(f52,plain,(
% 3.12/0.99    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | (~r1_orders_2(X0,X2,sK2(X0,X1,X2)) & r2_hidden(sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.12/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f50,f51])).
% 3.12/0.99  
% 3.12/0.99  fof(f77,plain,(
% 3.12/0.99    ( ! [X2,X0,X1] : (r1_lattice3(X0,X1,X2) | ~r1_orders_2(X0,X2,sK2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.12/0.99    inference(cnf_transformation,[],[f52])).
% 3.12/0.99  
% 3.12/0.99  fof(f75,plain,(
% 3.12/0.99    ( ! [X2,X0,X1] : (r1_lattice3(X0,X1,X2) | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.12/0.99    inference(cnf_transformation,[],[f52])).
% 3.12/0.99  
% 3.12/0.99  fof(f9,axiom,(
% 3.12/0.99    ! [X0] : (l1_orders_2(X0) => (v1_yellow_0(X0) <=> ? [X1] : (r1_lattice3(X0,u1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0)))))),
% 3.12/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.12/0.99  
% 3.12/0.99  fof(f31,plain,(
% 3.12/0.99    ! [X0] : ((v1_yellow_0(X0) <=> ? [X1] : (r1_lattice3(X0,u1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.12/0.99    inference(ennf_transformation,[],[f9])).
% 3.12/0.99  
% 3.12/0.99  fof(f53,plain,(
% 3.12/0.99    ! [X0] : (((v1_yellow_0(X0) | ! [X1] : (~r1_lattice3(X0,u1_struct_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X1] : (r1_lattice3(X0,u1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0))) | ~v1_yellow_0(X0))) | ~l1_orders_2(X0))),
% 3.12/0.99    inference(nnf_transformation,[],[f31])).
% 3.12/0.99  
% 3.12/0.99  fof(f54,plain,(
% 3.12/0.99    ! [X0] : (((v1_yellow_0(X0) | ! [X1] : (~r1_lattice3(X0,u1_struct_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X2] : (r1_lattice3(X0,u1_struct_0(X0),X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~v1_yellow_0(X0))) | ~l1_orders_2(X0))),
% 3.12/0.99    inference(rectify,[],[f53])).
% 3.12/0.99  
% 3.12/0.99  fof(f55,plain,(
% 3.12/0.99    ! [X0] : (? [X2] : (r1_lattice3(X0,u1_struct_0(X0),X2) & m1_subset_1(X2,u1_struct_0(X0))) => (r1_lattice3(X0,u1_struct_0(X0),sK3(X0)) & m1_subset_1(sK3(X0),u1_struct_0(X0))))),
% 3.12/0.99    introduced(choice_axiom,[])).
% 3.12/0.99  
% 3.12/0.99  fof(f56,plain,(
% 3.12/0.99    ! [X0] : (((v1_yellow_0(X0) | ! [X1] : (~r1_lattice3(X0,u1_struct_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)))) & ((r1_lattice3(X0,u1_struct_0(X0),sK3(X0)) & m1_subset_1(sK3(X0),u1_struct_0(X0))) | ~v1_yellow_0(X0))) | ~l1_orders_2(X0))),
% 3.12/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f54,f55])).
% 3.12/0.99  
% 3.12/0.99  fof(f80,plain,(
% 3.12/0.99    ( ! [X0,X1] : (v1_yellow_0(X0) | ~r1_lattice3(X0,u1_struct_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.12/0.99    inference(cnf_transformation,[],[f56])).
% 3.12/0.99  
% 3.12/0.99  fof(f10,axiom,(
% 3.12/0.99    ! [X0] : (l1_orders_2(X0) => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)))),
% 3.12/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.12/0.99  
% 3.12/0.99  fof(f32,plain,(
% 3.12/0.99    ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 3.12/0.99    inference(ennf_transformation,[],[f10])).
% 3.12/0.99  
% 3.12/0.99  fof(f81,plain,(
% 3.12/0.99    ( ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.12/0.99    inference(cnf_transformation,[],[f32])).
% 3.12/0.99  
% 3.12/0.99  fof(f76,plain,(
% 3.12/0.99    ( ! [X2,X0,X1] : (r1_lattice3(X0,X1,X2) | r2_hidden(sK2(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.12/0.99    inference(cnf_transformation,[],[f52])).
% 3.12/0.99  
% 3.12/0.99  fof(f1,axiom,(
% 3.12/0.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.12/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.12/0.99  
% 3.12/0.99  fof(f39,plain,(
% 3.12/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.12/0.99    inference(nnf_transformation,[],[f1])).
% 3.12/0.99  
% 3.12/0.99  fof(f40,plain,(
% 3.12/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.12/0.99    inference(rectify,[],[f39])).
% 3.12/0.99  
% 3.12/0.99  fof(f41,plain,(
% 3.12/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.12/0.99    introduced(choice_axiom,[])).
% 3.12/0.99  
% 3.12/0.99  fof(f42,plain,(
% 3.12/0.99    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.12/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f40,f41])).
% 3.12/0.99  
% 3.12/0.99  fof(f60,plain,(
% 3.12/0.99    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.12/0.99    inference(cnf_transformation,[],[f42])).
% 3.12/0.99  
% 3.12/0.99  fof(f11,axiom,(
% 3.12/0.99    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_orders_2(X0,k3_yellow_0(X0),X1)))),
% 3.12/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.12/0.99  
% 3.12/0.99  fof(f33,plain,(
% 3.12/0.99    ! [X0] : (! [X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 3.12/0.99    inference(ennf_transformation,[],[f11])).
% 3.12/0.99  
% 3.12/0.99  fof(f34,plain,(
% 3.12/0.99    ! [X0] : (! [X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 3.12/0.99    inference(flattening,[],[f33])).
% 3.12/0.99  
% 3.12/0.99  fof(f82,plain,(
% 3.12/0.99    ( ! [X0,X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 3.12/0.99    inference(cnf_transformation,[],[f34])).
% 3.12/0.99  
% 3.12/0.99  fof(f85,plain,(
% 3.12/0.99    ( ! [X0] : (v5_orders_2(k2_yellow_1(X0))) )),
% 3.12/0.99    inference(cnf_transformation,[],[f22])).
% 3.12/0.99  
% 3.12/0.99  fof(f73,plain,(
% 3.12/0.99    ( ! [X2,X0,X1] : (r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.12/0.99    inference(cnf_transformation,[],[f48])).
% 3.12/0.99  
% 3.12/0.99  fof(f89,plain,(
% 3.12/0.99    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 3.12/0.99    inference(cnf_transformation,[],[f57])).
% 3.12/0.99  
% 3.12/0.99  fof(f4,axiom,(
% 3.12/0.99    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 3.12/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.12/0.99  
% 3.12/0.99  fof(f24,plain,(
% 3.12/0.99    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 3.12/0.99    inference(ennf_transformation,[],[f4])).
% 3.12/0.99  
% 3.12/0.99  fof(f66,plain,(
% 3.12/0.99    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 3.12/0.99    inference(cnf_transformation,[],[f24])).
% 3.12/0.99  
% 3.12/0.99  fof(f93,plain,(
% 3.12/0.99    k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK4))),
% 3.12/0.99    inference(cnf_transformation,[],[f59])).
% 3.12/0.99  
% 3.12/0.99  fof(f91,plain,(
% 3.12/0.99    ~v1_xboole_0(sK4)),
% 3.12/0.99    inference(cnf_transformation,[],[f59])).
% 3.12/0.99  
% 3.12/0.99  cnf(c_32,negated_conjecture,
% 3.12/0.99      ( r2_hidden(k1_xboole_0,sK4) ),
% 3.12/0.99      inference(cnf_transformation,[],[f92]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_2763,plain,
% 3.12/0.99      ( r2_hidden(k1_xboole_0,sK4) = iProver_top ),
% 3.12/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_11,plain,
% 3.12/0.99      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 3.12/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_2764,plain,
% 3.12/0.99      ( m1_subset_1(X0,X1) = iProver_top
% 3.12/0.99      | r2_hidden(X0,X1) != iProver_top ),
% 3.12/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_3147,plain,
% 3.12/0.99      ( m1_subset_1(k1_xboole_0,sK4) = iProver_top ),
% 3.12/0.99      inference(superposition,[status(thm)],[c_2763,c_2764]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_5,plain,
% 3.12/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 3.12/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_2769,plain,
% 3.12/0.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.12/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_29,plain,
% 3.12/0.99      ( r3_orders_2(k2_yellow_1(X0),X1,X2)
% 3.12/0.99      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.12/0.99      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.12/0.99      | ~ r1_tarski(X1,X2)
% 3.12/0.99      | v1_xboole_0(X0) ),
% 3.12/0.99      inference(cnf_transformation,[],[f90]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_13,plain,
% 3.12/0.99      ( r1_orders_2(X0,X1,X2)
% 3.12/0.99      | ~ r3_orders_2(X0,X1,X2)
% 3.12/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.12/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.12/0.99      | v2_struct_0(X0)
% 3.12/0.99      | ~ v3_orders_2(X0)
% 3.12/0.99      | ~ l1_orders_2(X0) ),
% 3.12/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_25,plain,
% 3.12/0.99      ( v3_orders_2(k2_yellow_1(X0)) ),
% 3.12/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_387,plain,
% 3.12/0.99      ( r1_orders_2(X0,X1,X2)
% 3.12/0.99      | ~ r3_orders_2(X0,X1,X2)
% 3.12/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.12/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.12/0.99      | v2_struct_0(X0)
% 3.12/0.99      | ~ l1_orders_2(X0)
% 3.12/0.99      | k2_yellow_1(X3) != X0 ),
% 3.12/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_25]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_388,plain,
% 3.12/0.99      ( r1_orders_2(k2_yellow_1(X0),X1,X2)
% 3.12/0.99      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
% 3.12/0.99      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.12/0.99      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.12/0.99      | v2_struct_0(k2_yellow_1(X0))
% 3.12/0.99      | ~ l1_orders_2(k2_yellow_1(X0)) ),
% 3.12/0.99      inference(unflattening,[status(thm)],[c_387]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_23,plain,
% 3.12/0.99      ( l1_orders_2(k2_yellow_1(X0)) ),
% 3.12/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_392,plain,
% 3.12/0.99      ( v2_struct_0(k2_yellow_1(X0))
% 3.12/0.99      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.12/0.99      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.12/0.99      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
% 3.12/0.99      | r1_orders_2(k2_yellow_1(X0),X1,X2) ),
% 3.12/0.99      inference(global_propositional_subsumption,
% 3.12/0.99                [status(thm)],
% 3.12/0.99                [c_388,c_23]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_393,plain,
% 3.12/0.99      ( r1_orders_2(k2_yellow_1(X0),X1,X2)
% 3.12/0.99      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
% 3.12/0.99      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.12/0.99      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.12/0.99      | v2_struct_0(k2_yellow_1(X0)) ),
% 3.12/0.99      inference(renaming,[status(thm)],[c_392]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_26,plain,
% 3.12/0.99      ( ~ v2_struct_0(k2_yellow_1(X0)) | v1_xboole_0(X0) ),
% 3.12/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_473,plain,
% 3.12/0.99      ( r1_orders_2(k2_yellow_1(X0),X1,X2)
% 3.12/0.99      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
% 3.12/0.99      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.12/0.99      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.12/0.99      | v1_xboole_0(X0) ),
% 3.12/0.99      inference(resolution,[status(thm)],[c_393,c_26]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_821,plain,
% 3.12/0.99      ( r1_orders_2(k2_yellow_1(X0),X1,X2)
% 3.12/0.99      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.12/0.99      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.12/0.99      | ~ r1_tarski(X1,X2)
% 3.12/0.99      | v1_xboole_0(X0) ),
% 3.12/0.99      inference(resolution,[status(thm)],[c_29,c_473]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_2751,plain,
% 3.12/0.99      ( r1_orders_2(k2_yellow_1(X0),X1,X2) = iProver_top
% 3.12/0.99      | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 3.12/0.99      | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 3.12/0.99      | r1_tarski(X1,X2) != iProver_top
% 3.12/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.12/0.99      inference(predicate_to_equality,[status(thm)],[c_821]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_28,plain,
% 3.12/0.99      ( u1_struct_0(k2_yellow_1(X0)) = X0 ),
% 3.12/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_2885,plain,
% 3.12/0.99      ( r1_orders_2(k2_yellow_1(X0),X1,X2) = iProver_top
% 3.12/0.99      | m1_subset_1(X1,X0) != iProver_top
% 3.12/0.99      | m1_subset_1(X2,X0) != iProver_top
% 3.12/0.99      | r1_tarski(X1,X2) != iProver_top
% 3.12/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.12/0.99      inference(light_normalisation,[status(thm)],[c_2751,c_28]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_14,plain,
% 3.12/0.99      ( r1_lattice3(X0,X1,X2)
% 3.12/0.99      | ~ r1_orders_2(X0,X2,sK2(X0,X1,X2))
% 3.12/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.12/0.99      | ~ l1_orders_2(X0) ),
% 3.12/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_700,plain,
% 3.12/0.99      ( r1_lattice3(X0,X1,X2)
% 3.12/0.99      | ~ r1_orders_2(X0,X2,sK2(X0,X1,X2))
% 3.12/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.12/0.99      | k2_yellow_1(X3) != X0 ),
% 3.12/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_23]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_701,plain,
% 3.12/0.99      ( r1_lattice3(k2_yellow_1(X0),X1,X2)
% 3.12/0.99      | ~ r1_orders_2(k2_yellow_1(X0),X2,sK2(k2_yellow_1(X0),X1,X2))
% 3.12/0.99      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) ),
% 3.12/0.99      inference(unflattening,[status(thm)],[c_700]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_2753,plain,
% 3.12/0.99      ( r1_lattice3(k2_yellow_1(X0),X1,X2) = iProver_top
% 3.12/0.99      | r1_orders_2(k2_yellow_1(X0),X2,sK2(k2_yellow_1(X0),X1,X2)) != iProver_top
% 3.12/0.99      | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top ),
% 3.12/0.99      inference(predicate_to_equality,[status(thm)],[c_701]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_2869,plain,
% 3.12/0.99      ( r1_lattice3(k2_yellow_1(X0),X1,X2) = iProver_top
% 3.12/0.99      | r1_orders_2(k2_yellow_1(X0),X2,sK2(k2_yellow_1(X0),X1,X2)) != iProver_top
% 3.12/0.99      | m1_subset_1(X2,X0) != iProver_top ),
% 3.12/0.99      inference(light_normalisation,[status(thm)],[c_2753,c_28]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_4285,plain,
% 3.12/0.99      ( r1_lattice3(k2_yellow_1(X0),X1,X2) = iProver_top
% 3.12/0.99      | m1_subset_1(X2,X0) != iProver_top
% 3.12/0.99      | m1_subset_1(sK2(k2_yellow_1(X0),X1,X2),X0) != iProver_top
% 3.12/0.99      | r1_tarski(X2,sK2(k2_yellow_1(X0),X1,X2)) != iProver_top
% 3.12/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.12/0.99      inference(superposition,[status(thm)],[c_2885,c_2869]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_16,plain,
% 3.12/0.99      ( r1_lattice3(X0,X1,X2)
% 3.12/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.12/0.99      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
% 3.12/0.99      | ~ l1_orders_2(X0) ),
% 3.12/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_670,plain,
% 3.12/0.99      ( r1_lattice3(X0,X1,X2)
% 3.12/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.12/0.99      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
% 3.12/0.99      | k2_yellow_1(X3) != X0 ),
% 3.12/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_23]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_671,plain,
% 3.12/0.99      ( r1_lattice3(k2_yellow_1(X0),X1,X2)
% 3.12/0.99      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.12/0.99      | m1_subset_1(sK2(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0))) ),
% 3.12/0.99      inference(unflattening,[status(thm)],[c_670]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_2755,plain,
% 3.12/0.99      ( r1_lattice3(k2_yellow_1(X0),X1,X2) = iProver_top
% 3.12/0.99      | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 3.12/0.99      | m1_subset_1(sK2(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0))) = iProver_top ),
% 3.12/0.99      inference(predicate_to_equality,[status(thm)],[c_671]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_2862,plain,
% 3.12/0.99      ( r1_lattice3(k2_yellow_1(X0),X1,X2) = iProver_top
% 3.12/0.99      | m1_subset_1(X2,X0) != iProver_top
% 3.12/0.99      | m1_subset_1(sK2(k2_yellow_1(X0),X1,X2),X0) = iProver_top ),
% 3.12/0.99      inference(light_normalisation,[status(thm)],[c_2755,c_28]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_11095,plain,
% 3.12/0.99      ( m1_subset_1(X2,X0) != iProver_top
% 3.12/0.99      | r1_lattice3(k2_yellow_1(X0),X1,X2) = iProver_top
% 3.12/0.99      | r1_tarski(X2,sK2(k2_yellow_1(X0),X1,X2)) != iProver_top
% 3.12/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.12/0.99      inference(global_propositional_subsumption,
% 3.12/0.99                [status(thm)],
% 3.12/0.99                [c_4285,c_2862]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_11096,plain,
% 3.12/0.99      ( r1_lattice3(k2_yellow_1(X0),X1,X2) = iProver_top
% 3.12/0.99      | m1_subset_1(X2,X0) != iProver_top
% 3.12/0.99      | r1_tarski(X2,sK2(k2_yellow_1(X0),X1,X2)) != iProver_top
% 3.12/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.12/0.99      inference(renaming,[status(thm)],[c_11095]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_11106,plain,
% 3.12/0.99      ( r1_lattice3(k2_yellow_1(X0),X1,k1_xboole_0) = iProver_top
% 3.12/0.99      | m1_subset_1(k1_xboole_0,X0) != iProver_top
% 3.12/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.12/0.99      inference(superposition,[status(thm)],[c_2769,c_11096]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_18,plain,
% 3.12/0.99      ( ~ r1_lattice3(X0,u1_struct_0(X0),X1)
% 3.12/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.12/0.99      | v1_yellow_0(X0)
% 3.12/0.99      | ~ l1_orders_2(X0) ),
% 3.12/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_634,plain,
% 3.12/0.99      ( ~ r1_lattice3(X0,u1_struct_0(X0),X1)
% 3.12/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.12/0.99      | v1_yellow_0(X0)
% 3.12/0.99      | k2_yellow_1(X2) != X0 ),
% 3.12/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_23]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_635,plain,
% 3.12/0.99      ( ~ r1_lattice3(k2_yellow_1(X0),u1_struct_0(k2_yellow_1(X0)),X1)
% 3.12/0.99      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.12/0.99      | v1_yellow_0(k2_yellow_1(X0)) ),
% 3.12/0.99      inference(unflattening,[status(thm)],[c_634]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_2757,plain,
% 3.12/0.99      ( r1_lattice3(k2_yellow_1(X0),u1_struct_0(k2_yellow_1(X0)),X1) != iProver_top
% 3.12/0.99      | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 3.12/0.99      | v1_yellow_0(k2_yellow_1(X0)) = iProver_top ),
% 3.12/0.99      inference(predicate_to_equality,[status(thm)],[c_635]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_2848,plain,
% 3.12/0.99      ( r1_lattice3(k2_yellow_1(X0),X0,X1) != iProver_top
% 3.12/0.99      | m1_subset_1(X1,X0) != iProver_top
% 3.12/0.99      | v1_yellow_0(k2_yellow_1(X0)) = iProver_top ),
% 3.12/0.99      inference(light_normalisation,[status(thm)],[c_2757,c_28]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_11277,plain,
% 3.12/0.99      ( m1_subset_1(k1_xboole_0,X0) != iProver_top
% 3.12/0.99      | v1_yellow_0(k2_yellow_1(X0)) = iProver_top
% 3.12/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.12/0.99      inference(superposition,[status(thm)],[c_11106,c_2848]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_21,plain,
% 3.12/0.99      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
% 3.12/0.99      | ~ l1_orders_2(X0) ),
% 3.12/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_601,plain,
% 3.12/0.99      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
% 3.12/0.99      | k2_yellow_1(X1) != X0 ),
% 3.12/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_23]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_602,plain,
% 3.12/0.99      ( m1_subset_1(k3_yellow_0(k2_yellow_1(X0)),u1_struct_0(k2_yellow_1(X0))) ),
% 3.12/0.99      inference(unflattening,[status(thm)],[c_601]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_2760,plain,
% 3.12/0.99      ( m1_subset_1(k3_yellow_0(k2_yellow_1(X0)),u1_struct_0(k2_yellow_1(X0))) = iProver_top ),
% 3.12/0.99      inference(predicate_to_equality,[status(thm)],[c_602]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_2787,plain,
% 3.12/0.99      ( m1_subset_1(k3_yellow_0(k2_yellow_1(X0)),X0) = iProver_top ),
% 3.12/0.99      inference(light_normalisation,[status(thm)],[c_2760,c_28]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_15,plain,
% 3.12/0.99      ( r1_lattice3(X0,X1,X2)
% 3.12/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.12/0.99      | r2_hidden(sK2(X0,X1,X2),X1)
% 3.12/0.99      | ~ l1_orders_2(X0) ),
% 3.12/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_685,plain,
% 3.12/0.99      ( r1_lattice3(X0,X1,X2)
% 3.12/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.12/0.99      | r2_hidden(sK2(X0,X1,X2),X1)
% 3.12/0.99      | k2_yellow_1(X3) != X0 ),
% 3.12/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_23]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_686,plain,
% 3.12/0.99      ( r1_lattice3(k2_yellow_1(X0),X1,X2)
% 3.12/0.99      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.12/0.99      | r2_hidden(sK2(k2_yellow_1(X0),X1,X2),X1) ),
% 3.12/0.99      inference(unflattening,[status(thm)],[c_685]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_2754,plain,
% 3.12/0.99      ( r1_lattice3(k2_yellow_1(X0),X1,X2) = iProver_top
% 3.12/0.99      | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 3.12/0.99      | r2_hidden(sK2(k2_yellow_1(X0),X1,X2),X1) = iProver_top ),
% 3.12/0.99      inference(predicate_to_equality,[status(thm)],[c_686]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_2855,plain,
% 3.12/0.99      ( r1_lattice3(k2_yellow_1(X0),X1,X2) = iProver_top
% 3.12/0.99      | m1_subset_1(X2,X0) != iProver_top
% 3.12/0.99      | r2_hidden(sK2(k2_yellow_1(X0),X1,X2),X1) = iProver_top ),
% 3.12/0.99      inference(light_normalisation,[status(thm)],[c_2754,c_28]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_1,plain,
% 3.12/0.99      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.12/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_2773,plain,
% 3.12/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.12/0.99      | v1_xboole_0(X1) != iProver_top ),
% 3.12/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_3701,plain,
% 3.12/0.99      ( r1_lattice3(k2_yellow_1(X0),X1,X2) = iProver_top
% 3.12/0.99      | m1_subset_1(X2,X0) != iProver_top
% 3.12/0.99      | v1_xboole_0(X1) != iProver_top ),
% 3.12/0.99      inference(superposition,[status(thm)],[c_2855,c_2773]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_4440,plain,
% 3.12/0.99      ( m1_subset_1(X0,X1) != iProver_top
% 3.12/0.99      | v1_yellow_0(k2_yellow_1(X1)) = iProver_top
% 3.12/0.99      | v1_xboole_0(X1) != iProver_top ),
% 3.12/0.99      inference(superposition,[status(thm)],[c_3701,c_2848]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_4575,plain,
% 3.12/0.99      ( v1_yellow_0(k2_yellow_1(X0)) = iProver_top
% 3.12/0.99      | v1_xboole_0(X0) != iProver_top ),
% 3.12/0.99      inference(superposition,[status(thm)],[c_2787,c_4440]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_11301,plain,
% 3.12/0.99      ( v1_yellow_0(k2_yellow_1(X0)) = iProver_top
% 3.12/0.99      | m1_subset_1(k1_xboole_0,X0) != iProver_top ),
% 3.12/0.99      inference(global_propositional_subsumption,
% 3.12/0.99                [status(thm)],
% 3.12/0.99                [c_11277,c_4575]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_11302,plain,
% 3.12/0.99      ( m1_subset_1(k1_xboole_0,X0) != iProver_top
% 3.12/0.99      | v1_yellow_0(k2_yellow_1(X0)) = iProver_top ),
% 3.12/0.99      inference(renaming,[status(thm)],[c_11301]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_11310,plain,
% 3.12/0.99      ( v1_yellow_0(k2_yellow_1(sK4)) = iProver_top ),
% 3.12/0.99      inference(superposition,[status(thm)],[c_3147,c_11302]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_3920,plain,
% 3.12/0.99      ( m1_subset_1(k3_yellow_0(k2_yellow_1(sK4)),u1_struct_0(k2_yellow_1(sK4))) ),
% 3.12/0.99      inference(instantiation,[status(thm)],[c_602]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_3925,plain,
% 3.12/0.99      ( m1_subset_1(k3_yellow_0(k2_yellow_1(sK4)),u1_struct_0(k2_yellow_1(sK4))) = iProver_top ),
% 3.12/0.99      inference(predicate_to_equality,[status(thm)],[c_3920]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_3300,plain,
% 3.12/0.99      ( m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
% 3.12/0.99      | ~ r2_hidden(X0,u1_struct_0(k2_yellow_1(X1))) ),
% 3.12/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_3860,plain,
% 3.12/0.99      ( m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK4)))
% 3.12/0.99      | ~ r2_hidden(k1_xboole_0,u1_struct_0(k2_yellow_1(sK4))) ),
% 3.12/0.99      inference(instantiation,[status(thm)],[c_3300]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_3861,plain,
% 3.12/0.99      ( m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK4))) = iProver_top
% 3.12/0.99      | r2_hidden(k1_xboole_0,u1_struct_0(k2_yellow_1(sK4))) != iProver_top ),
% 3.12/0.99      inference(predicate_to_equality,[status(thm)],[c_3860]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_22,plain,
% 3.12/0.99      ( r1_orders_2(X0,k3_yellow_0(X0),X1)
% 3.12/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.12/0.99      | ~ v5_orders_2(X0)
% 3.12/0.99      | ~ v1_yellow_0(X0)
% 3.12/0.99      | v2_struct_0(X0)
% 3.12/0.99      | ~ l1_orders_2(X0) ),
% 3.12/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_24,plain,
% 3.12/0.99      ( v5_orders_2(k2_yellow_1(X0)) ),
% 3.12/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_358,plain,
% 3.12/0.99      ( r1_orders_2(X0,k3_yellow_0(X0),X1)
% 3.12/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.12/0.99      | ~ v1_yellow_0(X0)
% 3.12/0.99      | v2_struct_0(X0)
% 3.12/0.99      | ~ l1_orders_2(X0)
% 3.12/0.99      | k2_yellow_1(X2) != X0 ),
% 3.12/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_24]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_359,plain,
% 3.12/0.99      ( r1_orders_2(k2_yellow_1(X0),k3_yellow_0(k2_yellow_1(X0)),X1)
% 3.12/0.99      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.12/0.99      | ~ v1_yellow_0(k2_yellow_1(X0))
% 3.12/0.99      | v2_struct_0(k2_yellow_1(X0))
% 3.12/0.99      | ~ l1_orders_2(k2_yellow_1(X0)) ),
% 3.12/0.99      inference(unflattening,[status(thm)],[c_358]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_363,plain,
% 3.12/0.99      ( v2_struct_0(k2_yellow_1(X0))
% 3.12/0.99      | ~ v1_yellow_0(k2_yellow_1(X0))
% 3.12/0.99      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.12/0.99      | r1_orders_2(k2_yellow_1(X0),k3_yellow_0(k2_yellow_1(X0)),X1) ),
% 3.12/0.99      inference(global_propositional_subsumption,
% 3.12/0.99                [status(thm)],
% 3.12/0.99                [c_359,c_23]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_364,plain,
% 3.12/0.99      ( r1_orders_2(k2_yellow_1(X0),k3_yellow_0(k2_yellow_1(X0)),X1)
% 3.12/0.99      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.12/0.99      | ~ v1_yellow_0(k2_yellow_1(X0))
% 3.12/0.99      | v2_struct_0(k2_yellow_1(X0)) ),
% 3.12/0.99      inference(renaming,[status(thm)],[c_363]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_493,plain,
% 3.12/0.99      ( r1_orders_2(k2_yellow_1(X0),k3_yellow_0(k2_yellow_1(X0)),X1)
% 3.12/0.99      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.12/0.99      | ~ v1_yellow_0(k2_yellow_1(X0))
% 3.12/0.99      | v1_xboole_0(X0) ),
% 3.12/0.99      inference(resolution,[status(thm)],[c_364,c_26]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_3729,plain,
% 3.12/0.99      ( r1_orders_2(k2_yellow_1(sK4),k3_yellow_0(k2_yellow_1(sK4)),k1_xboole_0)
% 3.12/0.99      | ~ m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK4)))
% 3.12/0.99      | ~ v1_yellow_0(k2_yellow_1(sK4))
% 3.12/0.99      | v1_xboole_0(sK4) ),
% 3.12/0.99      inference(instantiation,[status(thm)],[c_493]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_3732,plain,
% 3.12/0.99      ( r1_orders_2(k2_yellow_1(sK4),k3_yellow_0(k2_yellow_1(sK4)),k1_xboole_0) = iProver_top
% 3.12/0.99      | m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK4))) != iProver_top
% 3.12/0.99      | v1_yellow_0(k2_yellow_1(sK4)) != iProver_top
% 3.12/0.99      | v1_xboole_0(sK4) = iProver_top ),
% 3.12/0.99      inference(predicate_to_equality,[status(thm)],[c_3729]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_12,plain,
% 3.12/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 3.12/0.99      | r3_orders_2(X0,X1,X2)
% 3.12/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.12/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.12/0.99      | v2_struct_0(X0)
% 3.12/0.99      | ~ v3_orders_2(X0)
% 3.12/0.99      | ~ l1_orders_2(X0) ),
% 3.12/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_414,plain,
% 3.12/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 3.12/0.99      | r3_orders_2(X0,X1,X2)
% 3.12/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.12/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.12/0.99      | v2_struct_0(X0)
% 3.12/0.99      | ~ l1_orders_2(X0)
% 3.12/0.99      | k2_yellow_1(X3) != X0 ),
% 3.12/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_25]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_415,plain,
% 3.12/0.99      ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
% 3.12/0.99      | r3_orders_2(k2_yellow_1(X0),X1,X2)
% 3.12/0.99      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.12/0.99      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.12/0.99      | v2_struct_0(k2_yellow_1(X0))
% 3.12/0.99      | ~ l1_orders_2(k2_yellow_1(X0)) ),
% 3.12/0.99      inference(unflattening,[status(thm)],[c_414]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_419,plain,
% 3.12/0.99      ( v2_struct_0(k2_yellow_1(X0))
% 3.12/0.99      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.12/0.99      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.12/0.99      | r3_orders_2(k2_yellow_1(X0),X1,X2)
% 3.12/0.99      | ~ r1_orders_2(k2_yellow_1(X0),X1,X2) ),
% 3.12/0.99      inference(global_propositional_subsumption,
% 3.12/0.99                [status(thm)],
% 3.12/0.99                [c_415,c_23]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_420,plain,
% 3.12/0.99      ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
% 3.12/0.99      | r3_orders_2(k2_yellow_1(X0),X1,X2)
% 3.12/0.99      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.12/0.99      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.12/0.99      | v2_struct_0(k2_yellow_1(X0)) ),
% 3.12/0.99      inference(renaming,[status(thm)],[c_419]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_453,plain,
% 3.12/0.99      ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
% 3.12/0.99      | r3_orders_2(k2_yellow_1(X0),X1,X2)
% 3.12/0.99      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.12/0.99      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.12/0.99      | v1_xboole_0(X0) ),
% 3.12/0.99      inference(resolution,[status(thm)],[c_420,c_26]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_30,plain,
% 3.12/0.99      ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
% 3.12/0.99      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.12/0.99      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.12/0.99      | r1_tarski(X1,X2)
% 3.12/0.99      | v1_xboole_0(X0) ),
% 3.12/0.99      inference(cnf_transformation,[],[f89]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_803,plain,
% 3.12/0.99      ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
% 3.12/0.99      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.12/0.99      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.12/0.99      | r1_tarski(X1,X2)
% 3.12/0.99      | v1_xboole_0(X0) ),
% 3.12/0.99      inference(resolution,[status(thm)],[c_453,c_30]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_3090,plain,
% 3.12/0.99      ( ~ r1_orders_2(k2_yellow_1(X0),k3_yellow_0(k2_yellow_1(sK4)),k1_xboole_0)
% 3.12/0.99      | ~ m1_subset_1(k3_yellow_0(k2_yellow_1(sK4)),u1_struct_0(k2_yellow_1(X0)))
% 3.12/0.99      | ~ m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(X0)))
% 3.12/0.99      | r1_tarski(k3_yellow_0(k2_yellow_1(sK4)),k1_xboole_0)
% 3.12/0.99      | v1_xboole_0(X0) ),
% 3.12/0.99      inference(instantiation,[status(thm)],[c_803]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_3727,plain,
% 3.12/0.99      ( ~ r1_orders_2(k2_yellow_1(sK4),k3_yellow_0(k2_yellow_1(sK4)),k1_xboole_0)
% 3.12/0.99      | ~ m1_subset_1(k3_yellow_0(k2_yellow_1(sK4)),u1_struct_0(k2_yellow_1(sK4)))
% 3.12/0.99      | ~ m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK4)))
% 3.12/0.99      | r1_tarski(k3_yellow_0(k2_yellow_1(sK4)),k1_xboole_0)
% 3.12/0.99      | v1_xboole_0(sK4) ),
% 3.12/0.99      inference(instantiation,[status(thm)],[c_3090]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_3730,plain,
% 3.12/0.99      ( r1_orders_2(k2_yellow_1(sK4),k3_yellow_0(k2_yellow_1(sK4)),k1_xboole_0) != iProver_top
% 3.12/0.99      | m1_subset_1(k3_yellow_0(k2_yellow_1(sK4)),u1_struct_0(k2_yellow_1(sK4))) != iProver_top
% 3.12/0.99      | m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK4))) != iProver_top
% 3.12/0.99      | r1_tarski(k3_yellow_0(k2_yellow_1(sK4)),k1_xboole_0) = iProver_top
% 3.12/0.99      | v1_xboole_0(sK4) = iProver_top ),
% 3.12/0.99      inference(predicate_to_equality,[status(thm)],[c_3727]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_3133,plain,
% 3.12/0.99      ( u1_struct_0(k2_yellow_1(sK4)) = sK4 ),
% 3.12/0.99      inference(instantiation,[status(thm)],[c_28]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_2281,plain,
% 3.12/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.12/0.99      theory(equality) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_3038,plain,
% 3.12/0.99      ( r2_hidden(X0,X1)
% 3.12/0.99      | ~ r2_hidden(k1_xboole_0,sK4)
% 3.12/0.99      | X1 != sK4
% 3.12/0.99      | X0 != k1_xboole_0 ),
% 3.12/0.99      inference(instantiation,[status(thm)],[c_2281]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_3132,plain,
% 3.12/0.99      ( r2_hidden(X0,u1_struct_0(k2_yellow_1(sK4)))
% 3.12/0.99      | ~ r2_hidden(k1_xboole_0,sK4)
% 3.12/0.99      | X0 != k1_xboole_0
% 3.12/0.99      | u1_struct_0(k2_yellow_1(sK4)) != sK4 ),
% 3.12/0.99      inference(instantiation,[status(thm)],[c_3038]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_3134,plain,
% 3.12/0.99      ( X0 != k1_xboole_0
% 3.12/0.99      | u1_struct_0(k2_yellow_1(sK4)) != sK4
% 3.12/0.99      | r2_hidden(X0,u1_struct_0(k2_yellow_1(sK4))) = iProver_top
% 3.12/0.99      | r2_hidden(k1_xboole_0,sK4) != iProver_top ),
% 3.12/0.99      inference(predicate_to_equality,[status(thm)],[c_3132]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_3136,plain,
% 3.12/0.99      ( u1_struct_0(k2_yellow_1(sK4)) != sK4
% 3.12/0.99      | k1_xboole_0 != k1_xboole_0
% 3.12/0.99      | r2_hidden(k1_xboole_0,u1_struct_0(k2_yellow_1(sK4))) = iProver_top
% 3.12/0.99      | r2_hidden(k1_xboole_0,sK4) != iProver_top ),
% 3.12/0.99      inference(instantiation,[status(thm)],[c_3134]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_6,plain,
% 3.12/0.99      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 3.12/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_2993,plain,
% 3.12/0.99      ( ~ r1_tarski(k3_yellow_0(k2_yellow_1(sK4)),k1_xboole_0)
% 3.12/0.99      | k1_xboole_0 = k3_yellow_0(k2_yellow_1(sK4)) ),
% 3.12/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_2994,plain,
% 3.12/0.99      ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(sK4))
% 3.12/0.99      | r1_tarski(k3_yellow_0(k2_yellow_1(sK4)),k1_xboole_0) != iProver_top ),
% 3.12/0.99      inference(predicate_to_equality,[status(thm)],[c_2993]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_104,plain,
% 3.12/0.99      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 3.12/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_101,plain,
% 3.12/0.99      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 3.12/0.99      | k1_xboole_0 = k1_xboole_0 ),
% 3.12/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_31,negated_conjecture,
% 3.12/0.99      ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK4)) ),
% 3.12/0.99      inference(cnf_transformation,[],[f93]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_35,plain,
% 3.12/0.99      ( r2_hidden(k1_xboole_0,sK4) = iProver_top ),
% 3.12/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_33,negated_conjecture,
% 3.12/0.99      ( ~ v1_xboole_0(sK4) ),
% 3.12/0.99      inference(cnf_transformation,[],[f91]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_34,plain,
% 3.12/0.99      ( v1_xboole_0(sK4) != iProver_top ),
% 3.12/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(contradiction,plain,
% 3.12/0.99      ( $false ),
% 3.12/0.99      inference(minisat,
% 3.12/0.99                [status(thm)],
% 3.12/0.99                [c_11310,c_3925,c_3861,c_3732,c_3730,c_3133,c_3136,
% 3.12/0.99                 c_2994,c_104,c_101,c_31,c_35,c_34]) ).
% 3.12/0.99  
% 3.12/0.99  
% 3.12/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.12/0.99  
% 3.12/0.99  ------                               Statistics
% 3.12/0.99  
% 3.12/0.99  ------ General
% 3.12/0.99  
% 3.12/0.99  abstr_ref_over_cycles:                  0
% 3.12/0.99  abstr_ref_under_cycles:                 0
% 3.12/0.99  gc_basic_clause_elim:                   0
% 3.12/0.99  forced_gc_time:                         0
% 3.12/0.99  parsing_time:                           0.008
% 3.12/0.99  unif_index_cands_time:                  0.
% 3.12/0.99  unif_index_add_time:                    0.
% 3.12/0.99  orderings_time:                         0.
% 3.12/0.99  out_proof_time:                         0.01
% 3.12/0.99  total_time:                             0.315
% 3.12/0.99  num_of_symbols:                         54
% 3.12/0.99  num_of_terms:                           7881
% 3.12/0.99  
% 3.12/0.99  ------ Preprocessing
% 3.12/0.99  
% 3.12/0.99  num_of_splits:                          0
% 3.12/0.99  num_of_split_atoms:                     0
% 3.12/0.99  num_of_reused_defs:                     0
% 3.12/0.99  num_eq_ax_congr_red:                    25
% 3.12/0.99  num_of_sem_filtered_clauses:            1
% 3.12/0.99  num_of_subtypes:                        0
% 3.12/0.99  monotx_restored_types:                  0
% 3.12/0.99  sat_num_of_epr_types:                   0
% 3.12/0.99  sat_num_of_non_cyclic_types:            0
% 3.12/0.99  sat_guarded_non_collapsed_types:        0
% 3.12/0.99  num_pure_diseq_elim:                    0
% 3.12/0.99  simp_replaced_by:                       0
% 3.12/0.99  res_preprocessed:                       145
% 3.12/0.99  prep_upred:                             0
% 3.12/0.99  prep_unflattend:                        86
% 3.12/0.99  smt_new_axioms:                         0
% 3.12/0.99  pred_elim_cands:                        7
% 3.12/0.99  pred_elim:                              5
% 3.12/0.99  pred_elim_cl:                           6
% 3.12/0.99  pred_elim_cycles:                       14
% 3.12/0.99  merged_defs:                            0
% 3.12/0.99  merged_defs_ncl:                        0
% 3.12/0.99  bin_hyper_res:                          0
% 3.12/0.99  prep_cycles:                            4
% 3.12/0.99  pred_elim_time:                         0.029
% 3.12/0.99  splitting_time:                         0.
% 3.12/0.99  sem_filter_time:                        0.
% 3.12/0.99  monotx_time:                            0.
% 3.12/0.99  subtype_inf_time:                       0.
% 3.12/0.99  
% 3.12/0.99  ------ Problem properties
% 3.12/0.99  
% 3.12/0.99  clauses:                                27
% 3.12/0.99  conjectures:                            3
% 3.12/0.99  epr:                                    10
% 3.12/0.99  horn:                                   19
% 3.12/0.99  ground:                                 3
% 3.12/0.99  unary:                                  7
% 3.12/0.99  binary:                                 8
% 3.12/0.99  lits:                                   66
% 3.12/0.99  lits_eq:                                4
% 3.12/0.99  fd_pure:                                0
% 3.12/0.99  fd_pseudo:                              0
% 3.12/0.99  fd_cond:                                1
% 3.12/0.99  fd_pseudo_cond:                         0
% 3.12/0.99  ac_symbols:                             0
% 3.12/0.99  
% 3.12/0.99  ------ Propositional Solver
% 3.12/0.99  
% 3.12/0.99  prop_solver_calls:                      30
% 3.12/0.99  prop_fast_solver_calls:                 1502
% 3.12/0.99  smt_solver_calls:                       0
% 3.12/0.99  smt_fast_solver_calls:                  0
% 3.12/0.99  prop_num_of_clauses:                    3657
% 3.12/0.99  prop_preprocess_simplified:             8621
% 3.12/0.99  prop_fo_subsumed:                       22
% 3.12/0.99  prop_solver_time:                       0.
% 3.12/0.99  smt_solver_time:                        0.
% 3.12/0.99  smt_fast_solver_time:                   0.
% 3.12/0.99  prop_fast_solver_time:                  0.
% 3.12/0.99  prop_unsat_core_time:                   0.
% 3.12/0.99  
% 3.12/0.99  ------ QBF
% 3.12/0.99  
% 3.12/0.99  qbf_q_res:                              0
% 3.12/0.99  qbf_num_tautologies:                    0
% 3.12/0.99  qbf_prep_cycles:                        0
% 3.12/0.99  
% 3.12/0.99  ------ BMC1
% 3.12/0.99  
% 3.12/0.99  bmc1_current_bound:                     -1
% 3.12/0.99  bmc1_last_solved_bound:                 -1
% 3.12/0.99  bmc1_unsat_core_size:                   -1
% 3.12/0.99  bmc1_unsat_core_parents_size:           -1
% 3.12/0.99  bmc1_merge_next_fun:                    0
% 3.12/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.12/0.99  
% 3.12/0.99  ------ Instantiation
% 3.12/0.99  
% 3.12/0.99  inst_num_of_clauses:                    932
% 3.12/0.99  inst_num_in_passive:                    237
% 3.12/0.99  inst_num_in_active:                     471
% 3.12/0.99  inst_num_in_unprocessed:                224
% 3.12/0.99  inst_num_of_loops:                      630
% 3.12/0.99  inst_num_of_learning_restarts:          0
% 3.12/0.99  inst_num_moves_active_passive:          155
% 3.12/0.99  inst_lit_activity:                      0
% 3.12/0.99  inst_lit_activity_moves:                0
% 3.12/0.99  inst_num_tautologies:                   0
% 3.12/0.99  inst_num_prop_implied:                  0
% 3.12/0.99  inst_num_existing_simplified:           0
% 3.12/0.99  inst_num_eq_res_simplified:             0
% 3.12/0.99  inst_num_child_elim:                    0
% 3.12/0.99  inst_num_of_dismatching_blockings:      444
% 3.12/0.99  inst_num_of_non_proper_insts:           1082
% 3.12/0.99  inst_num_of_duplicates:                 0
% 3.12/0.99  inst_inst_num_from_inst_to_res:         0
% 3.12/0.99  inst_dismatching_checking_time:         0.
% 3.12/0.99  
% 3.12/0.99  ------ Resolution
% 3.12/0.99  
% 3.12/0.99  res_num_of_clauses:                     0
% 3.12/0.99  res_num_in_passive:                     0
% 3.12/0.99  res_num_in_active:                      0
% 3.12/0.99  res_num_of_loops:                       149
% 3.12/0.99  res_forward_subset_subsumed:            96
% 3.12/0.99  res_backward_subset_subsumed:           0
% 3.12/0.99  res_forward_subsumed:                   0
% 3.12/0.99  res_backward_subsumed:                  0
% 3.12/0.99  res_forward_subsumption_resolution:     0
% 3.12/0.99  res_backward_subsumption_resolution:    0
% 3.12/0.99  res_clause_to_clause_subsumption:       2407
% 3.12/0.99  res_orphan_elimination:                 0
% 3.12/0.99  res_tautology_del:                      89
% 3.12/0.99  res_num_eq_res_simplified:              0
% 3.12/0.99  res_num_sel_changes:                    0
% 3.12/0.99  res_moves_from_active_to_pass:          0
% 3.12/0.99  
% 3.12/0.99  ------ Superposition
% 3.12/0.99  
% 3.12/0.99  sup_time_total:                         0.
% 3.12/0.99  sup_time_generating:                    0.
% 3.12/0.99  sup_time_sim_full:                      0.
% 3.12/0.99  sup_time_sim_immed:                     0.
% 3.12/0.99  
% 3.12/0.99  sup_num_of_clauses:                     275
% 3.12/0.99  sup_num_in_active:                      125
% 3.12/0.99  sup_num_in_passive:                     150
% 3.12/0.99  sup_num_of_loops:                       125
% 3.12/0.99  sup_fw_superposition:                   220
% 3.12/0.99  sup_bw_superposition:                   94
% 3.12/0.99  sup_immediate_simplified:               42
% 3.12/0.99  sup_given_eliminated:                   1
% 3.12/0.99  comparisons_done:                       0
% 3.12/0.99  comparisons_avoided:                    0
% 3.12/0.99  
% 3.12/0.99  ------ Simplifications
% 3.12/0.99  
% 3.12/0.99  
% 3.12/0.99  sim_fw_subset_subsumed:                 23
% 3.12/0.99  sim_bw_subset_subsumed:                 0
% 3.12/0.99  sim_fw_subsumed:                        19
% 3.12/0.99  sim_bw_subsumed:                        3
% 3.12/0.99  sim_fw_subsumption_res:                 2
% 3.12/0.99  sim_bw_subsumption_res:                 0
% 3.12/0.99  sim_tautology_del:                      16
% 3.12/0.99  sim_eq_tautology_del:                   1
% 3.12/0.99  sim_eq_res_simp:                        0
% 3.12/0.99  sim_fw_demodulated:                     0
% 3.12/0.99  sim_bw_demodulated:                     0
% 3.12/0.99  sim_light_normalised:                   11
% 3.12/0.99  sim_joinable_taut:                      0
% 3.12/0.99  sim_joinable_simp:                      0
% 3.12/0.99  sim_ac_normalised:                      0
% 3.12/0.99  sim_smt_subsumption:                    0
% 3.12/0.99  
%------------------------------------------------------------------------------
