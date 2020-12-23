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
% DateTime   : Thu Dec  3 12:20:14 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 423 expanded)
%              Number of clauses        :   88 ( 175 expanded)
%              Number of leaves         :   19 (  78 expanded)
%              Depth                    :   29
%              Number of atoms          :  580 (1307 expanded)
%              Number of equality atoms :  155 ( 346 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f10,axiom,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v4_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f19,plain,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f62,plain,(
    ! [X0] : v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f61,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f13,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
             => ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f14,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( r2_hidden(k1_xboole_0,X0)
       => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ( r2_hidden(k1_xboole_0,X0)
         => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f33,plain,(
    ? [X0] :
      ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0))
      & r2_hidden(k1_xboole_0,X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f34,plain,(
    ? [X0] :
      ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0))
      & r2_hidden(k1_xboole_0,X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f45,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0))
        & r2_hidden(k1_xboole_0,X0)
        & ~ v1_xboole_0(X0) )
   => ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK2))
      & r2_hidden(k1_xboole_0,sK2)
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK2))
    & r2_hidden(k1_xboole_0,sK2)
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f34,f45])).

fof(f69,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f11,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_orders_2(k2_yellow_1(X0))
        & ~ v2_struct_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ~ v2_struct_0(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k2_yellow_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k2_yellow_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f12,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f70,plain,(
    r2_hidden(k1_xboole_0,sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,k3_yellow_0(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,k3_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,k3_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_orders_2(X0,k3_yellow_0(X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f63,plain,(
    ! [X0] : v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r1_orders_2(X0,X2,X1)
                  & r1_orders_2(X0,X1,X2) )
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f23])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | ~ r1_orders_2(X0,X2,X1)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f59,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f71,plain,(
    k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK2)) ),
    inference(cnf_transformation,[],[f46])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f25])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
        & r2_hidden(sK0(X0,X1,X2),X1)
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_yellow_0(X0)
      <=> ? [X1] :
            ( r1_lattice3(X0,u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_yellow_0(X0)
      <=> ? [X1] :
            ( r1_lattice3(X0,u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f41,plain,(
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
    inference(rectify,[],[f40])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X2] :
          ( r1_lattice3(X0,u1_struct_0(X0),X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( r1_lattice3(X0,u1_struct_0(X0),sK1(X0))
        & m1_subset_1(sK1(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ( ( v1_yellow_0(X0)
          | ! [X1] :
              ( ~ r1_lattice3(X0,u1_struct_0(X0),X1)
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ( r1_lattice3(X0,u1_struct_0(X0),sK1(X0))
            & m1_subset_1(sK1(X0),u1_struct_0(X0)) )
          | ~ v1_yellow_0(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f41,f42])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v1_yellow_0(X0)
      | ~ r1_lattice3(X0,u1_struct_0(X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_3,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_16,plain,
    ( v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_399,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | k2_yellow_1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_16])).

cnf(c_400,plain,
    ( r1_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | v2_struct_0(k2_yellow_1(X0))
    | ~ l1_orders_2(k2_yellow_1(X0)) ),
    inference(unflattening,[status(thm)],[c_399])).

cnf(c_14,plain,
    ( l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_404,plain,
    ( v2_struct_0(k2_yellow_1(X0))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
    | r1_orders_2(k2_yellow_1(X0),X1,X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_400,c_14])).

cnf(c_405,plain,
    ( r1_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | v2_struct_0(k2_yellow_1(X0)) ),
    inference(renaming,[status(thm)],[c_404])).

cnf(c_0,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_20,plain,
    ( r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ r1_tarski(X1,X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_24,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_280,plain,
    ( r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ r1_tarski(X1,X2)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_24])).

cnf(c_281,plain,
    ( r3_orders_2(k2_yellow_1(sK2),X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK2)))
    | ~ r1_tarski(X0,X1) ),
    inference(unflattening,[status(thm)],[c_280])).

cnf(c_318,plain,
    ( r3_orders_2(k2_yellow_1(sK2),X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK2)))
    | X1 != X2
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_281])).

cnf(c_319,plain,
    ( r3_orders_2(k2_yellow_1(sK2),k1_xboole_0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK2)))
    | ~ m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK2))) ),
    inference(unflattening,[status(thm)],[c_318])).

cnf(c_537,plain,
    ( r1_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(sK2)))
    | ~ m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK2)))
    | v2_struct_0(k2_yellow_1(X0))
    | X3 != X2
    | k2_yellow_1(X0) != k2_yellow_1(sK2)
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_405,c_319])).

cnf(c_538,plain,
    ( r1_orders_2(k2_yellow_1(X0),k1_xboole_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK2)))
    | ~ m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK2)))
    | v2_struct_0(k2_yellow_1(X0))
    | k2_yellow_1(X0) != k2_yellow_1(sK2) ),
    inference(unflattening,[status(thm)],[c_537])).

cnf(c_17,plain,
    ( v1_xboole_0(X0)
    | ~ v2_struct_0(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_298,plain,
    ( ~ v2_struct_0(k2_yellow_1(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_24])).

cnf(c_299,plain,
    ( ~ v2_struct_0(k2_yellow_1(sK2)) ),
    inference(unflattening,[status(thm)],[c_298])).

cnf(c_572,plain,
    ( r1_orders_2(k2_yellow_1(X0),k1_xboole_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK2)))
    | ~ m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK2)))
    | k2_yellow_1(X0) != k2_yellow_1(sK2) ),
    inference(resolution_lifted,[status(thm)],[c_538,c_299])).

cnf(c_1973,plain,
    ( k2_yellow_1(X0) != k2_yellow_1(sK2)
    | r1_orders_2(k2_yellow_1(X0),k1_xboole_0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK2))) != iProver_top
    | m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_572])).

cnf(c_19,plain,
    ( u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2062,plain,
    ( k2_yellow_1(X0) != k2_yellow_1(sK2)
    | r1_orders_2(k2_yellow_1(X0),k1_xboole_0,X1) = iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK2))) != iProver_top
    | m1_subset_1(k1_xboole_0,X0) != iProver_top
    | m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1973,c_19])).

cnf(c_2063,plain,
    ( k2_yellow_1(X0) != k2_yellow_1(sK2)
    | r1_orders_2(k2_yellow_1(X0),k1_xboole_0,X1) = iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(X1,sK2) != iProver_top
    | m1_subset_1(k1_xboole_0,X0) != iProver_top
    | m1_subset_1(k1_xboole_0,sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2062,c_19])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_23,negated_conjecture,
    ( r2_hidden(k1_xboole_0,sK2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_714,plain,
    ( m1_subset_1(X0,X1)
    | sK2 != X1
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_23])).

cnf(c_715,plain,
    ( m1_subset_1(k1_xboole_0,sK2) ),
    inference(unflattening,[status(thm)],[c_714])).

cnf(c_716,plain,
    ( m1_subset_1(k1_xboole_0,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_715])).

cnf(c_2187,plain,
    ( m1_subset_1(k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X1,sK2) != iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | r1_orders_2(k2_yellow_1(X0),k1_xboole_0,X1) = iProver_top
    | k2_yellow_1(X0) != k2_yellow_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2063,c_716])).

cnf(c_2188,plain,
    ( k2_yellow_1(X0) != k2_yellow_1(sK2)
    | r1_orders_2(k2_yellow_1(X0),k1_xboole_0,X1) = iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(X1,sK2) != iProver_top
    | m1_subset_1(k1_xboole_0,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2187])).

cnf(c_2196,plain,
    ( r1_orders_2(k2_yellow_1(sK2),k1_xboole_0,X0) = iProver_top
    | m1_subset_1(X0,sK2) != iProver_top
    | m1_subset_1(k1_xboole_0,sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2188])).

cnf(c_2201,plain,
    ( m1_subset_1(X0,sK2) != iProver_top
    | r1_orders_2(k2_yellow_1(sK2),k1_xboole_0,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2196,c_716])).

cnf(c_2202,plain,
    ( r1_orders_2(k2_yellow_1(sK2),k1_xboole_0,X0) = iProver_top
    | m1_subset_1(X0,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_2201])).

cnf(c_13,plain,
    ( r1_orders_2(X0,k3_yellow_0(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v1_yellow_0(X0)
    | ~ v5_orders_2(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_15,plain,
    ( v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_337,plain,
    ( r1_orders_2(X0,k3_yellow_0(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v1_yellow_0(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | k2_yellow_1(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_15])).

cnf(c_338,plain,
    ( r1_orders_2(k2_yellow_1(X0),k3_yellow_0(k2_yellow_1(X0)),X1)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ v1_yellow_0(k2_yellow_1(X0))
    | v2_struct_0(k2_yellow_1(X0))
    | ~ l1_orders_2(k2_yellow_1(X0)) ),
    inference(unflattening,[status(thm)],[c_337])).

cnf(c_342,plain,
    ( v2_struct_0(k2_yellow_1(X0))
    | ~ v1_yellow_0(k2_yellow_1(X0))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | r1_orders_2(k2_yellow_1(X0),k3_yellow_0(k2_yellow_1(X0)),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_338,c_14])).

cnf(c_343,plain,
    ( r1_orders_2(k2_yellow_1(X0),k3_yellow_0(k2_yellow_1(X0)),X1)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ v1_yellow_0(k2_yellow_1(X0))
    | v2_struct_0(k2_yellow_1(X0)) ),
    inference(renaming,[status(thm)],[c_342])).

cnf(c_595,plain,
    ( r1_orders_2(k2_yellow_1(X0),k3_yellow_0(k2_yellow_1(X0)),X1)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ v1_yellow_0(k2_yellow_1(X0))
    | k2_yellow_1(X0) != k2_yellow_1(sK2) ),
    inference(resolution_lifted,[status(thm)],[c_343,c_299])).

cnf(c_1974,plain,
    ( k2_yellow_1(X0) != k2_yellow_1(sK2)
    | r1_orders_2(k2_yellow_1(X0),k3_yellow_0(k2_yellow_1(X0)),X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | v1_yellow_0(k2_yellow_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_595])).

cnf(c_2031,plain,
    ( k2_yellow_1(X0) != k2_yellow_1(sK2)
    | r1_orders_2(k2_yellow_1(X0),k3_yellow_0(k2_yellow_1(X0)),X1) = iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | v1_yellow_0(k2_yellow_1(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1974,c_19])).

cnf(c_2150,plain,
    ( r1_orders_2(k2_yellow_1(sK2),k3_yellow_0(k2_yellow_1(sK2)),X0) = iProver_top
    | m1_subset_1(X0,sK2) != iProver_top
    | v1_yellow_0(k2_yellow_1(sK2)) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2031])).

cnf(c_4,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | X2 = X1 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_361,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | X2 = X1
    | k2_yellow_1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_15])).

cnf(c_362,plain,
    ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ r1_orders_2(k2_yellow_1(X0),X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ l1_orders_2(k2_yellow_1(X0))
    | X1 = X2 ),
    inference(unflattening,[status(thm)],[c_361])).

cnf(c_366,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ r1_orders_2(k2_yellow_1(X0),X2,X1)
    | ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
    | X1 = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_362,c_14])).

cnf(c_367,plain,
    ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ r1_orders_2(k2_yellow_1(X0),X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | X1 = X2 ),
    inference(renaming,[status(thm)],[c_366])).

cnf(c_1975,plain,
    ( X0 = X1
    | r1_orders_2(k2_yellow_1(X2),X0,X1) != iProver_top
    | r1_orders_2(k2_yellow_1(X2),X1,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X2))) != iProver_top
    | m1_subset_1(X0,u1_struct_0(k2_yellow_1(X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_367])).

cnf(c_2040,plain,
    ( X0 = X1
    | r1_orders_2(k2_yellow_1(X2),X1,X0) != iProver_top
    | r1_orders_2(k2_yellow_1(X2),X0,X1) != iProver_top
    | m1_subset_1(X1,X2) != iProver_top
    | m1_subset_1(X0,X2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1975,c_19])).

cnf(c_2786,plain,
    ( k3_yellow_0(k2_yellow_1(sK2)) = X0
    | r1_orders_2(k2_yellow_1(sK2),X0,k3_yellow_0(k2_yellow_1(sK2))) != iProver_top
    | m1_subset_1(X0,sK2) != iProver_top
    | m1_subset_1(k3_yellow_0(k2_yellow_1(sK2)),sK2) != iProver_top
    | v1_yellow_0(k2_yellow_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2150,c_2040])).

cnf(c_12,plain,
    ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_788,plain,
    ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
    | k2_yellow_1(X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_14])).

cnf(c_789,plain,
    ( m1_subset_1(k3_yellow_0(k2_yellow_1(X0)),u1_struct_0(k2_yellow_1(X0))) ),
    inference(unflattening,[status(thm)],[c_788])).

cnf(c_1972,plain,
    ( m1_subset_1(k3_yellow_0(k2_yellow_1(X0)),u1_struct_0(k2_yellow_1(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_789])).

cnf(c_1986,plain,
    ( m1_subset_1(k3_yellow_0(k2_yellow_1(X0)),X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1972,c_19])).

cnf(c_2917,plain,
    ( k3_yellow_0(k2_yellow_1(sK2)) = X0
    | r1_orders_2(k2_yellow_1(sK2),X0,k3_yellow_0(k2_yellow_1(sK2))) != iProver_top
    | m1_subset_1(X0,sK2) != iProver_top
    | v1_yellow_0(k2_yellow_1(sK2)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2786,c_1986])).

cnf(c_2922,plain,
    ( k3_yellow_0(k2_yellow_1(sK2)) = k1_xboole_0
    | m1_subset_1(k3_yellow_0(k2_yellow_1(sK2)),sK2) != iProver_top
    | m1_subset_1(k1_xboole_0,sK2) != iProver_top
    | v1_yellow_0(k2_yellow_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2202,c_2917])).

cnf(c_22,negated_conjecture,
    ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK2)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1686,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1711,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1686])).

cnf(c_1687,plain,
    ( X0 != X1
    | X2 != X1
    | X0 = X2 ),
    theory(equality)).

cnf(c_2138,plain,
    ( k3_yellow_0(k2_yellow_1(sK2)) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k3_yellow_0(k2_yellow_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_1687])).

cnf(c_2139,plain,
    ( k3_yellow_0(k2_yellow_1(sK2)) != k1_xboole_0
    | k1_xboole_0 = k3_yellow_0(k2_yellow_1(sK2))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2138])).

cnf(c_7,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_857,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | k2_yellow_1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_14])).

cnf(c_858,plain,
    ( r1_lattice3(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | m1_subset_1(sK0(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0))) ),
    inference(unflattening,[status(thm)],[c_857])).

cnf(c_1967,plain,
    ( r1_lattice3(k2_yellow_1(X0),X1,X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | m1_subset_1(sK0(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_858])).

cnf(c_2017,plain,
    ( r1_lattice3(k2_yellow_1(X0),X1,X2) = iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(sK0(k2_yellow_1(X0),X1,X2),X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1967,c_19])).

cnf(c_5,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_887,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | k2_yellow_1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_14])).

cnf(c_888,plain,
    ( r1_lattice3(k2_yellow_1(X0),X1,X2)
    | ~ r1_orders_2(k2_yellow_1(X0),X2,sK0(k2_yellow_1(X0),X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) ),
    inference(unflattening,[status(thm)],[c_887])).

cnf(c_1965,plain,
    ( r1_lattice3(k2_yellow_1(X0),X1,X2) = iProver_top
    | r1_orders_2(k2_yellow_1(X0),X2,sK0(k2_yellow_1(X0),X1,X2)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_888])).

cnf(c_2024,plain,
    ( r1_lattice3(k2_yellow_1(X0),X1,X2) = iProver_top
    | r1_orders_2(k2_yellow_1(X0),X2,sK0(k2_yellow_1(X0),X1,X2)) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1965,c_19])).

cnf(c_2686,plain,
    ( r1_lattice3(k2_yellow_1(sK2),X0,k1_xboole_0) = iProver_top
    | m1_subset_1(sK0(k2_yellow_1(sK2),X0,k1_xboole_0),sK2) != iProver_top
    | m1_subset_1(k1_xboole_0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2202,c_2024])).

cnf(c_2772,plain,
    ( m1_subset_1(sK0(k2_yellow_1(sK2),X0,k1_xboole_0),sK2) != iProver_top
    | r1_lattice3(k2_yellow_1(sK2),X0,k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2686,c_716])).

cnf(c_2773,plain,
    ( r1_lattice3(k2_yellow_1(sK2),X0,k1_xboole_0) = iProver_top
    | m1_subset_1(sK0(k2_yellow_1(sK2),X0,k1_xboole_0),sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_2772])).

cnf(c_3054,plain,
    ( r1_lattice3(k2_yellow_1(sK2),X0,k1_xboole_0) = iProver_top
    | m1_subset_1(k1_xboole_0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2017,c_2773])).

cnf(c_3203,plain,
    ( r1_lattice3(k2_yellow_1(sK2),X0,k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3054,c_716])).

cnf(c_9,plain,
    ( ~ r1_lattice3(X0,u1_struct_0(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v1_yellow_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_821,plain,
    ( ~ r1_lattice3(X0,u1_struct_0(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v1_yellow_0(X0)
    | k2_yellow_1(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_14])).

cnf(c_822,plain,
    ( ~ r1_lattice3(k2_yellow_1(X0),u1_struct_0(k2_yellow_1(X0)),X1)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | v1_yellow_0(k2_yellow_1(X0)) ),
    inference(unflattening,[status(thm)],[c_821])).

cnf(c_1969,plain,
    ( r1_lattice3(k2_yellow_1(X0),u1_struct_0(k2_yellow_1(X0)),X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | v1_yellow_0(k2_yellow_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_822])).

cnf(c_2003,plain,
    ( r1_lattice3(k2_yellow_1(X0),X0,X1) != iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | v1_yellow_0(k2_yellow_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1969,c_19])).

cnf(c_3211,plain,
    ( m1_subset_1(k1_xboole_0,sK2) != iProver_top
    | v1_yellow_0(k2_yellow_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3203,c_2003])).

cnf(c_3418,plain,
    ( m1_subset_1(k3_yellow_0(k2_yellow_1(sK2)),sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2922,c_22,c_716,c_1711,c_2139,c_3211])).

cnf(c_3423,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3418,c_1986])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n014.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 12:16:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.08/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.01  
% 2.08/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.08/1.01  
% 2.08/1.01  ------  iProver source info
% 2.08/1.01  
% 2.08/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.08/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.08/1.01  git: non_committed_changes: false
% 2.08/1.01  git: last_make_outside_of_git: false
% 2.08/1.01  
% 2.08/1.01  ------ 
% 2.08/1.01  
% 2.08/1.01  ------ Input Options
% 2.08/1.01  
% 2.08/1.01  --out_options                           all
% 2.08/1.01  --tptp_safe_out                         true
% 2.08/1.01  --problem_path                          ""
% 2.08/1.01  --include_path                          ""
% 2.08/1.01  --clausifier                            res/vclausify_rel
% 2.08/1.01  --clausifier_options                    --mode clausify
% 2.08/1.01  --stdin                                 false
% 2.08/1.01  --stats_out                             all
% 2.08/1.01  
% 2.08/1.01  ------ General Options
% 2.08/1.01  
% 2.08/1.01  --fof                                   false
% 2.08/1.01  --time_out_real                         305.
% 2.08/1.01  --time_out_virtual                      -1.
% 2.08/1.01  --symbol_type_check                     false
% 2.08/1.01  --clausify_out                          false
% 2.08/1.01  --sig_cnt_out                           false
% 2.08/1.01  --trig_cnt_out                          false
% 2.08/1.01  --trig_cnt_out_tolerance                1.
% 2.08/1.01  --trig_cnt_out_sk_spl                   false
% 2.08/1.01  --abstr_cl_out                          false
% 2.08/1.01  
% 2.08/1.01  ------ Global Options
% 2.08/1.01  
% 2.08/1.01  --schedule                              default
% 2.08/1.01  --add_important_lit                     false
% 2.08/1.01  --prop_solver_per_cl                    1000
% 2.08/1.01  --min_unsat_core                        false
% 2.08/1.01  --soft_assumptions                      false
% 2.08/1.01  --soft_lemma_size                       3
% 2.08/1.01  --prop_impl_unit_size                   0
% 2.08/1.01  --prop_impl_unit                        []
% 2.08/1.01  --share_sel_clauses                     true
% 2.08/1.01  --reset_solvers                         false
% 2.08/1.01  --bc_imp_inh                            [conj_cone]
% 2.08/1.01  --conj_cone_tolerance                   3.
% 2.08/1.01  --extra_neg_conj                        none
% 2.08/1.01  --large_theory_mode                     true
% 2.08/1.01  --prolific_symb_bound                   200
% 2.08/1.01  --lt_threshold                          2000
% 2.08/1.01  --clause_weak_htbl                      true
% 2.08/1.01  --gc_record_bc_elim                     false
% 2.08/1.01  
% 2.08/1.01  ------ Preprocessing Options
% 2.08/1.01  
% 2.08/1.01  --preprocessing_flag                    true
% 2.08/1.01  --time_out_prep_mult                    0.1
% 2.08/1.01  --splitting_mode                        input
% 2.08/1.01  --splitting_grd                         true
% 2.08/1.01  --splitting_cvd                         false
% 2.08/1.01  --splitting_cvd_svl                     false
% 2.08/1.01  --splitting_nvd                         32
% 2.08/1.01  --sub_typing                            true
% 2.08/1.01  --prep_gs_sim                           true
% 2.08/1.01  --prep_unflatten                        true
% 2.08/1.01  --prep_res_sim                          true
% 2.08/1.01  --prep_upred                            true
% 2.08/1.01  --prep_sem_filter                       exhaustive
% 2.08/1.01  --prep_sem_filter_out                   false
% 2.08/1.01  --pred_elim                             true
% 2.08/1.01  --res_sim_input                         true
% 2.08/1.01  --eq_ax_congr_red                       true
% 2.08/1.01  --pure_diseq_elim                       true
% 2.08/1.01  --brand_transform                       false
% 2.08/1.01  --non_eq_to_eq                          false
% 2.08/1.01  --prep_def_merge                        true
% 2.08/1.01  --prep_def_merge_prop_impl              false
% 2.08/1.01  --prep_def_merge_mbd                    true
% 2.08/1.01  --prep_def_merge_tr_red                 false
% 2.08/1.01  --prep_def_merge_tr_cl                  false
% 2.08/1.01  --smt_preprocessing                     true
% 2.08/1.01  --smt_ac_axioms                         fast
% 2.08/1.01  --preprocessed_out                      false
% 2.08/1.01  --preprocessed_stats                    false
% 2.08/1.01  
% 2.08/1.01  ------ Abstraction refinement Options
% 2.08/1.01  
% 2.08/1.01  --abstr_ref                             []
% 2.08/1.01  --abstr_ref_prep                        false
% 2.08/1.01  --abstr_ref_until_sat                   false
% 2.08/1.01  --abstr_ref_sig_restrict                funpre
% 2.08/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.08/1.01  --abstr_ref_under                       []
% 2.08/1.01  
% 2.08/1.01  ------ SAT Options
% 2.08/1.01  
% 2.08/1.01  --sat_mode                              false
% 2.08/1.01  --sat_fm_restart_options                ""
% 2.08/1.01  --sat_gr_def                            false
% 2.08/1.01  --sat_epr_types                         true
% 2.08/1.01  --sat_non_cyclic_types                  false
% 2.08/1.01  --sat_finite_models                     false
% 2.08/1.01  --sat_fm_lemmas                         false
% 2.08/1.01  --sat_fm_prep                           false
% 2.08/1.01  --sat_fm_uc_incr                        true
% 2.08/1.01  --sat_out_model                         small
% 2.08/1.01  --sat_out_clauses                       false
% 2.08/1.01  
% 2.08/1.01  ------ QBF Options
% 2.08/1.01  
% 2.08/1.01  --qbf_mode                              false
% 2.08/1.01  --qbf_elim_univ                         false
% 2.08/1.01  --qbf_dom_inst                          none
% 2.08/1.01  --qbf_dom_pre_inst                      false
% 2.08/1.01  --qbf_sk_in                             false
% 2.08/1.01  --qbf_pred_elim                         true
% 2.08/1.01  --qbf_split                             512
% 2.08/1.01  
% 2.08/1.01  ------ BMC1 Options
% 2.08/1.01  
% 2.08/1.01  --bmc1_incremental                      false
% 2.08/1.01  --bmc1_axioms                           reachable_all
% 2.08/1.01  --bmc1_min_bound                        0
% 2.08/1.01  --bmc1_max_bound                        -1
% 2.08/1.01  --bmc1_max_bound_default                -1
% 2.08/1.01  --bmc1_symbol_reachability              true
% 2.08/1.01  --bmc1_property_lemmas                  false
% 2.08/1.01  --bmc1_k_induction                      false
% 2.08/1.01  --bmc1_non_equiv_states                 false
% 2.08/1.01  --bmc1_deadlock                         false
% 2.08/1.01  --bmc1_ucm                              false
% 2.08/1.01  --bmc1_add_unsat_core                   none
% 2.08/1.01  --bmc1_unsat_core_children              false
% 2.08/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.08/1.01  --bmc1_out_stat                         full
% 2.08/1.01  --bmc1_ground_init                      false
% 2.08/1.01  --bmc1_pre_inst_next_state              false
% 2.08/1.01  --bmc1_pre_inst_state                   false
% 2.08/1.01  --bmc1_pre_inst_reach_state             false
% 2.08/1.01  --bmc1_out_unsat_core                   false
% 2.08/1.01  --bmc1_aig_witness_out                  false
% 2.08/1.01  --bmc1_verbose                          false
% 2.08/1.01  --bmc1_dump_clauses_tptp                false
% 2.08/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.08/1.01  --bmc1_dump_file                        -
% 2.08/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.08/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.08/1.01  --bmc1_ucm_extend_mode                  1
% 2.08/1.01  --bmc1_ucm_init_mode                    2
% 2.08/1.01  --bmc1_ucm_cone_mode                    none
% 2.08/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.08/1.01  --bmc1_ucm_relax_model                  4
% 2.08/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.08/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.08/1.01  --bmc1_ucm_layered_model                none
% 2.08/1.01  --bmc1_ucm_max_lemma_size               10
% 2.08/1.01  
% 2.08/1.01  ------ AIG Options
% 2.08/1.01  
% 2.08/1.01  --aig_mode                              false
% 2.08/1.01  
% 2.08/1.01  ------ Instantiation Options
% 2.08/1.01  
% 2.08/1.01  --instantiation_flag                    true
% 2.08/1.01  --inst_sos_flag                         false
% 2.08/1.01  --inst_sos_phase                        true
% 2.08/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.08/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.08/1.01  --inst_lit_sel_side                     num_symb
% 2.08/1.01  --inst_solver_per_active                1400
% 2.08/1.01  --inst_solver_calls_frac                1.
% 2.08/1.01  --inst_passive_queue_type               priority_queues
% 2.08/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.08/1.01  --inst_passive_queues_freq              [25;2]
% 2.08/1.01  --inst_dismatching                      true
% 2.08/1.01  --inst_eager_unprocessed_to_passive     true
% 2.08/1.01  --inst_prop_sim_given                   true
% 2.08/1.01  --inst_prop_sim_new                     false
% 2.08/1.01  --inst_subs_new                         false
% 2.08/1.01  --inst_eq_res_simp                      false
% 2.08/1.01  --inst_subs_given                       false
% 2.08/1.01  --inst_orphan_elimination               true
% 2.08/1.01  --inst_learning_loop_flag               true
% 2.08/1.01  --inst_learning_start                   3000
% 2.08/1.01  --inst_learning_factor                  2
% 2.08/1.01  --inst_start_prop_sim_after_learn       3
% 2.08/1.01  --inst_sel_renew                        solver
% 2.08/1.01  --inst_lit_activity_flag                true
% 2.08/1.01  --inst_restr_to_given                   false
% 2.08/1.01  --inst_activity_threshold               500
% 2.08/1.01  --inst_out_proof                        true
% 2.08/1.01  
% 2.08/1.01  ------ Resolution Options
% 2.08/1.01  
% 2.08/1.01  --resolution_flag                       true
% 2.08/1.01  --res_lit_sel                           adaptive
% 2.08/1.01  --res_lit_sel_side                      none
% 2.08/1.01  --res_ordering                          kbo
% 2.08/1.01  --res_to_prop_solver                    active
% 2.08/1.01  --res_prop_simpl_new                    false
% 2.08/1.01  --res_prop_simpl_given                  true
% 2.08/1.01  --res_passive_queue_type                priority_queues
% 2.08/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.08/1.01  --res_passive_queues_freq               [15;5]
% 2.08/1.01  --res_forward_subs                      full
% 2.08/1.01  --res_backward_subs                     full
% 2.08/1.01  --res_forward_subs_resolution           true
% 2.08/1.01  --res_backward_subs_resolution          true
% 2.08/1.01  --res_orphan_elimination                true
% 2.08/1.01  --res_time_limit                        2.
% 2.08/1.01  --res_out_proof                         true
% 2.08/1.01  
% 2.08/1.01  ------ Superposition Options
% 2.08/1.01  
% 2.08/1.01  --superposition_flag                    true
% 2.08/1.01  --sup_passive_queue_type                priority_queues
% 2.08/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.08/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.08/1.01  --demod_completeness_check              fast
% 2.08/1.01  --demod_use_ground                      true
% 2.08/1.01  --sup_to_prop_solver                    passive
% 2.08/1.01  --sup_prop_simpl_new                    true
% 2.08/1.01  --sup_prop_simpl_given                  true
% 2.08/1.01  --sup_fun_splitting                     false
% 2.08/1.01  --sup_smt_interval                      50000
% 2.08/1.01  
% 2.08/1.01  ------ Superposition Simplification Setup
% 2.08/1.01  
% 2.08/1.01  --sup_indices_passive                   []
% 2.08/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.08/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.08/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.08/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.08/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.08/1.01  --sup_full_bw                           [BwDemod]
% 2.08/1.01  --sup_immed_triv                        [TrivRules]
% 2.08/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.08/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.08/1.01  --sup_immed_bw_main                     []
% 2.08/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.08/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.08/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.08/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.08/1.01  
% 2.08/1.01  ------ Combination Options
% 2.08/1.01  
% 2.08/1.01  --comb_res_mult                         3
% 2.08/1.01  --comb_sup_mult                         2
% 2.08/1.01  --comb_inst_mult                        10
% 2.08/1.01  
% 2.08/1.01  ------ Debug Options
% 2.08/1.01  
% 2.08/1.01  --dbg_backtrace                         false
% 2.08/1.01  --dbg_dump_prop_clauses                 false
% 2.08/1.01  --dbg_dump_prop_clauses_file            -
% 2.08/1.01  --dbg_out_stat                          false
% 2.08/1.01  ------ Parsing...
% 2.08/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.08/1.01  
% 2.08/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 2.08/1.01  
% 2.08/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.08/1.01  
% 2.08/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.08/1.01  ------ Proving...
% 2.08/1.01  ------ Problem Properties 
% 2.08/1.01  
% 2.08/1.01  
% 2.08/1.01  clauses                                 16
% 2.08/1.01  conjectures                             2
% 2.08/1.01  EPR                                     2
% 2.08/1.01  Horn                                    14
% 2.08/1.01  unary                                   5
% 2.08/1.01  binary                                  3
% 2.08/1.01  lits                                    43
% 2.08/1.01  lits eq                                 6
% 2.08/1.01  fd_pure                                 0
% 2.08/1.01  fd_pseudo                               0
% 2.08/1.01  fd_cond                                 0
% 2.08/1.01  fd_pseudo_cond                          1
% 2.08/1.01  AC symbols                              0
% 2.08/1.01  
% 2.08/1.01  ------ Schedule dynamic 5 is on 
% 2.08/1.01  
% 2.08/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.08/1.01  
% 2.08/1.01  
% 2.08/1.01  ------ 
% 2.08/1.01  Current options:
% 2.08/1.01  ------ 
% 2.08/1.01  
% 2.08/1.01  ------ Input Options
% 2.08/1.01  
% 2.08/1.01  --out_options                           all
% 2.08/1.01  --tptp_safe_out                         true
% 2.08/1.01  --problem_path                          ""
% 2.08/1.01  --include_path                          ""
% 2.08/1.01  --clausifier                            res/vclausify_rel
% 2.08/1.01  --clausifier_options                    --mode clausify
% 2.08/1.01  --stdin                                 false
% 2.08/1.01  --stats_out                             all
% 2.08/1.01  
% 2.08/1.01  ------ General Options
% 2.08/1.01  
% 2.08/1.01  --fof                                   false
% 2.08/1.01  --time_out_real                         305.
% 2.08/1.01  --time_out_virtual                      -1.
% 2.08/1.01  --symbol_type_check                     false
% 2.08/1.01  --clausify_out                          false
% 2.08/1.01  --sig_cnt_out                           false
% 2.08/1.01  --trig_cnt_out                          false
% 2.08/1.01  --trig_cnt_out_tolerance                1.
% 2.08/1.01  --trig_cnt_out_sk_spl                   false
% 2.08/1.01  --abstr_cl_out                          false
% 2.08/1.01  
% 2.08/1.01  ------ Global Options
% 2.08/1.01  
% 2.08/1.01  --schedule                              default
% 2.08/1.01  --add_important_lit                     false
% 2.08/1.01  --prop_solver_per_cl                    1000
% 2.08/1.01  --min_unsat_core                        false
% 2.08/1.01  --soft_assumptions                      false
% 2.08/1.01  --soft_lemma_size                       3
% 2.08/1.01  --prop_impl_unit_size                   0
% 2.08/1.01  --prop_impl_unit                        []
% 2.08/1.01  --share_sel_clauses                     true
% 2.08/1.01  --reset_solvers                         false
% 2.08/1.01  --bc_imp_inh                            [conj_cone]
% 2.08/1.01  --conj_cone_tolerance                   3.
% 2.08/1.01  --extra_neg_conj                        none
% 2.08/1.01  --large_theory_mode                     true
% 2.08/1.01  --prolific_symb_bound                   200
% 2.08/1.01  --lt_threshold                          2000
% 2.08/1.01  --clause_weak_htbl                      true
% 2.08/1.01  --gc_record_bc_elim                     false
% 2.08/1.01  
% 2.08/1.01  ------ Preprocessing Options
% 2.08/1.01  
% 2.08/1.01  --preprocessing_flag                    true
% 2.08/1.01  --time_out_prep_mult                    0.1
% 2.08/1.01  --splitting_mode                        input
% 2.08/1.01  --splitting_grd                         true
% 2.08/1.01  --splitting_cvd                         false
% 2.08/1.01  --splitting_cvd_svl                     false
% 2.08/1.01  --splitting_nvd                         32
% 2.08/1.01  --sub_typing                            true
% 2.08/1.01  --prep_gs_sim                           true
% 2.08/1.01  --prep_unflatten                        true
% 2.08/1.01  --prep_res_sim                          true
% 2.08/1.01  --prep_upred                            true
% 2.08/1.01  --prep_sem_filter                       exhaustive
% 2.08/1.01  --prep_sem_filter_out                   false
% 2.08/1.01  --pred_elim                             true
% 2.08/1.01  --res_sim_input                         true
% 2.08/1.01  --eq_ax_congr_red                       true
% 2.08/1.01  --pure_diseq_elim                       true
% 2.08/1.01  --brand_transform                       false
% 2.08/1.01  --non_eq_to_eq                          false
% 2.08/1.01  --prep_def_merge                        true
% 2.08/1.01  --prep_def_merge_prop_impl              false
% 2.08/1.01  --prep_def_merge_mbd                    true
% 2.08/1.01  --prep_def_merge_tr_red                 false
% 2.08/1.01  --prep_def_merge_tr_cl                  false
% 2.08/1.01  --smt_preprocessing                     true
% 2.08/1.01  --smt_ac_axioms                         fast
% 2.08/1.01  --preprocessed_out                      false
% 2.08/1.01  --preprocessed_stats                    false
% 2.08/1.01  
% 2.08/1.01  ------ Abstraction refinement Options
% 2.08/1.01  
% 2.08/1.01  --abstr_ref                             []
% 2.08/1.01  --abstr_ref_prep                        false
% 2.08/1.01  --abstr_ref_until_sat                   false
% 2.08/1.01  --abstr_ref_sig_restrict                funpre
% 2.08/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.08/1.01  --abstr_ref_under                       []
% 2.08/1.01  
% 2.08/1.01  ------ SAT Options
% 2.08/1.01  
% 2.08/1.01  --sat_mode                              false
% 2.08/1.01  --sat_fm_restart_options                ""
% 2.08/1.01  --sat_gr_def                            false
% 2.08/1.01  --sat_epr_types                         true
% 2.08/1.01  --sat_non_cyclic_types                  false
% 2.08/1.01  --sat_finite_models                     false
% 2.08/1.01  --sat_fm_lemmas                         false
% 2.08/1.01  --sat_fm_prep                           false
% 2.08/1.01  --sat_fm_uc_incr                        true
% 2.08/1.01  --sat_out_model                         small
% 2.08/1.01  --sat_out_clauses                       false
% 2.08/1.01  
% 2.08/1.01  ------ QBF Options
% 2.08/1.01  
% 2.08/1.01  --qbf_mode                              false
% 2.08/1.01  --qbf_elim_univ                         false
% 2.08/1.01  --qbf_dom_inst                          none
% 2.08/1.01  --qbf_dom_pre_inst                      false
% 2.08/1.01  --qbf_sk_in                             false
% 2.08/1.01  --qbf_pred_elim                         true
% 2.08/1.01  --qbf_split                             512
% 2.08/1.01  
% 2.08/1.01  ------ BMC1 Options
% 2.08/1.01  
% 2.08/1.01  --bmc1_incremental                      false
% 2.08/1.01  --bmc1_axioms                           reachable_all
% 2.08/1.01  --bmc1_min_bound                        0
% 2.08/1.01  --bmc1_max_bound                        -1
% 2.08/1.01  --bmc1_max_bound_default                -1
% 2.08/1.01  --bmc1_symbol_reachability              true
% 2.08/1.01  --bmc1_property_lemmas                  false
% 2.08/1.01  --bmc1_k_induction                      false
% 2.08/1.01  --bmc1_non_equiv_states                 false
% 2.08/1.01  --bmc1_deadlock                         false
% 2.08/1.01  --bmc1_ucm                              false
% 2.08/1.01  --bmc1_add_unsat_core                   none
% 2.08/1.01  --bmc1_unsat_core_children              false
% 2.08/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.08/1.01  --bmc1_out_stat                         full
% 2.08/1.01  --bmc1_ground_init                      false
% 2.08/1.01  --bmc1_pre_inst_next_state              false
% 2.08/1.01  --bmc1_pre_inst_state                   false
% 2.08/1.01  --bmc1_pre_inst_reach_state             false
% 2.08/1.01  --bmc1_out_unsat_core                   false
% 2.08/1.01  --bmc1_aig_witness_out                  false
% 2.08/1.01  --bmc1_verbose                          false
% 2.08/1.01  --bmc1_dump_clauses_tptp                false
% 2.08/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.08/1.01  --bmc1_dump_file                        -
% 2.08/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.08/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.08/1.01  --bmc1_ucm_extend_mode                  1
% 2.08/1.01  --bmc1_ucm_init_mode                    2
% 2.08/1.01  --bmc1_ucm_cone_mode                    none
% 2.08/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.08/1.01  --bmc1_ucm_relax_model                  4
% 2.08/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.08/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.08/1.01  --bmc1_ucm_layered_model                none
% 2.08/1.01  --bmc1_ucm_max_lemma_size               10
% 2.08/1.01  
% 2.08/1.01  ------ AIG Options
% 2.08/1.01  
% 2.08/1.01  --aig_mode                              false
% 2.08/1.01  
% 2.08/1.01  ------ Instantiation Options
% 2.08/1.01  
% 2.08/1.01  --instantiation_flag                    true
% 2.08/1.01  --inst_sos_flag                         false
% 2.08/1.01  --inst_sos_phase                        true
% 2.08/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.08/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.08/1.01  --inst_lit_sel_side                     none
% 2.08/1.01  --inst_solver_per_active                1400
% 2.08/1.01  --inst_solver_calls_frac                1.
% 2.08/1.01  --inst_passive_queue_type               priority_queues
% 2.08/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.08/1.01  --inst_passive_queues_freq              [25;2]
% 2.08/1.01  --inst_dismatching                      true
% 2.08/1.01  --inst_eager_unprocessed_to_passive     true
% 2.08/1.01  --inst_prop_sim_given                   true
% 2.08/1.01  --inst_prop_sim_new                     false
% 2.08/1.01  --inst_subs_new                         false
% 2.08/1.01  --inst_eq_res_simp                      false
% 2.08/1.01  --inst_subs_given                       false
% 2.08/1.01  --inst_orphan_elimination               true
% 2.08/1.01  --inst_learning_loop_flag               true
% 2.08/1.01  --inst_learning_start                   3000
% 2.08/1.01  --inst_learning_factor                  2
% 2.08/1.01  --inst_start_prop_sim_after_learn       3
% 2.08/1.01  --inst_sel_renew                        solver
% 2.08/1.01  --inst_lit_activity_flag                true
% 2.08/1.01  --inst_restr_to_given                   false
% 2.08/1.01  --inst_activity_threshold               500
% 2.08/1.01  --inst_out_proof                        true
% 2.08/1.01  
% 2.08/1.01  ------ Resolution Options
% 2.08/1.01  
% 2.08/1.01  --resolution_flag                       false
% 2.08/1.01  --res_lit_sel                           adaptive
% 2.08/1.01  --res_lit_sel_side                      none
% 2.08/1.01  --res_ordering                          kbo
% 2.08/1.01  --res_to_prop_solver                    active
% 2.08/1.01  --res_prop_simpl_new                    false
% 2.08/1.01  --res_prop_simpl_given                  true
% 2.08/1.01  --res_passive_queue_type                priority_queues
% 2.08/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.08/1.01  --res_passive_queues_freq               [15;5]
% 2.08/1.01  --res_forward_subs                      full
% 2.08/1.01  --res_backward_subs                     full
% 2.08/1.01  --res_forward_subs_resolution           true
% 2.08/1.01  --res_backward_subs_resolution          true
% 2.08/1.01  --res_orphan_elimination                true
% 2.08/1.01  --res_time_limit                        2.
% 2.08/1.01  --res_out_proof                         true
% 2.08/1.01  
% 2.08/1.01  ------ Superposition Options
% 2.08/1.01  
% 2.08/1.01  --superposition_flag                    true
% 2.08/1.01  --sup_passive_queue_type                priority_queues
% 2.08/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.08/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.08/1.01  --demod_completeness_check              fast
% 2.08/1.01  --demod_use_ground                      true
% 2.08/1.01  --sup_to_prop_solver                    passive
% 2.08/1.01  --sup_prop_simpl_new                    true
% 2.08/1.01  --sup_prop_simpl_given                  true
% 2.08/1.01  --sup_fun_splitting                     false
% 2.08/1.01  --sup_smt_interval                      50000
% 2.08/1.01  
% 2.08/1.01  ------ Superposition Simplification Setup
% 2.08/1.01  
% 2.08/1.01  --sup_indices_passive                   []
% 2.08/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.08/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.08/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.08/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.08/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.08/1.01  --sup_full_bw                           [BwDemod]
% 2.08/1.01  --sup_immed_triv                        [TrivRules]
% 2.08/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.08/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.08/1.01  --sup_immed_bw_main                     []
% 2.08/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.08/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.08/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.08/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.08/1.01  
% 2.08/1.01  ------ Combination Options
% 2.08/1.01  
% 2.08/1.01  --comb_res_mult                         3
% 2.08/1.01  --comb_sup_mult                         2
% 2.08/1.01  --comb_inst_mult                        10
% 2.08/1.01  
% 2.08/1.01  ------ Debug Options
% 2.08/1.01  
% 2.08/1.01  --dbg_backtrace                         false
% 2.08/1.01  --dbg_dump_prop_clauses                 false
% 2.08/1.01  --dbg_dump_prop_clauses_file            -
% 2.08/1.01  --dbg_out_stat                          false
% 2.08/1.01  
% 2.08/1.01  
% 2.08/1.01  
% 2.08/1.01  
% 2.08/1.01  ------ Proving...
% 2.08/1.01  
% 2.08/1.01  
% 2.08/1.01  % SZS status Theorem for theBenchmark.p
% 2.08/1.01  
% 2.08/1.01   Resolution empty clause
% 2.08/1.01  
% 2.08/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.08/1.01  
% 2.08/1.01  fof(f3,axiom,(
% 2.08/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 2.08/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/1.01  
% 2.08/1.01  fof(f21,plain,(
% 2.08/1.01    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.08/1.01    inference(ennf_transformation,[],[f3])).
% 2.08/1.01  
% 2.08/1.01  fof(f22,plain,(
% 2.08/1.01    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.08/1.01    inference(flattening,[],[f21])).
% 2.08/1.01  
% 2.08/1.01  fof(f35,plain,(
% 2.08/1.01    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.08/1.01    inference(nnf_transformation,[],[f22])).
% 2.08/1.01  
% 2.08/1.01  fof(f49,plain,(
% 2.08/1.01    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.08/1.01    inference(cnf_transformation,[],[f35])).
% 2.08/1.01  
% 2.08/1.01  fof(f10,axiom,(
% 2.08/1.01    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v4_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 2.08/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/1.01  
% 2.08/1.01  fof(f16,plain,(
% 2.08/1.01    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 2.08/1.01    inference(pure_predicate_removal,[],[f10])).
% 2.08/1.01  
% 2.08/1.01  fof(f19,plain,(
% 2.08/1.01    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)))),
% 2.08/1.01    inference(pure_predicate_removal,[],[f16])).
% 2.08/1.01  
% 2.08/1.01  fof(f62,plain,(
% 2.08/1.01    ( ! [X0] : (v3_orders_2(k2_yellow_1(X0))) )),
% 2.08/1.01    inference(cnf_transformation,[],[f19])).
% 2.08/1.01  
% 2.08/1.01  fof(f9,axiom,(
% 2.08/1.01    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 2.08/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/1.01  
% 2.08/1.01  fof(f18,plain,(
% 2.08/1.01    ! [X0] : l1_orders_2(k2_yellow_1(X0))),
% 2.08/1.01    inference(pure_predicate_removal,[],[f9])).
% 2.08/1.01  
% 2.08/1.01  fof(f61,plain,(
% 2.08/1.01    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 2.08/1.01    inference(cnf_transformation,[],[f18])).
% 2.08/1.01  
% 2.08/1.01  fof(f1,axiom,(
% 2.08/1.01    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.08/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/1.01  
% 2.08/1.01  fof(f47,plain,(
% 2.08/1.01    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.08/1.01    inference(cnf_transformation,[],[f1])).
% 2.08/1.01  
% 2.08/1.01  fof(f13,axiom,(
% 2.08/1.01    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)))))),
% 2.08/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/1.01  
% 2.08/1.01  fof(f32,plain,(
% 2.08/1.01    ! [X0] : (! [X1] : (! [X2] : ((r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 2.08/1.01    inference(ennf_transformation,[],[f13])).
% 2.08/1.01  
% 2.08/1.01  fof(f44,plain,(
% 2.08/1.01    ! [X0] : (! [X1] : (! [X2] : (((r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2)) & (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 2.08/1.01    inference(nnf_transformation,[],[f32])).
% 2.08/1.01  
% 2.08/1.01  fof(f68,plain,(
% 2.08/1.01    ( ! [X2,X0,X1] : (r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 2.08/1.01    inference(cnf_transformation,[],[f44])).
% 2.08/1.01  
% 2.08/1.01  fof(f14,conjecture,(
% 2.08/1.01    ! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k1_xboole_0,X0) => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))))),
% 2.08/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/1.01  
% 2.08/1.01  fof(f15,negated_conjecture,(
% 2.08/1.01    ~! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k1_xboole_0,X0) => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))))),
% 2.08/1.01    inference(negated_conjecture,[],[f14])).
% 2.08/1.01  
% 2.08/1.01  fof(f33,plain,(
% 2.08/1.01    ? [X0] : ((k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0)) & r2_hidden(k1_xboole_0,X0)) & ~v1_xboole_0(X0))),
% 2.08/1.01    inference(ennf_transformation,[],[f15])).
% 2.08/1.01  
% 2.08/1.01  fof(f34,plain,(
% 2.08/1.01    ? [X0] : (k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0)) & r2_hidden(k1_xboole_0,X0) & ~v1_xboole_0(X0))),
% 2.08/1.01    inference(flattening,[],[f33])).
% 2.08/1.01  
% 2.08/1.01  fof(f45,plain,(
% 2.08/1.01    ? [X0] : (k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0)) & r2_hidden(k1_xboole_0,X0) & ~v1_xboole_0(X0)) => (k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK2)) & r2_hidden(k1_xboole_0,sK2) & ~v1_xboole_0(sK2))),
% 2.08/1.01    introduced(choice_axiom,[])).
% 2.08/1.01  
% 2.08/1.01  fof(f46,plain,(
% 2.08/1.01    k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK2)) & r2_hidden(k1_xboole_0,sK2) & ~v1_xboole_0(sK2)),
% 2.08/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f34,f45])).
% 2.08/1.01  
% 2.08/1.01  fof(f69,plain,(
% 2.08/1.01    ~v1_xboole_0(sK2)),
% 2.08/1.01    inference(cnf_transformation,[],[f46])).
% 2.08/1.01  
% 2.08/1.01  fof(f11,axiom,(
% 2.08/1.01    ! [X0] : (~v1_xboole_0(X0) => (v1_orders_2(k2_yellow_1(X0)) & ~v2_struct_0(k2_yellow_1(X0))))),
% 2.08/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/1.01  
% 2.08/1.01  fof(f17,plain,(
% 2.08/1.01    ! [X0] : (~v1_xboole_0(X0) => ~v2_struct_0(k2_yellow_1(X0)))),
% 2.08/1.01    inference(pure_predicate_removal,[],[f11])).
% 2.08/1.01  
% 2.08/1.01  fof(f31,plain,(
% 2.08/1.01    ! [X0] : (~v2_struct_0(k2_yellow_1(X0)) | v1_xboole_0(X0))),
% 2.08/1.01    inference(ennf_transformation,[],[f17])).
% 2.08/1.01  
% 2.08/1.01  fof(f64,plain,(
% 2.08/1.01    ( ! [X0] : (~v2_struct_0(k2_yellow_1(X0)) | v1_xboole_0(X0)) )),
% 2.08/1.01    inference(cnf_transformation,[],[f31])).
% 2.08/1.01  
% 2.08/1.01  fof(f12,axiom,(
% 2.08/1.01    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 2.08/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/1.01  
% 2.08/1.01  fof(f65,plain,(
% 2.08/1.01    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 2.08/1.01    inference(cnf_transformation,[],[f12])).
% 2.08/1.01  
% 2.08/1.01  fof(f2,axiom,(
% 2.08/1.01    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 2.08/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/1.01  
% 2.08/1.01  fof(f20,plain,(
% 2.08/1.01    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 2.08/1.01    inference(ennf_transformation,[],[f2])).
% 2.08/1.01  
% 2.08/1.01  fof(f48,plain,(
% 2.08/1.01    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 2.08/1.01    inference(cnf_transformation,[],[f20])).
% 2.08/1.01  
% 2.08/1.01  fof(f70,plain,(
% 2.08/1.01    r2_hidden(k1_xboole_0,sK2)),
% 2.08/1.01    inference(cnf_transformation,[],[f46])).
% 2.08/1.01  
% 2.08/1.01  fof(f8,axiom,(
% 2.08/1.01    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_orders_2(X0,k3_yellow_0(X0),X1)))),
% 2.08/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/1.01  
% 2.08/1.01  fof(f29,plain,(
% 2.08/1.01    ! [X0] : (! [X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 2.08/1.01    inference(ennf_transformation,[],[f8])).
% 2.08/1.01  
% 2.08/1.01  fof(f30,plain,(
% 2.08/1.01    ! [X0] : (! [X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.08/1.01    inference(flattening,[],[f29])).
% 2.08/1.01  
% 2.08/1.01  fof(f60,plain,(
% 2.08/1.01    ( ! [X0,X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 2.08/1.01    inference(cnf_transformation,[],[f30])).
% 2.08/1.01  
% 2.08/1.01  fof(f63,plain,(
% 2.08/1.01    ( ! [X0] : (v5_orders_2(k2_yellow_1(X0))) )),
% 2.08/1.01    inference(cnf_transformation,[],[f19])).
% 2.08/1.01  
% 2.08/1.01  fof(f4,axiom,(
% 2.08/1.01    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X1) & r1_orders_2(X0,X1,X2)) => X1 = X2))))),
% 2.08/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/1.01  
% 2.08/1.01  fof(f23,plain,(
% 2.08/1.01    ! [X0] : (! [X1] : (! [X2] : ((X1 = X2 | (~r1_orders_2(X0,X2,X1) | ~r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0)))),
% 2.08/1.01    inference(ennf_transformation,[],[f4])).
% 2.08/1.01  
% 2.08/1.01  fof(f24,plain,(
% 2.08/1.01    ! [X0] : (! [X1] : (! [X2] : (X1 = X2 | ~r1_orders_2(X0,X2,X1) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 2.08/1.01    inference(flattening,[],[f23])).
% 2.08/1.01  
% 2.08/1.01  fof(f51,plain,(
% 2.08/1.01    ( ! [X2,X0,X1] : (X1 = X2 | ~r1_orders_2(X0,X2,X1) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 2.08/1.01    inference(cnf_transformation,[],[f24])).
% 2.08/1.01  
% 2.08/1.01  fof(f7,axiom,(
% 2.08/1.01    ! [X0] : (l1_orders_2(X0) => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)))),
% 2.08/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/1.01  
% 2.08/1.01  fof(f28,plain,(
% 2.08/1.01    ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 2.08/1.01    inference(ennf_transformation,[],[f7])).
% 2.08/1.01  
% 2.08/1.01  fof(f59,plain,(
% 2.08/1.01    ( ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.08/1.01    inference(cnf_transformation,[],[f28])).
% 2.08/1.01  
% 2.08/1.01  fof(f71,plain,(
% 2.08/1.01    k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK2))),
% 2.08/1.01    inference(cnf_transformation,[],[f46])).
% 2.08/1.01  
% 2.08/1.01  fof(f5,axiom,(
% 2.08/1.01    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X2,X3))))))),
% 2.08/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/1.01  
% 2.08/1.01  fof(f25,plain,(
% 2.08/1.01    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.08/1.01    inference(ennf_transformation,[],[f5])).
% 2.08/1.01  
% 2.08/1.01  fof(f26,plain,(
% 2.08/1.01    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.08/1.01    inference(flattening,[],[f25])).
% 2.08/1.01  
% 2.08/1.01  fof(f36,plain,(
% 2.08/1.01    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.08/1.01    inference(nnf_transformation,[],[f26])).
% 2.08/1.01  
% 2.08/1.01  fof(f37,plain,(
% 2.08/1.01    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.08/1.01    inference(rectify,[],[f36])).
% 2.08/1.01  
% 2.08/1.01  fof(f38,plain,(
% 2.08/1.01    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X2,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 2.08/1.01    introduced(choice_axiom,[])).
% 2.08/1.01  
% 2.08/1.01  fof(f39,plain,(
% 2.08/1.01    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | (~r1_orders_2(X0,X2,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.08/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).
% 2.08/1.01  
% 2.08/1.01  fof(f53,plain,(
% 2.08/1.01    ( ! [X2,X0,X1] : (r1_lattice3(X0,X1,X2) | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.08/1.01    inference(cnf_transformation,[],[f39])).
% 2.08/1.01  
% 2.08/1.01  fof(f55,plain,(
% 2.08/1.01    ( ! [X2,X0,X1] : (r1_lattice3(X0,X1,X2) | ~r1_orders_2(X0,X2,sK0(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.08/1.01    inference(cnf_transformation,[],[f39])).
% 2.08/1.01  
% 2.08/1.01  fof(f6,axiom,(
% 2.08/1.01    ! [X0] : (l1_orders_2(X0) => (v1_yellow_0(X0) <=> ? [X1] : (r1_lattice3(X0,u1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0)))))),
% 2.08/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/1.01  
% 2.08/1.01  fof(f27,plain,(
% 2.08/1.01    ! [X0] : ((v1_yellow_0(X0) <=> ? [X1] : (r1_lattice3(X0,u1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 2.08/1.01    inference(ennf_transformation,[],[f6])).
% 2.08/1.01  
% 2.08/1.01  fof(f40,plain,(
% 2.08/1.01    ! [X0] : (((v1_yellow_0(X0) | ! [X1] : (~r1_lattice3(X0,u1_struct_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X1] : (r1_lattice3(X0,u1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0))) | ~v1_yellow_0(X0))) | ~l1_orders_2(X0))),
% 2.08/1.01    inference(nnf_transformation,[],[f27])).
% 2.08/1.01  
% 2.08/1.01  fof(f41,plain,(
% 2.08/1.01    ! [X0] : (((v1_yellow_0(X0) | ! [X1] : (~r1_lattice3(X0,u1_struct_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X2] : (r1_lattice3(X0,u1_struct_0(X0),X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~v1_yellow_0(X0))) | ~l1_orders_2(X0))),
% 2.08/1.01    inference(rectify,[],[f40])).
% 2.08/1.01  
% 2.08/1.01  fof(f42,plain,(
% 2.08/1.01    ! [X0] : (? [X2] : (r1_lattice3(X0,u1_struct_0(X0),X2) & m1_subset_1(X2,u1_struct_0(X0))) => (r1_lattice3(X0,u1_struct_0(X0),sK1(X0)) & m1_subset_1(sK1(X0),u1_struct_0(X0))))),
% 2.08/1.01    introduced(choice_axiom,[])).
% 2.08/1.01  
% 2.08/1.01  fof(f43,plain,(
% 2.08/1.01    ! [X0] : (((v1_yellow_0(X0) | ! [X1] : (~r1_lattice3(X0,u1_struct_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)))) & ((r1_lattice3(X0,u1_struct_0(X0),sK1(X0)) & m1_subset_1(sK1(X0),u1_struct_0(X0))) | ~v1_yellow_0(X0))) | ~l1_orders_2(X0))),
% 2.08/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f41,f42])).
% 2.08/1.01  
% 2.08/1.01  fof(f58,plain,(
% 2.08/1.01    ( ! [X0,X1] : (v1_yellow_0(X0) | ~r1_lattice3(X0,u1_struct_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.08/1.01    inference(cnf_transformation,[],[f43])).
% 2.08/1.01  
% 2.08/1.01  cnf(c_3,plain,
% 2.08/1.01      ( r1_orders_2(X0,X1,X2)
% 2.08/1.01      | ~ r3_orders_2(X0,X1,X2)
% 2.08/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.08/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.08/1.01      | v2_struct_0(X0)
% 2.08/1.01      | ~ v3_orders_2(X0)
% 2.08/1.01      | ~ l1_orders_2(X0) ),
% 2.08/1.01      inference(cnf_transformation,[],[f49]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_16,plain,
% 2.08/1.01      ( v3_orders_2(k2_yellow_1(X0)) ),
% 2.08/1.01      inference(cnf_transformation,[],[f62]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_399,plain,
% 2.08/1.01      ( r1_orders_2(X0,X1,X2)
% 2.08/1.01      | ~ r3_orders_2(X0,X1,X2)
% 2.08/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.08/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.08/1.01      | v2_struct_0(X0)
% 2.08/1.01      | ~ l1_orders_2(X0)
% 2.08/1.01      | k2_yellow_1(X3) != X0 ),
% 2.08/1.01      inference(resolution_lifted,[status(thm)],[c_3,c_16]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_400,plain,
% 2.08/1.01      ( r1_orders_2(k2_yellow_1(X0),X1,X2)
% 2.08/1.01      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
% 2.08/1.01      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.08/1.01      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.08/1.01      | v2_struct_0(k2_yellow_1(X0))
% 2.08/1.01      | ~ l1_orders_2(k2_yellow_1(X0)) ),
% 2.08/1.01      inference(unflattening,[status(thm)],[c_399]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_14,plain,
% 2.08/1.01      ( l1_orders_2(k2_yellow_1(X0)) ),
% 2.08/1.01      inference(cnf_transformation,[],[f61]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_404,plain,
% 2.08/1.01      ( v2_struct_0(k2_yellow_1(X0))
% 2.08/1.01      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.08/1.01      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.08/1.01      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
% 2.08/1.01      | r1_orders_2(k2_yellow_1(X0),X1,X2) ),
% 2.08/1.01      inference(global_propositional_subsumption,[status(thm)],[c_400,c_14]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_405,plain,
% 2.08/1.01      ( r1_orders_2(k2_yellow_1(X0),X1,X2)
% 2.08/1.01      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
% 2.08/1.01      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.08/1.01      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.08/1.01      | v2_struct_0(k2_yellow_1(X0)) ),
% 2.08/1.01      inference(renaming,[status(thm)],[c_404]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_0,plain,
% 2.08/1.01      ( r1_tarski(k1_xboole_0,X0) ),
% 2.08/1.01      inference(cnf_transformation,[],[f47]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_20,plain,
% 2.08/1.01      ( r3_orders_2(k2_yellow_1(X0),X1,X2)
% 2.08/1.01      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.08/1.01      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.08/1.01      | ~ r1_tarski(X1,X2)
% 2.08/1.01      | v1_xboole_0(X0) ),
% 2.08/1.01      inference(cnf_transformation,[],[f68]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_24,negated_conjecture,
% 2.08/1.01      ( ~ v1_xboole_0(sK2) ),
% 2.08/1.01      inference(cnf_transformation,[],[f69]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_280,plain,
% 2.08/1.01      ( r3_orders_2(k2_yellow_1(X0),X1,X2)
% 2.08/1.01      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.08/1.01      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.08/1.01      | ~ r1_tarski(X1,X2)
% 2.08/1.01      | sK2 != X0 ),
% 2.08/1.01      inference(resolution_lifted,[status(thm)],[c_20,c_24]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_281,plain,
% 2.08/1.01      ( r3_orders_2(k2_yellow_1(sK2),X0,X1)
% 2.08/1.01      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK2)))
% 2.08/1.01      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK2)))
% 2.08/1.01      | ~ r1_tarski(X0,X1) ),
% 2.08/1.01      inference(unflattening,[status(thm)],[c_280]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_318,plain,
% 2.08/1.01      ( r3_orders_2(k2_yellow_1(sK2),X0,X1)
% 2.08/1.01      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK2)))
% 2.08/1.01      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK2)))
% 2.08/1.01      | X1 != X2
% 2.08/1.01      | k1_xboole_0 != X0 ),
% 2.08/1.01      inference(resolution_lifted,[status(thm)],[c_0,c_281]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_319,plain,
% 2.08/1.01      ( r3_orders_2(k2_yellow_1(sK2),k1_xboole_0,X0)
% 2.08/1.01      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK2)))
% 2.08/1.01      | ~ m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK2))) ),
% 2.08/1.01      inference(unflattening,[status(thm)],[c_318]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_537,plain,
% 2.08/1.01      ( r1_orders_2(k2_yellow_1(X0),X1,X2)
% 2.08/1.01      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.08/1.01      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.08/1.01      | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(sK2)))
% 2.08/1.01      | ~ m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK2)))
% 2.08/1.01      | v2_struct_0(k2_yellow_1(X0))
% 2.08/1.01      | X3 != X2
% 2.08/1.01      | k2_yellow_1(X0) != k2_yellow_1(sK2)
% 2.08/1.01      | k1_xboole_0 != X1 ),
% 2.08/1.01      inference(resolution_lifted,[status(thm)],[c_405,c_319]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_538,plain,
% 2.08/1.01      ( r1_orders_2(k2_yellow_1(X0),k1_xboole_0,X1)
% 2.08/1.01      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.08/1.01      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK2)))
% 2.08/1.01      | ~ m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(X0)))
% 2.08/1.01      | ~ m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK2)))
% 2.08/1.01      | v2_struct_0(k2_yellow_1(X0))
% 2.08/1.01      | k2_yellow_1(X0) != k2_yellow_1(sK2) ),
% 2.08/1.01      inference(unflattening,[status(thm)],[c_537]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_17,plain,
% 2.08/1.01      ( v1_xboole_0(X0) | ~ v2_struct_0(k2_yellow_1(X0)) ),
% 2.08/1.01      inference(cnf_transformation,[],[f64]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_298,plain,
% 2.08/1.01      ( ~ v2_struct_0(k2_yellow_1(X0)) | sK2 != X0 ),
% 2.08/1.01      inference(resolution_lifted,[status(thm)],[c_17,c_24]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_299,plain,
% 2.08/1.01      ( ~ v2_struct_0(k2_yellow_1(sK2)) ),
% 2.08/1.01      inference(unflattening,[status(thm)],[c_298]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_572,plain,
% 2.08/1.01      ( r1_orders_2(k2_yellow_1(X0),k1_xboole_0,X1)
% 2.08/1.01      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.08/1.01      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK2)))
% 2.08/1.01      | ~ m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(X0)))
% 2.08/1.01      | ~ m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK2)))
% 2.08/1.01      | k2_yellow_1(X0) != k2_yellow_1(sK2) ),
% 2.08/1.01      inference(resolution_lifted,[status(thm)],[c_538,c_299]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_1973,plain,
% 2.08/1.01      ( k2_yellow_1(X0) != k2_yellow_1(sK2)
% 2.08/1.01      | r1_orders_2(k2_yellow_1(X0),k1_xboole_0,X1) = iProver_top
% 2.08/1.01      | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 2.08/1.01      | m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK2))) != iProver_top
% 2.08/1.01      | m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 2.08/1.01      | m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK2))) != iProver_top ),
% 2.08/1.01      inference(predicate_to_equality,[status(thm)],[c_572]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_19,plain,
% 2.08/1.01      ( u1_struct_0(k2_yellow_1(X0)) = X0 ),
% 2.08/1.01      inference(cnf_transformation,[],[f65]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_2062,plain,
% 2.08/1.01      ( k2_yellow_1(X0) != k2_yellow_1(sK2)
% 2.08/1.01      | r1_orders_2(k2_yellow_1(X0),k1_xboole_0,X1) = iProver_top
% 2.08/1.01      | m1_subset_1(X1,X0) != iProver_top
% 2.08/1.01      | m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK2))) != iProver_top
% 2.08/1.01      | m1_subset_1(k1_xboole_0,X0) != iProver_top
% 2.08/1.01      | m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK2))) != iProver_top ),
% 2.08/1.01      inference(light_normalisation,[status(thm)],[c_1973,c_19]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_2063,plain,
% 2.08/1.01      ( k2_yellow_1(X0) != k2_yellow_1(sK2)
% 2.08/1.01      | r1_orders_2(k2_yellow_1(X0),k1_xboole_0,X1) = iProver_top
% 2.08/1.01      | m1_subset_1(X1,X0) != iProver_top
% 2.08/1.01      | m1_subset_1(X1,sK2) != iProver_top
% 2.08/1.01      | m1_subset_1(k1_xboole_0,X0) != iProver_top
% 2.08/1.01      | m1_subset_1(k1_xboole_0,sK2) != iProver_top ),
% 2.08/1.01      inference(demodulation,[status(thm)],[c_2062,c_19]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_1,plain,
% 2.08/1.01      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 2.08/1.01      inference(cnf_transformation,[],[f48]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_23,negated_conjecture,
% 2.08/1.01      ( r2_hidden(k1_xboole_0,sK2) ),
% 2.08/1.01      inference(cnf_transformation,[],[f70]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_714,plain,
% 2.08/1.01      ( m1_subset_1(X0,X1) | sK2 != X1 | k1_xboole_0 != X0 ),
% 2.08/1.01      inference(resolution_lifted,[status(thm)],[c_1,c_23]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_715,plain,
% 2.08/1.01      ( m1_subset_1(k1_xboole_0,sK2) ),
% 2.08/1.01      inference(unflattening,[status(thm)],[c_714]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_716,plain,
% 2.08/1.01      ( m1_subset_1(k1_xboole_0,sK2) = iProver_top ),
% 2.08/1.01      inference(predicate_to_equality,[status(thm)],[c_715]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_2187,plain,
% 2.08/1.01      ( m1_subset_1(k1_xboole_0,X0) != iProver_top
% 2.08/1.01      | m1_subset_1(X1,sK2) != iProver_top
% 2.08/1.01      | m1_subset_1(X1,X0) != iProver_top
% 2.08/1.01      | r1_orders_2(k2_yellow_1(X0),k1_xboole_0,X1) = iProver_top
% 2.08/1.01      | k2_yellow_1(X0) != k2_yellow_1(sK2) ),
% 2.08/1.01      inference(global_propositional_subsumption,[status(thm)],[c_2063,c_716]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_2188,plain,
% 2.08/1.01      ( k2_yellow_1(X0) != k2_yellow_1(sK2)
% 2.08/1.01      | r1_orders_2(k2_yellow_1(X0),k1_xboole_0,X1) = iProver_top
% 2.08/1.01      | m1_subset_1(X1,X0) != iProver_top
% 2.08/1.01      | m1_subset_1(X1,sK2) != iProver_top
% 2.08/1.01      | m1_subset_1(k1_xboole_0,X0) != iProver_top ),
% 2.08/1.01      inference(renaming,[status(thm)],[c_2187]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_2196,plain,
% 2.08/1.01      ( r1_orders_2(k2_yellow_1(sK2),k1_xboole_0,X0) = iProver_top
% 2.08/1.01      | m1_subset_1(X0,sK2) != iProver_top
% 2.08/1.01      | m1_subset_1(k1_xboole_0,sK2) != iProver_top ),
% 2.08/1.01      inference(equality_resolution,[status(thm)],[c_2188]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_2201,plain,
% 2.08/1.01      ( m1_subset_1(X0,sK2) != iProver_top
% 2.08/1.01      | r1_orders_2(k2_yellow_1(sK2),k1_xboole_0,X0) = iProver_top ),
% 2.08/1.01      inference(global_propositional_subsumption,[status(thm)],[c_2196,c_716]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_2202,plain,
% 2.08/1.01      ( r1_orders_2(k2_yellow_1(sK2),k1_xboole_0,X0) = iProver_top
% 2.08/1.01      | m1_subset_1(X0,sK2) != iProver_top ),
% 2.08/1.01      inference(renaming,[status(thm)],[c_2201]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_13,plain,
% 2.08/1.01      ( r1_orders_2(X0,k3_yellow_0(X0),X1)
% 2.08/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.08/1.01      | ~ v1_yellow_0(X0)
% 2.08/1.01      | ~ v5_orders_2(X0)
% 2.08/1.01      | v2_struct_0(X0)
% 2.08/1.01      | ~ l1_orders_2(X0) ),
% 2.08/1.01      inference(cnf_transformation,[],[f60]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_15,plain,
% 2.08/1.01      ( v5_orders_2(k2_yellow_1(X0)) ),
% 2.08/1.01      inference(cnf_transformation,[],[f63]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_337,plain,
% 2.08/1.01      ( r1_orders_2(X0,k3_yellow_0(X0),X1)
% 2.08/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.08/1.01      | ~ v1_yellow_0(X0)
% 2.08/1.01      | v2_struct_0(X0)
% 2.08/1.01      | ~ l1_orders_2(X0)
% 2.08/1.01      | k2_yellow_1(X2) != X0 ),
% 2.08/1.01      inference(resolution_lifted,[status(thm)],[c_13,c_15]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_338,plain,
% 2.08/1.01      ( r1_orders_2(k2_yellow_1(X0),k3_yellow_0(k2_yellow_1(X0)),X1)
% 2.08/1.01      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.08/1.01      | ~ v1_yellow_0(k2_yellow_1(X0))
% 2.08/1.01      | v2_struct_0(k2_yellow_1(X0))
% 2.08/1.01      | ~ l1_orders_2(k2_yellow_1(X0)) ),
% 2.08/1.01      inference(unflattening,[status(thm)],[c_337]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_342,plain,
% 2.08/1.01      ( v2_struct_0(k2_yellow_1(X0))
% 2.08/1.01      | ~ v1_yellow_0(k2_yellow_1(X0))
% 2.08/1.01      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.08/1.01      | r1_orders_2(k2_yellow_1(X0),k3_yellow_0(k2_yellow_1(X0)),X1) ),
% 2.08/1.01      inference(global_propositional_subsumption,[status(thm)],[c_338,c_14]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_343,plain,
% 2.08/1.01      ( r1_orders_2(k2_yellow_1(X0),k3_yellow_0(k2_yellow_1(X0)),X1)
% 2.08/1.01      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.08/1.01      | ~ v1_yellow_0(k2_yellow_1(X0))
% 2.08/1.01      | v2_struct_0(k2_yellow_1(X0)) ),
% 2.08/1.01      inference(renaming,[status(thm)],[c_342]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_595,plain,
% 2.08/1.01      ( r1_orders_2(k2_yellow_1(X0),k3_yellow_0(k2_yellow_1(X0)),X1)
% 2.08/1.01      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.08/1.01      | ~ v1_yellow_0(k2_yellow_1(X0))
% 2.08/1.01      | k2_yellow_1(X0) != k2_yellow_1(sK2) ),
% 2.08/1.01      inference(resolution_lifted,[status(thm)],[c_343,c_299]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_1974,plain,
% 2.08/1.01      ( k2_yellow_1(X0) != k2_yellow_1(sK2)
% 2.08/1.01      | r1_orders_2(k2_yellow_1(X0),k3_yellow_0(k2_yellow_1(X0)),X1) = iProver_top
% 2.08/1.01      | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 2.08/1.01      | v1_yellow_0(k2_yellow_1(X0)) != iProver_top ),
% 2.08/1.01      inference(predicate_to_equality,[status(thm)],[c_595]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_2031,plain,
% 2.08/1.01      ( k2_yellow_1(X0) != k2_yellow_1(sK2)
% 2.08/1.01      | r1_orders_2(k2_yellow_1(X0),k3_yellow_0(k2_yellow_1(X0)),X1) = iProver_top
% 2.08/1.01      | m1_subset_1(X1,X0) != iProver_top
% 2.08/1.01      | v1_yellow_0(k2_yellow_1(X0)) != iProver_top ),
% 2.08/1.01      inference(light_normalisation,[status(thm)],[c_1974,c_19]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_2150,plain,
% 2.08/1.01      ( r1_orders_2(k2_yellow_1(sK2),k3_yellow_0(k2_yellow_1(sK2)),X0) = iProver_top
% 2.08/1.01      | m1_subset_1(X0,sK2) != iProver_top
% 2.08/1.01      | v1_yellow_0(k2_yellow_1(sK2)) != iProver_top ),
% 2.08/1.01      inference(equality_resolution,[status(thm)],[c_2031]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_4,plain,
% 2.08/1.01      ( ~ r1_orders_2(X0,X1,X2)
% 2.08/1.01      | ~ r1_orders_2(X0,X2,X1)
% 2.08/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.08/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.08/1.01      | ~ v5_orders_2(X0)
% 2.08/1.01      | ~ l1_orders_2(X0)
% 2.08/1.01      | X2 = X1 ),
% 2.08/1.01      inference(cnf_transformation,[],[f51]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_361,plain,
% 2.08/1.01      ( ~ r1_orders_2(X0,X1,X2)
% 2.08/1.01      | ~ r1_orders_2(X0,X2,X1)
% 2.08/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.08/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.08/1.01      | ~ l1_orders_2(X0)
% 2.08/1.01      | X2 = X1
% 2.08/1.01      | k2_yellow_1(X3) != X0 ),
% 2.08/1.01      inference(resolution_lifted,[status(thm)],[c_4,c_15]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_362,plain,
% 2.08/1.01      ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
% 2.08/1.01      | ~ r1_orders_2(k2_yellow_1(X0),X2,X1)
% 2.08/1.01      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.08/1.01      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.08/1.01      | ~ l1_orders_2(k2_yellow_1(X0))
% 2.08/1.01      | X1 = X2 ),
% 2.08/1.01      inference(unflattening,[status(thm)],[c_361]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_366,plain,
% 2.08/1.01      ( ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.08/1.01      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.08/1.01      | ~ r1_orders_2(k2_yellow_1(X0),X2,X1)
% 2.08/1.01      | ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
% 2.08/1.01      | X1 = X2 ),
% 2.08/1.01      inference(global_propositional_subsumption,[status(thm)],[c_362,c_14]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_367,plain,
% 2.08/1.01      ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
% 2.08/1.01      | ~ r1_orders_2(k2_yellow_1(X0),X2,X1)
% 2.08/1.01      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.08/1.01      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.08/1.01      | X1 = X2 ),
% 2.08/1.01      inference(renaming,[status(thm)],[c_366]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_1975,plain,
% 2.08/1.01      ( X0 = X1
% 2.08/1.01      | r1_orders_2(k2_yellow_1(X2),X0,X1) != iProver_top
% 2.08/1.01      | r1_orders_2(k2_yellow_1(X2),X1,X0) != iProver_top
% 2.08/1.01      | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X2))) != iProver_top
% 2.08/1.01      | m1_subset_1(X0,u1_struct_0(k2_yellow_1(X2))) != iProver_top ),
% 2.08/1.01      inference(predicate_to_equality,[status(thm)],[c_367]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_2040,plain,
% 2.08/1.01      ( X0 = X1
% 2.08/1.01      | r1_orders_2(k2_yellow_1(X2),X1,X0) != iProver_top
% 2.08/1.01      | r1_orders_2(k2_yellow_1(X2),X0,X1) != iProver_top
% 2.08/1.01      | m1_subset_1(X1,X2) != iProver_top
% 2.08/1.01      | m1_subset_1(X0,X2) != iProver_top ),
% 2.08/1.01      inference(demodulation,[status(thm)],[c_1975,c_19]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_2786,plain,
% 2.08/1.01      ( k3_yellow_0(k2_yellow_1(sK2)) = X0
% 2.08/1.01      | r1_orders_2(k2_yellow_1(sK2),X0,k3_yellow_0(k2_yellow_1(sK2))) != iProver_top
% 2.08/1.01      | m1_subset_1(X0,sK2) != iProver_top
% 2.08/1.01      | m1_subset_1(k3_yellow_0(k2_yellow_1(sK2)),sK2) != iProver_top
% 2.08/1.01      | v1_yellow_0(k2_yellow_1(sK2)) != iProver_top ),
% 2.08/1.01      inference(superposition,[status(thm)],[c_2150,c_2040]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_12,plain,
% 2.08/1.01      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~ l1_orders_2(X0) ),
% 2.08/1.01      inference(cnf_transformation,[],[f59]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_788,plain,
% 2.08/1.01      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | k2_yellow_1(X1) != X0 ),
% 2.08/1.01      inference(resolution_lifted,[status(thm)],[c_12,c_14]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_789,plain,
% 2.08/1.01      ( m1_subset_1(k3_yellow_0(k2_yellow_1(X0)),u1_struct_0(k2_yellow_1(X0))) ),
% 2.08/1.01      inference(unflattening,[status(thm)],[c_788]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_1972,plain,
% 2.08/1.01      ( m1_subset_1(k3_yellow_0(k2_yellow_1(X0)),u1_struct_0(k2_yellow_1(X0))) = iProver_top ),
% 2.08/1.01      inference(predicate_to_equality,[status(thm)],[c_789]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_1986,plain,
% 2.08/1.01      ( m1_subset_1(k3_yellow_0(k2_yellow_1(X0)),X0) = iProver_top ),
% 2.08/1.01      inference(light_normalisation,[status(thm)],[c_1972,c_19]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_2917,plain,
% 2.08/1.01      ( k3_yellow_0(k2_yellow_1(sK2)) = X0
% 2.08/1.01      | r1_orders_2(k2_yellow_1(sK2),X0,k3_yellow_0(k2_yellow_1(sK2))) != iProver_top
% 2.08/1.01      | m1_subset_1(X0,sK2) != iProver_top
% 2.08/1.01      | v1_yellow_0(k2_yellow_1(sK2)) != iProver_top ),
% 2.08/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_2786,c_1986]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_2922,plain,
% 2.08/1.01      ( k3_yellow_0(k2_yellow_1(sK2)) = k1_xboole_0
% 2.08/1.01      | m1_subset_1(k3_yellow_0(k2_yellow_1(sK2)),sK2) != iProver_top
% 2.08/1.01      | m1_subset_1(k1_xboole_0,sK2) != iProver_top
% 2.08/1.01      | v1_yellow_0(k2_yellow_1(sK2)) != iProver_top ),
% 2.08/1.01      inference(superposition,[status(thm)],[c_2202,c_2917]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_22,negated_conjecture,
% 2.08/1.01      ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK2)) ),
% 2.08/1.01      inference(cnf_transformation,[],[f71]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_1686,plain,( X0 = X0 ),theory(equality) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_1711,plain,
% 2.08/1.01      ( k1_xboole_0 = k1_xboole_0 ),
% 2.08/1.01      inference(instantiation,[status(thm)],[c_1686]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_1687,plain,( X0 != X1 | X2 != X1 | X0 = X2 ),theory(equality) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_2138,plain,
% 2.08/1.01      ( k3_yellow_0(k2_yellow_1(sK2)) != X0
% 2.08/1.01      | k1_xboole_0 != X0
% 2.08/1.01      | k1_xboole_0 = k3_yellow_0(k2_yellow_1(sK2)) ),
% 2.08/1.01      inference(instantiation,[status(thm)],[c_1687]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_2139,plain,
% 2.08/1.01      ( k3_yellow_0(k2_yellow_1(sK2)) != k1_xboole_0
% 2.08/1.01      | k1_xboole_0 = k3_yellow_0(k2_yellow_1(sK2))
% 2.08/1.01      | k1_xboole_0 != k1_xboole_0 ),
% 2.08/1.01      inference(instantiation,[status(thm)],[c_2138]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_7,plain,
% 2.08/1.01      ( r1_lattice3(X0,X1,X2)
% 2.08/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.08/1.01      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 2.08/1.01      | ~ l1_orders_2(X0) ),
% 2.08/1.01      inference(cnf_transformation,[],[f53]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_857,plain,
% 2.08/1.01      ( r1_lattice3(X0,X1,X2)
% 2.08/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.08/1.01      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 2.08/1.01      | k2_yellow_1(X3) != X0 ),
% 2.08/1.01      inference(resolution_lifted,[status(thm)],[c_7,c_14]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_858,plain,
% 2.08/1.01      ( r1_lattice3(k2_yellow_1(X0),X1,X2)
% 2.08/1.01      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.08/1.01      | m1_subset_1(sK0(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0))) ),
% 2.08/1.01      inference(unflattening,[status(thm)],[c_857]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_1967,plain,
% 2.08/1.01      ( r1_lattice3(k2_yellow_1(X0),X1,X2) = iProver_top
% 2.08/1.01      | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 2.08/1.01      | m1_subset_1(sK0(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0))) = iProver_top ),
% 2.08/1.01      inference(predicate_to_equality,[status(thm)],[c_858]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_2017,plain,
% 2.08/1.01      ( r1_lattice3(k2_yellow_1(X0),X1,X2) = iProver_top
% 2.08/1.01      | m1_subset_1(X2,X0) != iProver_top
% 2.08/1.01      | m1_subset_1(sK0(k2_yellow_1(X0),X1,X2),X0) = iProver_top ),
% 2.08/1.01      inference(light_normalisation,[status(thm)],[c_1967,c_19]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_5,plain,
% 2.08/1.01      ( r1_lattice3(X0,X1,X2)
% 2.08/1.01      | ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
% 2.08/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.08/1.01      | ~ l1_orders_2(X0) ),
% 2.08/1.01      inference(cnf_transformation,[],[f55]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_887,plain,
% 2.08/1.01      ( r1_lattice3(X0,X1,X2)
% 2.08/1.01      | ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
% 2.08/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.08/1.01      | k2_yellow_1(X3) != X0 ),
% 2.08/1.01      inference(resolution_lifted,[status(thm)],[c_5,c_14]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_888,plain,
% 2.08/1.01      ( r1_lattice3(k2_yellow_1(X0),X1,X2)
% 2.08/1.01      | ~ r1_orders_2(k2_yellow_1(X0),X2,sK0(k2_yellow_1(X0),X1,X2))
% 2.08/1.01      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) ),
% 2.08/1.01      inference(unflattening,[status(thm)],[c_887]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_1965,plain,
% 2.08/1.01      ( r1_lattice3(k2_yellow_1(X0),X1,X2) = iProver_top
% 2.08/1.01      | r1_orders_2(k2_yellow_1(X0),X2,sK0(k2_yellow_1(X0),X1,X2)) != iProver_top
% 2.08/1.01      | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top ),
% 2.08/1.01      inference(predicate_to_equality,[status(thm)],[c_888]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_2024,plain,
% 2.08/1.01      ( r1_lattice3(k2_yellow_1(X0),X1,X2) = iProver_top
% 2.08/1.01      | r1_orders_2(k2_yellow_1(X0),X2,sK0(k2_yellow_1(X0),X1,X2)) != iProver_top
% 2.08/1.01      | m1_subset_1(X2,X0) != iProver_top ),
% 2.08/1.01      inference(light_normalisation,[status(thm)],[c_1965,c_19]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_2686,plain,
% 2.08/1.01      ( r1_lattice3(k2_yellow_1(sK2),X0,k1_xboole_0) = iProver_top
% 2.08/1.01      | m1_subset_1(sK0(k2_yellow_1(sK2),X0,k1_xboole_0),sK2) != iProver_top
% 2.08/1.01      | m1_subset_1(k1_xboole_0,sK2) != iProver_top ),
% 2.08/1.01      inference(superposition,[status(thm)],[c_2202,c_2024]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_2772,plain,
% 2.08/1.01      ( m1_subset_1(sK0(k2_yellow_1(sK2),X0,k1_xboole_0),sK2) != iProver_top
% 2.08/1.01      | r1_lattice3(k2_yellow_1(sK2),X0,k1_xboole_0) = iProver_top ),
% 2.08/1.01      inference(global_propositional_subsumption,[status(thm)],[c_2686,c_716]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_2773,plain,
% 2.08/1.01      ( r1_lattice3(k2_yellow_1(sK2),X0,k1_xboole_0) = iProver_top
% 2.08/1.01      | m1_subset_1(sK0(k2_yellow_1(sK2),X0,k1_xboole_0),sK2) != iProver_top ),
% 2.08/1.01      inference(renaming,[status(thm)],[c_2772]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_3054,plain,
% 2.08/1.01      ( r1_lattice3(k2_yellow_1(sK2),X0,k1_xboole_0) = iProver_top
% 2.08/1.01      | m1_subset_1(k1_xboole_0,sK2) != iProver_top ),
% 2.08/1.01      inference(superposition,[status(thm)],[c_2017,c_2773]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_3203,plain,
% 2.08/1.01      ( r1_lattice3(k2_yellow_1(sK2),X0,k1_xboole_0) = iProver_top ),
% 2.08/1.01      inference(global_propositional_subsumption,[status(thm)],[c_3054,c_716]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_9,plain,
% 2.08/1.01      ( ~ r1_lattice3(X0,u1_struct_0(X0),X1)
% 2.08/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.08/1.01      | v1_yellow_0(X0)
% 2.08/1.01      | ~ l1_orders_2(X0) ),
% 2.08/1.01      inference(cnf_transformation,[],[f58]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_821,plain,
% 2.08/1.01      ( ~ r1_lattice3(X0,u1_struct_0(X0),X1)
% 2.08/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.08/1.01      | v1_yellow_0(X0)
% 2.08/1.01      | k2_yellow_1(X2) != X0 ),
% 2.08/1.01      inference(resolution_lifted,[status(thm)],[c_9,c_14]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_822,plain,
% 2.08/1.01      ( ~ r1_lattice3(k2_yellow_1(X0),u1_struct_0(k2_yellow_1(X0)),X1)
% 2.08/1.01      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.08/1.01      | v1_yellow_0(k2_yellow_1(X0)) ),
% 2.08/1.01      inference(unflattening,[status(thm)],[c_821]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_1969,plain,
% 2.08/1.01      ( r1_lattice3(k2_yellow_1(X0),u1_struct_0(k2_yellow_1(X0)),X1) != iProver_top
% 2.08/1.01      | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 2.08/1.01      | v1_yellow_0(k2_yellow_1(X0)) = iProver_top ),
% 2.08/1.01      inference(predicate_to_equality,[status(thm)],[c_822]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_2003,plain,
% 2.08/1.01      ( r1_lattice3(k2_yellow_1(X0),X0,X1) != iProver_top
% 2.08/1.01      | m1_subset_1(X1,X0) != iProver_top
% 2.08/1.01      | v1_yellow_0(k2_yellow_1(X0)) = iProver_top ),
% 2.08/1.01      inference(light_normalisation,[status(thm)],[c_1969,c_19]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_3211,plain,
% 2.08/1.01      ( m1_subset_1(k1_xboole_0,sK2) != iProver_top
% 2.08/1.01      | v1_yellow_0(k2_yellow_1(sK2)) = iProver_top ),
% 2.08/1.01      inference(superposition,[status(thm)],[c_3203,c_2003]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_3418,plain,
% 2.08/1.01      ( m1_subset_1(k3_yellow_0(k2_yellow_1(sK2)),sK2) != iProver_top ),
% 2.08/1.01      inference(global_propositional_subsumption,
% 2.08/1.01                [status(thm)],
% 2.08/1.01                [c_2922,c_22,c_716,c_1711,c_2139,c_3211]) ).
% 2.08/1.01  
% 2.08/1.01  cnf(c_3423,plain,
% 2.08/1.01      ( $false ),
% 2.08/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_3418,c_1986]) ).
% 2.08/1.01  
% 2.08/1.01  
% 2.08/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.08/1.01  
% 2.08/1.01  ------                               Statistics
% 2.08/1.01  
% 2.08/1.01  ------ General
% 2.08/1.01  
% 2.08/1.01  abstr_ref_over_cycles:                  0
% 2.08/1.01  abstr_ref_under_cycles:                 0
% 2.08/1.01  gc_basic_clause_elim:                   0
% 2.08/1.01  forced_gc_time:                         0
% 2.08/1.01  parsing_time:                           0.009
% 2.08/1.01  unif_index_cands_time:                  0.
% 2.08/1.01  unif_index_add_time:                    0.
% 2.08/1.01  orderings_time:                         0.
% 2.08/1.01  out_proof_time:                         0.009
% 2.08/1.01  total_time:                             0.139
% 2.08/1.01  num_of_symbols:                         49
% 2.08/1.01  num_of_terms:                           3071
% 2.08/1.01  
% 2.08/1.01  ------ Preprocessing
% 2.08/1.01  
% 2.08/1.01  num_of_splits:                          0
% 2.08/1.01  num_of_split_atoms:                     0
% 2.08/1.01  num_of_reused_defs:                     0
% 2.08/1.01  num_eq_ax_congr_red:                    17
% 2.08/1.01  num_of_sem_filtered_clauses:            1
% 2.08/1.01  num_of_subtypes:                        0
% 2.08/1.01  monotx_restored_types:                  0
% 2.08/1.01  sat_num_of_epr_types:                   0
% 2.08/1.01  sat_num_of_non_cyclic_types:            0
% 2.08/1.01  sat_guarded_non_collapsed_types:        0
% 2.08/1.01  num_pure_diseq_elim:                    0
% 2.08/1.01  simp_replaced_by:                       0
% 2.08/1.01  res_preprocessed:                       100
% 2.08/1.01  prep_upred:                             0
% 2.08/1.01  prep_unflattend:                        62
% 2.08/1.01  smt_new_axioms:                         0
% 2.08/1.01  pred_elim_cands:                        5
% 2.08/1.01  pred_elim:                              7
% 2.08/1.01  pred_elim_cl:                           9
% 2.08/1.01  pred_elim_cycles:                       16
% 2.08/1.01  merged_defs:                            0
% 2.08/1.01  merged_defs_ncl:                        0
% 2.08/1.01  bin_hyper_res:                          0
% 2.08/1.01  prep_cycles:                            4
% 2.08/1.01  pred_elim_time:                         0.039
% 2.08/1.01  splitting_time:                         0.
% 2.08/1.01  sem_filter_time:                        0.
% 2.08/1.01  monotx_time:                            0.001
% 2.08/1.01  subtype_inf_time:                       0.
% 2.08/1.01  
% 2.08/1.01  ------ Problem properties
% 2.08/1.01  
% 2.08/1.01  clauses:                                16
% 2.08/1.01  conjectures:                            2
% 2.08/1.01  epr:                                    2
% 2.08/1.01  horn:                                   14
% 2.08/1.01  ground:                                 2
% 2.08/1.01  unary:                                  5
% 2.08/1.01  binary:                                 3
% 2.08/1.01  lits:                                   43
% 2.08/1.01  lits_eq:                                6
% 2.08/1.01  fd_pure:                                0
% 2.08/1.01  fd_pseudo:                              0
% 2.08/1.01  fd_cond:                                0
% 2.08/1.01  fd_pseudo_cond:                         1
% 2.08/1.01  ac_symbols:                             0
% 2.08/1.01  
% 2.08/1.01  ------ Propositional Solver
% 2.08/1.01  
% 2.08/1.01  prop_solver_calls:                      26
% 2.08/1.01  prop_fast_solver_calls:                 940
% 2.08/1.01  smt_solver_calls:                       0
% 2.08/1.01  smt_fast_solver_calls:                  0
% 2.08/1.01  prop_num_of_clauses:                    1007
% 2.08/1.01  prop_preprocess_simplified:             3810
% 2.08/1.01  prop_fo_subsumed:                       14
% 2.08/1.01  prop_solver_time:                       0.
% 2.08/1.01  smt_solver_time:                        0.
% 2.08/1.01  smt_fast_solver_time:                   0.
% 2.08/1.01  prop_fast_solver_time:                  0.
% 2.08/1.01  prop_unsat_core_time:                   0.
% 2.08/1.01  
% 2.08/1.01  ------ QBF
% 2.08/1.01  
% 2.08/1.01  qbf_q_res:                              0
% 2.08/1.01  qbf_num_tautologies:                    0
% 2.08/1.01  qbf_prep_cycles:                        0
% 2.08/1.01  
% 2.08/1.01  ------ BMC1
% 2.08/1.01  
% 2.08/1.01  bmc1_current_bound:                     -1
% 2.08/1.01  bmc1_last_solved_bound:                 -1
% 2.08/1.01  bmc1_unsat_core_size:                   -1
% 2.08/1.01  bmc1_unsat_core_parents_size:           -1
% 2.08/1.01  bmc1_merge_next_fun:                    0
% 2.08/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.08/1.01  
% 2.08/1.01  ------ Instantiation
% 2.08/1.01  
% 2.08/1.01  inst_num_of_clauses:                    253
% 2.08/1.01  inst_num_in_passive:                    11
% 2.08/1.01  inst_num_in_active:                     119
% 2.08/1.01  inst_num_in_unprocessed:                123
% 2.08/1.01  inst_num_of_loops:                      130
% 2.08/1.01  inst_num_of_learning_restarts:          0
% 2.08/1.01  inst_num_moves_active_passive:          9
% 2.08/1.01  inst_lit_activity:                      0
% 2.08/1.01  inst_lit_activity_moves:                0
% 2.08/1.01  inst_num_tautologies:                   0
% 2.08/1.01  inst_num_prop_implied:                  0
% 2.08/1.01  inst_num_existing_simplified:           0
% 2.08/1.01  inst_num_eq_res_simplified:             0
% 2.08/1.01  inst_num_child_elim:                    0
% 2.08/1.01  inst_num_of_dismatching_blockings:      64
% 2.08/1.01  inst_num_of_non_proper_insts:           212
% 2.08/1.01  inst_num_of_duplicates:                 0
% 2.08/1.01  inst_inst_num_from_inst_to_res:         0
% 2.08/1.01  inst_dismatching_checking_time:         0.
% 2.08/1.01  
% 2.08/1.01  ------ Resolution
% 2.08/1.01  
% 2.08/1.01  res_num_of_clauses:                     0
% 2.08/1.01  res_num_in_passive:                     0
% 2.08/1.01  res_num_in_active:                      0
% 2.08/1.01  res_num_of_loops:                       104
% 2.08/1.01  res_forward_subset_subsumed:            22
% 2.08/1.01  res_backward_subset_subsumed:           0
% 2.08/1.01  res_forward_subsumed:                   0
% 2.08/1.01  res_backward_subsumed:                  0
% 2.08/1.01  res_forward_subsumption_resolution:     0
% 2.08/1.01  res_backward_subsumption_resolution:    0
% 2.08/1.01  res_clause_to_clause_subsumption:       102
% 2.08/1.01  res_orphan_elimination:                 0
% 2.08/1.01  res_tautology_del:                      16
% 2.08/1.01  res_num_eq_res_simplified:              0
% 2.08/1.01  res_num_sel_changes:                    0
% 2.08/1.01  res_moves_from_active_to_pass:          0
% 2.08/1.01  
% 2.08/1.01  ------ Superposition
% 2.08/1.01  
% 2.08/1.01  sup_time_total:                         0.
% 2.08/1.01  sup_time_generating:                    0.
% 2.08/1.01  sup_time_sim_full:                      0.
% 2.08/1.01  sup_time_sim_immed:                     0.
% 2.08/1.01  
% 2.08/1.01  sup_num_of_clauses:                     28
% 2.08/1.01  sup_num_in_active:                      24
% 2.08/1.01  sup_num_in_passive:                     4
% 2.08/1.01  sup_num_of_loops:                       25
% 2.08/1.01  sup_fw_superposition:                   11
% 2.08/1.01  sup_bw_superposition:                   5
% 2.08/1.01  sup_immediate_simplified:               1
% 2.08/1.01  sup_given_eliminated:                   0
% 2.08/1.01  comparisons_done:                       0
% 2.08/1.01  comparisons_avoided:                    0
% 2.08/1.01  
% 2.08/1.01  ------ Simplifications
% 2.08/1.01  
% 2.08/1.01  
% 2.08/1.01  sim_fw_subset_subsumed:                 0
% 2.08/1.01  sim_bw_subset_subsumed:                 1
% 2.08/1.01  sim_fw_subsumed:                        1
% 2.08/1.01  sim_bw_subsumed:                        0
% 2.08/1.01  sim_fw_subsumption_res:                 3
% 2.08/1.01  sim_bw_subsumption_res:                 0
% 2.08/1.01  sim_tautology_del:                      1
% 2.08/1.01  sim_eq_tautology_del:                   2
% 2.08/1.01  sim_eq_res_simp:                        0
% 2.08/1.01  sim_fw_demodulated:                     2
% 2.08/1.01  sim_bw_demodulated:                     0
% 2.08/1.01  sim_light_normalised:                   10
% 2.08/1.01  sim_joinable_taut:                      0
% 2.08/1.01  sim_joinable_simp:                      0
% 2.08/1.01  sim_ac_normalised:                      0
% 2.08/1.01  sim_smt_subsumption:                    0
% 2.08/1.01  
%------------------------------------------------------------------------------
