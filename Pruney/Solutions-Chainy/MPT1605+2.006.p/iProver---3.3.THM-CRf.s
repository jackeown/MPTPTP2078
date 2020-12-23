%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:20:13 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 278 expanded)
%              Number of clauses        :   96 ( 127 expanded)
%              Number of leaves         :   20 (  54 expanded)
%              Depth                    :   29
%              Number of atoms          :  566 ( 904 expanded)
%              Number of equality atoms :  197 ( 284 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   15 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
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
    inference(rectify,[],[f8])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X1,X3)
          & r2_lattice3(X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X1,sK0(X0,X1,X2))
        & r2_lattice3(X0,X2,sK0(X0,X1,X2))
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f36])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X2) = X1
      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
      | ~ r2_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f11,axiom,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v4_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f19,plain,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f60,plain,(
    ! [X0] : v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f58,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f12,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f45,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v2_struct_0(X0) )
     => v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f24,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f44,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

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

fof(f39,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0))
        & r2_hidden(k1_xboole_0,X0)
        & ~ v1_xboole_0(X0) )
   => ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK1))
      & r2_hidden(k1_xboole_0,sK1)
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK1))
    & r2_hidden(k1_xboole_0,sK1)
    & ~ v1_xboole_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f39])).

fof(f65,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

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
    inference(nnf_transformation,[],[f27])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f59,plain,(
    ! [X0] : v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
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

fof(f38,plain,(
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

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f43,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f66,plain,(
    r2_hidden(k1_xboole_0,sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X2) = X1
      | ~ r1_orders_2(X0,X1,sK0(X0,X1,X2))
      | ~ r2_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f48,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( r1_lattice3(X0,k1_xboole_0,X1)
            & r2_lattice3(X0,k1_xboole_0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r2_lattice3(X0,k1_xboole_0,X1) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_lattice3(X0,k1_xboole_0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_lattice3(X0,k1_xboole_0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f67,plain,(
    k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK1)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_13,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X2,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_18,plain,
    ( v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_626,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X2,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2
    | k2_yellow_1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_18])).

cnf(c_627,plain,
    ( ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | m1_subset_1(sK0(k2_yellow_1(X0),X2,X1),u1_struct_0(k2_yellow_1(X0)))
    | ~ l1_orders_2(k2_yellow_1(X0))
    | k1_yellow_0(k2_yellow_1(X0),X1) = X2 ),
    inference(unflattening,[status(thm)],[c_626])).

cnf(c_17,plain,
    ( l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_631,plain,
    ( m1_subset_1(sK0(k2_yellow_1(X0),X2,X1),u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
    | k1_yellow_0(k2_yellow_1(X0),X1) = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_627,c_17])).

cnf(c_632,plain,
    ( ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | m1_subset_1(sK0(k2_yellow_1(X0),X2,X1),u1_struct_0(k2_yellow_1(X0)))
    | k1_yellow_0(k2_yellow_1(X0),X1) = X2 ),
    inference(renaming,[status(thm)],[c_631])).

cnf(c_1823,plain,
    ( k1_yellow_0(k2_yellow_1(X0),X1) = X2
    | r2_lattice3(k2_yellow_1(X0),X1,X2) != iProver_top
    | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | m1_subset_1(sK0(k2_yellow_1(X0),X2,X1),u1_struct_0(k2_yellow_1(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_632])).

cnf(c_21,plain,
    ( u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1880,plain,
    ( k1_yellow_0(k2_yellow_1(X0),X1) = X2
    | r2_lattice3(k2_yellow_1(X0),X1,X2) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(sK0(k2_yellow_1(X0),X2,X1),X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1823,c_21])).

cnf(c_4,plain,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_3,plain,
    ( ~ v2_struct_0(X0)
    | v1_xboole_0(k2_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_296,plain,
    ( ~ l1_orders_2(X0)
    | ~ v2_struct_0(X0)
    | v1_xboole_0(k2_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_4,c_3])).

cnf(c_26,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_328,plain,
    ( ~ l1_orders_2(X0)
    | ~ v2_struct_0(X0)
    | k2_struct_0(X0) != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_296,c_26])).

cnf(c_6,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_19,plain,
    ( v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_410,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | k2_yellow_1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_19])).

cnf(c_411,plain,
    ( r1_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ l1_orders_2(k2_yellow_1(X0))
    | v2_struct_0(k2_yellow_1(X0)) ),
    inference(unflattening,[status(thm)],[c_410])).

cnf(c_415,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
    | r1_orders_2(k2_yellow_1(X0),X1,X2)
    | v2_struct_0(k2_yellow_1(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_411,c_17])).

cnf(c_416,plain,
    ( r1_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | v2_struct_0(k2_yellow_1(X0)) ),
    inference(renaming,[status(thm)],[c_415])).

cnf(c_503,plain,
    ( r1_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ l1_orders_2(X3)
    | k2_yellow_1(X0) != X3
    | k2_struct_0(X3) != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_328,c_416])).

cnf(c_504,plain,
    ( r1_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ l1_orders_2(k2_yellow_1(X0))
    | k2_struct_0(k2_yellow_1(X0)) != sK1 ),
    inference(unflattening,[status(thm)],[c_503])).

cnf(c_508,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
    | r1_orders_2(k2_yellow_1(X0),X1,X2)
    | k2_struct_0(k2_yellow_1(X0)) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_504,c_17])).

cnf(c_509,plain,
    ( r1_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | k2_struct_0(k2_yellow_1(X0)) != sK1 ),
    inference(renaming,[status(thm)],[c_508])).

cnf(c_0,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_22,plain,
    ( r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ r1_tarski(X1,X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_358,plain,
    ( r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ r1_tarski(X1,X2)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_26])).

cnf(c_359,plain,
    ( r3_orders_2(k2_yellow_1(sK1),X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))
    | ~ r1_tarski(X0,X1) ),
    inference(unflattening,[status(thm)],[c_358])).

cnf(c_391,plain,
    ( r3_orders_2(k2_yellow_1(sK1),X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))
    | X1 != X2
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_359])).

cnf(c_392,plain,
    ( r3_orders_2(k2_yellow_1(sK1),k1_xboole_0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK1))) ),
    inference(unflattening,[status(thm)],[c_391])).

cnf(c_543,plain,
    ( r1_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK1)))
    | X3 != X2
    | k2_yellow_1(X0) != k2_yellow_1(sK1)
    | k2_struct_0(k2_yellow_1(X0)) != sK1
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_509,c_392])).

cnf(c_544,plain,
    ( r1_orders_2(k2_yellow_1(X0),k1_xboole_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK1)))
    | k2_yellow_1(X0) != k2_yellow_1(sK1)
    | k2_struct_0(k2_yellow_1(X0)) != sK1 ),
    inference(unflattening,[status(thm)],[c_543])).

cnf(c_1826,plain,
    ( k2_yellow_1(X0) != k2_yellow_1(sK1)
    | k2_struct_0(k2_yellow_1(X0)) != sK1
    | r1_orders_2(k2_yellow_1(X0),k1_xboole_0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_544])).

cnf(c_2,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_310,plain,
    ( ~ l1_orders_2(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_4,c_2])).

cnf(c_810,plain,
    ( k2_yellow_1(X0) != X1
    | u1_struct_0(X1) = k2_struct_0(X1) ),
    inference(resolution_lifted,[status(thm)],[c_310,c_17])).

cnf(c_811,plain,
    ( u1_struct_0(k2_yellow_1(X0)) = k2_struct_0(k2_yellow_1(X0)) ),
    inference(unflattening,[status(thm)],[c_810])).

cnf(c_1836,plain,
    ( k2_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_811,c_21])).

cnf(c_1918,plain,
    ( k2_yellow_1(X0) != k2_yellow_1(sK1)
    | sK1 != X0
    | r1_orders_2(k2_yellow_1(X0),k1_xboole_0,X1) = iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,X0) != iProver_top
    | m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1826,c_21,c_1836])).

cnf(c_1919,plain,
    ( k2_yellow_1(X0) != k2_yellow_1(sK1)
    | sK1 != X0
    | r1_orders_2(k2_yellow_1(X0),k1_xboole_0,X1) = iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(X1,sK1) != iProver_top
    | m1_subset_1(k1_xboole_0,X0) != iProver_top
    | m1_subset_1(k1_xboole_0,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1918,c_21])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_25,negated_conjecture,
    ( r2_hidden(k1_xboole_0,sK1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_287,plain,
    ( m1_subset_1(X0,X1)
    | sK1 != X1
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_25])).

cnf(c_288,plain,
    ( m1_subset_1(k1_xboole_0,sK1) ),
    inference(unflattening,[status(thm)],[c_287])).

cnf(c_1827,plain,
    ( m1_subset_1(k1_xboole_0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_288])).

cnf(c_1927,plain,
    ( k2_yellow_1(X0) != k2_yellow_1(sK1)
    | sK1 != X0
    | r1_orders_2(k2_yellow_1(X0),k1_xboole_0,X1) = iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(X1,sK1) != iProver_top
    | m1_subset_1(k1_xboole_0,X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1919,c_1827])).

cnf(c_1998,plain,
    ( sK1 != sK1
    | r1_orders_2(k2_yellow_1(sK1),k1_xboole_0,X0) = iProver_top
    | m1_subset_1(X0,sK1) != iProver_top
    | m1_subset_1(k1_xboole_0,sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1927])).

cnf(c_2002,plain,
    ( r1_orders_2(k2_yellow_1(sK1),k1_xboole_0,X0) = iProver_top
    | m1_subset_1(X0,sK1) != iProver_top
    | m1_subset_1(k1_xboole_0,sK1) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_1998])).

cnf(c_289,plain,
    ( m1_subset_1(k1_xboole_0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_288])).

cnf(c_2006,plain,
    ( m1_subset_1(X0,sK1) != iProver_top
    | r1_orders_2(k2_yellow_1(sK1),k1_xboole_0,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2002,c_289])).

cnf(c_2007,plain,
    ( r1_orders_2(k2_yellow_1(sK1),k1_xboole_0,X0) = iProver_top
    | m1_subset_1(X0,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_2006])).

cnf(c_11,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK0(X0,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_674,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK0(X0,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2
    | k2_yellow_1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_18])).

cnf(c_675,plain,
    ( ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
    | ~ r1_orders_2(k2_yellow_1(X0),X2,sK0(k2_yellow_1(X0),X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ l1_orders_2(k2_yellow_1(X0))
    | k1_yellow_0(k2_yellow_1(X0),X1) = X2 ),
    inference(unflattening,[status(thm)],[c_674])).

cnf(c_679,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ r1_orders_2(k2_yellow_1(X0),X2,sK0(k2_yellow_1(X0),X2,X1))
    | ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
    | k1_yellow_0(k2_yellow_1(X0),X1) = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_675,c_17])).

cnf(c_680,plain,
    ( ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
    | ~ r1_orders_2(k2_yellow_1(X0),X2,sK0(k2_yellow_1(X0),X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | k1_yellow_0(k2_yellow_1(X0),X1) = X2 ),
    inference(renaming,[status(thm)],[c_679])).

cnf(c_1821,plain,
    ( k1_yellow_0(k2_yellow_1(X0),X1) = X2
    | r2_lattice3(k2_yellow_1(X0),X1,X2) != iProver_top
    | r1_orders_2(k2_yellow_1(X0),X2,sK0(k2_yellow_1(X0),X2,X1)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_680])).

cnf(c_1898,plain,
    ( k1_yellow_0(k2_yellow_1(X0),X1) = X2
    | r2_lattice3(k2_yellow_1(X0),X1,X2) != iProver_top
    | r1_orders_2(k2_yellow_1(X0),X2,sK0(k2_yellow_1(X0),X2,X1)) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1821,c_21])).

cnf(c_2488,plain,
    ( k1_yellow_0(k2_yellow_1(sK1),X0) = k1_xboole_0
    | r2_lattice3(k2_yellow_1(sK1),X0,k1_xboole_0) != iProver_top
    | m1_subset_1(sK0(k2_yellow_1(sK1),k1_xboole_0,X0),sK1) != iProver_top
    | m1_subset_1(k1_xboole_0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2007,c_1898])).

cnf(c_2563,plain,
    ( m1_subset_1(sK0(k2_yellow_1(sK1),k1_xboole_0,X0),sK1) != iProver_top
    | r2_lattice3(k2_yellow_1(sK1),X0,k1_xboole_0) != iProver_top
    | k1_yellow_0(k2_yellow_1(sK1),X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2488,c_289])).

cnf(c_2564,plain,
    ( k1_yellow_0(k2_yellow_1(sK1),X0) = k1_xboole_0
    | r2_lattice3(k2_yellow_1(sK1),X0,k1_xboole_0) != iProver_top
    | m1_subset_1(sK0(k2_yellow_1(sK1),k1_xboole_0,X0),sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_2563])).

cnf(c_2572,plain,
    ( k1_yellow_0(k2_yellow_1(sK1),X0) = k1_xboole_0
    | r2_lattice3(k2_yellow_1(sK1),X0,k1_xboole_0) != iProver_top
    | m1_subset_1(k1_xboole_0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1880,c_2564])).

cnf(c_2581,plain,
    ( k1_yellow_0(k2_yellow_1(sK1),k1_xboole_0) = k1_xboole_0
    | r2_lattice3(k2_yellow_1(sK1),k1_xboole_0,k1_xboole_0) != iProver_top
    | m1_subset_1(k1_xboole_0,sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2572])).

cnf(c_1584,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2475,plain,
    ( k1_yellow_0(k2_yellow_1(sK1),k1_xboole_0) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK1),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1584])).

cnf(c_2476,plain,
    ( k1_yellow_0(k2_yellow_1(sK1),k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK1),k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2475])).

cnf(c_1984,plain,
    ( k3_yellow_0(k2_yellow_1(sK1)) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k3_yellow_0(k2_yellow_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_1584])).

cnf(c_2306,plain,
    ( k3_yellow_0(k2_yellow_1(sK1)) != k1_yellow_0(k2_yellow_1(sK1),k1_xboole_0)
    | k1_xboole_0 != k1_yellow_0(k2_yellow_1(sK1),k1_xboole_0)
    | k1_xboole_0 = k3_yellow_0(k2_yellow_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_1984])).

cnf(c_7,plain,
    ( ~ l1_orders_2(X0)
    | k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_828,plain,
    ( k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0)
    | k2_yellow_1(X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_17])).

cnf(c_829,plain,
    ( k1_yellow_0(k2_yellow_1(X0),k1_xboole_0) = k3_yellow_0(k2_yellow_1(X0)) ),
    inference(unflattening,[status(thm)],[c_828])).

cnf(c_2124,plain,
    ( k1_yellow_0(k2_yellow_1(sK1),k1_xboole_0) = k3_yellow_0(k2_yellow_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_829])).

cnf(c_2015,plain,
    ( X0 != X1
    | k3_yellow_0(k2_yellow_1(sK1)) != X1
    | k3_yellow_0(k2_yellow_1(sK1)) = X0 ),
    inference(instantiation,[status(thm)],[c_1584])).

cnf(c_2041,plain,
    ( X0 != k3_yellow_0(k2_yellow_1(sK1))
    | k3_yellow_0(k2_yellow_1(sK1)) = X0
    | k3_yellow_0(k2_yellow_1(sK1)) != k3_yellow_0(k2_yellow_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_2015])).

cnf(c_2123,plain,
    ( k1_yellow_0(k2_yellow_1(sK1),k1_xboole_0) != k3_yellow_0(k2_yellow_1(sK1))
    | k3_yellow_0(k2_yellow_1(sK1)) = k1_yellow_0(k2_yellow_1(sK1),k1_xboole_0)
    | k3_yellow_0(k2_yellow_1(sK1)) != k3_yellow_0(k2_yellow_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_2041])).

cnf(c_16,plain,
    ( r2_lattice3(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_816,plain,
    ( r2_lattice3(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | k2_yellow_1(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_17])).

cnf(c_817,plain,
    ( r2_lattice3(k2_yellow_1(X0),k1_xboole_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) ),
    inference(unflattening,[status(thm)],[c_816])).

cnf(c_2078,plain,
    ( r2_lattice3(k2_yellow_1(sK1),k1_xboole_0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1))) ),
    inference(instantiation,[status(thm)],[c_817])).

cnf(c_2079,plain,
    ( r2_lattice3(k2_yellow_1(sK1),k1_xboole_0,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2078])).

cnf(c_2081,plain,
    ( r2_lattice3(k2_yellow_1(sK1),k1_xboole_0,k1_xboole_0) = iProver_top
    | m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK1))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2079])).

cnf(c_1583,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2035,plain,
    ( k2_yellow_1(sK1) = k2_yellow_1(sK1) ),
    inference(instantiation,[status(thm)],[c_1583])).

cnf(c_1589,plain,
    ( X0 != X1
    | k3_yellow_0(X0) = k3_yellow_0(X1) ),
    theory(equality)).

cnf(c_2017,plain,
    ( k2_yellow_1(sK1) != X0
    | k3_yellow_0(k2_yellow_1(sK1)) = k3_yellow_0(X0) ),
    inference(instantiation,[status(thm)],[c_1589])).

cnf(c_2034,plain,
    ( k2_yellow_1(sK1) != k2_yellow_1(sK1)
    | k3_yellow_0(k2_yellow_1(sK1)) = k3_yellow_0(k2_yellow_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_2017])).

cnf(c_2021,plain,
    ( u1_struct_0(k2_yellow_1(sK1)) = sK1 ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_1585,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1986,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(k1_xboole_0,sK1)
    | X1 != sK1
    | X0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1585])).

cnf(c_2020,plain,
    ( m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(k1_xboole_0,sK1)
    | X0 != k1_xboole_0
    | u1_struct_0(k2_yellow_1(sK1)) != sK1 ),
    inference(instantiation,[status(thm)],[c_1986])).

cnf(c_2022,plain,
    ( X0 != k1_xboole_0
    | u1_struct_0(k2_yellow_1(sK1)) != sK1
    | m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1))) = iProver_top
    | m1_subset_1(k1_xboole_0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2020])).

cnf(c_2024,plain,
    ( u1_struct_0(k2_yellow_1(sK1)) != sK1
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK1))) = iProver_top
    | m1_subset_1(k1_xboole_0,sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2022])).

cnf(c_1608,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1583])).

cnf(c_24,negated_conjecture,
    ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK1)) ),
    inference(cnf_transformation,[],[f67])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2581,c_2476,c_2306,c_2124,c_2123,c_2081,c_2035,c_2034,c_2021,c_2024,c_1608,c_289,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n018.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 15:30:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.21/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.02  
% 2.21/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.21/1.02  
% 2.21/1.02  ------  iProver source info
% 2.21/1.02  
% 2.21/1.02  git: date: 2020-06-30 10:37:57 +0100
% 2.21/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.21/1.02  git: non_committed_changes: false
% 2.21/1.02  git: last_make_outside_of_git: false
% 2.21/1.02  
% 2.21/1.02  ------ 
% 2.21/1.02  
% 2.21/1.02  ------ Input Options
% 2.21/1.02  
% 2.21/1.02  --out_options                           all
% 2.21/1.02  --tptp_safe_out                         true
% 2.21/1.02  --problem_path                          ""
% 2.21/1.02  --include_path                          ""
% 2.21/1.02  --clausifier                            res/vclausify_rel
% 2.21/1.02  --clausifier_options                    --mode clausify
% 2.21/1.02  --stdin                                 false
% 2.21/1.02  --stats_out                             all
% 2.21/1.02  
% 2.21/1.02  ------ General Options
% 2.21/1.02  
% 2.21/1.02  --fof                                   false
% 2.21/1.02  --time_out_real                         305.
% 2.21/1.02  --time_out_virtual                      -1.
% 2.21/1.02  --symbol_type_check                     false
% 2.21/1.02  --clausify_out                          false
% 2.21/1.02  --sig_cnt_out                           false
% 2.21/1.02  --trig_cnt_out                          false
% 2.21/1.02  --trig_cnt_out_tolerance                1.
% 2.21/1.02  --trig_cnt_out_sk_spl                   false
% 2.21/1.02  --abstr_cl_out                          false
% 2.21/1.02  
% 2.21/1.02  ------ Global Options
% 2.21/1.02  
% 2.21/1.02  --schedule                              default
% 2.21/1.02  --add_important_lit                     false
% 2.21/1.02  --prop_solver_per_cl                    1000
% 2.21/1.02  --min_unsat_core                        false
% 2.21/1.02  --soft_assumptions                      false
% 2.21/1.02  --soft_lemma_size                       3
% 2.21/1.02  --prop_impl_unit_size                   0
% 2.21/1.02  --prop_impl_unit                        []
% 2.21/1.02  --share_sel_clauses                     true
% 2.21/1.02  --reset_solvers                         false
% 2.21/1.02  --bc_imp_inh                            [conj_cone]
% 2.21/1.02  --conj_cone_tolerance                   3.
% 2.21/1.02  --extra_neg_conj                        none
% 2.21/1.02  --large_theory_mode                     true
% 2.21/1.02  --prolific_symb_bound                   200
% 2.21/1.02  --lt_threshold                          2000
% 2.21/1.02  --clause_weak_htbl                      true
% 2.21/1.02  --gc_record_bc_elim                     false
% 2.21/1.02  
% 2.21/1.02  ------ Preprocessing Options
% 2.21/1.02  
% 2.21/1.02  --preprocessing_flag                    true
% 2.21/1.02  --time_out_prep_mult                    0.1
% 2.21/1.02  --splitting_mode                        input
% 2.21/1.02  --splitting_grd                         true
% 2.21/1.02  --splitting_cvd                         false
% 2.21/1.02  --splitting_cvd_svl                     false
% 2.21/1.02  --splitting_nvd                         32
% 2.21/1.02  --sub_typing                            true
% 2.21/1.02  --prep_gs_sim                           true
% 2.21/1.02  --prep_unflatten                        true
% 2.21/1.02  --prep_res_sim                          true
% 2.21/1.02  --prep_upred                            true
% 2.21/1.02  --prep_sem_filter                       exhaustive
% 2.21/1.02  --prep_sem_filter_out                   false
% 2.21/1.02  --pred_elim                             true
% 2.21/1.02  --res_sim_input                         true
% 2.21/1.02  --eq_ax_congr_red                       true
% 2.21/1.02  --pure_diseq_elim                       true
% 2.21/1.02  --brand_transform                       false
% 2.21/1.02  --non_eq_to_eq                          false
% 2.21/1.02  --prep_def_merge                        true
% 2.21/1.02  --prep_def_merge_prop_impl              false
% 2.21/1.02  --prep_def_merge_mbd                    true
% 2.21/1.02  --prep_def_merge_tr_red                 false
% 2.21/1.02  --prep_def_merge_tr_cl                  false
% 2.21/1.02  --smt_preprocessing                     true
% 2.21/1.02  --smt_ac_axioms                         fast
% 2.21/1.02  --preprocessed_out                      false
% 2.21/1.02  --preprocessed_stats                    false
% 2.21/1.02  
% 2.21/1.02  ------ Abstraction refinement Options
% 2.21/1.02  
% 2.21/1.02  --abstr_ref                             []
% 2.21/1.02  --abstr_ref_prep                        false
% 2.21/1.02  --abstr_ref_until_sat                   false
% 2.21/1.02  --abstr_ref_sig_restrict                funpre
% 2.21/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.21/1.02  --abstr_ref_under                       []
% 2.21/1.02  
% 2.21/1.02  ------ SAT Options
% 2.21/1.02  
% 2.21/1.02  --sat_mode                              false
% 2.21/1.02  --sat_fm_restart_options                ""
% 2.21/1.02  --sat_gr_def                            false
% 2.21/1.02  --sat_epr_types                         true
% 2.21/1.02  --sat_non_cyclic_types                  false
% 2.21/1.02  --sat_finite_models                     false
% 2.21/1.02  --sat_fm_lemmas                         false
% 2.21/1.02  --sat_fm_prep                           false
% 2.21/1.02  --sat_fm_uc_incr                        true
% 2.21/1.02  --sat_out_model                         small
% 2.21/1.02  --sat_out_clauses                       false
% 2.21/1.02  
% 2.21/1.02  ------ QBF Options
% 2.21/1.02  
% 2.21/1.02  --qbf_mode                              false
% 2.21/1.02  --qbf_elim_univ                         false
% 2.21/1.02  --qbf_dom_inst                          none
% 2.21/1.02  --qbf_dom_pre_inst                      false
% 2.21/1.02  --qbf_sk_in                             false
% 2.21/1.02  --qbf_pred_elim                         true
% 2.21/1.02  --qbf_split                             512
% 2.21/1.02  
% 2.21/1.02  ------ BMC1 Options
% 2.21/1.02  
% 2.21/1.02  --bmc1_incremental                      false
% 2.21/1.02  --bmc1_axioms                           reachable_all
% 2.21/1.02  --bmc1_min_bound                        0
% 2.21/1.02  --bmc1_max_bound                        -1
% 2.21/1.02  --bmc1_max_bound_default                -1
% 2.21/1.02  --bmc1_symbol_reachability              true
% 2.21/1.02  --bmc1_property_lemmas                  false
% 2.21/1.02  --bmc1_k_induction                      false
% 2.21/1.02  --bmc1_non_equiv_states                 false
% 2.21/1.02  --bmc1_deadlock                         false
% 2.21/1.02  --bmc1_ucm                              false
% 2.21/1.02  --bmc1_add_unsat_core                   none
% 2.21/1.02  --bmc1_unsat_core_children              false
% 2.21/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.21/1.02  --bmc1_out_stat                         full
% 2.21/1.02  --bmc1_ground_init                      false
% 2.21/1.02  --bmc1_pre_inst_next_state              false
% 2.21/1.02  --bmc1_pre_inst_state                   false
% 2.21/1.02  --bmc1_pre_inst_reach_state             false
% 2.21/1.02  --bmc1_out_unsat_core                   false
% 2.21/1.02  --bmc1_aig_witness_out                  false
% 2.21/1.02  --bmc1_verbose                          false
% 2.21/1.02  --bmc1_dump_clauses_tptp                false
% 2.21/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.21/1.02  --bmc1_dump_file                        -
% 2.21/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.21/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.21/1.02  --bmc1_ucm_extend_mode                  1
% 2.21/1.02  --bmc1_ucm_init_mode                    2
% 2.21/1.02  --bmc1_ucm_cone_mode                    none
% 2.21/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.21/1.02  --bmc1_ucm_relax_model                  4
% 2.21/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.21/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.21/1.02  --bmc1_ucm_layered_model                none
% 2.21/1.02  --bmc1_ucm_max_lemma_size               10
% 2.21/1.02  
% 2.21/1.02  ------ AIG Options
% 2.21/1.02  
% 2.21/1.02  --aig_mode                              false
% 2.21/1.02  
% 2.21/1.02  ------ Instantiation Options
% 2.21/1.02  
% 2.21/1.02  --instantiation_flag                    true
% 2.21/1.02  --inst_sos_flag                         false
% 2.21/1.02  --inst_sos_phase                        true
% 2.21/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.21/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.21/1.02  --inst_lit_sel_side                     num_symb
% 2.21/1.02  --inst_solver_per_active                1400
% 2.21/1.02  --inst_solver_calls_frac                1.
% 2.21/1.02  --inst_passive_queue_type               priority_queues
% 2.21/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.21/1.02  --inst_passive_queues_freq              [25;2]
% 2.21/1.02  --inst_dismatching                      true
% 2.21/1.02  --inst_eager_unprocessed_to_passive     true
% 2.21/1.02  --inst_prop_sim_given                   true
% 2.21/1.02  --inst_prop_sim_new                     false
% 2.21/1.02  --inst_subs_new                         false
% 2.21/1.02  --inst_eq_res_simp                      false
% 2.21/1.02  --inst_subs_given                       false
% 2.21/1.02  --inst_orphan_elimination               true
% 2.21/1.02  --inst_learning_loop_flag               true
% 2.21/1.02  --inst_learning_start                   3000
% 2.21/1.02  --inst_learning_factor                  2
% 2.21/1.02  --inst_start_prop_sim_after_learn       3
% 2.21/1.02  --inst_sel_renew                        solver
% 2.21/1.02  --inst_lit_activity_flag                true
% 2.21/1.02  --inst_restr_to_given                   false
% 2.21/1.02  --inst_activity_threshold               500
% 2.21/1.02  --inst_out_proof                        true
% 2.21/1.02  
% 2.21/1.02  ------ Resolution Options
% 2.21/1.02  
% 2.21/1.02  --resolution_flag                       true
% 2.21/1.02  --res_lit_sel                           adaptive
% 2.21/1.02  --res_lit_sel_side                      none
% 2.21/1.02  --res_ordering                          kbo
% 2.21/1.02  --res_to_prop_solver                    active
% 2.21/1.02  --res_prop_simpl_new                    false
% 2.21/1.02  --res_prop_simpl_given                  true
% 2.21/1.02  --res_passive_queue_type                priority_queues
% 2.21/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.21/1.02  --res_passive_queues_freq               [15;5]
% 2.21/1.02  --res_forward_subs                      full
% 2.21/1.02  --res_backward_subs                     full
% 2.21/1.02  --res_forward_subs_resolution           true
% 2.21/1.02  --res_backward_subs_resolution          true
% 2.21/1.02  --res_orphan_elimination                true
% 2.21/1.02  --res_time_limit                        2.
% 2.21/1.02  --res_out_proof                         true
% 2.21/1.02  
% 2.21/1.02  ------ Superposition Options
% 2.21/1.02  
% 2.21/1.02  --superposition_flag                    true
% 2.21/1.02  --sup_passive_queue_type                priority_queues
% 2.21/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.21/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.21/1.02  --demod_completeness_check              fast
% 2.21/1.02  --demod_use_ground                      true
% 2.21/1.02  --sup_to_prop_solver                    passive
% 2.21/1.02  --sup_prop_simpl_new                    true
% 2.21/1.02  --sup_prop_simpl_given                  true
% 2.21/1.02  --sup_fun_splitting                     false
% 2.21/1.02  --sup_smt_interval                      50000
% 2.21/1.02  
% 2.21/1.02  ------ Superposition Simplification Setup
% 2.21/1.02  
% 2.21/1.02  --sup_indices_passive                   []
% 2.21/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.21/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.21/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.21/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.21/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.21/1.02  --sup_full_bw                           [BwDemod]
% 2.21/1.02  --sup_immed_triv                        [TrivRules]
% 2.21/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.21/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.21/1.02  --sup_immed_bw_main                     []
% 2.21/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.21/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.21/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.21/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.21/1.02  
% 2.21/1.02  ------ Combination Options
% 2.21/1.02  
% 2.21/1.02  --comb_res_mult                         3
% 2.21/1.02  --comb_sup_mult                         2
% 2.21/1.02  --comb_inst_mult                        10
% 2.21/1.02  
% 2.21/1.02  ------ Debug Options
% 2.21/1.02  
% 2.21/1.02  --dbg_backtrace                         false
% 2.21/1.02  --dbg_dump_prop_clauses                 false
% 2.21/1.02  --dbg_dump_prop_clauses_file            -
% 2.21/1.02  --dbg_out_stat                          false
% 2.21/1.02  ------ Parsing...
% 2.21/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.21/1.02  
% 2.21/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 2.21/1.02  
% 2.21/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.21/1.02  
% 2.21/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.21/1.02  ------ Proving...
% 2.21/1.02  ------ Problem Properties 
% 2.21/1.02  
% 2.21/1.02  
% 2.21/1.02  clauses                                 16
% 2.21/1.02  conjectures                             1
% 2.21/1.02  EPR                                     1
% 2.21/1.02  Horn                                    12
% 2.21/1.02  unary                                   6
% 2.21/1.02  binary                                  1
% 2.21/1.02  lits                                    47
% 2.21/1.02  lits eq                                 10
% 2.21/1.02  fd_pure                                 0
% 2.21/1.02  fd_pseudo                               0
% 2.21/1.02  fd_cond                                 0
% 2.21/1.02  fd_pseudo_cond                          3
% 2.21/1.02  AC symbols                              0
% 2.21/1.02  
% 2.21/1.02  ------ Schedule dynamic 5 is on 
% 2.21/1.02  
% 2.21/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.21/1.02  
% 2.21/1.02  
% 2.21/1.02  ------ 
% 2.21/1.02  Current options:
% 2.21/1.02  ------ 
% 2.21/1.02  
% 2.21/1.02  ------ Input Options
% 2.21/1.02  
% 2.21/1.02  --out_options                           all
% 2.21/1.02  --tptp_safe_out                         true
% 2.21/1.02  --problem_path                          ""
% 2.21/1.02  --include_path                          ""
% 2.21/1.02  --clausifier                            res/vclausify_rel
% 2.21/1.02  --clausifier_options                    --mode clausify
% 2.21/1.02  --stdin                                 false
% 2.21/1.02  --stats_out                             all
% 2.21/1.02  
% 2.21/1.02  ------ General Options
% 2.21/1.02  
% 2.21/1.02  --fof                                   false
% 2.21/1.02  --time_out_real                         305.
% 2.21/1.02  --time_out_virtual                      -1.
% 2.21/1.02  --symbol_type_check                     false
% 2.21/1.02  --clausify_out                          false
% 2.21/1.02  --sig_cnt_out                           false
% 2.21/1.02  --trig_cnt_out                          false
% 2.21/1.02  --trig_cnt_out_tolerance                1.
% 2.21/1.02  --trig_cnt_out_sk_spl                   false
% 2.21/1.02  --abstr_cl_out                          false
% 2.21/1.02  
% 2.21/1.02  ------ Global Options
% 2.21/1.02  
% 2.21/1.02  --schedule                              default
% 2.21/1.02  --add_important_lit                     false
% 2.21/1.02  --prop_solver_per_cl                    1000
% 2.21/1.02  --min_unsat_core                        false
% 2.21/1.02  --soft_assumptions                      false
% 2.21/1.02  --soft_lemma_size                       3
% 2.21/1.02  --prop_impl_unit_size                   0
% 2.21/1.02  --prop_impl_unit                        []
% 2.21/1.02  --share_sel_clauses                     true
% 2.21/1.02  --reset_solvers                         false
% 2.21/1.02  --bc_imp_inh                            [conj_cone]
% 2.21/1.02  --conj_cone_tolerance                   3.
% 2.21/1.02  --extra_neg_conj                        none
% 2.21/1.02  --large_theory_mode                     true
% 2.21/1.02  --prolific_symb_bound                   200
% 2.21/1.02  --lt_threshold                          2000
% 2.21/1.02  --clause_weak_htbl                      true
% 2.21/1.02  --gc_record_bc_elim                     false
% 2.21/1.02  
% 2.21/1.02  ------ Preprocessing Options
% 2.21/1.02  
% 2.21/1.02  --preprocessing_flag                    true
% 2.21/1.02  --time_out_prep_mult                    0.1
% 2.21/1.02  --splitting_mode                        input
% 2.21/1.02  --splitting_grd                         true
% 2.21/1.02  --splitting_cvd                         false
% 2.21/1.02  --splitting_cvd_svl                     false
% 2.21/1.02  --splitting_nvd                         32
% 2.21/1.02  --sub_typing                            true
% 2.21/1.02  --prep_gs_sim                           true
% 2.21/1.02  --prep_unflatten                        true
% 2.21/1.02  --prep_res_sim                          true
% 2.21/1.02  --prep_upred                            true
% 2.21/1.02  --prep_sem_filter                       exhaustive
% 2.21/1.02  --prep_sem_filter_out                   false
% 2.21/1.02  --pred_elim                             true
% 2.21/1.02  --res_sim_input                         true
% 2.21/1.02  --eq_ax_congr_red                       true
% 2.21/1.02  --pure_diseq_elim                       true
% 2.21/1.02  --brand_transform                       false
% 2.21/1.02  --non_eq_to_eq                          false
% 2.21/1.02  --prep_def_merge                        true
% 2.21/1.02  --prep_def_merge_prop_impl              false
% 2.21/1.02  --prep_def_merge_mbd                    true
% 2.21/1.02  --prep_def_merge_tr_red                 false
% 2.21/1.02  --prep_def_merge_tr_cl                  false
% 2.21/1.02  --smt_preprocessing                     true
% 2.21/1.02  --smt_ac_axioms                         fast
% 2.21/1.02  --preprocessed_out                      false
% 2.21/1.02  --preprocessed_stats                    false
% 2.21/1.02  
% 2.21/1.02  ------ Abstraction refinement Options
% 2.21/1.02  
% 2.21/1.02  --abstr_ref                             []
% 2.21/1.02  --abstr_ref_prep                        false
% 2.21/1.02  --abstr_ref_until_sat                   false
% 2.21/1.02  --abstr_ref_sig_restrict                funpre
% 2.21/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.21/1.02  --abstr_ref_under                       []
% 2.21/1.02  
% 2.21/1.02  ------ SAT Options
% 2.21/1.02  
% 2.21/1.02  --sat_mode                              false
% 2.21/1.02  --sat_fm_restart_options                ""
% 2.21/1.02  --sat_gr_def                            false
% 2.21/1.02  --sat_epr_types                         true
% 2.21/1.02  --sat_non_cyclic_types                  false
% 2.21/1.02  --sat_finite_models                     false
% 2.21/1.02  --sat_fm_lemmas                         false
% 2.21/1.02  --sat_fm_prep                           false
% 2.21/1.02  --sat_fm_uc_incr                        true
% 2.21/1.02  --sat_out_model                         small
% 2.21/1.02  --sat_out_clauses                       false
% 2.21/1.02  
% 2.21/1.02  ------ QBF Options
% 2.21/1.02  
% 2.21/1.02  --qbf_mode                              false
% 2.21/1.02  --qbf_elim_univ                         false
% 2.21/1.02  --qbf_dom_inst                          none
% 2.21/1.02  --qbf_dom_pre_inst                      false
% 2.21/1.02  --qbf_sk_in                             false
% 2.21/1.02  --qbf_pred_elim                         true
% 2.21/1.02  --qbf_split                             512
% 2.21/1.02  
% 2.21/1.02  ------ BMC1 Options
% 2.21/1.02  
% 2.21/1.02  --bmc1_incremental                      false
% 2.21/1.02  --bmc1_axioms                           reachable_all
% 2.21/1.02  --bmc1_min_bound                        0
% 2.21/1.02  --bmc1_max_bound                        -1
% 2.21/1.02  --bmc1_max_bound_default                -1
% 2.21/1.02  --bmc1_symbol_reachability              true
% 2.21/1.02  --bmc1_property_lemmas                  false
% 2.21/1.02  --bmc1_k_induction                      false
% 2.21/1.02  --bmc1_non_equiv_states                 false
% 2.21/1.02  --bmc1_deadlock                         false
% 2.21/1.02  --bmc1_ucm                              false
% 2.21/1.02  --bmc1_add_unsat_core                   none
% 2.21/1.02  --bmc1_unsat_core_children              false
% 2.21/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.21/1.02  --bmc1_out_stat                         full
% 2.21/1.02  --bmc1_ground_init                      false
% 2.21/1.02  --bmc1_pre_inst_next_state              false
% 2.21/1.02  --bmc1_pre_inst_state                   false
% 2.21/1.02  --bmc1_pre_inst_reach_state             false
% 2.21/1.02  --bmc1_out_unsat_core                   false
% 2.21/1.02  --bmc1_aig_witness_out                  false
% 2.21/1.02  --bmc1_verbose                          false
% 2.21/1.02  --bmc1_dump_clauses_tptp                false
% 2.21/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.21/1.02  --bmc1_dump_file                        -
% 2.21/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.21/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.21/1.02  --bmc1_ucm_extend_mode                  1
% 2.21/1.02  --bmc1_ucm_init_mode                    2
% 2.21/1.02  --bmc1_ucm_cone_mode                    none
% 2.21/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.21/1.02  --bmc1_ucm_relax_model                  4
% 2.21/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.21/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.21/1.02  --bmc1_ucm_layered_model                none
% 2.21/1.02  --bmc1_ucm_max_lemma_size               10
% 2.21/1.02  
% 2.21/1.02  ------ AIG Options
% 2.21/1.02  
% 2.21/1.02  --aig_mode                              false
% 2.21/1.02  
% 2.21/1.02  ------ Instantiation Options
% 2.21/1.02  
% 2.21/1.02  --instantiation_flag                    true
% 2.21/1.02  --inst_sos_flag                         false
% 2.21/1.02  --inst_sos_phase                        true
% 2.21/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.21/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.21/1.02  --inst_lit_sel_side                     none
% 2.21/1.02  --inst_solver_per_active                1400
% 2.21/1.02  --inst_solver_calls_frac                1.
% 2.21/1.02  --inst_passive_queue_type               priority_queues
% 2.21/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.21/1.02  --inst_passive_queues_freq              [25;2]
% 2.21/1.02  --inst_dismatching                      true
% 2.21/1.02  --inst_eager_unprocessed_to_passive     true
% 2.21/1.02  --inst_prop_sim_given                   true
% 2.21/1.02  --inst_prop_sim_new                     false
% 2.21/1.02  --inst_subs_new                         false
% 2.21/1.02  --inst_eq_res_simp                      false
% 2.21/1.02  --inst_subs_given                       false
% 2.21/1.02  --inst_orphan_elimination               true
% 2.21/1.02  --inst_learning_loop_flag               true
% 2.21/1.02  --inst_learning_start                   3000
% 2.21/1.02  --inst_learning_factor                  2
% 2.21/1.02  --inst_start_prop_sim_after_learn       3
% 2.21/1.02  --inst_sel_renew                        solver
% 2.21/1.02  --inst_lit_activity_flag                true
% 2.21/1.02  --inst_restr_to_given                   false
% 2.21/1.02  --inst_activity_threshold               500
% 2.21/1.02  --inst_out_proof                        true
% 2.21/1.02  
% 2.21/1.02  ------ Resolution Options
% 2.21/1.02  
% 2.21/1.02  --resolution_flag                       false
% 2.21/1.02  --res_lit_sel                           adaptive
% 2.21/1.02  --res_lit_sel_side                      none
% 2.21/1.02  --res_ordering                          kbo
% 2.21/1.02  --res_to_prop_solver                    active
% 2.21/1.02  --res_prop_simpl_new                    false
% 2.21/1.02  --res_prop_simpl_given                  true
% 2.21/1.02  --res_passive_queue_type                priority_queues
% 2.21/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.21/1.02  --res_passive_queues_freq               [15;5]
% 2.21/1.02  --res_forward_subs                      full
% 2.21/1.02  --res_backward_subs                     full
% 2.21/1.02  --res_forward_subs_resolution           true
% 2.21/1.02  --res_backward_subs_resolution          true
% 2.21/1.02  --res_orphan_elimination                true
% 2.21/1.02  --res_time_limit                        2.
% 2.21/1.02  --res_out_proof                         true
% 2.21/1.02  
% 2.21/1.02  ------ Superposition Options
% 2.21/1.02  
% 2.21/1.02  --superposition_flag                    true
% 2.21/1.02  --sup_passive_queue_type                priority_queues
% 2.21/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.21/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.21/1.02  --demod_completeness_check              fast
% 2.21/1.02  --demod_use_ground                      true
% 2.21/1.02  --sup_to_prop_solver                    passive
% 2.21/1.02  --sup_prop_simpl_new                    true
% 2.21/1.02  --sup_prop_simpl_given                  true
% 2.21/1.02  --sup_fun_splitting                     false
% 2.21/1.02  --sup_smt_interval                      50000
% 2.21/1.02  
% 2.21/1.02  ------ Superposition Simplification Setup
% 2.21/1.02  
% 2.21/1.02  --sup_indices_passive                   []
% 2.21/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.21/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.21/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.21/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.21/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.21/1.02  --sup_full_bw                           [BwDemod]
% 2.21/1.02  --sup_immed_triv                        [TrivRules]
% 2.21/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.21/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.21/1.02  --sup_immed_bw_main                     []
% 2.21/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.21/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.21/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.21/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.21/1.02  
% 2.21/1.02  ------ Combination Options
% 2.21/1.02  
% 2.21/1.02  --comb_res_mult                         3
% 2.21/1.02  --comb_sup_mult                         2
% 2.21/1.02  --comb_inst_mult                        10
% 2.21/1.02  
% 2.21/1.02  ------ Debug Options
% 2.21/1.02  
% 2.21/1.02  --dbg_backtrace                         false
% 2.21/1.02  --dbg_dump_prop_clauses                 false
% 2.21/1.02  --dbg_dump_prop_clauses_file            -
% 2.21/1.02  --dbg_out_stat                          false
% 2.21/1.02  
% 2.21/1.02  
% 2.21/1.02  
% 2.21/1.02  
% 2.21/1.02  ------ Proving...
% 2.21/1.02  
% 2.21/1.02  
% 2.21/1.02  % SZS status Theorem for theBenchmark.p
% 2.21/1.02  
% 2.21/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 2.21/1.02  
% 2.21/1.02  fof(f8,axiom,(
% 2.21/1.02    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1)) => (r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1)) & ((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1))))))),
% 2.21/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.21/1.02  
% 2.21/1.02  fof(f16,plain,(
% 2.21/1.02    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1)) => (r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1)) & ((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) => (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X4) => r1_orders_2(X0,X1,X4))) & r2_lattice3(X0,X2,X1))))))),
% 2.21/1.02    inference(rectify,[],[f8])).
% 2.21/1.02  
% 2.21/1.02  fof(f29,plain,(
% 2.21/1.02    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | (? [X3] : ((~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3)) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1))) & ((! [X4] : ((r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | (~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0)))),
% 2.21/1.02    inference(ennf_transformation,[],[f16])).
% 2.21/1.02  
% 2.21/1.02  fof(f30,plain,(
% 2.21/1.02    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | ? [X3] : (~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | ~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 2.21/1.02    inference(flattening,[],[f29])).
% 2.21/1.02  
% 2.21/1.02  fof(f36,plain,(
% 2.21/1.02    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X1,sK0(X0,X1,X2)) & r2_lattice3(X0,X2,sK0(X0,X1,X2)) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 2.21/1.02    introduced(choice_axiom,[])).
% 2.21/1.02  
% 2.21/1.02  fof(f37,plain,(
% 2.21/1.02    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | (~r1_orders_2(X0,X1,sK0(X0,X1,X2)) & r2_lattice3(X0,X2,sK0(X0,X1,X2)) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | ~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 2.21/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f36])).
% 2.21/1.02  
% 2.21/1.02  fof(f51,plain,(
% 2.21/1.02    ( ! [X2,X0,X1] : (k1_yellow_0(X0,X2) = X1 | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) | ~r2_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 2.21/1.02    inference(cnf_transformation,[],[f37])).
% 2.21/1.02  
% 2.21/1.02  fof(f11,axiom,(
% 2.21/1.02    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v4_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 2.21/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.21/1.02  
% 2.21/1.02  fof(f17,plain,(
% 2.21/1.02    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 2.21/1.02    inference(pure_predicate_removal,[],[f11])).
% 2.21/1.02  
% 2.21/1.02  fof(f19,plain,(
% 2.21/1.02    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)))),
% 2.21/1.02    inference(pure_predicate_removal,[],[f17])).
% 2.21/1.02  
% 2.21/1.02  fof(f60,plain,(
% 2.21/1.02    ( ! [X0] : (v5_orders_2(k2_yellow_1(X0))) )),
% 2.21/1.02    inference(cnf_transformation,[],[f19])).
% 2.21/1.02  
% 2.21/1.02  fof(f10,axiom,(
% 2.21/1.02    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 2.21/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.21/1.02  
% 2.21/1.02  fof(f18,plain,(
% 2.21/1.02    ! [X0] : l1_orders_2(k2_yellow_1(X0))),
% 2.21/1.02    inference(pure_predicate_removal,[],[f10])).
% 2.21/1.02  
% 2.21/1.02  fof(f58,plain,(
% 2.21/1.02    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 2.21/1.02    inference(cnf_transformation,[],[f18])).
% 2.21/1.02  
% 2.21/1.02  fof(f12,axiom,(
% 2.21/1.02    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 2.21/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.21/1.02  
% 2.21/1.02  fof(f61,plain,(
% 2.21/1.02    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 2.21/1.02    inference(cnf_transformation,[],[f12])).
% 2.21/1.02  
% 2.21/1.02  fof(f5,axiom,(
% 2.21/1.02    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 2.21/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.21/1.02  
% 2.21/1.02  fof(f25,plain,(
% 2.21/1.02    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 2.21/1.02    inference(ennf_transformation,[],[f5])).
% 2.21/1.02  
% 2.21/1.02  fof(f45,plain,(
% 2.21/1.02    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 2.21/1.02    inference(cnf_transformation,[],[f25])).
% 2.21/1.02  
% 2.21/1.02  fof(f4,axiom,(
% 2.21/1.02    ! [X0] : ((l1_struct_0(X0) & v2_struct_0(X0)) => v1_xboole_0(k2_struct_0(X0)))),
% 2.21/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.21/1.02  
% 2.21/1.02  fof(f23,plain,(
% 2.21/1.02    ! [X0] : (v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | ~v2_struct_0(X0)))),
% 2.21/1.02    inference(ennf_transformation,[],[f4])).
% 2.21/1.02  
% 2.21/1.02  fof(f24,plain,(
% 2.21/1.02    ! [X0] : (v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | ~v2_struct_0(X0))),
% 2.21/1.02    inference(flattening,[],[f23])).
% 2.21/1.02  
% 2.21/1.02  fof(f44,plain,(
% 2.21/1.02    ( ! [X0] : (v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | ~v2_struct_0(X0)) )),
% 2.21/1.02    inference(cnf_transformation,[],[f24])).
% 2.21/1.02  
% 2.21/1.02  fof(f14,conjecture,(
% 2.21/1.02    ! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k1_xboole_0,X0) => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))))),
% 2.21/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.21/1.02  
% 2.21/1.02  fof(f15,negated_conjecture,(
% 2.21/1.02    ~! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k1_xboole_0,X0) => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))))),
% 2.21/1.02    inference(negated_conjecture,[],[f14])).
% 2.21/1.02  
% 2.21/1.02  fof(f33,plain,(
% 2.21/1.02    ? [X0] : ((k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0)) & r2_hidden(k1_xboole_0,X0)) & ~v1_xboole_0(X0))),
% 2.21/1.02    inference(ennf_transformation,[],[f15])).
% 2.21/1.02  
% 2.21/1.02  fof(f34,plain,(
% 2.21/1.02    ? [X0] : (k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0)) & r2_hidden(k1_xboole_0,X0) & ~v1_xboole_0(X0))),
% 2.21/1.02    inference(flattening,[],[f33])).
% 2.21/1.02  
% 2.21/1.02  fof(f39,plain,(
% 2.21/1.02    ? [X0] : (k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0)) & r2_hidden(k1_xboole_0,X0) & ~v1_xboole_0(X0)) => (k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK1)) & r2_hidden(k1_xboole_0,sK1) & ~v1_xboole_0(sK1))),
% 2.21/1.02    introduced(choice_axiom,[])).
% 2.21/1.02  
% 2.21/1.02  fof(f40,plain,(
% 2.21/1.02    k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK1)) & r2_hidden(k1_xboole_0,sK1) & ~v1_xboole_0(sK1)),
% 2.21/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f39])).
% 2.21/1.02  
% 2.21/1.02  fof(f65,plain,(
% 2.21/1.02    ~v1_xboole_0(sK1)),
% 2.21/1.02    inference(cnf_transformation,[],[f40])).
% 2.21/1.02  
% 2.21/1.02  fof(f6,axiom,(
% 2.21/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 2.21/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.21/1.02  
% 2.21/1.02  fof(f26,plain,(
% 2.21/1.02    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.21/1.02    inference(ennf_transformation,[],[f6])).
% 2.21/1.02  
% 2.21/1.02  fof(f27,plain,(
% 2.21/1.02    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.21/1.02    inference(flattening,[],[f26])).
% 2.21/1.02  
% 2.21/1.02  fof(f35,plain,(
% 2.21/1.02    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.21/1.02    inference(nnf_transformation,[],[f27])).
% 2.21/1.02  
% 2.21/1.02  fof(f46,plain,(
% 2.21/1.02    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.21/1.02    inference(cnf_transformation,[],[f35])).
% 2.21/1.02  
% 2.21/1.02  fof(f59,plain,(
% 2.21/1.02    ( ! [X0] : (v3_orders_2(k2_yellow_1(X0))) )),
% 2.21/1.02    inference(cnf_transformation,[],[f19])).
% 2.21/1.02  
% 2.21/1.02  fof(f1,axiom,(
% 2.21/1.02    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.21/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.21/1.02  
% 2.21/1.02  fof(f41,plain,(
% 2.21/1.02    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.21/1.02    inference(cnf_transformation,[],[f1])).
% 2.21/1.02  
% 2.21/1.02  fof(f13,axiom,(
% 2.21/1.02    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)))))),
% 2.21/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.21/1.02  
% 2.21/1.02  fof(f32,plain,(
% 2.21/1.02    ! [X0] : (! [X1] : (! [X2] : ((r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 2.21/1.02    inference(ennf_transformation,[],[f13])).
% 2.21/1.02  
% 2.21/1.02  fof(f38,plain,(
% 2.21/1.02    ! [X0] : (! [X1] : (! [X2] : (((r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2)) & (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 2.21/1.02    inference(nnf_transformation,[],[f32])).
% 2.21/1.02  
% 2.21/1.02  fof(f64,plain,(
% 2.21/1.02    ( ! [X2,X0,X1] : (r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 2.21/1.02    inference(cnf_transformation,[],[f38])).
% 2.21/1.02  
% 2.21/1.02  fof(f3,axiom,(
% 2.21/1.02    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.21/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.21/1.02  
% 2.21/1.02  fof(f22,plain,(
% 2.21/1.02    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.21/1.02    inference(ennf_transformation,[],[f3])).
% 2.21/1.02  
% 2.21/1.02  fof(f43,plain,(
% 2.21/1.02    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.21/1.02    inference(cnf_transformation,[],[f22])).
% 2.21/1.02  
% 2.21/1.02  fof(f2,axiom,(
% 2.21/1.02    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 2.21/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.21/1.02  
% 2.21/1.02  fof(f21,plain,(
% 2.21/1.02    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 2.21/1.02    inference(ennf_transformation,[],[f2])).
% 2.21/1.02  
% 2.21/1.02  fof(f42,plain,(
% 2.21/1.02    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 2.21/1.02    inference(cnf_transformation,[],[f21])).
% 2.21/1.02  
% 2.21/1.02  fof(f66,plain,(
% 2.21/1.02    r2_hidden(k1_xboole_0,sK1)),
% 2.21/1.02    inference(cnf_transformation,[],[f40])).
% 2.21/1.02  
% 2.21/1.02  fof(f53,plain,(
% 2.21/1.02    ( ! [X2,X0,X1] : (k1_yellow_0(X0,X2) = X1 | ~r1_orders_2(X0,X1,sK0(X0,X1,X2)) | ~r2_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 2.21/1.02    inference(cnf_transformation,[],[f37])).
% 2.21/1.02  
% 2.21/1.02  fof(f7,axiom,(
% 2.21/1.02    ! [X0] : (l1_orders_2(X0) => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0))),
% 2.21/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.21/1.02  
% 2.21/1.02  fof(f28,plain,(
% 2.21/1.02    ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0))),
% 2.21/1.02    inference(ennf_transformation,[],[f7])).
% 2.21/1.02  
% 2.21/1.02  fof(f48,plain,(
% 2.21/1.02    ( ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0)) )),
% 2.21/1.02    inference(cnf_transformation,[],[f28])).
% 2.21/1.02  
% 2.21/1.02  fof(f9,axiom,(
% 2.21/1.02    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (r1_lattice3(X0,k1_xboole_0,X1) & r2_lattice3(X0,k1_xboole_0,X1))))),
% 2.21/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.21/1.02  
% 2.21/1.02  fof(f20,plain,(
% 2.21/1.02    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r2_lattice3(X0,k1_xboole_0,X1)))),
% 2.21/1.02    inference(pure_predicate_removal,[],[f9])).
% 2.21/1.02  
% 2.21/1.02  fof(f31,plain,(
% 2.21/1.02    ! [X0] : (! [X1] : (r2_lattice3(X0,k1_xboole_0,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.21/1.02    inference(ennf_transformation,[],[f20])).
% 2.21/1.02  
% 2.21/1.02  fof(f57,plain,(
% 2.21/1.02    ( ! [X0,X1] : (r2_lattice3(X0,k1_xboole_0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.21/1.02    inference(cnf_transformation,[],[f31])).
% 2.21/1.02  
% 2.21/1.02  fof(f67,plain,(
% 2.21/1.02    k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK1))),
% 2.21/1.02    inference(cnf_transformation,[],[f40])).
% 2.21/1.02  
% 2.21/1.02  cnf(c_13,plain,
% 2.21/1.02      ( ~ r2_lattice3(X0,X1,X2)
% 2.21/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.21/1.02      | m1_subset_1(sK0(X0,X2,X1),u1_struct_0(X0))
% 2.21/1.02      | ~ v5_orders_2(X0)
% 2.21/1.02      | ~ l1_orders_2(X0)
% 2.21/1.02      | k1_yellow_0(X0,X1) = X2 ),
% 2.21/1.02      inference(cnf_transformation,[],[f51]) ).
% 2.21/1.02  
% 2.21/1.02  cnf(c_18,plain,
% 2.21/1.02      ( v5_orders_2(k2_yellow_1(X0)) ),
% 2.21/1.02      inference(cnf_transformation,[],[f60]) ).
% 2.21/1.02  
% 2.21/1.02  cnf(c_626,plain,
% 2.21/1.02      ( ~ r2_lattice3(X0,X1,X2)
% 2.21/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.21/1.02      | m1_subset_1(sK0(X0,X2,X1),u1_struct_0(X0))
% 2.21/1.02      | ~ l1_orders_2(X0)
% 2.21/1.02      | k1_yellow_0(X0,X1) = X2
% 2.21/1.02      | k2_yellow_1(X3) != X0 ),
% 2.21/1.02      inference(resolution_lifted,[status(thm)],[c_13,c_18]) ).
% 2.21/1.02  
% 2.21/1.02  cnf(c_627,plain,
% 2.21/1.02      ( ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
% 2.21/1.02      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.21/1.02      | m1_subset_1(sK0(k2_yellow_1(X0),X2,X1),u1_struct_0(k2_yellow_1(X0)))
% 2.21/1.02      | ~ l1_orders_2(k2_yellow_1(X0))
% 2.21/1.02      | k1_yellow_0(k2_yellow_1(X0),X1) = X2 ),
% 2.21/1.02      inference(unflattening,[status(thm)],[c_626]) ).
% 2.21/1.02  
% 2.21/1.02  cnf(c_17,plain,
% 2.21/1.02      ( l1_orders_2(k2_yellow_1(X0)) ),
% 2.21/1.02      inference(cnf_transformation,[],[f58]) ).
% 2.21/1.02  
% 2.21/1.02  cnf(c_631,plain,
% 2.21/1.02      ( m1_subset_1(sK0(k2_yellow_1(X0),X2,X1),u1_struct_0(k2_yellow_1(X0)))
% 2.21/1.02      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.21/1.02      | ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
% 2.21/1.02      | k1_yellow_0(k2_yellow_1(X0),X1) = X2 ),
% 2.21/1.02      inference(global_propositional_subsumption,
% 2.21/1.02                [status(thm)],
% 2.21/1.02                [c_627,c_17]) ).
% 2.21/1.02  
% 2.21/1.02  cnf(c_632,plain,
% 2.21/1.02      ( ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
% 2.21/1.02      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.21/1.02      | m1_subset_1(sK0(k2_yellow_1(X0),X2,X1),u1_struct_0(k2_yellow_1(X0)))
% 2.21/1.02      | k1_yellow_0(k2_yellow_1(X0),X1) = X2 ),
% 2.21/1.02      inference(renaming,[status(thm)],[c_631]) ).
% 2.21/1.02  
% 2.21/1.02  cnf(c_1823,plain,
% 2.21/1.02      ( k1_yellow_0(k2_yellow_1(X0),X1) = X2
% 2.21/1.02      | r2_lattice3(k2_yellow_1(X0),X1,X2) != iProver_top
% 2.21/1.02      | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 2.21/1.02      | m1_subset_1(sK0(k2_yellow_1(X0),X2,X1),u1_struct_0(k2_yellow_1(X0))) = iProver_top ),
% 2.21/1.02      inference(predicate_to_equality,[status(thm)],[c_632]) ).
% 2.21/1.02  
% 2.21/1.02  cnf(c_21,plain,
% 2.21/1.02      ( u1_struct_0(k2_yellow_1(X0)) = X0 ),
% 2.21/1.02      inference(cnf_transformation,[],[f61]) ).
% 2.21/1.02  
% 2.21/1.02  cnf(c_1880,plain,
% 2.21/1.02      ( k1_yellow_0(k2_yellow_1(X0),X1) = X2
% 2.21/1.02      | r2_lattice3(k2_yellow_1(X0),X1,X2) != iProver_top
% 2.21/1.02      | m1_subset_1(X2,X0) != iProver_top
% 2.21/1.02      | m1_subset_1(sK0(k2_yellow_1(X0),X2,X1),X0) = iProver_top ),
% 2.21/1.02      inference(light_normalisation,[status(thm)],[c_1823,c_21]) ).
% 2.21/1.02  
% 2.21/1.02  cnf(c_4,plain,
% 2.21/1.02      ( ~ l1_orders_2(X0) | l1_struct_0(X0) ),
% 2.21/1.02      inference(cnf_transformation,[],[f45]) ).
% 2.21/1.02  
% 2.21/1.02  cnf(c_3,plain,
% 2.21/1.02      ( ~ v2_struct_0(X0)
% 2.21/1.02      | v1_xboole_0(k2_struct_0(X0))
% 2.21/1.02      | ~ l1_struct_0(X0) ),
% 2.21/1.02      inference(cnf_transformation,[],[f44]) ).
% 2.21/1.02  
% 2.21/1.02  cnf(c_296,plain,
% 2.21/1.02      ( ~ l1_orders_2(X0)
% 2.21/1.02      | ~ v2_struct_0(X0)
% 2.21/1.02      | v1_xboole_0(k2_struct_0(X0)) ),
% 2.21/1.02      inference(resolution,[status(thm)],[c_4,c_3]) ).
% 2.21/1.02  
% 2.21/1.02  cnf(c_26,negated_conjecture,
% 2.21/1.02      ( ~ v1_xboole_0(sK1) ),
% 2.21/1.02      inference(cnf_transformation,[],[f65]) ).
% 2.21/1.02  
% 2.21/1.02  cnf(c_328,plain,
% 2.21/1.02      ( ~ l1_orders_2(X0) | ~ v2_struct_0(X0) | k2_struct_0(X0) != sK1 ),
% 2.21/1.02      inference(resolution_lifted,[status(thm)],[c_296,c_26]) ).
% 2.21/1.02  
% 2.21/1.02  cnf(c_6,plain,
% 2.21/1.02      ( r1_orders_2(X0,X1,X2)
% 2.21/1.02      | ~ r3_orders_2(X0,X1,X2)
% 2.21/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.21/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.21/1.02      | ~ v3_orders_2(X0)
% 2.21/1.02      | ~ l1_orders_2(X0)
% 2.21/1.02      | v2_struct_0(X0) ),
% 2.21/1.02      inference(cnf_transformation,[],[f46]) ).
% 2.21/1.02  
% 2.21/1.02  cnf(c_19,plain,
% 2.21/1.02      ( v3_orders_2(k2_yellow_1(X0)) ),
% 2.21/1.02      inference(cnf_transformation,[],[f59]) ).
% 2.21/1.02  
% 2.21/1.02  cnf(c_410,plain,
% 2.21/1.02      ( r1_orders_2(X0,X1,X2)
% 2.21/1.02      | ~ r3_orders_2(X0,X1,X2)
% 2.21/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.21/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.21/1.02      | ~ l1_orders_2(X0)
% 2.21/1.02      | v2_struct_0(X0)
% 2.21/1.02      | k2_yellow_1(X3) != X0 ),
% 2.21/1.02      inference(resolution_lifted,[status(thm)],[c_6,c_19]) ).
% 2.21/1.02  
% 2.21/1.02  cnf(c_411,plain,
% 2.21/1.02      ( r1_orders_2(k2_yellow_1(X0),X1,X2)
% 2.21/1.02      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
% 2.21/1.02      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.21/1.02      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.21/1.02      | ~ l1_orders_2(k2_yellow_1(X0))
% 2.21/1.02      | v2_struct_0(k2_yellow_1(X0)) ),
% 2.21/1.02      inference(unflattening,[status(thm)],[c_410]) ).
% 2.21/1.02  
% 2.21/1.02  cnf(c_415,plain,
% 2.21/1.02      ( ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.21/1.02      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.21/1.02      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
% 2.21/1.02      | r1_orders_2(k2_yellow_1(X0),X1,X2)
% 2.21/1.02      | v2_struct_0(k2_yellow_1(X0)) ),
% 2.21/1.02      inference(global_propositional_subsumption,
% 2.21/1.02                [status(thm)],
% 2.21/1.02                [c_411,c_17]) ).
% 2.21/1.02  
% 2.21/1.02  cnf(c_416,plain,
% 2.21/1.02      ( r1_orders_2(k2_yellow_1(X0),X1,X2)
% 2.21/1.02      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
% 2.21/1.02      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.21/1.02      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.21/1.02      | v2_struct_0(k2_yellow_1(X0)) ),
% 2.21/1.02      inference(renaming,[status(thm)],[c_415]) ).
% 2.21/1.02  
% 2.21/1.02  cnf(c_503,plain,
% 2.21/1.02      ( r1_orders_2(k2_yellow_1(X0),X1,X2)
% 2.21/1.02      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
% 2.21/1.02      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.21/1.02      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.21/1.02      | ~ l1_orders_2(X3)
% 2.21/1.02      | k2_yellow_1(X0) != X3
% 2.21/1.02      | k2_struct_0(X3) != sK1 ),
% 2.21/1.02      inference(resolution_lifted,[status(thm)],[c_328,c_416]) ).
% 2.21/1.02  
% 2.21/1.02  cnf(c_504,plain,
% 2.21/1.02      ( r1_orders_2(k2_yellow_1(X0),X1,X2)
% 2.21/1.02      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
% 2.21/1.02      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.21/1.02      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.21/1.02      | ~ l1_orders_2(k2_yellow_1(X0))
% 2.21/1.02      | k2_struct_0(k2_yellow_1(X0)) != sK1 ),
% 2.21/1.02      inference(unflattening,[status(thm)],[c_503]) ).
% 2.21/1.02  
% 2.21/1.02  cnf(c_508,plain,
% 2.21/1.02      ( ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.21/1.02      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.21/1.02      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
% 2.21/1.02      | r1_orders_2(k2_yellow_1(X0),X1,X2)
% 2.21/1.02      | k2_struct_0(k2_yellow_1(X0)) != sK1 ),
% 2.21/1.02      inference(global_propositional_subsumption,
% 2.21/1.02                [status(thm)],
% 2.21/1.02                [c_504,c_17]) ).
% 2.21/1.02  
% 2.21/1.02  cnf(c_509,plain,
% 2.21/1.02      ( r1_orders_2(k2_yellow_1(X0),X1,X2)
% 2.21/1.02      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
% 2.21/1.02      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.21/1.02      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.21/1.02      | k2_struct_0(k2_yellow_1(X0)) != sK1 ),
% 2.21/1.02      inference(renaming,[status(thm)],[c_508]) ).
% 2.21/1.02  
% 2.21/1.02  cnf(c_0,plain,
% 2.21/1.02      ( r1_tarski(k1_xboole_0,X0) ),
% 2.21/1.02      inference(cnf_transformation,[],[f41]) ).
% 2.21/1.02  
% 2.21/1.02  cnf(c_22,plain,
% 2.21/1.02      ( r3_orders_2(k2_yellow_1(X0),X1,X2)
% 2.21/1.02      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.21/1.02      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.21/1.02      | ~ r1_tarski(X1,X2)
% 2.21/1.02      | v1_xboole_0(X0) ),
% 2.21/1.02      inference(cnf_transformation,[],[f64]) ).
% 2.21/1.02  
% 2.21/1.02  cnf(c_358,plain,
% 2.21/1.02      ( r3_orders_2(k2_yellow_1(X0),X1,X2)
% 2.21/1.02      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.21/1.02      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.21/1.02      | ~ r1_tarski(X1,X2)
% 2.21/1.02      | sK1 != X0 ),
% 2.21/1.02      inference(resolution_lifted,[status(thm)],[c_22,c_26]) ).
% 2.21/1.02  
% 2.21/1.02  cnf(c_359,plain,
% 2.21/1.02      ( r3_orders_2(k2_yellow_1(sK1),X0,X1)
% 2.21/1.02      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
% 2.21/1.02      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))
% 2.21/1.02      | ~ r1_tarski(X0,X1) ),
% 2.21/1.02      inference(unflattening,[status(thm)],[c_358]) ).
% 2.21/1.02  
% 2.21/1.02  cnf(c_391,plain,
% 2.21/1.02      ( r3_orders_2(k2_yellow_1(sK1),X0,X1)
% 2.21/1.02      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
% 2.21/1.02      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))
% 2.21/1.02      | X1 != X2
% 2.21/1.02      | k1_xboole_0 != X0 ),
% 2.21/1.02      inference(resolution_lifted,[status(thm)],[c_0,c_359]) ).
% 2.21/1.02  
% 2.21/1.02  cnf(c_392,plain,
% 2.21/1.02      ( r3_orders_2(k2_yellow_1(sK1),k1_xboole_0,X0)
% 2.21/1.02      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
% 2.21/1.02      | ~ m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK1))) ),
% 2.21/1.02      inference(unflattening,[status(thm)],[c_391]) ).
% 2.21/1.02  
% 2.21/1.02  cnf(c_543,plain,
% 2.21/1.02      ( r1_orders_2(k2_yellow_1(X0),X1,X2)
% 2.21/1.02      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.21/1.02      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.21/1.02      | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(sK1)))
% 2.21/1.02      | ~ m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK1)))
% 2.21/1.02      | X3 != X2
% 2.21/1.02      | k2_yellow_1(X0) != k2_yellow_1(sK1)
% 2.21/1.02      | k2_struct_0(k2_yellow_1(X0)) != sK1
% 2.21/1.02      | k1_xboole_0 != X1 ),
% 2.21/1.02      inference(resolution_lifted,[status(thm)],[c_509,c_392]) ).
% 2.21/1.02  
% 2.21/1.02  cnf(c_544,plain,
% 2.21/1.02      ( r1_orders_2(k2_yellow_1(X0),k1_xboole_0,X1)
% 2.21/1.02      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.21/1.02      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))
% 2.21/1.02      | ~ m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(X0)))
% 2.21/1.02      | ~ m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK1)))
% 2.21/1.02      | k2_yellow_1(X0) != k2_yellow_1(sK1)
% 2.21/1.02      | k2_struct_0(k2_yellow_1(X0)) != sK1 ),
% 2.21/1.02      inference(unflattening,[status(thm)],[c_543]) ).
% 2.21/1.02  
% 2.21/1.02  cnf(c_1826,plain,
% 2.21/1.02      ( k2_yellow_1(X0) != k2_yellow_1(sK1)
% 2.21/1.02      | k2_struct_0(k2_yellow_1(X0)) != sK1
% 2.21/1.02      | r1_orders_2(k2_yellow_1(X0),k1_xboole_0,X1) = iProver_top
% 2.21/1.03      | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 2.21/1.03      | m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1))) != iProver_top
% 2.21/1.03      | m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 2.21/1.03      | m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK1))) != iProver_top ),
% 2.21/1.03      inference(predicate_to_equality,[status(thm)],[c_544]) ).
% 2.21/1.03  
% 2.21/1.03  cnf(c_2,plain,
% 2.21/1.03      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.21/1.03      inference(cnf_transformation,[],[f43]) ).
% 2.21/1.03  
% 2.21/1.03  cnf(c_310,plain,
% 2.21/1.03      ( ~ l1_orders_2(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.21/1.03      inference(resolution,[status(thm)],[c_4,c_2]) ).
% 2.21/1.03  
% 2.21/1.03  cnf(c_810,plain,
% 2.21/1.03      ( k2_yellow_1(X0) != X1 | u1_struct_0(X1) = k2_struct_0(X1) ),
% 2.21/1.03      inference(resolution_lifted,[status(thm)],[c_310,c_17]) ).
% 2.21/1.03  
% 2.21/1.03  cnf(c_811,plain,
% 2.21/1.03      ( u1_struct_0(k2_yellow_1(X0)) = k2_struct_0(k2_yellow_1(X0)) ),
% 2.21/1.03      inference(unflattening,[status(thm)],[c_810]) ).
% 2.21/1.03  
% 2.21/1.03  cnf(c_1836,plain,
% 2.21/1.03      ( k2_struct_0(k2_yellow_1(X0)) = X0 ),
% 2.21/1.03      inference(light_normalisation,[status(thm)],[c_811,c_21]) ).
% 2.21/1.03  
% 2.21/1.03  cnf(c_1918,plain,
% 2.21/1.03      ( k2_yellow_1(X0) != k2_yellow_1(sK1)
% 2.21/1.03      | sK1 != X0
% 2.21/1.03      | r1_orders_2(k2_yellow_1(X0),k1_xboole_0,X1) = iProver_top
% 2.21/1.03      | m1_subset_1(X1,X0) != iProver_top
% 2.21/1.03      | m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1))) != iProver_top
% 2.21/1.03      | m1_subset_1(k1_xboole_0,X0) != iProver_top
% 2.21/1.03      | m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK1))) != iProver_top ),
% 2.21/1.03      inference(light_normalisation,[status(thm)],[c_1826,c_21,c_1836]) ).
% 2.21/1.03  
% 2.21/1.03  cnf(c_1919,plain,
% 2.21/1.03      ( k2_yellow_1(X0) != k2_yellow_1(sK1)
% 2.21/1.03      | sK1 != X0
% 2.21/1.03      | r1_orders_2(k2_yellow_1(X0),k1_xboole_0,X1) = iProver_top
% 2.21/1.03      | m1_subset_1(X1,X0) != iProver_top
% 2.21/1.03      | m1_subset_1(X1,sK1) != iProver_top
% 2.21/1.03      | m1_subset_1(k1_xboole_0,X0) != iProver_top
% 2.21/1.03      | m1_subset_1(k1_xboole_0,sK1) != iProver_top ),
% 2.21/1.03      inference(demodulation,[status(thm)],[c_1918,c_21]) ).
% 2.21/1.03  
% 2.21/1.03  cnf(c_1,plain,
% 2.21/1.03      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 2.21/1.03      inference(cnf_transformation,[],[f42]) ).
% 2.21/1.03  
% 2.21/1.03  cnf(c_25,negated_conjecture,
% 2.21/1.03      ( r2_hidden(k1_xboole_0,sK1) ),
% 2.21/1.03      inference(cnf_transformation,[],[f66]) ).
% 2.21/1.03  
% 2.21/1.03  cnf(c_287,plain,
% 2.21/1.03      ( m1_subset_1(X0,X1) | sK1 != X1 | k1_xboole_0 != X0 ),
% 2.21/1.03      inference(resolution_lifted,[status(thm)],[c_1,c_25]) ).
% 2.21/1.03  
% 2.21/1.03  cnf(c_288,plain,
% 2.21/1.03      ( m1_subset_1(k1_xboole_0,sK1) ),
% 2.21/1.03      inference(unflattening,[status(thm)],[c_287]) ).
% 2.21/1.03  
% 2.21/1.03  cnf(c_1827,plain,
% 2.21/1.03      ( m1_subset_1(k1_xboole_0,sK1) = iProver_top ),
% 2.21/1.03      inference(predicate_to_equality,[status(thm)],[c_288]) ).
% 2.21/1.03  
% 2.21/1.03  cnf(c_1927,plain,
% 2.21/1.03      ( k2_yellow_1(X0) != k2_yellow_1(sK1)
% 2.21/1.03      | sK1 != X0
% 2.21/1.03      | r1_orders_2(k2_yellow_1(X0),k1_xboole_0,X1) = iProver_top
% 2.21/1.03      | m1_subset_1(X1,X0) != iProver_top
% 2.21/1.03      | m1_subset_1(X1,sK1) != iProver_top
% 2.21/1.03      | m1_subset_1(k1_xboole_0,X0) != iProver_top ),
% 2.21/1.03      inference(forward_subsumption_resolution,
% 2.21/1.03                [status(thm)],
% 2.21/1.03                [c_1919,c_1827]) ).
% 2.21/1.03  
% 2.21/1.03  cnf(c_1998,plain,
% 2.21/1.03      ( sK1 != sK1
% 2.21/1.03      | r1_orders_2(k2_yellow_1(sK1),k1_xboole_0,X0) = iProver_top
% 2.21/1.03      | m1_subset_1(X0,sK1) != iProver_top
% 2.21/1.03      | m1_subset_1(k1_xboole_0,sK1) != iProver_top ),
% 2.21/1.03      inference(equality_resolution,[status(thm)],[c_1927]) ).
% 2.21/1.03  
% 2.21/1.03  cnf(c_2002,plain,
% 2.21/1.03      ( r1_orders_2(k2_yellow_1(sK1),k1_xboole_0,X0) = iProver_top
% 2.21/1.03      | m1_subset_1(X0,sK1) != iProver_top
% 2.21/1.03      | m1_subset_1(k1_xboole_0,sK1) != iProver_top ),
% 2.21/1.03      inference(equality_resolution_simp,[status(thm)],[c_1998]) ).
% 2.21/1.03  
% 2.21/1.03  cnf(c_289,plain,
% 2.21/1.03      ( m1_subset_1(k1_xboole_0,sK1) = iProver_top ),
% 2.21/1.03      inference(predicate_to_equality,[status(thm)],[c_288]) ).
% 2.21/1.03  
% 2.21/1.03  cnf(c_2006,plain,
% 2.21/1.03      ( m1_subset_1(X0,sK1) != iProver_top
% 2.21/1.03      | r1_orders_2(k2_yellow_1(sK1),k1_xboole_0,X0) = iProver_top ),
% 2.21/1.03      inference(global_propositional_subsumption,
% 2.21/1.03                [status(thm)],
% 2.21/1.03                [c_2002,c_289]) ).
% 2.21/1.03  
% 2.21/1.03  cnf(c_2007,plain,
% 2.21/1.03      ( r1_orders_2(k2_yellow_1(sK1),k1_xboole_0,X0) = iProver_top
% 2.21/1.03      | m1_subset_1(X0,sK1) != iProver_top ),
% 2.21/1.03      inference(renaming,[status(thm)],[c_2006]) ).
% 2.21/1.03  
% 2.21/1.03  cnf(c_11,plain,
% 2.21/1.03      ( ~ r2_lattice3(X0,X1,X2)
% 2.21/1.03      | ~ r1_orders_2(X0,X2,sK0(X0,X2,X1))
% 2.21/1.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.21/1.03      | ~ v5_orders_2(X0)
% 2.21/1.03      | ~ l1_orders_2(X0)
% 2.21/1.03      | k1_yellow_0(X0,X1) = X2 ),
% 2.21/1.03      inference(cnf_transformation,[],[f53]) ).
% 2.21/1.03  
% 2.21/1.03  cnf(c_674,plain,
% 2.21/1.03      ( ~ r2_lattice3(X0,X1,X2)
% 2.21/1.03      | ~ r1_orders_2(X0,X2,sK0(X0,X2,X1))
% 2.21/1.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.21/1.03      | ~ l1_orders_2(X0)
% 2.21/1.03      | k1_yellow_0(X0,X1) = X2
% 2.21/1.03      | k2_yellow_1(X3) != X0 ),
% 2.21/1.03      inference(resolution_lifted,[status(thm)],[c_11,c_18]) ).
% 2.21/1.03  
% 2.21/1.03  cnf(c_675,plain,
% 2.21/1.03      ( ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
% 2.21/1.03      | ~ r1_orders_2(k2_yellow_1(X0),X2,sK0(k2_yellow_1(X0),X2,X1))
% 2.21/1.03      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.21/1.03      | ~ l1_orders_2(k2_yellow_1(X0))
% 2.21/1.03      | k1_yellow_0(k2_yellow_1(X0),X1) = X2 ),
% 2.21/1.03      inference(unflattening,[status(thm)],[c_674]) ).
% 2.21/1.03  
% 2.21/1.03  cnf(c_679,plain,
% 2.21/1.03      ( ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.21/1.03      | ~ r1_orders_2(k2_yellow_1(X0),X2,sK0(k2_yellow_1(X0),X2,X1))
% 2.21/1.03      | ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
% 2.21/1.03      | k1_yellow_0(k2_yellow_1(X0),X1) = X2 ),
% 2.21/1.03      inference(global_propositional_subsumption,
% 2.21/1.03                [status(thm)],
% 2.21/1.03                [c_675,c_17]) ).
% 2.21/1.03  
% 2.21/1.03  cnf(c_680,plain,
% 2.21/1.03      ( ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
% 2.21/1.03      | ~ r1_orders_2(k2_yellow_1(X0),X2,sK0(k2_yellow_1(X0),X2,X1))
% 2.21/1.03      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.21/1.03      | k1_yellow_0(k2_yellow_1(X0),X1) = X2 ),
% 2.21/1.03      inference(renaming,[status(thm)],[c_679]) ).
% 2.21/1.03  
% 2.21/1.03  cnf(c_1821,plain,
% 2.21/1.03      ( k1_yellow_0(k2_yellow_1(X0),X1) = X2
% 2.21/1.03      | r2_lattice3(k2_yellow_1(X0),X1,X2) != iProver_top
% 2.21/1.03      | r1_orders_2(k2_yellow_1(X0),X2,sK0(k2_yellow_1(X0),X2,X1)) != iProver_top
% 2.21/1.03      | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top ),
% 2.21/1.03      inference(predicate_to_equality,[status(thm)],[c_680]) ).
% 2.21/1.03  
% 2.21/1.03  cnf(c_1898,plain,
% 2.21/1.03      ( k1_yellow_0(k2_yellow_1(X0),X1) = X2
% 2.21/1.03      | r2_lattice3(k2_yellow_1(X0),X1,X2) != iProver_top
% 2.21/1.03      | r1_orders_2(k2_yellow_1(X0),X2,sK0(k2_yellow_1(X0),X2,X1)) != iProver_top
% 2.21/1.03      | m1_subset_1(X2,X0) != iProver_top ),
% 2.21/1.03      inference(light_normalisation,[status(thm)],[c_1821,c_21]) ).
% 2.21/1.03  
% 2.21/1.03  cnf(c_2488,plain,
% 2.21/1.03      ( k1_yellow_0(k2_yellow_1(sK1),X0) = k1_xboole_0
% 2.21/1.03      | r2_lattice3(k2_yellow_1(sK1),X0,k1_xboole_0) != iProver_top
% 2.21/1.03      | m1_subset_1(sK0(k2_yellow_1(sK1),k1_xboole_0,X0),sK1) != iProver_top
% 2.21/1.03      | m1_subset_1(k1_xboole_0,sK1) != iProver_top ),
% 2.21/1.03      inference(superposition,[status(thm)],[c_2007,c_1898]) ).
% 2.21/1.03  
% 2.21/1.03  cnf(c_2563,plain,
% 2.21/1.03      ( m1_subset_1(sK0(k2_yellow_1(sK1),k1_xboole_0,X0),sK1) != iProver_top
% 2.21/1.03      | r2_lattice3(k2_yellow_1(sK1),X0,k1_xboole_0) != iProver_top
% 2.21/1.03      | k1_yellow_0(k2_yellow_1(sK1),X0) = k1_xboole_0 ),
% 2.21/1.03      inference(global_propositional_subsumption,
% 2.21/1.03                [status(thm)],
% 2.21/1.03                [c_2488,c_289]) ).
% 2.21/1.03  
% 2.21/1.03  cnf(c_2564,plain,
% 2.21/1.03      ( k1_yellow_0(k2_yellow_1(sK1),X0) = k1_xboole_0
% 2.21/1.03      | r2_lattice3(k2_yellow_1(sK1),X0,k1_xboole_0) != iProver_top
% 2.21/1.03      | m1_subset_1(sK0(k2_yellow_1(sK1),k1_xboole_0,X0),sK1) != iProver_top ),
% 2.21/1.03      inference(renaming,[status(thm)],[c_2563]) ).
% 2.21/1.03  
% 2.21/1.03  cnf(c_2572,plain,
% 2.21/1.03      ( k1_yellow_0(k2_yellow_1(sK1),X0) = k1_xboole_0
% 2.21/1.03      | r2_lattice3(k2_yellow_1(sK1),X0,k1_xboole_0) != iProver_top
% 2.21/1.03      | m1_subset_1(k1_xboole_0,sK1) != iProver_top ),
% 2.21/1.03      inference(superposition,[status(thm)],[c_1880,c_2564]) ).
% 2.21/1.03  
% 2.21/1.03  cnf(c_2581,plain,
% 2.21/1.03      ( k1_yellow_0(k2_yellow_1(sK1),k1_xboole_0) = k1_xboole_0
% 2.21/1.03      | r2_lattice3(k2_yellow_1(sK1),k1_xboole_0,k1_xboole_0) != iProver_top
% 2.21/1.03      | m1_subset_1(k1_xboole_0,sK1) != iProver_top ),
% 2.21/1.03      inference(instantiation,[status(thm)],[c_2572]) ).
% 2.21/1.03  
% 2.21/1.03  cnf(c_1584,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.21/1.03  
% 2.21/1.03  cnf(c_2475,plain,
% 2.21/1.03      ( k1_yellow_0(k2_yellow_1(sK1),k1_xboole_0) != X0
% 2.21/1.03      | k1_xboole_0 != X0
% 2.21/1.03      | k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK1),k1_xboole_0) ),
% 2.21/1.03      inference(instantiation,[status(thm)],[c_1584]) ).
% 2.21/1.03  
% 2.21/1.03  cnf(c_2476,plain,
% 2.21/1.03      ( k1_yellow_0(k2_yellow_1(sK1),k1_xboole_0) != k1_xboole_0
% 2.21/1.03      | k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK1),k1_xboole_0)
% 2.21/1.03      | k1_xboole_0 != k1_xboole_0 ),
% 2.21/1.03      inference(instantiation,[status(thm)],[c_2475]) ).
% 2.21/1.03  
% 2.21/1.03  cnf(c_1984,plain,
% 2.21/1.03      ( k3_yellow_0(k2_yellow_1(sK1)) != X0
% 2.21/1.03      | k1_xboole_0 != X0
% 2.21/1.03      | k1_xboole_0 = k3_yellow_0(k2_yellow_1(sK1)) ),
% 2.21/1.03      inference(instantiation,[status(thm)],[c_1584]) ).
% 2.21/1.03  
% 2.21/1.03  cnf(c_2306,plain,
% 2.21/1.03      ( k3_yellow_0(k2_yellow_1(sK1)) != k1_yellow_0(k2_yellow_1(sK1),k1_xboole_0)
% 2.21/1.03      | k1_xboole_0 != k1_yellow_0(k2_yellow_1(sK1),k1_xboole_0)
% 2.21/1.03      | k1_xboole_0 = k3_yellow_0(k2_yellow_1(sK1)) ),
% 2.21/1.03      inference(instantiation,[status(thm)],[c_1984]) ).
% 2.21/1.03  
% 2.21/1.03  cnf(c_7,plain,
% 2.21/1.03      ( ~ l1_orders_2(X0)
% 2.21/1.03      | k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0) ),
% 2.21/1.03      inference(cnf_transformation,[],[f48]) ).
% 2.21/1.03  
% 2.21/1.03  cnf(c_828,plain,
% 2.21/1.03      ( k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0)
% 2.21/1.03      | k2_yellow_1(X1) != X0 ),
% 2.21/1.03      inference(resolution_lifted,[status(thm)],[c_7,c_17]) ).
% 2.21/1.03  
% 2.21/1.03  cnf(c_829,plain,
% 2.21/1.03      ( k1_yellow_0(k2_yellow_1(X0),k1_xboole_0) = k3_yellow_0(k2_yellow_1(X0)) ),
% 2.21/1.03      inference(unflattening,[status(thm)],[c_828]) ).
% 2.21/1.03  
% 2.21/1.03  cnf(c_2124,plain,
% 2.21/1.03      ( k1_yellow_0(k2_yellow_1(sK1),k1_xboole_0) = k3_yellow_0(k2_yellow_1(sK1)) ),
% 2.21/1.03      inference(instantiation,[status(thm)],[c_829]) ).
% 2.21/1.03  
% 2.21/1.03  cnf(c_2015,plain,
% 2.21/1.03      ( X0 != X1
% 2.21/1.03      | k3_yellow_0(k2_yellow_1(sK1)) != X1
% 2.21/1.03      | k3_yellow_0(k2_yellow_1(sK1)) = X0 ),
% 2.21/1.03      inference(instantiation,[status(thm)],[c_1584]) ).
% 2.21/1.03  
% 2.21/1.03  cnf(c_2041,plain,
% 2.21/1.03      ( X0 != k3_yellow_0(k2_yellow_1(sK1))
% 2.21/1.03      | k3_yellow_0(k2_yellow_1(sK1)) = X0
% 2.21/1.03      | k3_yellow_0(k2_yellow_1(sK1)) != k3_yellow_0(k2_yellow_1(sK1)) ),
% 2.21/1.03      inference(instantiation,[status(thm)],[c_2015]) ).
% 2.21/1.03  
% 2.21/1.03  cnf(c_2123,plain,
% 2.21/1.03      ( k1_yellow_0(k2_yellow_1(sK1),k1_xboole_0) != k3_yellow_0(k2_yellow_1(sK1))
% 2.21/1.03      | k3_yellow_0(k2_yellow_1(sK1)) = k1_yellow_0(k2_yellow_1(sK1),k1_xboole_0)
% 2.21/1.03      | k3_yellow_0(k2_yellow_1(sK1)) != k3_yellow_0(k2_yellow_1(sK1)) ),
% 2.21/1.03      inference(instantiation,[status(thm)],[c_2041]) ).
% 2.21/1.03  
% 2.21/1.03  cnf(c_16,plain,
% 2.21/1.03      ( r2_lattice3(X0,k1_xboole_0,X1)
% 2.21/1.03      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.21/1.03      | ~ l1_orders_2(X0) ),
% 2.21/1.03      inference(cnf_transformation,[],[f57]) ).
% 2.21/1.03  
% 2.21/1.03  cnf(c_816,plain,
% 2.21/1.03      ( r2_lattice3(X0,k1_xboole_0,X1)
% 2.21/1.03      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.21/1.03      | k2_yellow_1(X2) != X0 ),
% 2.21/1.03      inference(resolution_lifted,[status(thm)],[c_16,c_17]) ).
% 2.21/1.03  
% 2.21/1.03  cnf(c_817,plain,
% 2.21/1.03      ( r2_lattice3(k2_yellow_1(X0),k1_xboole_0,X1)
% 2.21/1.03      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) ),
% 2.21/1.03      inference(unflattening,[status(thm)],[c_816]) ).
% 2.21/1.03  
% 2.21/1.03  cnf(c_2078,plain,
% 2.21/1.03      ( r2_lattice3(k2_yellow_1(sK1),k1_xboole_0,X0)
% 2.21/1.03      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1))) ),
% 2.21/1.03      inference(instantiation,[status(thm)],[c_817]) ).
% 2.21/1.03  
% 2.21/1.03  cnf(c_2079,plain,
% 2.21/1.03      ( r2_lattice3(k2_yellow_1(sK1),k1_xboole_0,X0) = iProver_top
% 2.21/1.03      | m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1))) != iProver_top ),
% 2.21/1.03      inference(predicate_to_equality,[status(thm)],[c_2078]) ).
% 2.21/1.03  
% 2.21/1.03  cnf(c_2081,plain,
% 2.21/1.03      ( r2_lattice3(k2_yellow_1(sK1),k1_xboole_0,k1_xboole_0) = iProver_top
% 2.21/1.03      | m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK1))) != iProver_top ),
% 2.21/1.03      inference(instantiation,[status(thm)],[c_2079]) ).
% 2.21/1.03  
% 2.21/1.03  cnf(c_1583,plain,( X0 = X0 ),theory(equality) ).
% 2.21/1.03  
% 2.21/1.03  cnf(c_2035,plain,
% 2.21/1.03      ( k2_yellow_1(sK1) = k2_yellow_1(sK1) ),
% 2.21/1.03      inference(instantiation,[status(thm)],[c_1583]) ).
% 2.21/1.03  
% 2.21/1.03  cnf(c_1589,plain,
% 2.21/1.03      ( X0 != X1 | k3_yellow_0(X0) = k3_yellow_0(X1) ),
% 2.21/1.03      theory(equality) ).
% 2.21/1.03  
% 2.21/1.03  cnf(c_2017,plain,
% 2.21/1.03      ( k2_yellow_1(sK1) != X0
% 2.21/1.03      | k3_yellow_0(k2_yellow_1(sK1)) = k3_yellow_0(X0) ),
% 2.21/1.03      inference(instantiation,[status(thm)],[c_1589]) ).
% 2.21/1.03  
% 2.21/1.03  cnf(c_2034,plain,
% 2.21/1.03      ( k2_yellow_1(sK1) != k2_yellow_1(sK1)
% 2.21/1.03      | k3_yellow_0(k2_yellow_1(sK1)) = k3_yellow_0(k2_yellow_1(sK1)) ),
% 2.21/1.03      inference(instantiation,[status(thm)],[c_2017]) ).
% 2.21/1.03  
% 2.21/1.03  cnf(c_2021,plain,
% 2.21/1.03      ( u1_struct_0(k2_yellow_1(sK1)) = sK1 ),
% 2.21/1.03      inference(instantiation,[status(thm)],[c_21]) ).
% 2.21/1.03  
% 2.21/1.03  cnf(c_1585,plain,
% 2.21/1.03      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.21/1.03      theory(equality) ).
% 2.21/1.03  
% 2.21/1.03  cnf(c_1986,plain,
% 2.21/1.03      ( m1_subset_1(X0,X1)
% 2.21/1.03      | ~ m1_subset_1(k1_xboole_0,sK1)
% 2.21/1.03      | X1 != sK1
% 2.21/1.03      | X0 != k1_xboole_0 ),
% 2.21/1.03      inference(instantiation,[status(thm)],[c_1585]) ).
% 2.21/1.03  
% 2.21/1.03  cnf(c_2020,plain,
% 2.21/1.03      ( m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
% 2.21/1.03      | ~ m1_subset_1(k1_xboole_0,sK1)
% 2.21/1.03      | X0 != k1_xboole_0
% 2.21/1.03      | u1_struct_0(k2_yellow_1(sK1)) != sK1 ),
% 2.21/1.03      inference(instantiation,[status(thm)],[c_1986]) ).
% 2.21/1.03  
% 2.21/1.03  cnf(c_2022,plain,
% 2.21/1.03      ( X0 != k1_xboole_0
% 2.21/1.03      | u1_struct_0(k2_yellow_1(sK1)) != sK1
% 2.21/1.03      | m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1))) = iProver_top
% 2.21/1.03      | m1_subset_1(k1_xboole_0,sK1) != iProver_top ),
% 2.21/1.03      inference(predicate_to_equality,[status(thm)],[c_2020]) ).
% 2.21/1.03  
% 2.21/1.03  cnf(c_2024,plain,
% 2.21/1.03      ( u1_struct_0(k2_yellow_1(sK1)) != sK1
% 2.21/1.03      | k1_xboole_0 != k1_xboole_0
% 2.21/1.03      | m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK1))) = iProver_top
% 2.21/1.03      | m1_subset_1(k1_xboole_0,sK1) != iProver_top ),
% 2.21/1.03      inference(instantiation,[status(thm)],[c_2022]) ).
% 2.21/1.03  
% 2.21/1.03  cnf(c_1608,plain,
% 2.21/1.03      ( k1_xboole_0 = k1_xboole_0 ),
% 2.21/1.03      inference(instantiation,[status(thm)],[c_1583]) ).
% 2.21/1.03  
% 2.21/1.03  cnf(c_24,negated_conjecture,
% 2.21/1.03      ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK1)) ),
% 2.21/1.03      inference(cnf_transformation,[],[f67]) ).
% 2.21/1.03  
% 2.21/1.03  cnf(contradiction,plain,
% 2.21/1.03      ( $false ),
% 2.21/1.03      inference(minisat,
% 2.21/1.03                [status(thm)],
% 2.21/1.03                [c_2581,c_2476,c_2306,c_2124,c_2123,c_2081,c_2035,c_2034,
% 2.21/1.03                 c_2021,c_2024,c_1608,c_289,c_24]) ).
% 2.21/1.03  
% 2.21/1.03  
% 2.21/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 2.21/1.03  
% 2.21/1.03  ------                               Statistics
% 2.21/1.03  
% 2.21/1.03  ------ General
% 2.21/1.03  
% 2.21/1.03  abstr_ref_over_cycles:                  0
% 2.21/1.03  abstr_ref_under_cycles:                 0
% 2.21/1.03  gc_basic_clause_elim:                   0
% 2.21/1.03  forced_gc_time:                         0
% 2.21/1.03  parsing_time:                           0.011
% 2.21/1.03  unif_index_cands_time:                  0.
% 2.21/1.03  unif_index_add_time:                    0.
% 2.21/1.03  orderings_time:                         0.
% 2.21/1.03  out_proof_time:                         0.014
% 2.21/1.03  total_time:                             0.132
% 2.21/1.03  num_of_symbols:                         54
% 2.21/1.03  num_of_terms:                           1657
% 2.21/1.03  
% 2.21/1.03  ------ Preprocessing
% 2.21/1.03  
% 2.21/1.03  num_of_splits:                          0
% 2.21/1.03  num_of_split_atoms:                     0
% 2.21/1.03  num_of_reused_defs:                     0
% 2.21/1.03  num_eq_ax_congr_red:                    23
% 2.21/1.03  num_of_sem_filtered_clauses:            1
% 2.21/1.03  num_of_subtypes:                        0
% 2.21/1.03  monotx_restored_types:                  0
% 2.21/1.03  sat_num_of_epr_types:                   0
% 2.21/1.03  sat_num_of_non_cyclic_types:            0
% 2.21/1.03  sat_guarded_non_collapsed_types:        0
% 2.21/1.03  num_pure_diseq_elim:                    0
% 2.21/1.03  simp_replaced_by:                       0
% 2.21/1.03  res_preprocessed:                       102
% 2.21/1.03  prep_upred:                             0
% 2.21/1.03  prep_unflattend:                        39
% 2.21/1.03  smt_new_axioms:                         0
% 2.21/1.03  pred_elim_cands:                        4
% 2.21/1.03  pred_elim:                              9
% 2.21/1.03  pred_elim_cl:                           11
% 2.21/1.03  pred_elim_cycles:                       13
% 2.21/1.03  merged_defs:                            0
% 2.21/1.03  merged_defs_ncl:                        0
% 2.21/1.03  bin_hyper_res:                          0
% 2.21/1.03  prep_cycles:                            4
% 2.21/1.03  pred_elim_time:                         0.028
% 2.21/1.03  splitting_time:                         0.
% 2.21/1.03  sem_filter_time:                        0.
% 2.21/1.03  monotx_time:                            0.
% 2.21/1.03  subtype_inf_time:                       0.
% 2.21/1.03  
% 2.21/1.03  ------ Problem properties
% 2.21/1.03  
% 2.21/1.03  clauses:                                16
% 2.21/1.03  conjectures:                            1
% 2.21/1.03  epr:                                    1
% 2.21/1.03  horn:                                   12
% 2.21/1.03  ground:                                 2
% 2.21/1.03  unary:                                  6
% 2.21/1.03  binary:                                 1
% 2.21/1.03  lits:                                   47
% 2.21/1.03  lits_eq:                                10
% 2.21/1.03  fd_pure:                                0
% 2.21/1.03  fd_pseudo:                              0
% 2.21/1.03  fd_cond:                                0
% 2.21/1.03  fd_pseudo_cond:                         3
% 2.21/1.03  ac_symbols:                             0
% 2.21/1.03  
% 2.21/1.03  ------ Propositional Solver
% 2.21/1.03  
% 2.21/1.03  prop_solver_calls:                      27
% 2.21/1.03  prop_fast_solver_calls:                 973
% 2.21/1.03  smt_solver_calls:                       0
% 2.21/1.03  smt_fast_solver_calls:                  0
% 2.21/1.03  prop_num_of_clauses:                    635
% 2.21/1.03  prop_preprocess_simplified:             3150
% 2.21/1.03  prop_fo_subsumed:                       17
% 2.21/1.03  prop_solver_time:                       0.
% 2.21/1.03  smt_solver_time:                        0.
% 2.21/1.03  smt_fast_solver_time:                   0.
% 2.21/1.03  prop_fast_solver_time:                  0.
% 2.21/1.03  prop_unsat_core_time:                   0.
% 2.21/1.03  
% 2.21/1.03  ------ QBF
% 2.21/1.03  
% 2.21/1.03  qbf_q_res:                              0
% 2.21/1.03  qbf_num_tautologies:                    0
% 2.21/1.03  qbf_prep_cycles:                        0
% 2.21/1.03  
% 2.21/1.03  ------ BMC1
% 2.21/1.03  
% 2.21/1.03  bmc1_current_bound:                     -1
% 2.21/1.03  bmc1_last_solved_bound:                 -1
% 2.21/1.03  bmc1_unsat_core_size:                   -1
% 2.21/1.03  bmc1_unsat_core_parents_size:           -1
% 2.21/1.03  bmc1_merge_next_fun:                    0
% 2.21/1.03  bmc1_unsat_core_clauses_time:           0.
% 2.21/1.03  
% 2.21/1.03  ------ Instantiation
% 2.21/1.03  
% 2.21/1.03  inst_num_of_clauses:                    151
% 2.21/1.03  inst_num_in_passive:                    30
% 2.21/1.03  inst_num_in_active:                     92
% 2.21/1.03  inst_num_in_unprocessed:                29
% 2.21/1.03  inst_num_of_loops:                      100
% 2.21/1.03  inst_num_of_learning_restarts:          0
% 2.21/1.03  inst_num_moves_active_passive:          4
% 2.21/1.03  inst_lit_activity:                      0
% 2.21/1.03  inst_lit_activity_moves:                0
% 2.21/1.03  inst_num_tautologies:                   0
% 2.21/1.03  inst_num_prop_implied:                  0
% 2.21/1.03  inst_num_existing_simplified:           0
% 2.21/1.03  inst_num_eq_res_simplified:             0
% 2.21/1.03  inst_num_child_elim:                    0
% 2.21/1.03  inst_num_of_dismatching_blockings:      16
% 2.21/1.03  inst_num_of_non_proper_insts:           102
% 2.21/1.03  inst_num_of_duplicates:                 0
% 2.21/1.03  inst_inst_num_from_inst_to_res:         0
% 2.21/1.03  inst_dismatching_checking_time:         0.
% 2.21/1.03  
% 2.21/1.03  ------ Resolution
% 2.21/1.03  
% 2.21/1.03  res_num_of_clauses:                     0
% 2.21/1.03  res_num_in_passive:                     0
% 2.21/1.03  res_num_in_active:                      0
% 2.21/1.03  res_num_of_loops:                       106
% 2.21/1.03  res_forward_subset_subsumed:            21
% 2.21/1.03  res_backward_subset_subsumed:           0
% 2.21/1.03  res_forward_subsumed:                   0
% 2.21/1.03  res_backward_subsumed:                  0
% 2.21/1.03  res_forward_subsumption_resolution:     0
% 2.21/1.03  res_backward_subsumption_resolution:    0
% 2.21/1.03  res_clause_to_clause_subsumption:       76
% 2.21/1.03  res_orphan_elimination:                 0
% 2.21/1.03  res_tautology_del:                      10
% 2.21/1.03  res_num_eq_res_simplified:              0
% 2.21/1.03  res_num_sel_changes:                    0
% 2.21/1.03  res_moves_from_active_to_pass:          0
% 2.21/1.03  
% 2.21/1.03  ------ Superposition
% 2.21/1.03  
% 2.21/1.03  sup_time_total:                         0.
% 2.21/1.03  sup_time_generating:                    0.
% 2.21/1.03  sup_time_sim_full:                      0.
% 2.21/1.03  sup_time_sim_immed:                     0.
% 2.21/1.03  
% 2.21/1.03  sup_num_of_clauses:                     21
% 2.21/1.03  sup_num_in_active:                      18
% 2.21/1.03  sup_num_in_passive:                     3
% 2.21/1.03  sup_num_of_loops:                       18
% 2.21/1.03  sup_fw_superposition:                   8
% 2.21/1.03  sup_bw_superposition:                   0
% 2.21/1.03  sup_immediate_simplified:               2
% 2.21/1.03  sup_given_eliminated:                   0
% 2.21/1.03  comparisons_done:                       0
% 2.21/1.03  comparisons_avoided:                    0
% 2.21/1.03  
% 2.21/1.03  ------ Simplifications
% 2.21/1.03  
% 2.21/1.03  
% 2.21/1.03  sim_fw_subset_subsumed:                 1
% 2.21/1.03  sim_bw_subset_subsumed:                 1
% 2.21/1.03  sim_fw_subsumed:                        1
% 2.21/1.03  sim_bw_subsumed:                        0
% 2.21/1.03  sim_fw_subsumption_res:                 1
% 2.21/1.03  sim_bw_subsumption_res:                 0
% 2.21/1.03  sim_tautology_del:                      0
% 2.21/1.03  sim_eq_tautology_del:                   0
% 2.21/1.03  sim_eq_res_simp:                        1
% 2.21/1.03  sim_fw_demodulated:                     1
% 2.21/1.03  sim_bw_demodulated:                     0
% 2.21/1.03  sim_light_normalised:                   12
% 2.21/1.03  sim_joinable_taut:                      0
% 2.21/1.03  sim_joinable_simp:                      0
% 2.21/1.03  sim_ac_normalised:                      0
% 2.21/1.03  sim_smt_subsumption:                    0
% 2.21/1.03  
%------------------------------------------------------------------------------
