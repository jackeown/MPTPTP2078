%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:20:12 EST 2020

% Result     : Theorem 2.73s
% Output     : CNFRefutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 193 expanded)
%              Number of clauses        :   70 (  79 expanded)
%              Number of leaves         :   21 (  37 expanded)
%              Depth                    :   24
%              Number of atoms          :  523 ( 703 expanded)
%              Number of equality atoms :  133 ( 169 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   15 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( r2_hidden(k1_xboole_0,X0)
       => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ( r2_hidden(k1_xboole_0,X0)
         => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f34,plain,(
    ? [X0] :
      ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0))
      & r2_hidden(k1_xboole_0,X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f35,plain,(
    ? [X0] :
      ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0))
      & r2_hidden(k1_xboole_0,X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f48,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0))
        & r2_hidden(k1_xboole_0,X0)
        & ~ v1_xboole_0(X0) )
   => ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK3))
      & r2_hidden(k1_xboole_0,sK3)
      & ~ v1_xboole_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK3))
    & r2_hidden(k1_xboole_0,sK3)
    & ~ v1_xboole_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f35,f48])).

fof(f79,plain,(
    r2_hidden(k1_xboole_0,sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( r1_lattice3(X0,k1_xboole_0,X1)
            & r2_lattice3(X0,k1_xboole_0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r2_lattice3(X0,k1_xboole_0,X1) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_lattice3(X0,k1_xboole_0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r2_lattice3(X0,k1_xboole_0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f71,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f13,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f40])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f41,f42])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).

fof(f50,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f14,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
             => ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f58,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v2_struct_0(X0) )
     => v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f25,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f57,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

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

fof(f44,plain,(
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

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f12,axiom,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v4_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f20,plain,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f72,plain,(
    ! [X0] : v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f9,axiom,(
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

fof(f17,plain,(
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
    inference(rectify,[],[f9])).

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
    inference(ennf_transformation,[],[f17])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f45,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X1,X3)
          & r2_lattice3(X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X1,sK2(X0,X1,X2))
        & r2_lattice3(X0,X2,sK2(X0,X1,X2))
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
                | ( ~ r1_orders_2(X0,X1,sK2(X0,X1,X2))
                  & r2_lattice3(X0,X2,sK2(X0,X1,X2))
                  & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f45])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X2) = X1
      | ~ r1_orders_2(X0,X1,sK2(X0,X1,X2))
      | ~ r2_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f73,plain,(
    ! [X0] : v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X2) = X1
      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
      | ~ r2_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f61,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f80,plain,(
    k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK3)) ),
    inference(cnf_transformation,[],[f49])).

fof(f78,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_29,negated_conjecture,
    ( r2_hidden(k1_xboole_0,sK3) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2536,plain,
    ( r2_hidden(k1_xboole_0,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_6,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2537,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2808,plain,
    ( m1_subset_1(k1_xboole_0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2536,c_2537])).

cnf(c_20,plain,
    ( r2_lattice3(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_21,plain,
    ( l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1069,plain,
    ( r2_lattice3(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | k2_yellow_1(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_21])).

cnf(c_1070,plain,
    ( r2_lattice3(k2_yellow_1(X0),k1_xboole_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) ),
    inference(unflattening,[status(thm)],[c_1069])).

cnf(c_2524,plain,
    ( r2_lattice3(k2_yellow_1(X0),k1_xboole_0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1070])).

cnf(c_25,plain,
    ( u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2578,plain,
    ( r2_lattice3(k2_yellow_1(X0),k1_xboole_0,X1) = iProver_top
    | m1_subset_1(X1,X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2524,c_25])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2540,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2542,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2972,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2540,c_2542])).

cnf(c_26,plain,
    ( r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ r1_tarski(X1,X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_8,plain,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_7,plain,
    ( ~ v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_327,plain,
    ( ~ l1_orders_2(X0)
    | ~ v2_struct_0(X0)
    | v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_8,c_7])).

cnf(c_10,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_23,plain,
    ( v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_345,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | k2_yellow_1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_23])).

cnf(c_346,plain,
    ( r1_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ l1_orders_2(k2_yellow_1(X0))
    | v2_struct_0(k2_yellow_1(X0)) ),
    inference(unflattening,[status(thm)],[c_345])).

cnf(c_350,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
    | r1_orders_2(k2_yellow_1(X0),X1,X2)
    | v2_struct_0(k2_yellow_1(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_346,c_21])).

cnf(c_351,plain,
    ( r1_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | v2_struct_0(k2_yellow_1(X0)) ),
    inference(renaming,[status(thm)],[c_350])).

cnf(c_438,plain,
    ( r1_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ l1_orders_2(X3)
    | v1_xboole_0(u1_struct_0(X3))
    | k2_yellow_1(X0) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_327,c_351])).

cnf(c_439,plain,
    ( r1_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ l1_orders_2(k2_yellow_1(X0))
    | v1_xboole_0(u1_struct_0(k2_yellow_1(X0))) ),
    inference(unflattening,[status(thm)],[c_438])).

cnf(c_443,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
    | r1_orders_2(k2_yellow_1(X0),X1,X2)
    | v1_xboole_0(u1_struct_0(k2_yellow_1(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_439,c_21])).

cnf(c_444,plain,
    ( r1_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | v1_xboole_0(u1_struct_0(k2_yellow_1(X0))) ),
    inference(renaming,[status(thm)],[c_443])).

cnf(c_640,plain,
    ( r1_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ r1_tarski(X1,X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(u1_struct_0(k2_yellow_1(X0))) ),
    inference(resolution,[status(thm)],[c_26,c_444])).

cnf(c_2533,plain,
    ( r1_orders_2(k2_yellow_1(X0),X1,X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(u1_struct_0(k2_yellow_1(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_640])).

cnf(c_2650,plain,
    ( r1_orders_2(k2_yellow_1(X0),X1,X2) = iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2533,c_25])).

cnf(c_15,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK2(X0,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_22,plain,
    ( v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_933,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK2(X0,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2
    | k2_yellow_1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_22])).

cnf(c_934,plain,
    ( ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
    | ~ r1_orders_2(k2_yellow_1(X0),X2,sK2(k2_yellow_1(X0),X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ l1_orders_2(k2_yellow_1(X0))
    | k1_yellow_0(k2_yellow_1(X0),X1) = X2 ),
    inference(unflattening,[status(thm)],[c_933])).

cnf(c_938,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ r1_orders_2(k2_yellow_1(X0),X2,sK2(k2_yellow_1(X0),X2,X1))
    | ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
    | k1_yellow_0(k2_yellow_1(X0),X1) = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_934,c_21])).

cnf(c_939,plain,
    ( ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
    | ~ r1_orders_2(k2_yellow_1(X0),X2,sK2(k2_yellow_1(X0),X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | k1_yellow_0(k2_yellow_1(X0),X1) = X2 ),
    inference(renaming,[status(thm)],[c_938])).

cnf(c_2528,plain,
    ( k1_yellow_0(k2_yellow_1(X0),X1) = X2
    | r2_lattice3(k2_yellow_1(X0),X1,X2) != iProver_top
    | r1_orders_2(k2_yellow_1(X0),X2,sK2(k2_yellow_1(X0),X2,X1)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_939])).

cnf(c_2641,plain,
    ( k1_yellow_0(k2_yellow_1(X0),X1) = X2
    | r2_lattice3(k2_yellow_1(X0),X1,X2) != iProver_top
    | r1_orders_2(k2_yellow_1(X0),X2,sK2(k2_yellow_1(X0),X2,X1)) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2528,c_25])).

cnf(c_3490,plain,
    ( k1_yellow_0(k2_yellow_1(X0),X1) = X2
    | r2_lattice3(k2_yellow_1(X0),X1,X2) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(sK2(k2_yellow_1(X0),X2,X1),X0) != iProver_top
    | r1_tarski(X2,sK2(k2_yellow_1(X0),X2,X1)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2650,c_2641])).

cnf(c_17,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK2(X0,X2,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_885,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK2(X0,X2,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2
    | k2_yellow_1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_22])).

cnf(c_886,plain,
    ( ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | m1_subset_1(sK2(k2_yellow_1(X0),X2,X1),u1_struct_0(k2_yellow_1(X0)))
    | ~ l1_orders_2(k2_yellow_1(X0))
    | k1_yellow_0(k2_yellow_1(X0),X1) = X2 ),
    inference(unflattening,[status(thm)],[c_885])).

cnf(c_890,plain,
    ( m1_subset_1(sK2(k2_yellow_1(X0),X2,X1),u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
    | k1_yellow_0(k2_yellow_1(X0),X1) = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_886,c_21])).

cnf(c_891,plain,
    ( ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | m1_subset_1(sK2(k2_yellow_1(X0),X2,X1),u1_struct_0(k2_yellow_1(X0)))
    | k1_yellow_0(k2_yellow_1(X0),X1) = X2 ),
    inference(renaming,[status(thm)],[c_890])).

cnf(c_2530,plain,
    ( k1_yellow_0(k2_yellow_1(X0),X1) = X2
    | r2_lattice3(k2_yellow_1(X0),X1,X2) != iProver_top
    | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | m1_subset_1(sK2(k2_yellow_1(X0),X2,X1),u1_struct_0(k2_yellow_1(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_891])).

cnf(c_2623,plain,
    ( k1_yellow_0(k2_yellow_1(X0),X1) = X2
    | r2_lattice3(k2_yellow_1(X0),X1,X2) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(sK2(k2_yellow_1(X0),X2,X1),X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2530,c_25])).

cnf(c_4389,plain,
    ( m1_subset_1(X2,X0) != iProver_top
    | r2_lattice3(k2_yellow_1(X0),X1,X2) != iProver_top
    | k1_yellow_0(k2_yellow_1(X0),X1) = X2
    | r1_tarski(X2,sK2(k2_yellow_1(X0),X2,X1)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3490,c_2623])).

cnf(c_4390,plain,
    ( k1_yellow_0(k2_yellow_1(X0),X1) = X2
    | r2_lattice3(k2_yellow_1(X0),X1,X2) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | r1_tarski(X2,sK2(k2_yellow_1(X0),X2,X1)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_4389])).

cnf(c_4398,plain,
    ( k1_yellow_0(k2_yellow_1(X0),X1) = X2
    | r2_lattice3(k2_yellow_1(X0),X1,X2) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2972,c_4390])).

cnf(c_4409,plain,
    ( k1_yellow_0(k2_yellow_1(X0),k1_xboole_0) = X1
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2578,c_4398])).

cnf(c_11,plain,
    ( ~ l1_orders_2(X0)
    | k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1081,plain,
    ( k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0)
    | k2_yellow_1(X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_21])).

cnf(c_1082,plain,
    ( k1_yellow_0(k2_yellow_1(X0),k1_xboole_0) = k3_yellow_0(k2_yellow_1(X0)) ),
    inference(unflattening,[status(thm)],[c_1081])).

cnf(c_4414,plain,
    ( k3_yellow_0(k2_yellow_1(X0)) = X1
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4409,c_1082])).

cnf(c_4537,plain,
    ( k3_yellow_0(k2_yellow_1(sK3)) = k1_xboole_0
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2808,c_4414])).

cnf(c_2127,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2771,plain,
    ( k3_yellow_0(k2_yellow_1(sK3)) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k3_yellow_0(k2_yellow_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_2127])).

cnf(c_2772,plain,
    ( k3_yellow_0(k2_yellow_1(sK3)) != k1_xboole_0
    | k1_xboole_0 = k3_yellow_0(k2_yellow_1(sK3))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2771])).

cnf(c_2126,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2153,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2126])).

cnf(c_5,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_95,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_28,negated_conjecture,
    ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK3)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_30,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_31,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4537,c_2772,c_2153,c_95,c_28,c_31])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:09:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.73/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/0.98  
% 2.73/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.73/0.98  
% 2.73/0.98  ------  iProver source info
% 2.73/0.98  
% 2.73/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.73/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.73/0.98  git: non_committed_changes: false
% 2.73/0.98  git: last_make_outside_of_git: false
% 2.73/0.98  
% 2.73/0.98  ------ 
% 2.73/0.98  
% 2.73/0.98  ------ Input Options
% 2.73/0.98  
% 2.73/0.98  --out_options                           all
% 2.73/0.98  --tptp_safe_out                         true
% 2.73/0.98  --problem_path                          ""
% 2.73/0.98  --include_path                          ""
% 2.73/0.98  --clausifier                            res/vclausify_rel
% 2.73/0.98  --clausifier_options                    --mode clausify
% 2.73/0.98  --stdin                                 false
% 2.73/0.98  --stats_out                             all
% 2.73/0.98  
% 2.73/0.98  ------ General Options
% 2.73/0.98  
% 2.73/0.98  --fof                                   false
% 2.73/0.98  --time_out_real                         305.
% 2.73/0.98  --time_out_virtual                      -1.
% 2.73/0.98  --symbol_type_check                     false
% 2.73/0.98  --clausify_out                          false
% 2.73/0.98  --sig_cnt_out                           false
% 2.73/0.98  --trig_cnt_out                          false
% 2.73/0.98  --trig_cnt_out_tolerance                1.
% 2.73/0.98  --trig_cnt_out_sk_spl                   false
% 2.73/0.98  --abstr_cl_out                          false
% 2.73/0.98  
% 2.73/0.98  ------ Global Options
% 2.73/0.98  
% 2.73/0.98  --schedule                              default
% 2.73/0.98  --add_important_lit                     false
% 2.73/0.98  --prop_solver_per_cl                    1000
% 2.73/0.98  --min_unsat_core                        false
% 2.73/0.98  --soft_assumptions                      false
% 2.73/0.98  --soft_lemma_size                       3
% 2.73/0.98  --prop_impl_unit_size                   0
% 2.73/0.98  --prop_impl_unit                        []
% 2.73/0.98  --share_sel_clauses                     true
% 2.73/0.98  --reset_solvers                         false
% 2.73/0.98  --bc_imp_inh                            [conj_cone]
% 2.73/0.98  --conj_cone_tolerance                   3.
% 2.73/0.98  --extra_neg_conj                        none
% 2.73/0.98  --large_theory_mode                     true
% 2.73/0.98  --prolific_symb_bound                   200
% 2.73/0.98  --lt_threshold                          2000
% 2.73/0.98  --clause_weak_htbl                      true
% 2.73/0.98  --gc_record_bc_elim                     false
% 2.73/0.98  
% 2.73/0.98  ------ Preprocessing Options
% 2.73/0.98  
% 2.73/0.98  --preprocessing_flag                    true
% 2.73/0.98  --time_out_prep_mult                    0.1
% 2.73/0.98  --splitting_mode                        input
% 2.73/0.98  --splitting_grd                         true
% 2.73/0.98  --splitting_cvd                         false
% 2.73/0.98  --splitting_cvd_svl                     false
% 2.73/0.98  --splitting_nvd                         32
% 2.73/0.98  --sub_typing                            true
% 2.73/0.98  --prep_gs_sim                           true
% 2.73/0.98  --prep_unflatten                        true
% 2.73/0.98  --prep_res_sim                          true
% 2.73/0.98  --prep_upred                            true
% 2.73/0.98  --prep_sem_filter                       exhaustive
% 2.73/0.98  --prep_sem_filter_out                   false
% 2.73/0.98  --pred_elim                             true
% 2.73/0.98  --res_sim_input                         true
% 2.73/0.98  --eq_ax_congr_red                       true
% 2.73/0.98  --pure_diseq_elim                       true
% 2.73/0.98  --brand_transform                       false
% 2.73/0.98  --non_eq_to_eq                          false
% 2.73/0.98  --prep_def_merge                        true
% 2.73/0.98  --prep_def_merge_prop_impl              false
% 2.73/0.98  --prep_def_merge_mbd                    true
% 2.73/0.98  --prep_def_merge_tr_red                 false
% 2.73/0.98  --prep_def_merge_tr_cl                  false
% 2.73/0.98  --smt_preprocessing                     true
% 2.73/0.98  --smt_ac_axioms                         fast
% 2.73/0.98  --preprocessed_out                      false
% 2.73/0.98  --preprocessed_stats                    false
% 2.73/0.98  
% 2.73/0.98  ------ Abstraction refinement Options
% 2.73/0.98  
% 2.73/0.98  --abstr_ref                             []
% 2.73/0.98  --abstr_ref_prep                        false
% 2.73/0.98  --abstr_ref_until_sat                   false
% 2.73/0.98  --abstr_ref_sig_restrict                funpre
% 2.73/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.73/0.98  --abstr_ref_under                       []
% 2.73/0.98  
% 2.73/0.98  ------ SAT Options
% 2.73/0.98  
% 2.73/0.98  --sat_mode                              false
% 2.73/0.98  --sat_fm_restart_options                ""
% 2.73/0.98  --sat_gr_def                            false
% 2.73/0.98  --sat_epr_types                         true
% 2.73/0.98  --sat_non_cyclic_types                  false
% 2.73/0.98  --sat_finite_models                     false
% 2.73/0.98  --sat_fm_lemmas                         false
% 2.73/0.98  --sat_fm_prep                           false
% 2.73/0.98  --sat_fm_uc_incr                        true
% 2.73/0.98  --sat_out_model                         small
% 2.73/0.98  --sat_out_clauses                       false
% 2.73/0.98  
% 2.73/0.98  ------ QBF Options
% 2.73/0.98  
% 2.73/0.98  --qbf_mode                              false
% 2.73/0.98  --qbf_elim_univ                         false
% 2.73/0.98  --qbf_dom_inst                          none
% 2.73/0.98  --qbf_dom_pre_inst                      false
% 2.73/0.98  --qbf_sk_in                             false
% 2.73/0.98  --qbf_pred_elim                         true
% 2.73/0.98  --qbf_split                             512
% 2.73/0.98  
% 2.73/0.98  ------ BMC1 Options
% 2.73/0.98  
% 2.73/0.98  --bmc1_incremental                      false
% 2.73/0.98  --bmc1_axioms                           reachable_all
% 2.73/0.98  --bmc1_min_bound                        0
% 2.73/0.98  --bmc1_max_bound                        -1
% 2.73/0.98  --bmc1_max_bound_default                -1
% 2.73/0.98  --bmc1_symbol_reachability              true
% 2.73/0.98  --bmc1_property_lemmas                  false
% 2.73/0.98  --bmc1_k_induction                      false
% 2.73/0.98  --bmc1_non_equiv_states                 false
% 2.73/0.98  --bmc1_deadlock                         false
% 2.73/0.98  --bmc1_ucm                              false
% 2.73/0.98  --bmc1_add_unsat_core                   none
% 2.73/0.98  --bmc1_unsat_core_children              false
% 2.73/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.73/0.98  --bmc1_out_stat                         full
% 2.73/0.98  --bmc1_ground_init                      false
% 2.73/0.98  --bmc1_pre_inst_next_state              false
% 2.73/0.98  --bmc1_pre_inst_state                   false
% 2.73/0.98  --bmc1_pre_inst_reach_state             false
% 2.73/0.98  --bmc1_out_unsat_core                   false
% 2.73/0.98  --bmc1_aig_witness_out                  false
% 2.73/0.98  --bmc1_verbose                          false
% 2.73/0.98  --bmc1_dump_clauses_tptp                false
% 2.73/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.73/0.98  --bmc1_dump_file                        -
% 2.73/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.73/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.73/0.98  --bmc1_ucm_extend_mode                  1
% 2.73/0.98  --bmc1_ucm_init_mode                    2
% 2.73/0.98  --bmc1_ucm_cone_mode                    none
% 2.73/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.73/0.98  --bmc1_ucm_relax_model                  4
% 2.73/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.73/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.73/0.98  --bmc1_ucm_layered_model                none
% 2.73/0.98  --bmc1_ucm_max_lemma_size               10
% 2.73/0.98  
% 2.73/0.98  ------ AIG Options
% 2.73/0.98  
% 2.73/0.98  --aig_mode                              false
% 2.73/0.98  
% 2.73/0.98  ------ Instantiation Options
% 2.73/0.98  
% 2.73/0.98  --instantiation_flag                    true
% 2.73/0.98  --inst_sos_flag                         false
% 2.73/0.98  --inst_sos_phase                        true
% 2.73/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.73/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.73/0.98  --inst_lit_sel_side                     num_symb
% 2.73/0.98  --inst_solver_per_active                1400
% 2.73/0.98  --inst_solver_calls_frac                1.
% 2.73/0.98  --inst_passive_queue_type               priority_queues
% 2.73/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.73/0.98  --inst_passive_queues_freq              [25;2]
% 2.73/0.98  --inst_dismatching                      true
% 2.73/0.98  --inst_eager_unprocessed_to_passive     true
% 2.73/0.98  --inst_prop_sim_given                   true
% 2.73/0.98  --inst_prop_sim_new                     false
% 2.73/0.98  --inst_subs_new                         false
% 2.73/0.98  --inst_eq_res_simp                      false
% 2.73/0.98  --inst_subs_given                       false
% 2.73/0.98  --inst_orphan_elimination               true
% 2.73/0.98  --inst_learning_loop_flag               true
% 2.73/0.98  --inst_learning_start                   3000
% 2.73/0.98  --inst_learning_factor                  2
% 2.73/0.98  --inst_start_prop_sim_after_learn       3
% 2.73/0.98  --inst_sel_renew                        solver
% 2.73/0.98  --inst_lit_activity_flag                true
% 2.73/0.98  --inst_restr_to_given                   false
% 2.73/0.98  --inst_activity_threshold               500
% 2.73/0.98  --inst_out_proof                        true
% 2.73/0.98  
% 2.73/0.98  ------ Resolution Options
% 2.73/0.98  
% 2.73/0.98  --resolution_flag                       true
% 2.73/0.98  --res_lit_sel                           adaptive
% 2.73/0.98  --res_lit_sel_side                      none
% 2.73/0.98  --res_ordering                          kbo
% 2.73/0.98  --res_to_prop_solver                    active
% 2.73/0.98  --res_prop_simpl_new                    false
% 2.73/0.98  --res_prop_simpl_given                  true
% 2.73/0.98  --res_passive_queue_type                priority_queues
% 2.73/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.73/0.98  --res_passive_queues_freq               [15;5]
% 2.73/0.98  --res_forward_subs                      full
% 2.73/0.98  --res_backward_subs                     full
% 2.73/0.98  --res_forward_subs_resolution           true
% 2.73/0.98  --res_backward_subs_resolution          true
% 2.73/0.98  --res_orphan_elimination                true
% 2.73/0.98  --res_time_limit                        2.
% 2.73/0.98  --res_out_proof                         true
% 2.73/0.98  
% 2.73/0.98  ------ Superposition Options
% 2.73/0.98  
% 2.73/0.98  --superposition_flag                    true
% 2.73/0.98  --sup_passive_queue_type                priority_queues
% 2.73/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.73/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.73/0.98  --demod_completeness_check              fast
% 2.73/0.98  --demod_use_ground                      true
% 2.73/0.98  --sup_to_prop_solver                    passive
% 2.73/0.98  --sup_prop_simpl_new                    true
% 2.73/0.98  --sup_prop_simpl_given                  true
% 2.73/0.98  --sup_fun_splitting                     false
% 2.73/0.98  --sup_smt_interval                      50000
% 2.73/0.98  
% 2.73/0.98  ------ Superposition Simplification Setup
% 2.73/0.98  
% 2.73/0.98  --sup_indices_passive                   []
% 2.73/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.73/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/0.98  --sup_full_bw                           [BwDemod]
% 2.73/0.98  --sup_immed_triv                        [TrivRules]
% 2.73/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.73/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/0.98  --sup_immed_bw_main                     []
% 2.73/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.73/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.73/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.73/0.98  
% 2.73/0.98  ------ Combination Options
% 2.73/0.98  
% 2.73/0.98  --comb_res_mult                         3
% 2.73/0.98  --comb_sup_mult                         2
% 2.73/0.98  --comb_inst_mult                        10
% 2.73/0.98  
% 2.73/0.98  ------ Debug Options
% 2.73/0.98  
% 2.73/0.98  --dbg_backtrace                         false
% 2.73/0.98  --dbg_dump_prop_clauses                 false
% 2.73/0.98  --dbg_dump_prop_clauses_file            -
% 2.73/0.98  --dbg_out_stat                          false
% 2.73/0.98  ------ Parsing...
% 2.73/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.73/0.98  
% 2.73/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 2.73/0.98  
% 2.73/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.73/0.98  
% 2.73/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.73/0.98  ------ Proving...
% 2.73/0.98  ------ Problem Properties 
% 2.73/0.98  
% 2.73/0.98  
% 2.73/0.98  clauses                                 24
% 2.73/0.98  conjectures                             3
% 2.73/0.98  EPR                                     6
% 2.73/0.98  Horn                                    16
% 2.73/0.98  unary                                   7
% 2.73/0.98  binary                                  6
% 2.73/0.98  lits                                    66
% 2.73/0.98  lits eq                                 7
% 2.73/0.98  fd_pure                                 0
% 2.73/0.98  fd_pseudo                               0
% 2.73/0.98  fd_cond                                 0
% 2.73/0.98  fd_pseudo_cond                          3
% 2.73/0.98  AC symbols                              0
% 2.73/0.98  
% 2.73/0.98  ------ Schedule dynamic 5 is on 
% 2.73/0.98  
% 2.73/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.73/0.98  
% 2.73/0.98  
% 2.73/0.98  ------ 
% 2.73/0.98  Current options:
% 2.73/0.98  ------ 
% 2.73/0.98  
% 2.73/0.98  ------ Input Options
% 2.73/0.98  
% 2.73/0.98  --out_options                           all
% 2.73/0.98  --tptp_safe_out                         true
% 2.73/0.98  --problem_path                          ""
% 2.73/0.98  --include_path                          ""
% 2.73/0.98  --clausifier                            res/vclausify_rel
% 2.73/0.98  --clausifier_options                    --mode clausify
% 2.73/0.98  --stdin                                 false
% 2.73/0.98  --stats_out                             all
% 2.73/0.98  
% 2.73/0.98  ------ General Options
% 2.73/0.98  
% 2.73/0.98  --fof                                   false
% 2.73/0.98  --time_out_real                         305.
% 2.73/0.98  --time_out_virtual                      -1.
% 2.73/0.98  --symbol_type_check                     false
% 2.73/0.98  --clausify_out                          false
% 2.73/0.98  --sig_cnt_out                           false
% 2.73/0.98  --trig_cnt_out                          false
% 2.73/0.98  --trig_cnt_out_tolerance                1.
% 2.73/0.98  --trig_cnt_out_sk_spl                   false
% 2.73/0.98  --abstr_cl_out                          false
% 2.73/0.98  
% 2.73/0.98  ------ Global Options
% 2.73/0.98  
% 2.73/0.98  --schedule                              default
% 2.73/0.98  --add_important_lit                     false
% 2.73/0.98  --prop_solver_per_cl                    1000
% 2.73/0.98  --min_unsat_core                        false
% 2.73/0.98  --soft_assumptions                      false
% 2.73/0.98  --soft_lemma_size                       3
% 2.73/0.98  --prop_impl_unit_size                   0
% 2.73/0.98  --prop_impl_unit                        []
% 2.73/0.98  --share_sel_clauses                     true
% 2.73/0.98  --reset_solvers                         false
% 2.73/0.98  --bc_imp_inh                            [conj_cone]
% 2.73/0.98  --conj_cone_tolerance                   3.
% 2.73/0.98  --extra_neg_conj                        none
% 2.73/0.98  --large_theory_mode                     true
% 2.73/0.98  --prolific_symb_bound                   200
% 2.73/0.98  --lt_threshold                          2000
% 2.73/0.98  --clause_weak_htbl                      true
% 2.73/0.98  --gc_record_bc_elim                     false
% 2.73/0.98  
% 2.73/0.98  ------ Preprocessing Options
% 2.73/0.98  
% 2.73/0.98  --preprocessing_flag                    true
% 2.73/0.98  --time_out_prep_mult                    0.1
% 2.73/0.98  --splitting_mode                        input
% 2.73/0.98  --splitting_grd                         true
% 2.73/0.98  --splitting_cvd                         false
% 2.73/0.98  --splitting_cvd_svl                     false
% 2.73/0.98  --splitting_nvd                         32
% 2.73/0.98  --sub_typing                            true
% 2.73/0.98  --prep_gs_sim                           true
% 2.73/0.98  --prep_unflatten                        true
% 2.73/0.98  --prep_res_sim                          true
% 2.73/0.98  --prep_upred                            true
% 2.73/0.98  --prep_sem_filter                       exhaustive
% 2.73/0.98  --prep_sem_filter_out                   false
% 2.73/0.98  --pred_elim                             true
% 2.73/0.98  --res_sim_input                         true
% 2.73/0.98  --eq_ax_congr_red                       true
% 2.73/0.98  --pure_diseq_elim                       true
% 2.73/0.98  --brand_transform                       false
% 2.73/0.98  --non_eq_to_eq                          false
% 2.73/0.98  --prep_def_merge                        true
% 2.73/0.98  --prep_def_merge_prop_impl              false
% 2.73/0.98  --prep_def_merge_mbd                    true
% 2.73/0.98  --prep_def_merge_tr_red                 false
% 2.73/0.98  --prep_def_merge_tr_cl                  false
% 2.73/0.98  --smt_preprocessing                     true
% 2.73/0.98  --smt_ac_axioms                         fast
% 2.73/0.98  --preprocessed_out                      false
% 2.73/0.98  --preprocessed_stats                    false
% 2.73/0.98  
% 2.73/0.98  ------ Abstraction refinement Options
% 2.73/0.98  
% 2.73/0.98  --abstr_ref                             []
% 2.73/0.98  --abstr_ref_prep                        false
% 2.73/0.98  --abstr_ref_until_sat                   false
% 2.73/0.98  --abstr_ref_sig_restrict                funpre
% 2.73/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.73/0.98  --abstr_ref_under                       []
% 2.73/0.98  
% 2.73/0.98  ------ SAT Options
% 2.73/0.98  
% 2.73/0.98  --sat_mode                              false
% 2.73/0.98  --sat_fm_restart_options                ""
% 2.73/0.98  --sat_gr_def                            false
% 2.73/0.98  --sat_epr_types                         true
% 2.73/0.98  --sat_non_cyclic_types                  false
% 2.73/0.98  --sat_finite_models                     false
% 2.73/0.98  --sat_fm_lemmas                         false
% 2.73/0.98  --sat_fm_prep                           false
% 2.73/0.98  --sat_fm_uc_incr                        true
% 2.73/0.98  --sat_out_model                         small
% 2.73/0.98  --sat_out_clauses                       false
% 2.73/0.98  
% 2.73/0.98  ------ QBF Options
% 2.73/0.98  
% 2.73/0.98  --qbf_mode                              false
% 2.73/0.98  --qbf_elim_univ                         false
% 2.73/0.98  --qbf_dom_inst                          none
% 2.73/0.98  --qbf_dom_pre_inst                      false
% 2.73/0.98  --qbf_sk_in                             false
% 2.73/0.98  --qbf_pred_elim                         true
% 2.73/0.98  --qbf_split                             512
% 2.73/0.98  
% 2.73/0.98  ------ BMC1 Options
% 2.73/0.98  
% 2.73/0.98  --bmc1_incremental                      false
% 2.73/0.98  --bmc1_axioms                           reachable_all
% 2.73/0.98  --bmc1_min_bound                        0
% 2.73/0.98  --bmc1_max_bound                        -1
% 2.73/0.98  --bmc1_max_bound_default                -1
% 2.73/0.98  --bmc1_symbol_reachability              true
% 2.73/0.98  --bmc1_property_lemmas                  false
% 2.73/0.98  --bmc1_k_induction                      false
% 2.73/0.98  --bmc1_non_equiv_states                 false
% 2.73/0.98  --bmc1_deadlock                         false
% 2.73/0.98  --bmc1_ucm                              false
% 2.73/0.98  --bmc1_add_unsat_core                   none
% 2.73/0.98  --bmc1_unsat_core_children              false
% 2.73/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.73/0.98  --bmc1_out_stat                         full
% 2.73/0.98  --bmc1_ground_init                      false
% 2.73/0.98  --bmc1_pre_inst_next_state              false
% 2.73/0.98  --bmc1_pre_inst_state                   false
% 2.73/0.98  --bmc1_pre_inst_reach_state             false
% 2.73/0.98  --bmc1_out_unsat_core                   false
% 2.73/0.98  --bmc1_aig_witness_out                  false
% 2.73/0.98  --bmc1_verbose                          false
% 2.73/0.98  --bmc1_dump_clauses_tptp                false
% 2.73/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.73/0.98  --bmc1_dump_file                        -
% 2.73/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.73/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.73/0.98  --bmc1_ucm_extend_mode                  1
% 2.73/0.98  --bmc1_ucm_init_mode                    2
% 2.73/0.98  --bmc1_ucm_cone_mode                    none
% 2.73/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.73/0.98  --bmc1_ucm_relax_model                  4
% 2.73/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.73/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.73/0.98  --bmc1_ucm_layered_model                none
% 2.73/0.98  --bmc1_ucm_max_lemma_size               10
% 2.73/0.98  
% 2.73/0.98  ------ AIG Options
% 2.73/0.98  
% 2.73/0.98  --aig_mode                              false
% 2.73/0.98  
% 2.73/0.98  ------ Instantiation Options
% 2.73/0.98  
% 2.73/0.98  --instantiation_flag                    true
% 2.73/0.98  --inst_sos_flag                         false
% 2.73/0.98  --inst_sos_phase                        true
% 2.73/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.73/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.73/0.98  --inst_lit_sel_side                     none
% 2.73/0.98  --inst_solver_per_active                1400
% 2.73/0.98  --inst_solver_calls_frac                1.
% 2.73/0.98  --inst_passive_queue_type               priority_queues
% 2.73/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.73/0.98  --inst_passive_queues_freq              [25;2]
% 2.73/0.98  --inst_dismatching                      true
% 2.73/0.98  --inst_eager_unprocessed_to_passive     true
% 2.73/0.98  --inst_prop_sim_given                   true
% 2.73/0.98  --inst_prop_sim_new                     false
% 2.73/0.98  --inst_subs_new                         false
% 2.73/0.98  --inst_eq_res_simp                      false
% 2.73/0.98  --inst_subs_given                       false
% 2.73/0.98  --inst_orphan_elimination               true
% 2.73/0.98  --inst_learning_loop_flag               true
% 2.73/0.98  --inst_learning_start                   3000
% 2.73/0.98  --inst_learning_factor                  2
% 2.73/0.98  --inst_start_prop_sim_after_learn       3
% 2.73/0.98  --inst_sel_renew                        solver
% 2.73/0.98  --inst_lit_activity_flag                true
% 2.73/0.98  --inst_restr_to_given                   false
% 2.73/0.98  --inst_activity_threshold               500
% 2.73/0.98  --inst_out_proof                        true
% 2.73/0.98  
% 2.73/0.98  ------ Resolution Options
% 2.73/0.98  
% 2.73/0.98  --resolution_flag                       false
% 2.73/0.98  --res_lit_sel                           adaptive
% 2.73/0.98  --res_lit_sel_side                      none
% 2.73/0.98  --res_ordering                          kbo
% 2.73/0.98  --res_to_prop_solver                    active
% 2.73/0.98  --res_prop_simpl_new                    false
% 2.73/0.98  --res_prop_simpl_given                  true
% 2.73/0.98  --res_passive_queue_type                priority_queues
% 2.73/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.73/0.98  --res_passive_queues_freq               [15;5]
% 2.73/0.98  --res_forward_subs                      full
% 2.73/0.98  --res_backward_subs                     full
% 2.73/0.98  --res_forward_subs_resolution           true
% 2.73/0.98  --res_backward_subs_resolution          true
% 2.73/0.98  --res_orphan_elimination                true
% 2.73/0.98  --res_time_limit                        2.
% 2.73/0.98  --res_out_proof                         true
% 2.73/0.98  
% 2.73/0.98  ------ Superposition Options
% 2.73/0.98  
% 2.73/0.98  --superposition_flag                    true
% 2.73/0.98  --sup_passive_queue_type                priority_queues
% 2.73/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.73/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.73/0.98  --demod_completeness_check              fast
% 2.73/0.98  --demod_use_ground                      true
% 2.73/0.98  --sup_to_prop_solver                    passive
% 2.73/0.98  --sup_prop_simpl_new                    true
% 2.73/0.98  --sup_prop_simpl_given                  true
% 2.73/0.98  --sup_fun_splitting                     false
% 2.73/0.98  --sup_smt_interval                      50000
% 2.73/0.98  
% 2.73/0.98  ------ Superposition Simplification Setup
% 2.73/0.98  
% 2.73/0.98  --sup_indices_passive                   []
% 2.73/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.73/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/0.98  --sup_full_bw                           [BwDemod]
% 2.73/0.98  --sup_immed_triv                        [TrivRules]
% 2.73/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.73/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/0.98  --sup_immed_bw_main                     []
% 2.73/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.73/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.73/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.73/0.98  
% 2.73/0.98  ------ Combination Options
% 2.73/0.98  
% 2.73/0.98  --comb_res_mult                         3
% 2.73/0.98  --comb_sup_mult                         2
% 2.73/0.98  --comb_inst_mult                        10
% 2.73/0.98  
% 2.73/0.98  ------ Debug Options
% 2.73/0.98  
% 2.73/0.98  --dbg_backtrace                         false
% 2.73/0.98  --dbg_dump_prop_clauses                 false
% 2.73/0.98  --dbg_dump_prop_clauses_file            -
% 2.73/0.98  --dbg_out_stat                          false
% 2.73/0.98  
% 2.73/0.98  
% 2.73/0.98  
% 2.73/0.98  
% 2.73/0.98  ------ Proving...
% 2.73/0.98  
% 2.73/0.98  
% 2.73/0.98  % SZS status Theorem for theBenchmark.p
% 2.73/0.98  
% 2.73/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.73/0.98  
% 2.73/0.98  fof(f15,conjecture,(
% 2.73/0.98    ! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k1_xboole_0,X0) => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))))),
% 2.73/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/0.98  
% 2.73/0.98  fof(f16,negated_conjecture,(
% 2.73/0.98    ~! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k1_xboole_0,X0) => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))))),
% 2.73/0.98    inference(negated_conjecture,[],[f15])).
% 2.73/0.98  
% 2.73/0.98  fof(f34,plain,(
% 2.73/0.98    ? [X0] : ((k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0)) & r2_hidden(k1_xboole_0,X0)) & ~v1_xboole_0(X0))),
% 2.73/0.98    inference(ennf_transformation,[],[f16])).
% 2.73/0.98  
% 2.73/0.98  fof(f35,plain,(
% 2.73/0.98    ? [X0] : (k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0)) & r2_hidden(k1_xboole_0,X0) & ~v1_xboole_0(X0))),
% 2.73/0.98    inference(flattening,[],[f34])).
% 2.73/0.98  
% 2.73/0.98  fof(f48,plain,(
% 2.73/0.98    ? [X0] : (k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0)) & r2_hidden(k1_xboole_0,X0) & ~v1_xboole_0(X0)) => (k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK3)) & r2_hidden(k1_xboole_0,sK3) & ~v1_xboole_0(sK3))),
% 2.73/0.98    introduced(choice_axiom,[])).
% 2.73/0.98  
% 2.73/0.98  fof(f49,plain,(
% 2.73/0.98    k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK3)) & r2_hidden(k1_xboole_0,sK3) & ~v1_xboole_0(sK3)),
% 2.73/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f35,f48])).
% 2.73/0.98  
% 2.73/0.98  fof(f79,plain,(
% 2.73/0.98    r2_hidden(k1_xboole_0,sK3)),
% 2.73/0.98    inference(cnf_transformation,[],[f49])).
% 2.73/0.98  
% 2.73/0.98  fof(f4,axiom,(
% 2.73/0.98    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 2.73/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/0.98  
% 2.73/0.98  fof(f23,plain,(
% 2.73/0.98    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 2.73/0.98    inference(ennf_transformation,[],[f4])).
% 2.73/0.98  
% 2.73/0.98  fof(f56,plain,(
% 2.73/0.98    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 2.73/0.98    inference(cnf_transformation,[],[f23])).
% 2.73/0.98  
% 2.73/0.98  fof(f10,axiom,(
% 2.73/0.98    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (r1_lattice3(X0,k1_xboole_0,X1) & r2_lattice3(X0,k1_xboole_0,X1))))),
% 2.73/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/0.98  
% 2.73/0.98  fof(f21,plain,(
% 2.73/0.98    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r2_lattice3(X0,k1_xboole_0,X1)))),
% 2.73/0.98    inference(pure_predicate_removal,[],[f10])).
% 2.73/0.98  
% 2.73/0.98  fof(f32,plain,(
% 2.73/0.98    ! [X0] : (! [X1] : (r2_lattice3(X0,k1_xboole_0,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.73/0.98    inference(ennf_transformation,[],[f21])).
% 2.73/0.98  
% 2.73/0.98  fof(f70,plain,(
% 2.73/0.98    ( ! [X0,X1] : (r2_lattice3(X0,k1_xboole_0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.73/0.98    inference(cnf_transformation,[],[f32])).
% 2.73/0.98  
% 2.73/0.98  fof(f11,axiom,(
% 2.73/0.98    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 2.73/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/0.98  
% 2.73/0.98  fof(f19,plain,(
% 2.73/0.98    ! [X0] : l1_orders_2(k2_yellow_1(X0))),
% 2.73/0.98    inference(pure_predicate_removal,[],[f11])).
% 2.73/0.98  
% 2.73/0.98  fof(f71,plain,(
% 2.73/0.98    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 2.73/0.98    inference(cnf_transformation,[],[f19])).
% 2.73/0.98  
% 2.73/0.98  fof(f13,axiom,(
% 2.73/0.98    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 2.73/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/0.98  
% 2.73/0.98  fof(f74,plain,(
% 2.73/0.98    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 2.73/0.98    inference(cnf_transformation,[],[f13])).
% 2.73/0.98  
% 2.73/0.98  fof(f2,axiom,(
% 2.73/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.73/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/0.98  
% 2.73/0.98  fof(f22,plain,(
% 2.73/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.73/0.98    inference(ennf_transformation,[],[f2])).
% 2.73/0.98  
% 2.73/0.98  fof(f40,plain,(
% 2.73/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.73/0.98    inference(nnf_transformation,[],[f22])).
% 2.73/0.98  
% 2.73/0.98  fof(f41,plain,(
% 2.73/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.73/0.98    inference(rectify,[],[f40])).
% 2.73/0.98  
% 2.73/0.98  fof(f42,plain,(
% 2.73/0.98    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 2.73/0.98    introduced(choice_axiom,[])).
% 2.73/0.98  
% 2.73/0.98  fof(f43,plain,(
% 2.73/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.73/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f41,f42])).
% 2.73/0.98  
% 2.73/0.98  fof(f53,plain,(
% 2.73/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 2.73/0.98    inference(cnf_transformation,[],[f43])).
% 2.73/0.98  
% 2.73/0.98  fof(f1,axiom,(
% 2.73/0.98    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.73/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/0.98  
% 2.73/0.98  fof(f36,plain,(
% 2.73/0.98    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.73/0.98    inference(nnf_transformation,[],[f1])).
% 2.73/0.98  
% 2.73/0.98  fof(f37,plain,(
% 2.73/0.98    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.73/0.98    inference(rectify,[],[f36])).
% 2.73/0.98  
% 2.73/0.98  fof(f38,plain,(
% 2.73/0.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.73/0.98    introduced(choice_axiom,[])).
% 2.73/0.98  
% 2.73/0.98  fof(f39,plain,(
% 2.73/0.98    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.73/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).
% 2.73/0.98  
% 2.73/0.98  fof(f50,plain,(
% 2.73/0.98    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.73/0.98    inference(cnf_transformation,[],[f39])).
% 2.73/0.98  
% 2.73/0.98  fof(f14,axiom,(
% 2.73/0.98    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)))))),
% 2.73/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/0.98  
% 2.73/0.98  fof(f33,plain,(
% 2.73/0.98    ! [X0] : (! [X1] : (! [X2] : ((r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 2.73/0.98    inference(ennf_transformation,[],[f14])).
% 2.73/0.98  
% 2.73/0.98  fof(f47,plain,(
% 2.73/0.98    ! [X0] : (! [X1] : (! [X2] : (((r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2)) & (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 2.73/0.98    inference(nnf_transformation,[],[f33])).
% 2.73/0.98  
% 2.73/0.98  fof(f77,plain,(
% 2.73/0.98    ( ! [X2,X0,X1] : (r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 2.73/0.98    inference(cnf_transformation,[],[f47])).
% 2.73/0.98  
% 2.73/0.98  fof(f6,axiom,(
% 2.73/0.98    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 2.73/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/0.98  
% 2.73/0.98  fof(f26,plain,(
% 2.73/0.98    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 2.73/0.98    inference(ennf_transformation,[],[f6])).
% 2.73/0.98  
% 2.73/0.98  fof(f58,plain,(
% 2.73/0.98    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 2.73/0.98    inference(cnf_transformation,[],[f26])).
% 2.73/0.98  
% 2.73/0.98  fof(f5,axiom,(
% 2.73/0.98    ! [X0] : ((l1_struct_0(X0) & v2_struct_0(X0)) => v1_xboole_0(u1_struct_0(X0)))),
% 2.73/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/0.98  
% 2.73/0.98  fof(f24,plain,(
% 2.73/0.98    ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v2_struct_0(X0)))),
% 2.73/0.98    inference(ennf_transformation,[],[f5])).
% 2.73/0.98  
% 2.73/0.98  fof(f25,plain,(
% 2.73/0.98    ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v2_struct_0(X0))),
% 2.73/0.98    inference(flattening,[],[f24])).
% 2.73/0.98  
% 2.73/0.98  fof(f57,plain,(
% 2.73/0.98    ( ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v2_struct_0(X0)) )),
% 2.73/0.98    inference(cnf_transformation,[],[f25])).
% 2.73/0.98  
% 2.73/0.98  fof(f7,axiom,(
% 2.73/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 2.73/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/0.98  
% 2.73/0.98  fof(f27,plain,(
% 2.73/0.98    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.73/0.98    inference(ennf_transformation,[],[f7])).
% 2.73/0.98  
% 2.73/0.98  fof(f28,plain,(
% 2.73/0.98    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.73/0.98    inference(flattening,[],[f27])).
% 2.73/0.98  
% 2.73/0.98  fof(f44,plain,(
% 2.73/0.98    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.73/0.98    inference(nnf_transformation,[],[f28])).
% 2.73/0.98  
% 2.73/0.98  fof(f59,plain,(
% 2.73/0.98    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.73/0.98    inference(cnf_transformation,[],[f44])).
% 2.73/0.98  
% 2.73/0.98  fof(f12,axiom,(
% 2.73/0.98    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v4_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 2.73/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/0.98  
% 2.73/0.98  fof(f18,plain,(
% 2.73/0.98    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 2.73/0.98    inference(pure_predicate_removal,[],[f12])).
% 2.73/0.98  
% 2.73/0.98  fof(f20,plain,(
% 2.73/0.98    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)))),
% 2.73/0.98    inference(pure_predicate_removal,[],[f18])).
% 2.73/0.98  
% 2.73/0.98  fof(f72,plain,(
% 2.73/0.98    ( ! [X0] : (v3_orders_2(k2_yellow_1(X0))) )),
% 2.73/0.98    inference(cnf_transformation,[],[f20])).
% 2.73/0.98  
% 2.73/0.98  fof(f9,axiom,(
% 2.73/0.98    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1)) => (r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1)) & ((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1))))))),
% 2.73/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/0.98  
% 2.73/0.98  fof(f17,plain,(
% 2.73/0.98    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1)) => (r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1)) & ((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) => (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X4) => r1_orders_2(X0,X1,X4))) & r2_lattice3(X0,X2,X1))))))),
% 2.73/0.98    inference(rectify,[],[f9])).
% 2.73/0.98  
% 2.73/0.98  fof(f30,plain,(
% 2.73/0.98    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | (? [X3] : ((~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3)) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1))) & ((! [X4] : ((r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | (~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0)))),
% 2.73/0.98    inference(ennf_transformation,[],[f17])).
% 2.73/0.98  
% 2.73/0.98  fof(f31,plain,(
% 2.73/0.98    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | ? [X3] : (~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | ~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 2.73/0.98    inference(flattening,[],[f30])).
% 2.73/0.98  
% 2.73/0.98  fof(f45,plain,(
% 2.73/0.98    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X1,sK2(X0,X1,X2)) & r2_lattice3(X0,X2,sK2(X0,X1,X2)) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))))),
% 2.73/0.98    introduced(choice_axiom,[])).
% 2.73/0.98  
% 2.73/0.98  fof(f46,plain,(
% 2.73/0.98    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | (~r1_orders_2(X0,X1,sK2(X0,X1,X2)) & r2_lattice3(X0,X2,sK2(X0,X1,X2)) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | ~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 2.73/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f45])).
% 2.73/0.98  
% 2.73/0.98  fof(f66,plain,(
% 2.73/0.98    ( ! [X2,X0,X1] : (k1_yellow_0(X0,X2) = X1 | ~r1_orders_2(X0,X1,sK2(X0,X1,X2)) | ~r2_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 2.73/0.98    inference(cnf_transformation,[],[f46])).
% 2.73/0.98  
% 2.73/0.98  fof(f73,plain,(
% 2.73/0.98    ( ! [X0] : (v5_orders_2(k2_yellow_1(X0))) )),
% 2.73/0.98    inference(cnf_transformation,[],[f20])).
% 2.73/0.98  
% 2.73/0.98  fof(f64,plain,(
% 2.73/0.98    ( ! [X2,X0,X1] : (k1_yellow_0(X0,X2) = X1 | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) | ~r2_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 2.73/0.98    inference(cnf_transformation,[],[f46])).
% 2.73/0.98  
% 2.73/0.98  fof(f8,axiom,(
% 2.73/0.98    ! [X0] : (l1_orders_2(X0) => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0))),
% 2.73/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/0.98  
% 2.73/0.98  fof(f29,plain,(
% 2.73/0.98    ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0))),
% 2.73/0.98    inference(ennf_transformation,[],[f8])).
% 2.73/0.98  
% 2.73/0.98  fof(f61,plain,(
% 2.73/0.98    ( ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0)) )),
% 2.73/0.98    inference(cnf_transformation,[],[f29])).
% 2.73/0.98  
% 2.73/0.98  fof(f3,axiom,(
% 2.73/0.98    v1_xboole_0(k1_xboole_0)),
% 2.73/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/0.98  
% 2.73/0.98  fof(f55,plain,(
% 2.73/0.98    v1_xboole_0(k1_xboole_0)),
% 2.73/0.98    inference(cnf_transformation,[],[f3])).
% 2.73/0.98  
% 2.73/0.98  fof(f80,plain,(
% 2.73/0.98    k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK3))),
% 2.73/0.98    inference(cnf_transformation,[],[f49])).
% 2.73/0.98  
% 2.73/0.98  fof(f78,plain,(
% 2.73/0.98    ~v1_xboole_0(sK3)),
% 2.73/0.98    inference(cnf_transformation,[],[f49])).
% 2.73/0.98  
% 2.73/0.98  cnf(c_29,negated_conjecture,
% 2.73/0.98      ( r2_hidden(k1_xboole_0,sK3) ),
% 2.73/0.98      inference(cnf_transformation,[],[f79]) ).
% 2.73/0.98  
% 2.73/0.98  cnf(c_2536,plain,
% 2.73/0.98      ( r2_hidden(k1_xboole_0,sK3) = iProver_top ),
% 2.73/0.98      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.73/0.98  
% 2.73/0.98  cnf(c_6,plain,
% 2.73/0.98      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 2.73/0.98      inference(cnf_transformation,[],[f56]) ).
% 2.73/0.98  
% 2.73/0.98  cnf(c_2537,plain,
% 2.73/0.98      ( m1_subset_1(X0,X1) = iProver_top
% 2.73/0.98      | r2_hidden(X0,X1) != iProver_top ),
% 2.73/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.73/0.98  
% 2.73/0.98  cnf(c_2808,plain,
% 2.73/0.98      ( m1_subset_1(k1_xboole_0,sK3) = iProver_top ),
% 2.73/0.98      inference(superposition,[status(thm)],[c_2536,c_2537]) ).
% 2.73/0.98  
% 2.73/0.98  cnf(c_20,plain,
% 2.73/0.98      ( r2_lattice3(X0,k1_xboole_0,X1)
% 2.73/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.73/0.98      | ~ l1_orders_2(X0) ),
% 2.73/0.98      inference(cnf_transformation,[],[f70]) ).
% 2.73/0.98  
% 2.73/0.98  cnf(c_21,plain,
% 2.73/0.98      ( l1_orders_2(k2_yellow_1(X0)) ),
% 2.73/0.98      inference(cnf_transformation,[],[f71]) ).
% 2.73/0.98  
% 2.73/0.98  cnf(c_1069,plain,
% 2.73/0.98      ( r2_lattice3(X0,k1_xboole_0,X1)
% 2.73/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.73/0.98      | k2_yellow_1(X2) != X0 ),
% 2.73/0.98      inference(resolution_lifted,[status(thm)],[c_20,c_21]) ).
% 2.73/0.98  
% 2.73/0.98  cnf(c_1070,plain,
% 2.73/0.98      ( r2_lattice3(k2_yellow_1(X0),k1_xboole_0,X1)
% 2.73/0.98      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) ),
% 2.73/0.98      inference(unflattening,[status(thm)],[c_1069]) ).
% 2.73/0.98  
% 2.73/0.98  cnf(c_2524,plain,
% 2.73/0.98      ( r2_lattice3(k2_yellow_1(X0),k1_xboole_0,X1) = iProver_top
% 2.73/0.98      | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top ),
% 2.73/0.98      inference(predicate_to_equality,[status(thm)],[c_1070]) ).
% 2.73/0.98  
% 2.73/0.98  cnf(c_25,plain,
% 2.73/0.98      ( u1_struct_0(k2_yellow_1(X0)) = X0 ),
% 2.73/0.98      inference(cnf_transformation,[],[f74]) ).
% 2.73/0.98  
% 2.73/0.98  cnf(c_2578,plain,
% 2.73/0.98      ( r2_lattice3(k2_yellow_1(X0),k1_xboole_0,X1) = iProver_top
% 2.73/0.98      | m1_subset_1(X1,X0) != iProver_top ),
% 2.73/0.98      inference(light_normalisation,[status(thm)],[c_2524,c_25]) ).
% 2.73/0.98  
% 2.73/0.98  cnf(c_3,plain,
% 2.73/0.98      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 2.73/0.98      inference(cnf_transformation,[],[f53]) ).
% 2.73/0.98  
% 2.73/0.98  cnf(c_2540,plain,
% 2.73/0.98      ( r1_tarski(X0,X1) = iProver_top
% 2.73/0.98      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 2.73/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.73/0.98  
% 2.73/0.98  cnf(c_1,plain,
% 2.73/0.98      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.73/0.98      inference(cnf_transformation,[],[f50]) ).
% 2.73/0.98  
% 2.73/0.98  cnf(c_2542,plain,
% 2.73/0.98      ( r2_hidden(X0,X1) != iProver_top
% 2.73/0.98      | v1_xboole_0(X1) != iProver_top ),
% 2.73/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.73/0.98  
% 2.73/0.98  cnf(c_2972,plain,
% 2.73/0.98      ( r1_tarski(X0,X1) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 2.73/0.98      inference(superposition,[status(thm)],[c_2540,c_2542]) ).
% 2.73/0.98  
% 2.73/0.98  cnf(c_26,plain,
% 2.73/0.98      ( r3_orders_2(k2_yellow_1(X0),X1,X2)
% 2.73/0.98      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.73/0.98      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.73/0.98      | ~ r1_tarski(X1,X2)
% 2.73/0.98      | v1_xboole_0(X0) ),
% 2.73/0.98      inference(cnf_transformation,[],[f77]) ).
% 2.73/0.98  
% 2.73/0.98  cnf(c_8,plain,
% 2.73/0.98      ( ~ l1_orders_2(X0) | l1_struct_0(X0) ),
% 2.73/0.98      inference(cnf_transformation,[],[f58]) ).
% 2.73/0.98  
% 2.73/0.98  cnf(c_7,plain,
% 2.73/0.98      ( ~ v2_struct_0(X0)
% 2.73/0.98      | ~ l1_struct_0(X0)
% 2.73/0.98      | v1_xboole_0(u1_struct_0(X0)) ),
% 2.73/0.98      inference(cnf_transformation,[],[f57]) ).
% 2.73/0.98  
% 2.73/0.98  cnf(c_327,plain,
% 2.73/0.98      ( ~ l1_orders_2(X0)
% 2.73/0.98      | ~ v2_struct_0(X0)
% 2.73/0.98      | v1_xboole_0(u1_struct_0(X0)) ),
% 2.73/0.98      inference(resolution,[status(thm)],[c_8,c_7]) ).
% 2.73/0.98  
% 2.73/0.98  cnf(c_10,plain,
% 2.73/0.98      ( r1_orders_2(X0,X1,X2)
% 2.73/0.98      | ~ r3_orders_2(X0,X1,X2)
% 2.73/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.73/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.73/0.98      | ~ v3_orders_2(X0)
% 2.73/0.98      | ~ l1_orders_2(X0)
% 2.73/0.98      | v2_struct_0(X0) ),
% 2.73/0.98      inference(cnf_transformation,[],[f59]) ).
% 2.73/0.98  
% 2.73/0.98  cnf(c_23,plain,
% 2.73/0.98      ( v3_orders_2(k2_yellow_1(X0)) ),
% 2.73/0.98      inference(cnf_transformation,[],[f72]) ).
% 2.73/0.98  
% 2.73/0.98  cnf(c_345,plain,
% 2.73/0.98      ( r1_orders_2(X0,X1,X2)
% 2.73/0.98      | ~ r3_orders_2(X0,X1,X2)
% 2.73/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.73/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.73/0.98      | ~ l1_orders_2(X0)
% 2.73/0.98      | v2_struct_0(X0)
% 2.73/0.98      | k2_yellow_1(X3) != X0 ),
% 2.73/0.98      inference(resolution_lifted,[status(thm)],[c_10,c_23]) ).
% 2.73/0.98  
% 2.73/0.98  cnf(c_346,plain,
% 2.73/0.98      ( r1_orders_2(k2_yellow_1(X0),X1,X2)
% 2.73/0.98      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
% 2.73/0.98      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.73/0.98      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.73/0.98      | ~ l1_orders_2(k2_yellow_1(X0))
% 2.73/0.98      | v2_struct_0(k2_yellow_1(X0)) ),
% 2.73/0.98      inference(unflattening,[status(thm)],[c_345]) ).
% 2.73/0.98  
% 2.73/0.98  cnf(c_350,plain,
% 2.73/0.98      ( ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.73/0.98      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.73/0.98      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
% 2.73/0.98      | r1_orders_2(k2_yellow_1(X0),X1,X2)
% 2.73/0.98      | v2_struct_0(k2_yellow_1(X0)) ),
% 2.73/0.98      inference(global_propositional_subsumption,
% 2.73/0.98                [status(thm)],
% 2.73/0.98                [c_346,c_21]) ).
% 2.73/0.98  
% 2.73/0.98  cnf(c_351,plain,
% 2.73/0.98      ( r1_orders_2(k2_yellow_1(X0),X1,X2)
% 2.73/0.98      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
% 2.73/0.98      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.73/0.98      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.73/0.98      | v2_struct_0(k2_yellow_1(X0)) ),
% 2.73/0.98      inference(renaming,[status(thm)],[c_350]) ).
% 2.73/0.98  
% 2.73/0.98  cnf(c_438,plain,
% 2.73/0.98      ( r1_orders_2(k2_yellow_1(X0),X1,X2)
% 2.73/0.98      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
% 2.73/0.98      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.73/0.98      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.73/0.98      | ~ l1_orders_2(X3)
% 2.73/0.98      | v1_xboole_0(u1_struct_0(X3))
% 2.73/0.98      | k2_yellow_1(X0) != X3 ),
% 2.73/0.98      inference(resolution_lifted,[status(thm)],[c_327,c_351]) ).
% 2.73/0.98  
% 2.73/0.98  cnf(c_439,plain,
% 2.73/0.98      ( r1_orders_2(k2_yellow_1(X0),X1,X2)
% 2.73/0.98      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
% 2.73/0.98      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.73/0.98      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.73/0.98      | ~ l1_orders_2(k2_yellow_1(X0))
% 2.73/0.98      | v1_xboole_0(u1_struct_0(k2_yellow_1(X0))) ),
% 2.73/0.98      inference(unflattening,[status(thm)],[c_438]) ).
% 2.73/0.98  
% 2.73/0.98  cnf(c_443,plain,
% 2.73/0.98      ( ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.73/0.98      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.73/0.98      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
% 2.73/0.98      | r1_orders_2(k2_yellow_1(X0),X1,X2)
% 2.73/0.98      | v1_xboole_0(u1_struct_0(k2_yellow_1(X0))) ),
% 2.73/0.98      inference(global_propositional_subsumption,
% 2.73/0.98                [status(thm)],
% 2.73/0.98                [c_439,c_21]) ).
% 2.73/0.98  
% 2.73/0.98  cnf(c_444,plain,
% 2.73/0.98      ( r1_orders_2(k2_yellow_1(X0),X1,X2)
% 2.73/0.98      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
% 2.73/0.98      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.73/0.98      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.73/0.98      | v1_xboole_0(u1_struct_0(k2_yellow_1(X0))) ),
% 2.73/0.98      inference(renaming,[status(thm)],[c_443]) ).
% 2.73/0.98  
% 2.73/0.98  cnf(c_640,plain,
% 2.73/0.98      ( r1_orders_2(k2_yellow_1(X0),X1,X2)
% 2.73/0.98      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.73/0.98      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.73/0.98      | ~ r1_tarski(X1,X2)
% 2.73/0.98      | v1_xboole_0(X0)
% 2.73/0.98      | v1_xboole_0(u1_struct_0(k2_yellow_1(X0))) ),
% 2.73/0.98      inference(resolution,[status(thm)],[c_26,c_444]) ).
% 2.73/0.98  
% 2.73/0.98  cnf(c_2533,plain,
% 2.73/0.98      ( r1_orders_2(k2_yellow_1(X0),X1,X2) = iProver_top
% 2.73/0.98      | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 2.73/0.98      | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 2.73/0.98      | r1_tarski(X1,X2) != iProver_top
% 2.73/0.98      | v1_xboole_0(X0) = iProver_top
% 2.73/0.98      | v1_xboole_0(u1_struct_0(k2_yellow_1(X0))) = iProver_top ),
% 2.73/0.98      inference(predicate_to_equality,[status(thm)],[c_640]) ).
% 2.73/0.98  
% 2.73/0.98  cnf(c_2650,plain,
% 2.73/0.98      ( r1_orders_2(k2_yellow_1(X0),X1,X2) = iProver_top
% 2.73/0.98      | m1_subset_1(X1,X0) != iProver_top
% 2.73/0.98      | m1_subset_1(X2,X0) != iProver_top
% 2.73/0.98      | r1_tarski(X1,X2) != iProver_top
% 2.73/0.98      | v1_xboole_0(X0) = iProver_top ),
% 2.73/0.98      inference(light_normalisation,[status(thm)],[c_2533,c_25]) ).
% 2.73/0.98  
% 2.73/0.98  cnf(c_15,plain,
% 2.73/0.98      ( ~ r2_lattice3(X0,X1,X2)
% 2.73/0.98      | ~ r1_orders_2(X0,X2,sK2(X0,X2,X1))
% 2.73/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.73/0.98      | ~ v5_orders_2(X0)
% 2.73/0.98      | ~ l1_orders_2(X0)
% 2.73/0.98      | k1_yellow_0(X0,X1) = X2 ),
% 2.73/0.98      inference(cnf_transformation,[],[f66]) ).
% 2.73/0.98  
% 2.73/0.98  cnf(c_22,plain,
% 2.73/0.98      ( v5_orders_2(k2_yellow_1(X0)) ),
% 2.73/0.98      inference(cnf_transformation,[],[f73]) ).
% 2.73/0.98  
% 2.73/0.98  cnf(c_933,plain,
% 2.73/0.98      ( ~ r2_lattice3(X0,X1,X2)
% 2.73/0.98      | ~ r1_orders_2(X0,X2,sK2(X0,X2,X1))
% 2.73/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.73/0.98      | ~ l1_orders_2(X0)
% 2.73/0.98      | k1_yellow_0(X0,X1) = X2
% 2.73/0.98      | k2_yellow_1(X3) != X0 ),
% 2.73/0.98      inference(resolution_lifted,[status(thm)],[c_15,c_22]) ).
% 2.73/0.98  
% 2.73/0.98  cnf(c_934,plain,
% 2.73/0.98      ( ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
% 2.73/0.98      | ~ r1_orders_2(k2_yellow_1(X0),X2,sK2(k2_yellow_1(X0),X2,X1))
% 2.73/0.98      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.73/0.98      | ~ l1_orders_2(k2_yellow_1(X0))
% 2.73/0.98      | k1_yellow_0(k2_yellow_1(X0),X1) = X2 ),
% 2.73/0.98      inference(unflattening,[status(thm)],[c_933]) ).
% 2.73/0.98  
% 2.73/0.98  cnf(c_938,plain,
% 2.73/0.98      ( ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.73/0.98      | ~ r1_orders_2(k2_yellow_1(X0),X2,sK2(k2_yellow_1(X0),X2,X1))
% 2.73/0.98      | ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
% 2.73/0.98      | k1_yellow_0(k2_yellow_1(X0),X1) = X2 ),
% 2.73/0.98      inference(global_propositional_subsumption,
% 2.73/0.98                [status(thm)],
% 2.73/0.98                [c_934,c_21]) ).
% 2.73/0.98  
% 2.73/0.98  cnf(c_939,plain,
% 2.73/0.98      ( ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
% 2.73/0.98      | ~ r1_orders_2(k2_yellow_1(X0),X2,sK2(k2_yellow_1(X0),X2,X1))
% 2.73/0.98      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.73/0.98      | k1_yellow_0(k2_yellow_1(X0),X1) = X2 ),
% 2.73/0.98      inference(renaming,[status(thm)],[c_938]) ).
% 2.73/0.98  
% 2.73/0.98  cnf(c_2528,plain,
% 2.73/0.98      ( k1_yellow_0(k2_yellow_1(X0),X1) = X2
% 2.73/0.98      | r2_lattice3(k2_yellow_1(X0),X1,X2) != iProver_top
% 2.73/0.98      | r1_orders_2(k2_yellow_1(X0),X2,sK2(k2_yellow_1(X0),X2,X1)) != iProver_top
% 2.73/0.98      | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top ),
% 2.73/0.98      inference(predicate_to_equality,[status(thm)],[c_939]) ).
% 2.73/0.98  
% 2.73/0.98  cnf(c_2641,plain,
% 2.73/0.98      ( k1_yellow_0(k2_yellow_1(X0),X1) = X2
% 2.73/0.98      | r2_lattice3(k2_yellow_1(X0),X1,X2) != iProver_top
% 2.73/0.98      | r1_orders_2(k2_yellow_1(X0),X2,sK2(k2_yellow_1(X0),X2,X1)) != iProver_top
% 2.73/0.98      | m1_subset_1(X2,X0) != iProver_top ),
% 2.73/0.98      inference(light_normalisation,[status(thm)],[c_2528,c_25]) ).
% 2.73/0.98  
% 2.73/0.98  cnf(c_3490,plain,
% 2.73/0.98      ( k1_yellow_0(k2_yellow_1(X0),X1) = X2
% 2.73/0.98      | r2_lattice3(k2_yellow_1(X0),X1,X2) != iProver_top
% 2.73/0.98      | m1_subset_1(X2,X0) != iProver_top
% 2.73/0.98      | m1_subset_1(sK2(k2_yellow_1(X0),X2,X1),X0) != iProver_top
% 2.73/0.98      | r1_tarski(X2,sK2(k2_yellow_1(X0),X2,X1)) != iProver_top
% 2.73/0.98      | v1_xboole_0(X0) = iProver_top ),
% 2.73/0.98      inference(superposition,[status(thm)],[c_2650,c_2641]) ).
% 2.73/0.98  
% 2.73/0.98  cnf(c_17,plain,
% 2.73/0.98      ( ~ r2_lattice3(X0,X1,X2)
% 2.73/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.73/0.98      | m1_subset_1(sK2(X0,X2,X1),u1_struct_0(X0))
% 2.73/0.98      | ~ v5_orders_2(X0)
% 2.73/0.98      | ~ l1_orders_2(X0)
% 2.73/0.98      | k1_yellow_0(X0,X1) = X2 ),
% 2.73/0.98      inference(cnf_transformation,[],[f64]) ).
% 2.73/0.98  
% 2.73/0.98  cnf(c_885,plain,
% 2.73/0.98      ( ~ r2_lattice3(X0,X1,X2)
% 2.73/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.73/0.98      | m1_subset_1(sK2(X0,X2,X1),u1_struct_0(X0))
% 2.73/0.98      | ~ l1_orders_2(X0)
% 2.73/0.98      | k1_yellow_0(X0,X1) = X2
% 2.73/0.98      | k2_yellow_1(X3) != X0 ),
% 2.73/0.98      inference(resolution_lifted,[status(thm)],[c_17,c_22]) ).
% 2.73/0.98  
% 2.73/0.98  cnf(c_886,plain,
% 2.73/0.98      ( ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
% 2.73/0.98      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.73/0.98      | m1_subset_1(sK2(k2_yellow_1(X0),X2,X1),u1_struct_0(k2_yellow_1(X0)))
% 2.73/0.98      | ~ l1_orders_2(k2_yellow_1(X0))
% 2.73/0.98      | k1_yellow_0(k2_yellow_1(X0),X1) = X2 ),
% 2.73/0.98      inference(unflattening,[status(thm)],[c_885]) ).
% 2.73/0.98  
% 2.73/0.98  cnf(c_890,plain,
% 2.73/0.98      ( m1_subset_1(sK2(k2_yellow_1(X0),X2,X1),u1_struct_0(k2_yellow_1(X0)))
% 2.73/0.98      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.73/0.98      | ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
% 2.73/0.98      | k1_yellow_0(k2_yellow_1(X0),X1) = X2 ),
% 2.73/0.98      inference(global_propositional_subsumption,
% 2.73/0.98                [status(thm)],
% 2.73/0.98                [c_886,c_21]) ).
% 2.73/0.98  
% 2.73/0.98  cnf(c_891,plain,
% 2.73/0.98      ( ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
% 2.73/0.98      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.73/0.98      | m1_subset_1(sK2(k2_yellow_1(X0),X2,X1),u1_struct_0(k2_yellow_1(X0)))
% 2.73/0.98      | k1_yellow_0(k2_yellow_1(X0),X1) = X2 ),
% 2.73/0.98      inference(renaming,[status(thm)],[c_890]) ).
% 2.73/0.98  
% 2.73/0.98  cnf(c_2530,plain,
% 2.73/0.98      ( k1_yellow_0(k2_yellow_1(X0),X1) = X2
% 2.73/0.98      | r2_lattice3(k2_yellow_1(X0),X1,X2) != iProver_top
% 2.73/0.98      | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 2.73/0.98      | m1_subset_1(sK2(k2_yellow_1(X0),X2,X1),u1_struct_0(k2_yellow_1(X0))) = iProver_top ),
% 2.73/0.98      inference(predicate_to_equality,[status(thm)],[c_891]) ).
% 2.73/0.98  
% 2.73/0.98  cnf(c_2623,plain,
% 2.73/0.98      ( k1_yellow_0(k2_yellow_1(X0),X1) = X2
% 2.73/0.98      | r2_lattice3(k2_yellow_1(X0),X1,X2) != iProver_top
% 2.73/0.98      | m1_subset_1(X2,X0) != iProver_top
% 2.73/0.98      | m1_subset_1(sK2(k2_yellow_1(X0),X2,X1),X0) = iProver_top ),
% 2.73/0.98      inference(light_normalisation,[status(thm)],[c_2530,c_25]) ).
% 2.73/0.98  
% 2.73/0.98  cnf(c_4389,plain,
% 2.73/0.98      ( m1_subset_1(X2,X0) != iProver_top
% 2.73/0.98      | r2_lattice3(k2_yellow_1(X0),X1,X2) != iProver_top
% 2.73/0.98      | k1_yellow_0(k2_yellow_1(X0),X1) = X2
% 2.73/0.98      | r1_tarski(X2,sK2(k2_yellow_1(X0),X2,X1)) != iProver_top
% 2.73/0.98      | v1_xboole_0(X0) = iProver_top ),
% 2.73/0.98      inference(global_propositional_subsumption,
% 2.73/0.98                [status(thm)],
% 2.73/0.98                [c_3490,c_2623]) ).
% 2.73/0.98  
% 2.73/0.98  cnf(c_4390,plain,
% 2.73/0.98      ( k1_yellow_0(k2_yellow_1(X0),X1) = X2
% 2.73/0.98      | r2_lattice3(k2_yellow_1(X0),X1,X2) != iProver_top
% 2.73/0.98      | m1_subset_1(X2,X0) != iProver_top
% 2.73/0.98      | r1_tarski(X2,sK2(k2_yellow_1(X0),X2,X1)) != iProver_top
% 2.73/0.98      | v1_xboole_0(X0) = iProver_top ),
% 2.73/0.98      inference(renaming,[status(thm)],[c_4389]) ).
% 2.73/0.98  
% 2.73/0.98  cnf(c_4398,plain,
% 2.73/0.98      ( k1_yellow_0(k2_yellow_1(X0),X1) = X2
% 2.73/0.98      | r2_lattice3(k2_yellow_1(X0),X1,X2) != iProver_top
% 2.73/0.98      | m1_subset_1(X2,X0) != iProver_top
% 2.73/0.98      | v1_xboole_0(X2) != iProver_top
% 2.73/0.98      | v1_xboole_0(X0) = iProver_top ),
% 2.73/0.98      inference(superposition,[status(thm)],[c_2972,c_4390]) ).
% 2.73/0.98  
% 2.73/0.98  cnf(c_4409,plain,
% 2.73/0.98      ( k1_yellow_0(k2_yellow_1(X0),k1_xboole_0) = X1
% 2.73/0.98      | m1_subset_1(X1,X0) != iProver_top
% 2.73/0.98      | v1_xboole_0(X1) != iProver_top
% 2.73/0.98      | v1_xboole_0(X0) = iProver_top ),
% 2.73/0.98      inference(superposition,[status(thm)],[c_2578,c_4398]) ).
% 2.73/0.98  
% 2.73/0.98  cnf(c_11,plain,
% 2.73/0.98      ( ~ l1_orders_2(X0)
% 2.73/0.98      | k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0) ),
% 2.73/0.98      inference(cnf_transformation,[],[f61]) ).
% 2.73/0.98  
% 2.73/0.98  cnf(c_1081,plain,
% 2.73/0.98      ( k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0)
% 2.73/0.98      | k2_yellow_1(X1) != X0 ),
% 2.73/0.98      inference(resolution_lifted,[status(thm)],[c_11,c_21]) ).
% 2.73/0.98  
% 2.73/0.98  cnf(c_1082,plain,
% 2.73/0.98      ( k1_yellow_0(k2_yellow_1(X0),k1_xboole_0) = k3_yellow_0(k2_yellow_1(X0)) ),
% 2.73/0.98      inference(unflattening,[status(thm)],[c_1081]) ).
% 2.73/0.98  
% 2.73/0.98  cnf(c_4414,plain,
% 2.73/0.98      ( k3_yellow_0(k2_yellow_1(X0)) = X1
% 2.73/0.98      | m1_subset_1(X1,X0) != iProver_top
% 2.73/0.98      | v1_xboole_0(X1) != iProver_top
% 2.73/0.98      | v1_xboole_0(X0) = iProver_top ),
% 2.73/0.98      inference(demodulation,[status(thm)],[c_4409,c_1082]) ).
% 2.73/0.98  
% 2.73/0.98  cnf(c_4537,plain,
% 2.73/0.98      ( k3_yellow_0(k2_yellow_1(sK3)) = k1_xboole_0
% 2.73/0.98      | v1_xboole_0(sK3) = iProver_top
% 2.73/0.98      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.73/0.98      inference(superposition,[status(thm)],[c_2808,c_4414]) ).
% 2.73/0.98  
% 2.73/0.98  cnf(c_2127,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.73/0.98  
% 2.73/0.98  cnf(c_2771,plain,
% 2.73/0.98      ( k3_yellow_0(k2_yellow_1(sK3)) != X0
% 2.73/0.98      | k1_xboole_0 != X0
% 2.73/0.98      | k1_xboole_0 = k3_yellow_0(k2_yellow_1(sK3)) ),
% 2.73/0.98      inference(instantiation,[status(thm)],[c_2127]) ).
% 2.73/0.98  
% 2.73/0.98  cnf(c_2772,plain,
% 2.73/0.98      ( k3_yellow_0(k2_yellow_1(sK3)) != k1_xboole_0
% 2.73/0.98      | k1_xboole_0 = k3_yellow_0(k2_yellow_1(sK3))
% 2.73/0.98      | k1_xboole_0 != k1_xboole_0 ),
% 2.73/0.98      inference(instantiation,[status(thm)],[c_2771]) ).
% 2.73/0.98  
% 2.73/0.98  cnf(c_2126,plain,( X0 = X0 ),theory(equality) ).
% 2.73/0.98  
% 2.73/0.98  cnf(c_2153,plain,
% 2.73/0.98      ( k1_xboole_0 = k1_xboole_0 ),
% 2.73/0.98      inference(instantiation,[status(thm)],[c_2126]) ).
% 2.73/0.98  
% 2.73/0.98  cnf(c_5,plain,
% 2.73/0.98      ( v1_xboole_0(k1_xboole_0) ),
% 2.73/0.98      inference(cnf_transformation,[],[f55]) ).
% 2.73/0.98  
% 2.73/0.98  cnf(c_95,plain,
% 2.73/0.98      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.73/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.73/0.98  
% 2.73/0.98  cnf(c_28,negated_conjecture,
% 2.73/0.98      ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK3)) ),
% 2.73/0.98      inference(cnf_transformation,[],[f80]) ).
% 2.73/0.98  
% 2.73/0.98  cnf(c_30,negated_conjecture,
% 2.73/0.98      ( ~ v1_xboole_0(sK3) ),
% 2.73/0.98      inference(cnf_transformation,[],[f78]) ).
% 2.73/0.98  
% 2.73/0.98  cnf(c_31,plain,
% 2.73/0.98      ( v1_xboole_0(sK3) != iProver_top ),
% 2.73/0.98      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.73/0.98  
% 2.73/0.98  cnf(contradiction,plain,
% 2.73/0.98      ( $false ),
% 2.73/0.98      inference(minisat,
% 2.73/0.98                [status(thm)],
% 2.73/0.98                [c_4537,c_2772,c_2153,c_95,c_28,c_31]) ).
% 2.73/0.98  
% 2.73/0.98  
% 2.73/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.73/0.98  
% 2.73/0.98  ------                               Statistics
% 2.73/0.98  
% 2.73/0.98  ------ General
% 2.73/0.98  
% 2.73/0.98  abstr_ref_over_cycles:                  0
% 2.73/0.98  abstr_ref_under_cycles:                 0
% 2.73/0.98  gc_basic_clause_elim:                   0
% 2.73/0.98  forced_gc_time:                         0
% 2.73/0.98  parsing_time:                           0.01
% 2.73/0.98  unif_index_cands_time:                  0.
% 2.73/0.98  unif_index_add_time:                    0.
% 2.73/0.98  orderings_time:                         0.
% 2.73/0.98  out_proof_time:                         0.022
% 2.73/0.98  total_time:                             0.202
% 2.73/0.98  num_of_symbols:                         55
% 2.73/0.98  num_of_terms:                           2602
% 2.73/0.98  
% 2.73/0.98  ------ Preprocessing
% 2.73/0.98  
% 2.73/0.98  num_of_splits:                          0
% 2.73/0.98  num_of_split_atoms:                     0
% 2.73/0.98  num_of_reused_defs:                     0
% 2.73/0.98  num_eq_ax_congr_red:                    36
% 2.73/0.98  num_of_sem_filtered_clauses:            1
% 2.73/0.98  num_of_subtypes:                        0
% 2.73/0.98  monotx_restored_types:                  0
% 2.73/0.98  sat_num_of_epr_types:                   0
% 2.73/0.98  sat_num_of_non_cyclic_types:            0
% 2.73/0.98  sat_guarded_non_collapsed_types:        0
% 2.73/0.98  num_pure_diseq_elim:                    0
% 2.73/0.98  simp_replaced_by:                       0
% 2.73/0.98  res_preprocessed:                       132
% 2.73/0.98  prep_upred:                             0
% 2.73/0.98  prep_unflattend:                        52
% 2.73/0.98  smt_new_axioms:                         0
% 2.73/0.98  pred_elim_cands:                        7
% 2.73/0.98  pred_elim:                              6
% 2.73/0.98  pred_elim_cl:                           7
% 2.73/0.98  pred_elim_cycles:                       13
% 2.73/0.98  merged_defs:                            0
% 2.73/0.98  merged_defs_ncl:                        0
% 2.73/0.98  bin_hyper_res:                          0
% 2.73/0.98  prep_cycles:                            4
% 2.73/0.98  pred_elim_time:                         0.046
% 2.73/0.98  splitting_time:                         0.
% 2.73/0.98  sem_filter_time:                        0.
% 2.73/0.98  monotx_time:                            0.001
% 2.73/0.98  subtype_inf_time:                       0.
% 2.73/0.98  
% 2.73/0.98  ------ Problem properties
% 2.73/0.98  
% 2.73/0.98  clauses:                                24
% 2.73/0.98  conjectures:                            3
% 2.73/0.98  epr:                                    6
% 2.73/0.98  horn:                                   16
% 2.73/0.98  ground:                                 4
% 2.73/0.98  unary:                                  7
% 2.73/0.98  binary:                                 6
% 2.73/0.98  lits:                                   66
% 2.73/0.98  lits_eq:                                7
% 2.73/0.98  fd_pure:                                0
% 2.73/0.98  fd_pseudo:                              0
% 2.73/0.98  fd_cond:                                0
% 2.73/0.98  fd_pseudo_cond:                         3
% 2.73/0.98  ac_symbols:                             0
% 2.73/0.98  
% 2.73/0.98  ------ Propositional Solver
% 2.73/0.98  
% 2.73/0.98  prop_solver_calls:                      28
% 2.73/0.98  prop_fast_solver_calls:                 1316
% 2.73/0.98  smt_solver_calls:                       0
% 2.73/0.98  smt_fast_solver_calls:                  0
% 2.73/0.98  prop_num_of_clauses:                    1126
% 2.73/0.98  prop_preprocess_simplified:             4905
% 2.73/0.98  prop_fo_subsumed:                       14
% 2.73/0.98  prop_solver_time:                       0.
% 2.73/0.98  smt_solver_time:                        0.
% 2.73/0.98  smt_fast_solver_time:                   0.
% 2.73/0.98  prop_fast_solver_time:                  0.
% 2.73/0.98  prop_unsat_core_time:                   0.
% 2.73/0.98  
% 2.73/0.98  ------ QBF
% 2.73/0.98  
% 2.73/0.98  qbf_q_res:                              0
% 2.73/0.98  qbf_num_tautologies:                    0
% 2.73/0.98  qbf_prep_cycles:                        0
% 2.73/0.98  
% 2.73/0.98  ------ BMC1
% 2.73/0.98  
% 2.73/0.98  bmc1_current_bound:                     -1
% 2.73/0.98  bmc1_last_solved_bound:                 -1
% 2.73/0.98  bmc1_unsat_core_size:                   -1
% 2.73/0.98  bmc1_unsat_core_parents_size:           -1
% 2.73/0.98  bmc1_merge_next_fun:                    0
% 2.73/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.73/0.98  
% 2.73/0.98  ------ Instantiation
% 2.73/0.98  
% 2.73/0.98  inst_num_of_clauses:                    320
% 2.73/0.98  inst_num_in_passive:                    65
% 2.73/0.98  inst_num_in_active:                     195
% 2.73/0.98  inst_num_in_unprocessed:                60
% 2.73/0.98  inst_num_of_loops:                      200
% 2.73/0.98  inst_num_of_learning_restarts:          0
% 2.73/0.98  inst_num_moves_active_passive:          1
% 2.73/0.98  inst_lit_activity:                      0
% 2.73/0.98  inst_lit_activity_moves:                0
% 2.73/0.98  inst_num_tautologies:                   0
% 2.73/0.98  inst_num_prop_implied:                  0
% 2.73/0.98  inst_num_existing_simplified:           0
% 2.73/0.98  inst_num_eq_res_simplified:             0
% 2.73/0.98  inst_num_child_elim:                    0
% 2.73/0.98  inst_num_of_dismatching_blockings:      33
% 2.73/0.98  inst_num_of_non_proper_insts:           277
% 2.73/0.98  inst_num_of_duplicates:                 0
% 2.73/0.98  inst_inst_num_from_inst_to_res:         0
% 2.73/0.98  inst_dismatching_checking_time:         0.
% 2.73/0.98  
% 2.73/0.98  ------ Resolution
% 2.73/0.98  
% 2.73/0.98  res_num_of_clauses:                     0
% 2.73/0.98  res_num_in_passive:                     0
% 2.73/0.98  res_num_in_active:                      0
% 2.73/0.98  res_num_of_loops:                       136
% 2.73/0.98  res_forward_subset_subsumed:            48
% 2.73/0.98  res_backward_subset_subsumed:           0
% 2.73/0.98  res_forward_subsumed:                   0
% 2.73/0.98  res_backward_subsumed:                  0
% 2.73/0.98  res_forward_subsumption_resolution:     0
% 2.73/0.98  res_backward_subsumption_resolution:    0
% 2.73/0.98  res_clause_to_clause_subsumption:       200
% 2.73/0.98  res_orphan_elimination:                 0
% 2.73/0.98  res_tautology_del:                      25
% 2.73/0.98  res_num_eq_res_simplified:              0
% 2.73/0.98  res_num_sel_changes:                    0
% 2.73/0.98  res_moves_from_active_to_pass:          0
% 2.73/0.98  
% 2.73/0.98  ------ Superposition
% 2.73/0.98  
% 2.73/0.98  sup_time_total:                         0.
% 2.73/0.98  sup_time_generating:                    0.
% 2.73/0.98  sup_time_sim_full:                      0.
% 2.73/0.98  sup_time_sim_immed:                     0.
% 2.73/0.98  
% 2.73/0.98  sup_num_of_clauses:                     48
% 2.73/0.98  sup_num_in_active:                      39
% 2.73/0.98  sup_num_in_passive:                     9
% 2.73/0.98  sup_num_of_loops:                       38
% 2.73/0.98  sup_fw_superposition:                   26
% 2.73/0.98  sup_bw_superposition:                   15
% 2.73/0.98  sup_immediate_simplified:               10
% 2.73/0.98  sup_given_eliminated:                   0
% 2.73/0.98  comparisons_done:                       0
% 2.73/0.98  comparisons_avoided:                    0
% 2.73/0.98  
% 2.73/0.98  ------ Simplifications
% 2.73/0.98  
% 2.73/0.98  
% 2.73/0.98  sim_fw_subset_subsumed:                 1
% 2.73/0.98  sim_bw_subset_subsumed:                 0
% 2.73/0.98  sim_fw_subsumed:                        5
% 2.73/0.98  sim_bw_subsumed:                        0
% 2.73/0.98  sim_fw_subsumption_res:                 4
% 2.73/0.98  sim_bw_subsumption_res:                 0
% 2.73/0.98  sim_tautology_del:                      7
% 2.73/0.98  sim_eq_tautology_del:                   2
% 2.73/0.98  sim_eq_res_simp:                        0
% 2.73/0.98  sim_fw_demodulated:                     1
% 2.73/0.98  sim_bw_demodulated:                     0
% 2.73/0.98  sim_light_normalised:                   18
% 2.73/0.98  sim_joinable_taut:                      0
% 2.73/0.98  sim_joinable_simp:                      0
% 2.73/0.98  sim_ac_normalised:                      0
% 2.73/0.98  sim_smt_subsumption:                    0
% 2.73/0.98  
%------------------------------------------------------------------------------
