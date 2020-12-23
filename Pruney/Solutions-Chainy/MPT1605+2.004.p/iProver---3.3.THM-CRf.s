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
% DateTime   : Thu Dec  3 12:20:12 EST 2020

% Result     : Theorem 2.62s
% Output     : CNFRefutation 2.62s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 190 expanded)
%              Number of clauses        :   72 (  83 expanded)
%              Number of leaves         :   20 (  38 expanded)
%              Depth                    :   21
%              Number of atoms          :  524 ( 706 expanded)
%              Number of equality atoms :  148 ( 191 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   15 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f31,plain,(
    ? [X0] :
      ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0))
      & r2_hidden(k1_xboole_0,X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f32,plain,(
    ? [X0] :
      ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0))
      & r2_hidden(k1_xboole_0,X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f45,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0))
        & r2_hidden(k1_xboole_0,X0)
        & ~ v1_xboole_0(X0) )
   => ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK3))
      & r2_hidden(k1_xboole_0,sK3)
      & ~ v1_xboole_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK3))
    & r2_hidden(k1_xboole_0,sK3)
    & ~ v1_xboole_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f45])).

fof(f76,plain,(
    r2_hidden(k1_xboole_0,sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f24])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f39,plain,(
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
    inference(rectify,[],[f38])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK1(X0,X1,X2),X2)
        & r2_hidden(sK1(X0,X1,X2),X1)
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f39,f40])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | r2_hidden(sK1(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f67,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f12,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f33])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).

fof(f47,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

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

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

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
    inference(nnf_transformation,[],[f23])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f10,axiom,(
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
    inference(pure_predicate_removal,[],[f10])).

fof(f18,plain,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f68,plain,(
    ! [X0] : v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f11,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_orders_2(k2_yellow_1(X0))
        & ~ v2_struct_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ~ v2_struct_0(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k2_yellow_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k2_yellow_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

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

fof(f27,plain,(
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

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X1,X3)
          & r2_lattice3(X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X1,sK2(X0,X1,X2))
        & r2_lattice3(X0,X2,sK2(X0,X1,X2))
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f28,f42])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X2) = X1
      | ~ r1_orders_2(X0,X1,sK2(X0,X1,X2))
      | ~ r2_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f69,plain,(
    ! [X0] : v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X2) = X1
      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
      | ~ r2_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f58,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f77,plain,(
    k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK3)) ),
    inference(cnf_transformation,[],[f46])).

fof(f75,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_29,negated_conjecture,
    ( r2_hidden(k1_xboole_0,sK3) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_3366,plain,
    ( r2_hidden(k1_xboole_0,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_4,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_3367,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3676,plain,
    ( m1_subset_1(k1_xboole_0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3366,c_3367])).

cnf(c_8,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK1(X0,X1,X2),X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_20,plain,
    ( l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1162,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK1(X0,X1,X2),X1)
    | k2_yellow_1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_20])).

cnf(c_1163,plain,
    ( r2_lattice3(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | r2_hidden(sK1(k2_yellow_1(X0),X1,X2),X1) ),
    inference(unflattening,[status(thm)],[c_1162])).

cnf(c_3352,plain,
    ( r2_lattice3(k2_yellow_1(X0),X1,X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | r2_hidden(sK1(k2_yellow_1(X0),X1,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1163])).

cnf(c_25,plain,
    ( u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_3400,plain,
    ( r2_lattice3(k2_yellow_1(X0),X1,X2) = iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | r2_hidden(sK1(k2_yellow_1(X0),X1,X2),X1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3352,c_25])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_3370,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3751,plain,
    ( r2_lattice3(k2_yellow_1(X0),X1,X2) = iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3400,c_3370])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_3368,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_26,plain,
    ( r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ r1_tarski(X1,X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_6,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_22,plain,
    ( v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_384,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | k2_yellow_1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_22])).

cnf(c_385,plain,
    ( r1_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | v2_struct_0(k2_yellow_1(X0))
    | ~ l1_orders_2(k2_yellow_1(X0)) ),
    inference(unflattening,[status(thm)],[c_384])).

cnf(c_389,plain,
    ( v2_struct_0(k2_yellow_1(X0))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
    | r1_orders_2(k2_yellow_1(X0),X1,X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_385,c_20])).

cnf(c_390,plain,
    ( r1_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | v2_struct_0(k2_yellow_1(X0)) ),
    inference(renaming,[status(thm)],[c_389])).

cnf(c_23,plain,
    ( ~ v2_struct_0(k2_yellow_1(X0))
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_468,plain,
    ( r1_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | v1_xboole_0(X0) ),
    inference(resolution,[status(thm)],[c_390,c_23])).

cnf(c_517,plain,
    ( r1_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ r1_tarski(X1,X2)
    | v1_xboole_0(X0) ),
    inference(resolution,[status(thm)],[c_26,c_468])).

cnf(c_3363,plain,
    ( r1_orders_2(k2_yellow_1(X0),X1,X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_517])).

cnf(c_3482,plain,
    ( r1_orders_2(k2_yellow_1(X0),X1,X2) = iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3363,c_25])).

cnf(c_15,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK2(X0,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_21,plain,
    ( v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_986,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK2(X0,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2
    | k2_yellow_1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_21])).

cnf(c_987,plain,
    ( ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
    | ~ r1_orders_2(k2_yellow_1(X0),X2,sK2(k2_yellow_1(X0),X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ l1_orders_2(k2_yellow_1(X0))
    | k1_yellow_0(k2_yellow_1(X0),X1) = X2 ),
    inference(unflattening,[status(thm)],[c_986])).

cnf(c_991,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ r1_orders_2(k2_yellow_1(X0),X2,sK2(k2_yellow_1(X0),X2,X1))
    | ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
    | k1_yellow_0(k2_yellow_1(X0),X1) = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_987,c_20])).

cnf(c_992,plain,
    ( ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
    | ~ r1_orders_2(k2_yellow_1(X0),X2,sK2(k2_yellow_1(X0),X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | k1_yellow_0(k2_yellow_1(X0),X1) = X2 ),
    inference(renaming,[status(thm)],[c_991])).

cnf(c_3358,plain,
    ( k1_yellow_0(k2_yellow_1(X0),X1) = X2
    | r2_lattice3(k2_yellow_1(X0),X1,X2) != iProver_top
    | r1_orders_2(k2_yellow_1(X0),X2,sK2(k2_yellow_1(X0),X2,X1)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_992])).

cnf(c_3473,plain,
    ( k1_yellow_0(k2_yellow_1(X0),X1) = X2
    | r2_lattice3(k2_yellow_1(X0),X1,X2) != iProver_top
    | r1_orders_2(k2_yellow_1(X0),X2,sK2(k2_yellow_1(X0),X2,X1)) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3358,c_25])).

cnf(c_4362,plain,
    ( k1_yellow_0(k2_yellow_1(X0),X1) = X2
    | r2_lattice3(k2_yellow_1(X0),X1,X2) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(sK2(k2_yellow_1(X0),X2,X1),X0) != iProver_top
    | r1_tarski(X2,sK2(k2_yellow_1(X0),X2,X1)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3482,c_3473])).

cnf(c_17,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK2(X0,X2,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_938,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK2(X0,X2,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2
    | k2_yellow_1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_21])).

cnf(c_939,plain,
    ( ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | m1_subset_1(sK2(k2_yellow_1(X0),X2,X1),u1_struct_0(k2_yellow_1(X0)))
    | ~ l1_orders_2(k2_yellow_1(X0))
    | k1_yellow_0(k2_yellow_1(X0),X1) = X2 ),
    inference(unflattening,[status(thm)],[c_938])).

cnf(c_943,plain,
    ( m1_subset_1(sK2(k2_yellow_1(X0),X2,X1),u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
    | k1_yellow_0(k2_yellow_1(X0),X1) = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_939,c_20])).

cnf(c_944,plain,
    ( ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | m1_subset_1(sK2(k2_yellow_1(X0),X2,X1),u1_struct_0(k2_yellow_1(X0)))
    | k1_yellow_0(k2_yellow_1(X0),X1) = X2 ),
    inference(renaming,[status(thm)],[c_943])).

cnf(c_3360,plain,
    ( k1_yellow_0(k2_yellow_1(X0),X1) = X2
    | r2_lattice3(k2_yellow_1(X0),X1,X2) != iProver_top
    | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | m1_subset_1(sK2(k2_yellow_1(X0),X2,X1),u1_struct_0(k2_yellow_1(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_944])).

cnf(c_3455,plain,
    ( k1_yellow_0(k2_yellow_1(X0),X1) = X2
    | r2_lattice3(k2_yellow_1(X0),X1,X2) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(sK2(k2_yellow_1(X0),X2,X1),X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3360,c_25])).

cnf(c_6482,plain,
    ( m1_subset_1(X2,X0) != iProver_top
    | r2_lattice3(k2_yellow_1(X0),X1,X2) != iProver_top
    | k1_yellow_0(k2_yellow_1(X0),X1) = X2
    | r1_tarski(X2,sK2(k2_yellow_1(X0),X2,X1)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4362,c_3455])).

cnf(c_6483,plain,
    ( k1_yellow_0(k2_yellow_1(X0),X1) = X2
    | r2_lattice3(k2_yellow_1(X0),X1,X2) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | r1_tarski(X2,sK2(k2_yellow_1(X0),X2,X1)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_6482])).

cnf(c_6491,plain,
    ( k1_yellow_0(k2_yellow_1(X0),X1) = k1_xboole_0
    | r2_lattice3(k2_yellow_1(X0),X1,k1_xboole_0) != iProver_top
    | m1_subset_1(k1_xboole_0,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3368,c_6483])).

cnf(c_6584,plain,
    ( k1_yellow_0(k2_yellow_1(X0),X1) = k1_xboole_0
    | m1_subset_1(k1_xboole_0,X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3751,c_6491])).

cnf(c_6591,plain,
    ( k1_yellow_0(k2_yellow_1(sK3),X0) = k1_xboole_0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3676,c_6584])).

cnf(c_6593,plain,
    ( k1_yellow_0(k2_yellow_1(sK3),k1_xboole_0) = k1_xboole_0
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6591])).

cnf(c_2929,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_4463,plain,
    ( k1_yellow_0(k2_yellow_1(sK3),k1_xboole_0) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK3),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2929])).

cnf(c_4464,plain,
    ( k1_yellow_0(k2_yellow_1(sK3),k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK3),k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4463])).

cnf(c_3610,plain,
    ( k3_yellow_0(k2_yellow_1(sK3)) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k3_yellow_0(k2_yellow_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_2929])).

cnf(c_4134,plain,
    ( k3_yellow_0(k2_yellow_1(sK3)) != k1_yellow_0(k2_yellow_1(sK3),k1_xboole_0)
    | k1_xboole_0 != k1_yellow_0(k2_yellow_1(sK3),k1_xboole_0)
    | k1_xboole_0 = k3_yellow_0(k2_yellow_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_3610])).

cnf(c_11,plain,
    ( ~ l1_orders_2(X0)
    | k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1122,plain,
    ( k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0)
    | k2_yellow_1(X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_20])).

cnf(c_1123,plain,
    ( k1_yellow_0(k2_yellow_1(X0),k1_xboole_0) = k3_yellow_0(k2_yellow_1(X0)) ),
    inference(unflattening,[status(thm)],[c_1122])).

cnf(c_3935,plain,
    ( k1_yellow_0(k2_yellow_1(sK3),k1_xboole_0) = k3_yellow_0(k2_yellow_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_1123])).

cnf(c_3657,plain,
    ( X0 != X1
    | k3_yellow_0(k2_yellow_1(sK3)) != X1
    | k3_yellow_0(k2_yellow_1(sK3)) = X0 ),
    inference(instantiation,[status(thm)],[c_2929])).

cnf(c_3782,plain,
    ( X0 != k3_yellow_0(k2_yellow_1(sK3))
    | k3_yellow_0(k2_yellow_1(sK3)) = X0
    | k3_yellow_0(k2_yellow_1(sK3)) != k3_yellow_0(k2_yellow_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_3657])).

cnf(c_3934,plain,
    ( k1_yellow_0(k2_yellow_1(sK3),k1_xboole_0) != k3_yellow_0(k2_yellow_1(sK3))
    | k3_yellow_0(k2_yellow_1(sK3)) = k1_yellow_0(k2_yellow_1(sK3),k1_xboole_0)
    | k3_yellow_0(k2_yellow_1(sK3)) != k3_yellow_0(k2_yellow_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_3782])).

cnf(c_2928,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3783,plain,
    ( k3_yellow_0(k2_yellow_1(sK3)) = k3_yellow_0(k2_yellow_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_2928])).

cnf(c_2959,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2928])).

cnf(c_2,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_104,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_28,negated_conjecture,
    ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK3)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_30,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_31,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6593,c_4464,c_4134,c_3935,c_3934,c_3783,c_2959,c_104,c_28,c_31])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:06:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.62/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.01  
% 2.62/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.62/1.01  
% 2.62/1.01  ------  iProver source info
% 2.62/1.01  
% 2.62/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.62/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.62/1.01  git: non_committed_changes: false
% 2.62/1.01  git: last_make_outside_of_git: false
% 2.62/1.01  
% 2.62/1.01  ------ 
% 2.62/1.01  
% 2.62/1.01  ------ Input Options
% 2.62/1.01  
% 2.62/1.01  --out_options                           all
% 2.62/1.01  --tptp_safe_out                         true
% 2.62/1.01  --problem_path                          ""
% 2.62/1.01  --include_path                          ""
% 2.62/1.01  --clausifier                            res/vclausify_rel
% 2.62/1.01  --clausifier_options                    --mode clausify
% 2.62/1.01  --stdin                                 false
% 2.62/1.01  --stats_out                             all
% 2.62/1.01  
% 2.62/1.01  ------ General Options
% 2.62/1.01  
% 2.62/1.01  --fof                                   false
% 2.62/1.01  --time_out_real                         305.
% 2.62/1.01  --time_out_virtual                      -1.
% 2.62/1.01  --symbol_type_check                     false
% 2.62/1.01  --clausify_out                          false
% 2.62/1.01  --sig_cnt_out                           false
% 2.62/1.01  --trig_cnt_out                          false
% 2.62/1.01  --trig_cnt_out_tolerance                1.
% 2.62/1.01  --trig_cnt_out_sk_spl                   false
% 2.62/1.01  --abstr_cl_out                          false
% 2.62/1.01  
% 2.62/1.01  ------ Global Options
% 2.62/1.01  
% 2.62/1.01  --schedule                              default
% 2.62/1.01  --add_important_lit                     false
% 2.62/1.01  --prop_solver_per_cl                    1000
% 2.62/1.01  --min_unsat_core                        false
% 2.62/1.01  --soft_assumptions                      false
% 2.62/1.01  --soft_lemma_size                       3
% 2.62/1.01  --prop_impl_unit_size                   0
% 2.62/1.01  --prop_impl_unit                        []
% 2.62/1.01  --share_sel_clauses                     true
% 2.62/1.01  --reset_solvers                         false
% 2.62/1.01  --bc_imp_inh                            [conj_cone]
% 2.62/1.01  --conj_cone_tolerance                   3.
% 2.62/1.01  --extra_neg_conj                        none
% 2.62/1.01  --large_theory_mode                     true
% 2.62/1.01  --prolific_symb_bound                   200
% 2.62/1.01  --lt_threshold                          2000
% 2.62/1.01  --clause_weak_htbl                      true
% 2.62/1.01  --gc_record_bc_elim                     false
% 2.62/1.01  
% 2.62/1.01  ------ Preprocessing Options
% 2.62/1.01  
% 2.62/1.01  --preprocessing_flag                    true
% 2.62/1.01  --time_out_prep_mult                    0.1
% 2.62/1.01  --splitting_mode                        input
% 2.62/1.01  --splitting_grd                         true
% 2.62/1.01  --splitting_cvd                         false
% 2.62/1.01  --splitting_cvd_svl                     false
% 2.62/1.01  --splitting_nvd                         32
% 2.62/1.01  --sub_typing                            true
% 2.62/1.01  --prep_gs_sim                           true
% 2.62/1.01  --prep_unflatten                        true
% 2.62/1.01  --prep_res_sim                          true
% 2.62/1.01  --prep_upred                            true
% 2.62/1.01  --prep_sem_filter                       exhaustive
% 2.62/1.01  --prep_sem_filter_out                   false
% 2.62/1.01  --pred_elim                             true
% 2.62/1.01  --res_sim_input                         true
% 2.62/1.01  --eq_ax_congr_red                       true
% 2.62/1.01  --pure_diseq_elim                       true
% 2.62/1.01  --brand_transform                       false
% 2.62/1.01  --non_eq_to_eq                          false
% 2.62/1.01  --prep_def_merge                        true
% 2.62/1.01  --prep_def_merge_prop_impl              false
% 2.62/1.01  --prep_def_merge_mbd                    true
% 2.62/1.01  --prep_def_merge_tr_red                 false
% 2.62/1.01  --prep_def_merge_tr_cl                  false
% 2.62/1.01  --smt_preprocessing                     true
% 2.62/1.01  --smt_ac_axioms                         fast
% 2.62/1.01  --preprocessed_out                      false
% 2.62/1.01  --preprocessed_stats                    false
% 2.62/1.01  
% 2.62/1.01  ------ Abstraction refinement Options
% 2.62/1.01  
% 2.62/1.01  --abstr_ref                             []
% 2.62/1.01  --abstr_ref_prep                        false
% 2.62/1.01  --abstr_ref_until_sat                   false
% 2.62/1.01  --abstr_ref_sig_restrict                funpre
% 2.62/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.62/1.01  --abstr_ref_under                       []
% 2.62/1.01  
% 2.62/1.01  ------ SAT Options
% 2.62/1.01  
% 2.62/1.01  --sat_mode                              false
% 2.62/1.01  --sat_fm_restart_options                ""
% 2.62/1.01  --sat_gr_def                            false
% 2.62/1.01  --sat_epr_types                         true
% 2.62/1.01  --sat_non_cyclic_types                  false
% 2.62/1.01  --sat_finite_models                     false
% 2.62/1.01  --sat_fm_lemmas                         false
% 2.62/1.01  --sat_fm_prep                           false
% 2.62/1.01  --sat_fm_uc_incr                        true
% 2.62/1.01  --sat_out_model                         small
% 2.62/1.01  --sat_out_clauses                       false
% 2.62/1.01  
% 2.62/1.01  ------ QBF Options
% 2.62/1.01  
% 2.62/1.01  --qbf_mode                              false
% 2.62/1.01  --qbf_elim_univ                         false
% 2.62/1.01  --qbf_dom_inst                          none
% 2.62/1.01  --qbf_dom_pre_inst                      false
% 2.62/1.01  --qbf_sk_in                             false
% 2.62/1.01  --qbf_pred_elim                         true
% 2.62/1.01  --qbf_split                             512
% 2.62/1.01  
% 2.62/1.01  ------ BMC1 Options
% 2.62/1.01  
% 2.62/1.01  --bmc1_incremental                      false
% 2.62/1.01  --bmc1_axioms                           reachable_all
% 2.62/1.01  --bmc1_min_bound                        0
% 2.62/1.01  --bmc1_max_bound                        -1
% 2.62/1.01  --bmc1_max_bound_default                -1
% 2.62/1.01  --bmc1_symbol_reachability              true
% 2.62/1.01  --bmc1_property_lemmas                  false
% 2.62/1.01  --bmc1_k_induction                      false
% 2.62/1.01  --bmc1_non_equiv_states                 false
% 2.62/1.01  --bmc1_deadlock                         false
% 2.62/1.01  --bmc1_ucm                              false
% 2.62/1.01  --bmc1_add_unsat_core                   none
% 2.62/1.01  --bmc1_unsat_core_children              false
% 2.62/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.62/1.01  --bmc1_out_stat                         full
% 2.62/1.01  --bmc1_ground_init                      false
% 2.62/1.01  --bmc1_pre_inst_next_state              false
% 2.62/1.01  --bmc1_pre_inst_state                   false
% 2.62/1.01  --bmc1_pre_inst_reach_state             false
% 2.62/1.01  --bmc1_out_unsat_core                   false
% 2.62/1.01  --bmc1_aig_witness_out                  false
% 2.62/1.01  --bmc1_verbose                          false
% 2.62/1.01  --bmc1_dump_clauses_tptp                false
% 2.62/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.62/1.01  --bmc1_dump_file                        -
% 2.62/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.62/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.62/1.01  --bmc1_ucm_extend_mode                  1
% 2.62/1.01  --bmc1_ucm_init_mode                    2
% 2.62/1.01  --bmc1_ucm_cone_mode                    none
% 2.62/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.62/1.01  --bmc1_ucm_relax_model                  4
% 2.62/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.62/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.62/1.01  --bmc1_ucm_layered_model                none
% 2.62/1.01  --bmc1_ucm_max_lemma_size               10
% 2.62/1.01  
% 2.62/1.01  ------ AIG Options
% 2.62/1.01  
% 2.62/1.01  --aig_mode                              false
% 2.62/1.01  
% 2.62/1.01  ------ Instantiation Options
% 2.62/1.01  
% 2.62/1.01  --instantiation_flag                    true
% 2.62/1.01  --inst_sos_flag                         false
% 2.62/1.01  --inst_sos_phase                        true
% 2.62/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.62/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.62/1.01  --inst_lit_sel_side                     num_symb
% 2.62/1.01  --inst_solver_per_active                1400
% 2.62/1.01  --inst_solver_calls_frac                1.
% 2.62/1.01  --inst_passive_queue_type               priority_queues
% 2.62/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.62/1.01  --inst_passive_queues_freq              [25;2]
% 2.62/1.01  --inst_dismatching                      true
% 2.62/1.01  --inst_eager_unprocessed_to_passive     true
% 2.62/1.01  --inst_prop_sim_given                   true
% 2.62/1.01  --inst_prop_sim_new                     false
% 2.62/1.01  --inst_subs_new                         false
% 2.62/1.01  --inst_eq_res_simp                      false
% 2.62/1.01  --inst_subs_given                       false
% 2.62/1.01  --inst_orphan_elimination               true
% 2.62/1.01  --inst_learning_loop_flag               true
% 2.62/1.01  --inst_learning_start                   3000
% 2.62/1.01  --inst_learning_factor                  2
% 2.62/1.01  --inst_start_prop_sim_after_learn       3
% 2.62/1.01  --inst_sel_renew                        solver
% 2.62/1.01  --inst_lit_activity_flag                true
% 2.62/1.01  --inst_restr_to_given                   false
% 2.62/1.01  --inst_activity_threshold               500
% 2.62/1.01  --inst_out_proof                        true
% 2.62/1.01  
% 2.62/1.01  ------ Resolution Options
% 2.62/1.01  
% 2.62/1.01  --resolution_flag                       true
% 2.62/1.01  --res_lit_sel                           adaptive
% 2.62/1.01  --res_lit_sel_side                      none
% 2.62/1.01  --res_ordering                          kbo
% 2.62/1.01  --res_to_prop_solver                    active
% 2.62/1.01  --res_prop_simpl_new                    false
% 2.62/1.01  --res_prop_simpl_given                  true
% 2.62/1.01  --res_passive_queue_type                priority_queues
% 2.62/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.62/1.01  --res_passive_queues_freq               [15;5]
% 2.62/1.01  --res_forward_subs                      full
% 2.62/1.01  --res_backward_subs                     full
% 2.62/1.01  --res_forward_subs_resolution           true
% 2.62/1.01  --res_backward_subs_resolution          true
% 2.62/1.01  --res_orphan_elimination                true
% 2.62/1.01  --res_time_limit                        2.
% 2.62/1.01  --res_out_proof                         true
% 2.62/1.01  
% 2.62/1.01  ------ Superposition Options
% 2.62/1.01  
% 2.62/1.01  --superposition_flag                    true
% 2.62/1.01  --sup_passive_queue_type                priority_queues
% 2.62/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.62/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.62/1.01  --demod_completeness_check              fast
% 2.62/1.01  --demod_use_ground                      true
% 2.62/1.01  --sup_to_prop_solver                    passive
% 2.62/1.01  --sup_prop_simpl_new                    true
% 2.62/1.01  --sup_prop_simpl_given                  true
% 2.62/1.01  --sup_fun_splitting                     false
% 2.62/1.01  --sup_smt_interval                      50000
% 2.62/1.01  
% 2.62/1.01  ------ Superposition Simplification Setup
% 2.62/1.01  
% 2.62/1.01  --sup_indices_passive                   []
% 2.62/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.62/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.62/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.62/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.62/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.62/1.01  --sup_full_bw                           [BwDemod]
% 2.62/1.01  --sup_immed_triv                        [TrivRules]
% 2.62/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.62/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.62/1.01  --sup_immed_bw_main                     []
% 2.62/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.62/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.62/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.62/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.62/1.01  
% 2.62/1.01  ------ Combination Options
% 2.62/1.01  
% 2.62/1.01  --comb_res_mult                         3
% 2.62/1.01  --comb_sup_mult                         2
% 2.62/1.01  --comb_inst_mult                        10
% 2.62/1.01  
% 2.62/1.01  ------ Debug Options
% 2.62/1.01  
% 2.62/1.01  --dbg_backtrace                         false
% 2.62/1.01  --dbg_dump_prop_clauses                 false
% 2.62/1.01  --dbg_dump_prop_clauses_file            -
% 2.62/1.01  --dbg_out_stat                          false
% 2.62/1.01  ------ Parsing...
% 2.62/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.62/1.01  
% 2.62/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 2.62/1.01  
% 2.62/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.62/1.01  
% 2.62/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.62/1.01  ------ Proving...
% 2.62/1.01  ------ Problem Properties 
% 2.62/1.01  
% 2.62/1.01  
% 2.62/1.01  clauses                                 25
% 2.62/1.01  conjectures                             3
% 2.62/1.01  EPR                                     6
% 2.62/1.01  Horn                                    16
% 2.62/1.01  unary                                   8
% 2.62/1.01  binary                                  3
% 2.62/1.01  lits                                    70
% 2.62/1.01  lits eq                                 7
% 2.62/1.01  fd_pure                                 0
% 2.62/1.01  fd_pseudo                               0
% 2.62/1.01  fd_cond                                 0
% 2.62/1.01  fd_pseudo_cond                          3
% 2.62/1.01  AC symbols                              0
% 2.62/1.01  
% 2.62/1.01  ------ Schedule dynamic 5 is on 
% 2.62/1.01  
% 2.62/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.62/1.01  
% 2.62/1.01  
% 2.62/1.01  ------ 
% 2.62/1.01  Current options:
% 2.62/1.01  ------ 
% 2.62/1.01  
% 2.62/1.01  ------ Input Options
% 2.62/1.01  
% 2.62/1.01  --out_options                           all
% 2.62/1.01  --tptp_safe_out                         true
% 2.62/1.01  --problem_path                          ""
% 2.62/1.01  --include_path                          ""
% 2.62/1.01  --clausifier                            res/vclausify_rel
% 2.62/1.01  --clausifier_options                    --mode clausify
% 2.62/1.01  --stdin                                 false
% 2.62/1.01  --stats_out                             all
% 2.62/1.01  
% 2.62/1.01  ------ General Options
% 2.62/1.01  
% 2.62/1.01  --fof                                   false
% 2.62/1.01  --time_out_real                         305.
% 2.62/1.01  --time_out_virtual                      -1.
% 2.62/1.01  --symbol_type_check                     false
% 2.62/1.01  --clausify_out                          false
% 2.62/1.01  --sig_cnt_out                           false
% 2.62/1.01  --trig_cnt_out                          false
% 2.62/1.01  --trig_cnt_out_tolerance                1.
% 2.62/1.01  --trig_cnt_out_sk_spl                   false
% 2.62/1.01  --abstr_cl_out                          false
% 2.62/1.01  
% 2.62/1.01  ------ Global Options
% 2.62/1.01  
% 2.62/1.01  --schedule                              default
% 2.62/1.01  --add_important_lit                     false
% 2.62/1.01  --prop_solver_per_cl                    1000
% 2.62/1.01  --min_unsat_core                        false
% 2.62/1.01  --soft_assumptions                      false
% 2.62/1.01  --soft_lemma_size                       3
% 2.62/1.01  --prop_impl_unit_size                   0
% 2.62/1.01  --prop_impl_unit                        []
% 2.62/1.01  --share_sel_clauses                     true
% 2.62/1.01  --reset_solvers                         false
% 2.62/1.01  --bc_imp_inh                            [conj_cone]
% 2.62/1.01  --conj_cone_tolerance                   3.
% 2.62/1.01  --extra_neg_conj                        none
% 2.62/1.01  --large_theory_mode                     true
% 2.62/1.01  --prolific_symb_bound                   200
% 2.62/1.01  --lt_threshold                          2000
% 2.62/1.01  --clause_weak_htbl                      true
% 2.62/1.01  --gc_record_bc_elim                     false
% 2.62/1.01  
% 2.62/1.01  ------ Preprocessing Options
% 2.62/1.01  
% 2.62/1.01  --preprocessing_flag                    true
% 2.62/1.01  --time_out_prep_mult                    0.1
% 2.62/1.01  --splitting_mode                        input
% 2.62/1.01  --splitting_grd                         true
% 2.62/1.01  --splitting_cvd                         false
% 2.62/1.01  --splitting_cvd_svl                     false
% 2.62/1.01  --splitting_nvd                         32
% 2.62/1.01  --sub_typing                            true
% 2.62/1.01  --prep_gs_sim                           true
% 2.62/1.01  --prep_unflatten                        true
% 2.62/1.01  --prep_res_sim                          true
% 2.62/1.01  --prep_upred                            true
% 2.62/1.01  --prep_sem_filter                       exhaustive
% 2.62/1.01  --prep_sem_filter_out                   false
% 2.62/1.01  --pred_elim                             true
% 2.62/1.01  --res_sim_input                         true
% 2.62/1.01  --eq_ax_congr_red                       true
% 2.62/1.01  --pure_diseq_elim                       true
% 2.62/1.01  --brand_transform                       false
% 2.62/1.01  --non_eq_to_eq                          false
% 2.62/1.01  --prep_def_merge                        true
% 2.62/1.01  --prep_def_merge_prop_impl              false
% 2.62/1.01  --prep_def_merge_mbd                    true
% 2.62/1.01  --prep_def_merge_tr_red                 false
% 2.62/1.01  --prep_def_merge_tr_cl                  false
% 2.62/1.01  --smt_preprocessing                     true
% 2.62/1.01  --smt_ac_axioms                         fast
% 2.62/1.01  --preprocessed_out                      false
% 2.62/1.01  --preprocessed_stats                    false
% 2.62/1.01  
% 2.62/1.01  ------ Abstraction refinement Options
% 2.62/1.01  
% 2.62/1.01  --abstr_ref                             []
% 2.62/1.01  --abstr_ref_prep                        false
% 2.62/1.01  --abstr_ref_until_sat                   false
% 2.62/1.01  --abstr_ref_sig_restrict                funpre
% 2.62/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.62/1.01  --abstr_ref_under                       []
% 2.62/1.01  
% 2.62/1.01  ------ SAT Options
% 2.62/1.01  
% 2.62/1.01  --sat_mode                              false
% 2.62/1.01  --sat_fm_restart_options                ""
% 2.62/1.01  --sat_gr_def                            false
% 2.62/1.01  --sat_epr_types                         true
% 2.62/1.01  --sat_non_cyclic_types                  false
% 2.62/1.01  --sat_finite_models                     false
% 2.62/1.01  --sat_fm_lemmas                         false
% 2.62/1.01  --sat_fm_prep                           false
% 2.62/1.01  --sat_fm_uc_incr                        true
% 2.62/1.01  --sat_out_model                         small
% 2.62/1.01  --sat_out_clauses                       false
% 2.62/1.01  
% 2.62/1.01  ------ QBF Options
% 2.62/1.01  
% 2.62/1.01  --qbf_mode                              false
% 2.62/1.01  --qbf_elim_univ                         false
% 2.62/1.01  --qbf_dom_inst                          none
% 2.62/1.01  --qbf_dom_pre_inst                      false
% 2.62/1.01  --qbf_sk_in                             false
% 2.62/1.01  --qbf_pred_elim                         true
% 2.62/1.01  --qbf_split                             512
% 2.62/1.01  
% 2.62/1.01  ------ BMC1 Options
% 2.62/1.01  
% 2.62/1.01  --bmc1_incremental                      false
% 2.62/1.01  --bmc1_axioms                           reachable_all
% 2.62/1.01  --bmc1_min_bound                        0
% 2.62/1.01  --bmc1_max_bound                        -1
% 2.62/1.01  --bmc1_max_bound_default                -1
% 2.62/1.01  --bmc1_symbol_reachability              true
% 2.62/1.01  --bmc1_property_lemmas                  false
% 2.62/1.01  --bmc1_k_induction                      false
% 2.62/1.01  --bmc1_non_equiv_states                 false
% 2.62/1.01  --bmc1_deadlock                         false
% 2.62/1.01  --bmc1_ucm                              false
% 2.62/1.01  --bmc1_add_unsat_core                   none
% 2.62/1.01  --bmc1_unsat_core_children              false
% 2.62/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.62/1.01  --bmc1_out_stat                         full
% 2.62/1.01  --bmc1_ground_init                      false
% 2.62/1.01  --bmc1_pre_inst_next_state              false
% 2.62/1.01  --bmc1_pre_inst_state                   false
% 2.62/1.01  --bmc1_pre_inst_reach_state             false
% 2.62/1.01  --bmc1_out_unsat_core                   false
% 2.62/1.01  --bmc1_aig_witness_out                  false
% 2.62/1.01  --bmc1_verbose                          false
% 2.62/1.01  --bmc1_dump_clauses_tptp                false
% 2.62/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.62/1.01  --bmc1_dump_file                        -
% 2.62/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.62/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.62/1.01  --bmc1_ucm_extend_mode                  1
% 2.62/1.01  --bmc1_ucm_init_mode                    2
% 2.62/1.01  --bmc1_ucm_cone_mode                    none
% 2.62/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.62/1.01  --bmc1_ucm_relax_model                  4
% 2.62/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.62/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.62/1.01  --bmc1_ucm_layered_model                none
% 2.62/1.01  --bmc1_ucm_max_lemma_size               10
% 2.62/1.01  
% 2.62/1.01  ------ AIG Options
% 2.62/1.01  
% 2.62/1.01  --aig_mode                              false
% 2.62/1.01  
% 2.62/1.01  ------ Instantiation Options
% 2.62/1.01  
% 2.62/1.01  --instantiation_flag                    true
% 2.62/1.01  --inst_sos_flag                         false
% 2.62/1.01  --inst_sos_phase                        true
% 2.62/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.62/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.62/1.01  --inst_lit_sel_side                     none
% 2.62/1.01  --inst_solver_per_active                1400
% 2.62/1.01  --inst_solver_calls_frac                1.
% 2.62/1.01  --inst_passive_queue_type               priority_queues
% 2.62/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.62/1.01  --inst_passive_queues_freq              [25;2]
% 2.62/1.01  --inst_dismatching                      true
% 2.62/1.01  --inst_eager_unprocessed_to_passive     true
% 2.62/1.01  --inst_prop_sim_given                   true
% 2.62/1.01  --inst_prop_sim_new                     false
% 2.62/1.01  --inst_subs_new                         false
% 2.62/1.01  --inst_eq_res_simp                      false
% 2.62/1.01  --inst_subs_given                       false
% 2.62/1.01  --inst_orphan_elimination               true
% 2.62/1.01  --inst_learning_loop_flag               true
% 2.62/1.01  --inst_learning_start                   3000
% 2.62/1.01  --inst_learning_factor                  2
% 2.62/1.01  --inst_start_prop_sim_after_learn       3
% 2.62/1.01  --inst_sel_renew                        solver
% 2.62/1.01  --inst_lit_activity_flag                true
% 2.62/1.01  --inst_restr_to_given                   false
% 2.62/1.01  --inst_activity_threshold               500
% 2.62/1.01  --inst_out_proof                        true
% 2.62/1.01  
% 2.62/1.01  ------ Resolution Options
% 2.62/1.01  
% 2.62/1.01  --resolution_flag                       false
% 2.62/1.01  --res_lit_sel                           adaptive
% 2.62/1.01  --res_lit_sel_side                      none
% 2.62/1.01  --res_ordering                          kbo
% 2.62/1.01  --res_to_prop_solver                    active
% 2.62/1.01  --res_prop_simpl_new                    false
% 2.62/1.01  --res_prop_simpl_given                  true
% 2.62/1.01  --res_passive_queue_type                priority_queues
% 2.62/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.62/1.01  --res_passive_queues_freq               [15;5]
% 2.62/1.01  --res_forward_subs                      full
% 2.62/1.01  --res_backward_subs                     full
% 2.62/1.01  --res_forward_subs_resolution           true
% 2.62/1.01  --res_backward_subs_resolution          true
% 2.62/1.01  --res_orphan_elimination                true
% 2.62/1.01  --res_time_limit                        2.
% 2.62/1.01  --res_out_proof                         true
% 2.62/1.01  
% 2.62/1.01  ------ Superposition Options
% 2.62/1.01  
% 2.62/1.01  --superposition_flag                    true
% 2.62/1.01  --sup_passive_queue_type                priority_queues
% 2.62/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.62/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.62/1.01  --demod_completeness_check              fast
% 2.62/1.01  --demod_use_ground                      true
% 2.62/1.01  --sup_to_prop_solver                    passive
% 2.62/1.01  --sup_prop_simpl_new                    true
% 2.62/1.01  --sup_prop_simpl_given                  true
% 2.62/1.01  --sup_fun_splitting                     false
% 2.62/1.01  --sup_smt_interval                      50000
% 2.62/1.01  
% 2.62/1.01  ------ Superposition Simplification Setup
% 2.62/1.01  
% 2.62/1.01  --sup_indices_passive                   []
% 2.62/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.62/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.62/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.62/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.62/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.62/1.01  --sup_full_bw                           [BwDemod]
% 2.62/1.01  --sup_immed_triv                        [TrivRules]
% 2.62/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.62/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.62/1.01  --sup_immed_bw_main                     []
% 2.62/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.62/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.62/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.62/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.62/1.01  
% 2.62/1.01  ------ Combination Options
% 2.62/1.01  
% 2.62/1.01  --comb_res_mult                         3
% 2.62/1.01  --comb_sup_mult                         2
% 2.62/1.01  --comb_inst_mult                        10
% 2.62/1.01  
% 2.62/1.01  ------ Debug Options
% 2.62/1.01  
% 2.62/1.01  --dbg_backtrace                         false
% 2.62/1.01  --dbg_dump_prop_clauses                 false
% 2.62/1.01  --dbg_dump_prop_clauses_file            -
% 2.62/1.01  --dbg_out_stat                          false
% 2.62/1.01  
% 2.62/1.01  
% 2.62/1.01  
% 2.62/1.01  
% 2.62/1.01  ------ Proving...
% 2.62/1.01  
% 2.62/1.01  
% 2.62/1.01  % SZS status Theorem for theBenchmark.p
% 2.62/1.01  
% 2.62/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.62/1.01  
% 2.62/1.01  fof(f14,conjecture,(
% 2.62/1.01    ! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k1_xboole_0,X0) => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))))),
% 2.62/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.62/1.01  
% 2.62/1.01  fof(f15,negated_conjecture,(
% 2.62/1.01    ~! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k1_xboole_0,X0) => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))))),
% 2.62/1.01    inference(negated_conjecture,[],[f14])).
% 2.62/1.01  
% 2.62/1.01  fof(f31,plain,(
% 2.62/1.01    ? [X0] : ((k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0)) & r2_hidden(k1_xboole_0,X0)) & ~v1_xboole_0(X0))),
% 2.62/1.01    inference(ennf_transformation,[],[f15])).
% 2.62/1.01  
% 2.62/1.01  fof(f32,plain,(
% 2.62/1.01    ? [X0] : (k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0)) & r2_hidden(k1_xboole_0,X0) & ~v1_xboole_0(X0))),
% 2.62/1.01    inference(flattening,[],[f31])).
% 2.62/1.01  
% 2.62/1.01  fof(f45,plain,(
% 2.62/1.01    ? [X0] : (k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0)) & r2_hidden(k1_xboole_0,X0) & ~v1_xboole_0(X0)) => (k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK3)) & r2_hidden(k1_xboole_0,sK3) & ~v1_xboole_0(sK3))),
% 2.62/1.01    introduced(choice_axiom,[])).
% 2.62/1.01  
% 2.62/1.01  fof(f46,plain,(
% 2.62/1.01    k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK3)) & r2_hidden(k1_xboole_0,sK3) & ~v1_xboole_0(sK3)),
% 2.62/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f45])).
% 2.62/1.01  
% 2.62/1.01  fof(f76,plain,(
% 2.62/1.01    r2_hidden(k1_xboole_0,sK3)),
% 2.62/1.01    inference(cnf_transformation,[],[f46])).
% 2.62/1.01  
% 2.62/1.01  fof(f4,axiom,(
% 2.62/1.01    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 2.62/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.62/1.01  
% 2.62/1.01  fof(f21,plain,(
% 2.62/1.01    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 2.62/1.01    inference(ennf_transformation,[],[f4])).
% 2.62/1.01  
% 2.62/1.01  fof(f51,plain,(
% 2.62/1.01    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 2.62/1.01    inference(cnf_transformation,[],[f21])).
% 2.62/1.01  
% 2.62/1.01  fof(f6,axiom,(
% 2.62/1.01    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X3,X2))))))),
% 2.62/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.62/1.01  
% 2.62/1.01  fof(f24,plain,(
% 2.62/1.01    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.62/1.01    inference(ennf_transformation,[],[f6])).
% 2.62/1.01  
% 2.62/1.01  fof(f25,plain,(
% 2.62/1.01    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.62/1.01    inference(flattening,[],[f24])).
% 2.62/1.01  
% 2.62/1.01  fof(f38,plain,(
% 2.62/1.01    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.62/1.01    inference(nnf_transformation,[],[f25])).
% 2.62/1.01  
% 2.62/1.01  fof(f39,plain,(
% 2.62/1.01    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.62/1.01    inference(rectify,[],[f38])).
% 2.62/1.01  
% 2.62/1.01  fof(f40,plain,(
% 2.62/1.01    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK1(X0,X1,X2),X2) & r2_hidden(sK1(X0,X1,X2),X1) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))))),
% 2.62/1.01    introduced(choice_axiom,[])).
% 2.62/1.01  
% 2.62/1.01  fof(f41,plain,(
% 2.62/1.01    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | (~r1_orders_2(X0,sK1(X0,X1,X2),X2) & r2_hidden(sK1(X0,X1,X2),X1) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.62/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f39,f40])).
% 2.62/1.01  
% 2.62/1.01  fof(f56,plain,(
% 2.62/1.01    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | r2_hidden(sK1(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.62/1.01    inference(cnf_transformation,[],[f41])).
% 2.62/1.01  
% 2.62/1.01  fof(f9,axiom,(
% 2.62/1.01    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 2.62/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.62/1.01  
% 2.62/1.01  fof(f20,plain,(
% 2.62/1.01    ! [X0] : l1_orders_2(k2_yellow_1(X0))),
% 2.62/1.01    inference(pure_predicate_removal,[],[f9])).
% 2.62/1.01  
% 2.62/1.01  fof(f67,plain,(
% 2.62/1.01    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 2.62/1.01    inference(cnf_transformation,[],[f20])).
% 2.62/1.01  
% 2.62/1.01  fof(f12,axiom,(
% 2.62/1.01    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 2.62/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.62/1.01  
% 2.62/1.01  fof(f71,plain,(
% 2.62/1.01    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 2.62/1.01    inference(cnf_transformation,[],[f12])).
% 2.62/1.01  
% 2.62/1.01  fof(f1,axiom,(
% 2.62/1.01    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.62/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.62/1.01  
% 2.62/1.01  fof(f33,plain,(
% 2.62/1.01    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.62/1.01    inference(nnf_transformation,[],[f1])).
% 2.62/1.01  
% 2.62/1.01  fof(f34,plain,(
% 2.62/1.01    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.62/1.01    inference(rectify,[],[f33])).
% 2.62/1.01  
% 2.62/1.01  fof(f35,plain,(
% 2.62/1.01    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.62/1.01    introduced(choice_axiom,[])).
% 2.62/1.01  
% 2.62/1.01  fof(f36,plain,(
% 2.62/1.01    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.62/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).
% 2.62/1.01  
% 2.62/1.01  fof(f47,plain,(
% 2.62/1.01    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.62/1.01    inference(cnf_transformation,[],[f36])).
% 2.62/1.01  
% 2.62/1.01  fof(f3,axiom,(
% 2.62/1.01    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.62/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.62/1.01  
% 2.62/1.01  fof(f50,plain,(
% 2.62/1.01    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.62/1.01    inference(cnf_transformation,[],[f3])).
% 2.62/1.01  
% 2.62/1.01  fof(f13,axiom,(
% 2.62/1.01    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)))))),
% 2.62/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.62/1.01  
% 2.62/1.01  fof(f30,plain,(
% 2.62/1.01    ! [X0] : (! [X1] : (! [X2] : ((r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 2.62/1.01    inference(ennf_transformation,[],[f13])).
% 2.62/1.01  
% 2.62/1.01  fof(f44,plain,(
% 2.62/1.01    ! [X0] : (! [X1] : (! [X2] : (((r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2)) & (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 2.62/1.01    inference(nnf_transformation,[],[f30])).
% 2.62/1.01  
% 2.62/1.01  fof(f74,plain,(
% 2.62/1.01    ( ! [X2,X0,X1] : (r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 2.62/1.01    inference(cnf_transformation,[],[f44])).
% 2.62/1.01  
% 2.62/1.01  fof(f5,axiom,(
% 2.62/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 2.62/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.62/1.01  
% 2.62/1.01  fof(f22,plain,(
% 2.62/1.01    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.62/1.01    inference(ennf_transformation,[],[f5])).
% 2.62/1.01  
% 2.62/1.01  fof(f23,plain,(
% 2.62/1.01    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.62/1.01    inference(flattening,[],[f22])).
% 2.62/1.01  
% 2.62/1.01  fof(f37,plain,(
% 2.62/1.01    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.62/1.01    inference(nnf_transformation,[],[f23])).
% 2.62/1.01  
% 2.62/1.01  fof(f52,plain,(
% 2.62/1.01    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.62/1.01    inference(cnf_transformation,[],[f37])).
% 2.62/1.01  
% 2.62/1.01  fof(f10,axiom,(
% 2.62/1.01    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v4_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 2.62/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.62/1.01  
% 2.62/1.01  fof(f17,plain,(
% 2.62/1.01    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 2.62/1.01    inference(pure_predicate_removal,[],[f10])).
% 2.62/1.01  
% 2.62/1.01  fof(f18,plain,(
% 2.62/1.01    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)))),
% 2.62/1.01    inference(pure_predicate_removal,[],[f17])).
% 2.62/1.01  
% 2.62/1.01  fof(f68,plain,(
% 2.62/1.01    ( ! [X0] : (v3_orders_2(k2_yellow_1(X0))) )),
% 2.62/1.01    inference(cnf_transformation,[],[f18])).
% 2.62/1.01  
% 2.62/1.01  fof(f11,axiom,(
% 2.62/1.01    ! [X0] : (~v1_xboole_0(X0) => (v1_orders_2(k2_yellow_1(X0)) & ~v2_struct_0(k2_yellow_1(X0))))),
% 2.62/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.62/1.01  
% 2.62/1.01  fof(f19,plain,(
% 2.62/1.01    ! [X0] : (~v1_xboole_0(X0) => ~v2_struct_0(k2_yellow_1(X0)))),
% 2.62/1.01    inference(pure_predicate_removal,[],[f11])).
% 2.62/1.01  
% 2.62/1.01  fof(f29,plain,(
% 2.62/1.01    ! [X0] : (~v2_struct_0(k2_yellow_1(X0)) | v1_xboole_0(X0))),
% 2.62/1.01    inference(ennf_transformation,[],[f19])).
% 2.62/1.01  
% 2.62/1.01  fof(f70,plain,(
% 2.62/1.01    ( ! [X0] : (~v2_struct_0(k2_yellow_1(X0)) | v1_xboole_0(X0)) )),
% 2.62/1.01    inference(cnf_transformation,[],[f29])).
% 2.62/1.01  
% 2.62/1.01  fof(f8,axiom,(
% 2.62/1.01    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1)) => (r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1)) & ((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1))))))),
% 2.62/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.62/1.01  
% 2.62/1.01  fof(f16,plain,(
% 2.62/1.01    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1)) => (r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1)) & ((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) => (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X4) => r1_orders_2(X0,X1,X4))) & r2_lattice3(X0,X2,X1))))))),
% 2.62/1.01    inference(rectify,[],[f8])).
% 2.62/1.01  
% 2.62/1.01  fof(f27,plain,(
% 2.62/1.01    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | (? [X3] : ((~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3)) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1))) & ((! [X4] : ((r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | (~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0)))),
% 2.62/1.01    inference(ennf_transformation,[],[f16])).
% 2.62/1.01  
% 2.62/1.01  fof(f28,plain,(
% 2.62/1.01    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | ? [X3] : (~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | ~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 2.62/1.01    inference(flattening,[],[f27])).
% 2.62/1.01  
% 2.62/1.01  fof(f42,plain,(
% 2.62/1.01    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X1,sK2(X0,X1,X2)) & r2_lattice3(X0,X2,sK2(X0,X1,X2)) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))))),
% 2.62/1.01    introduced(choice_axiom,[])).
% 2.62/1.01  
% 2.62/1.01  fof(f43,plain,(
% 2.62/1.01    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | (~r1_orders_2(X0,X1,sK2(X0,X1,X2)) & r2_lattice3(X0,X2,sK2(X0,X1,X2)) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | ~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 2.62/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f28,f42])).
% 2.62/1.01  
% 2.62/1.01  fof(f63,plain,(
% 2.62/1.01    ( ! [X2,X0,X1] : (k1_yellow_0(X0,X2) = X1 | ~r1_orders_2(X0,X1,sK2(X0,X1,X2)) | ~r2_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 2.62/1.01    inference(cnf_transformation,[],[f43])).
% 2.62/1.01  
% 2.62/1.01  fof(f69,plain,(
% 2.62/1.01    ( ! [X0] : (v5_orders_2(k2_yellow_1(X0))) )),
% 2.62/1.01    inference(cnf_transformation,[],[f18])).
% 2.62/1.01  
% 2.62/1.01  fof(f61,plain,(
% 2.62/1.01    ( ! [X2,X0,X1] : (k1_yellow_0(X0,X2) = X1 | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) | ~r2_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 2.62/1.01    inference(cnf_transformation,[],[f43])).
% 2.62/1.01  
% 2.62/1.01  fof(f7,axiom,(
% 2.62/1.01    ! [X0] : (l1_orders_2(X0) => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0))),
% 2.62/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.62/1.01  
% 2.62/1.01  fof(f26,plain,(
% 2.62/1.01    ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0))),
% 2.62/1.01    inference(ennf_transformation,[],[f7])).
% 2.62/1.01  
% 2.62/1.01  fof(f58,plain,(
% 2.62/1.01    ( ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0)) )),
% 2.62/1.01    inference(cnf_transformation,[],[f26])).
% 2.62/1.01  
% 2.62/1.01  fof(f2,axiom,(
% 2.62/1.01    v1_xboole_0(k1_xboole_0)),
% 2.62/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.62/1.01  
% 2.62/1.01  fof(f49,plain,(
% 2.62/1.01    v1_xboole_0(k1_xboole_0)),
% 2.62/1.01    inference(cnf_transformation,[],[f2])).
% 2.62/1.01  
% 2.62/1.01  fof(f77,plain,(
% 2.62/1.01    k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK3))),
% 2.62/1.01    inference(cnf_transformation,[],[f46])).
% 2.62/1.01  
% 2.62/1.01  fof(f75,plain,(
% 2.62/1.01    ~v1_xboole_0(sK3)),
% 2.62/1.01    inference(cnf_transformation,[],[f46])).
% 2.62/1.01  
% 2.62/1.01  cnf(c_29,negated_conjecture,
% 2.62/1.01      ( r2_hidden(k1_xboole_0,sK3) ),
% 2.62/1.01      inference(cnf_transformation,[],[f76]) ).
% 2.62/1.01  
% 2.62/1.01  cnf(c_3366,plain,
% 2.62/1.01      ( r2_hidden(k1_xboole_0,sK3) = iProver_top ),
% 2.62/1.01      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.62/1.01  
% 2.62/1.01  cnf(c_4,plain,
% 2.62/1.01      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 2.62/1.01      inference(cnf_transformation,[],[f51]) ).
% 2.62/1.01  
% 2.62/1.01  cnf(c_3367,plain,
% 2.62/1.01      ( m1_subset_1(X0,X1) = iProver_top
% 2.62/1.01      | r2_hidden(X0,X1) != iProver_top ),
% 2.62/1.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.62/1.01  
% 2.62/1.01  cnf(c_3676,plain,
% 2.62/1.01      ( m1_subset_1(k1_xboole_0,sK3) = iProver_top ),
% 2.62/1.01      inference(superposition,[status(thm)],[c_3366,c_3367]) ).
% 2.62/1.01  
% 2.62/1.01  cnf(c_8,plain,
% 2.62/1.01      ( r2_lattice3(X0,X1,X2)
% 2.62/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.62/1.01      | r2_hidden(sK1(X0,X1,X2),X1)
% 2.62/1.01      | ~ l1_orders_2(X0) ),
% 2.62/1.01      inference(cnf_transformation,[],[f56]) ).
% 2.62/1.01  
% 2.62/1.01  cnf(c_20,plain,
% 2.62/1.01      ( l1_orders_2(k2_yellow_1(X0)) ),
% 2.62/1.01      inference(cnf_transformation,[],[f67]) ).
% 2.62/1.01  
% 2.62/1.01  cnf(c_1162,plain,
% 2.62/1.01      ( r2_lattice3(X0,X1,X2)
% 2.62/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.62/1.01      | r2_hidden(sK1(X0,X1,X2),X1)
% 2.62/1.01      | k2_yellow_1(X3) != X0 ),
% 2.62/1.01      inference(resolution_lifted,[status(thm)],[c_8,c_20]) ).
% 2.62/1.01  
% 2.62/1.01  cnf(c_1163,plain,
% 2.62/1.01      ( r2_lattice3(k2_yellow_1(X0),X1,X2)
% 2.62/1.01      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.62/1.01      | r2_hidden(sK1(k2_yellow_1(X0),X1,X2),X1) ),
% 2.62/1.01      inference(unflattening,[status(thm)],[c_1162]) ).
% 2.62/1.01  
% 2.62/1.01  cnf(c_3352,plain,
% 2.62/1.01      ( r2_lattice3(k2_yellow_1(X0),X1,X2) = iProver_top
% 2.62/1.01      | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 2.62/1.01      | r2_hidden(sK1(k2_yellow_1(X0),X1,X2),X1) = iProver_top ),
% 2.62/1.01      inference(predicate_to_equality,[status(thm)],[c_1163]) ).
% 2.62/1.01  
% 2.62/1.01  cnf(c_25,plain,
% 2.62/1.01      ( u1_struct_0(k2_yellow_1(X0)) = X0 ),
% 2.62/1.01      inference(cnf_transformation,[],[f71]) ).
% 2.62/1.01  
% 2.62/1.01  cnf(c_3400,plain,
% 2.62/1.01      ( r2_lattice3(k2_yellow_1(X0),X1,X2) = iProver_top
% 2.62/1.01      | m1_subset_1(X2,X0) != iProver_top
% 2.62/1.01      | r2_hidden(sK1(k2_yellow_1(X0),X1,X2),X1) = iProver_top ),
% 2.62/1.01      inference(light_normalisation,[status(thm)],[c_3352,c_25]) ).
% 2.62/1.01  
% 2.62/1.01  cnf(c_1,plain,
% 2.62/1.01      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.62/1.01      inference(cnf_transformation,[],[f47]) ).
% 2.62/1.01  
% 2.62/1.01  cnf(c_3370,plain,
% 2.62/1.01      ( r2_hidden(X0,X1) != iProver_top
% 2.62/1.01      | v1_xboole_0(X1) != iProver_top ),
% 2.62/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.62/1.01  
% 2.62/1.01  cnf(c_3751,plain,
% 2.62/1.01      ( r2_lattice3(k2_yellow_1(X0),X1,X2) = iProver_top
% 2.62/1.01      | m1_subset_1(X2,X0) != iProver_top
% 2.62/1.01      | v1_xboole_0(X1) != iProver_top ),
% 2.62/1.01      inference(superposition,[status(thm)],[c_3400,c_3370]) ).
% 2.62/1.01  
% 2.62/1.01  cnf(c_3,plain,
% 2.62/1.01      ( r1_tarski(k1_xboole_0,X0) ),
% 2.62/1.01      inference(cnf_transformation,[],[f50]) ).
% 2.62/1.01  
% 2.62/1.01  cnf(c_3368,plain,
% 2.62/1.01      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.62/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.62/1.01  
% 2.62/1.01  cnf(c_26,plain,
% 2.62/1.01      ( r3_orders_2(k2_yellow_1(X0),X1,X2)
% 2.62/1.01      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.62/1.01      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.62/1.01      | ~ r1_tarski(X1,X2)
% 2.62/1.01      | v1_xboole_0(X0) ),
% 2.62/1.01      inference(cnf_transformation,[],[f74]) ).
% 2.62/1.01  
% 2.62/1.01  cnf(c_6,plain,
% 2.62/1.01      ( r1_orders_2(X0,X1,X2)
% 2.62/1.01      | ~ r3_orders_2(X0,X1,X2)
% 2.62/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.62/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.62/1.01      | v2_struct_0(X0)
% 2.62/1.01      | ~ v3_orders_2(X0)
% 2.62/1.01      | ~ l1_orders_2(X0) ),
% 2.62/1.01      inference(cnf_transformation,[],[f52]) ).
% 2.62/1.01  
% 2.62/1.01  cnf(c_22,plain,
% 2.62/1.01      ( v3_orders_2(k2_yellow_1(X0)) ),
% 2.62/1.01      inference(cnf_transformation,[],[f68]) ).
% 2.62/1.01  
% 2.62/1.01  cnf(c_384,plain,
% 2.62/1.01      ( r1_orders_2(X0,X1,X2)
% 2.62/1.01      | ~ r3_orders_2(X0,X1,X2)
% 2.62/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.62/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.62/1.01      | v2_struct_0(X0)
% 2.62/1.01      | ~ l1_orders_2(X0)
% 2.62/1.01      | k2_yellow_1(X3) != X0 ),
% 2.62/1.01      inference(resolution_lifted,[status(thm)],[c_6,c_22]) ).
% 2.62/1.01  
% 2.62/1.01  cnf(c_385,plain,
% 2.62/1.01      ( r1_orders_2(k2_yellow_1(X0),X1,X2)
% 2.62/1.01      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
% 2.62/1.01      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.62/1.01      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.62/1.01      | v2_struct_0(k2_yellow_1(X0))
% 2.62/1.01      | ~ l1_orders_2(k2_yellow_1(X0)) ),
% 2.62/1.01      inference(unflattening,[status(thm)],[c_384]) ).
% 2.62/1.01  
% 2.62/1.01  cnf(c_389,plain,
% 2.62/1.01      ( v2_struct_0(k2_yellow_1(X0))
% 2.62/1.01      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.62/1.01      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.62/1.01      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
% 2.62/1.01      | r1_orders_2(k2_yellow_1(X0),X1,X2) ),
% 2.62/1.01      inference(global_propositional_subsumption,
% 2.62/1.01                [status(thm)],
% 2.62/1.01                [c_385,c_20]) ).
% 2.62/1.01  
% 2.62/1.01  cnf(c_390,plain,
% 2.62/1.01      ( r1_orders_2(k2_yellow_1(X0),X1,X2)
% 2.62/1.01      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
% 2.62/1.01      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.62/1.01      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.62/1.01      | v2_struct_0(k2_yellow_1(X0)) ),
% 2.62/1.01      inference(renaming,[status(thm)],[c_389]) ).
% 2.62/1.01  
% 2.62/1.01  cnf(c_23,plain,
% 2.62/1.01      ( ~ v2_struct_0(k2_yellow_1(X0)) | v1_xboole_0(X0) ),
% 2.62/1.01      inference(cnf_transformation,[],[f70]) ).
% 2.62/1.01  
% 2.62/1.01  cnf(c_468,plain,
% 2.62/1.01      ( r1_orders_2(k2_yellow_1(X0),X1,X2)
% 2.62/1.01      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
% 2.62/1.01      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.62/1.01      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.62/1.01      | v1_xboole_0(X0) ),
% 2.62/1.01      inference(resolution,[status(thm)],[c_390,c_23]) ).
% 2.62/1.01  
% 2.62/1.01  cnf(c_517,plain,
% 2.62/1.01      ( r1_orders_2(k2_yellow_1(X0),X1,X2)
% 2.62/1.01      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.62/1.01      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.62/1.01      | ~ r1_tarski(X1,X2)
% 2.62/1.01      | v1_xboole_0(X0) ),
% 2.62/1.01      inference(resolution,[status(thm)],[c_26,c_468]) ).
% 2.62/1.01  
% 2.62/1.01  cnf(c_3363,plain,
% 2.62/1.01      ( r1_orders_2(k2_yellow_1(X0),X1,X2) = iProver_top
% 2.62/1.01      | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 2.62/1.01      | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 2.62/1.01      | r1_tarski(X1,X2) != iProver_top
% 2.62/1.01      | v1_xboole_0(X0) = iProver_top ),
% 2.62/1.01      inference(predicate_to_equality,[status(thm)],[c_517]) ).
% 2.62/1.01  
% 2.62/1.01  cnf(c_3482,plain,
% 2.62/1.01      ( r1_orders_2(k2_yellow_1(X0),X1,X2) = iProver_top
% 2.62/1.01      | m1_subset_1(X2,X0) != iProver_top
% 2.62/1.01      | m1_subset_1(X1,X0) != iProver_top
% 2.62/1.01      | r1_tarski(X1,X2) != iProver_top
% 2.62/1.01      | v1_xboole_0(X0) = iProver_top ),
% 2.62/1.01      inference(light_normalisation,[status(thm)],[c_3363,c_25]) ).
% 2.62/1.01  
% 2.62/1.01  cnf(c_15,plain,
% 2.62/1.01      ( ~ r2_lattice3(X0,X1,X2)
% 2.62/1.01      | ~ r1_orders_2(X0,X2,sK2(X0,X2,X1))
% 2.62/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.62/1.01      | ~ v5_orders_2(X0)
% 2.62/1.01      | ~ l1_orders_2(X0)
% 2.62/1.01      | k1_yellow_0(X0,X1) = X2 ),
% 2.62/1.01      inference(cnf_transformation,[],[f63]) ).
% 2.62/1.01  
% 2.62/1.01  cnf(c_21,plain,
% 2.62/1.01      ( v5_orders_2(k2_yellow_1(X0)) ),
% 2.62/1.01      inference(cnf_transformation,[],[f69]) ).
% 2.62/1.01  
% 2.62/1.01  cnf(c_986,plain,
% 2.62/1.01      ( ~ r2_lattice3(X0,X1,X2)
% 2.62/1.01      | ~ r1_orders_2(X0,X2,sK2(X0,X2,X1))
% 2.62/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.62/1.01      | ~ l1_orders_2(X0)
% 2.62/1.01      | k1_yellow_0(X0,X1) = X2
% 2.62/1.01      | k2_yellow_1(X3) != X0 ),
% 2.62/1.01      inference(resolution_lifted,[status(thm)],[c_15,c_21]) ).
% 2.62/1.01  
% 2.62/1.01  cnf(c_987,plain,
% 2.62/1.01      ( ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
% 2.62/1.01      | ~ r1_orders_2(k2_yellow_1(X0),X2,sK2(k2_yellow_1(X0),X2,X1))
% 2.62/1.01      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.62/1.01      | ~ l1_orders_2(k2_yellow_1(X0))
% 2.62/1.01      | k1_yellow_0(k2_yellow_1(X0),X1) = X2 ),
% 2.62/1.01      inference(unflattening,[status(thm)],[c_986]) ).
% 2.62/1.01  
% 2.62/1.01  cnf(c_991,plain,
% 2.62/1.01      ( ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.62/1.01      | ~ r1_orders_2(k2_yellow_1(X0),X2,sK2(k2_yellow_1(X0),X2,X1))
% 2.62/1.01      | ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
% 2.62/1.01      | k1_yellow_0(k2_yellow_1(X0),X1) = X2 ),
% 2.62/1.01      inference(global_propositional_subsumption,
% 2.62/1.01                [status(thm)],
% 2.62/1.01                [c_987,c_20]) ).
% 2.62/1.01  
% 2.62/1.01  cnf(c_992,plain,
% 2.62/1.01      ( ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
% 2.62/1.01      | ~ r1_orders_2(k2_yellow_1(X0),X2,sK2(k2_yellow_1(X0),X2,X1))
% 2.62/1.01      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.62/1.01      | k1_yellow_0(k2_yellow_1(X0),X1) = X2 ),
% 2.62/1.01      inference(renaming,[status(thm)],[c_991]) ).
% 2.62/1.01  
% 2.62/1.01  cnf(c_3358,plain,
% 2.62/1.01      ( k1_yellow_0(k2_yellow_1(X0),X1) = X2
% 2.62/1.01      | r2_lattice3(k2_yellow_1(X0),X1,X2) != iProver_top
% 2.62/1.01      | r1_orders_2(k2_yellow_1(X0),X2,sK2(k2_yellow_1(X0),X2,X1)) != iProver_top
% 2.62/1.01      | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top ),
% 2.62/1.01      inference(predicate_to_equality,[status(thm)],[c_992]) ).
% 2.62/1.01  
% 2.62/1.01  cnf(c_3473,plain,
% 2.62/1.01      ( k1_yellow_0(k2_yellow_1(X0),X1) = X2
% 2.62/1.01      | r2_lattice3(k2_yellow_1(X0),X1,X2) != iProver_top
% 2.62/1.01      | r1_orders_2(k2_yellow_1(X0),X2,sK2(k2_yellow_1(X0),X2,X1)) != iProver_top
% 2.62/1.01      | m1_subset_1(X2,X0) != iProver_top ),
% 2.62/1.01      inference(light_normalisation,[status(thm)],[c_3358,c_25]) ).
% 2.62/1.01  
% 2.62/1.01  cnf(c_4362,plain,
% 2.62/1.01      ( k1_yellow_0(k2_yellow_1(X0),X1) = X2
% 2.62/1.01      | r2_lattice3(k2_yellow_1(X0),X1,X2) != iProver_top
% 2.62/1.01      | m1_subset_1(X2,X0) != iProver_top
% 2.62/1.01      | m1_subset_1(sK2(k2_yellow_1(X0),X2,X1),X0) != iProver_top
% 2.62/1.01      | r1_tarski(X2,sK2(k2_yellow_1(X0),X2,X1)) != iProver_top
% 2.62/1.01      | v1_xboole_0(X0) = iProver_top ),
% 2.62/1.01      inference(superposition,[status(thm)],[c_3482,c_3473]) ).
% 2.62/1.01  
% 2.62/1.01  cnf(c_17,plain,
% 2.62/1.01      ( ~ r2_lattice3(X0,X1,X2)
% 2.62/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.62/1.01      | m1_subset_1(sK2(X0,X2,X1),u1_struct_0(X0))
% 2.62/1.01      | ~ v5_orders_2(X0)
% 2.62/1.01      | ~ l1_orders_2(X0)
% 2.62/1.01      | k1_yellow_0(X0,X1) = X2 ),
% 2.62/1.01      inference(cnf_transformation,[],[f61]) ).
% 2.62/1.01  
% 2.62/1.01  cnf(c_938,plain,
% 2.62/1.01      ( ~ r2_lattice3(X0,X1,X2)
% 2.62/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.62/1.01      | m1_subset_1(sK2(X0,X2,X1),u1_struct_0(X0))
% 2.62/1.01      | ~ l1_orders_2(X0)
% 2.62/1.01      | k1_yellow_0(X0,X1) = X2
% 2.62/1.01      | k2_yellow_1(X3) != X0 ),
% 2.62/1.01      inference(resolution_lifted,[status(thm)],[c_17,c_21]) ).
% 2.62/1.01  
% 2.62/1.01  cnf(c_939,plain,
% 2.62/1.01      ( ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
% 2.62/1.01      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.62/1.01      | m1_subset_1(sK2(k2_yellow_1(X0),X2,X1),u1_struct_0(k2_yellow_1(X0)))
% 2.62/1.01      | ~ l1_orders_2(k2_yellow_1(X0))
% 2.62/1.01      | k1_yellow_0(k2_yellow_1(X0),X1) = X2 ),
% 2.62/1.01      inference(unflattening,[status(thm)],[c_938]) ).
% 2.62/1.01  
% 2.62/1.01  cnf(c_943,plain,
% 2.62/1.01      ( m1_subset_1(sK2(k2_yellow_1(X0),X2,X1),u1_struct_0(k2_yellow_1(X0)))
% 2.62/1.01      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.62/1.01      | ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
% 2.62/1.01      | k1_yellow_0(k2_yellow_1(X0),X1) = X2 ),
% 2.62/1.01      inference(global_propositional_subsumption,
% 2.62/1.01                [status(thm)],
% 2.62/1.01                [c_939,c_20]) ).
% 2.62/1.01  
% 2.62/1.01  cnf(c_944,plain,
% 2.62/1.01      ( ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
% 2.62/1.01      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.62/1.01      | m1_subset_1(sK2(k2_yellow_1(X0),X2,X1),u1_struct_0(k2_yellow_1(X0)))
% 2.62/1.01      | k1_yellow_0(k2_yellow_1(X0),X1) = X2 ),
% 2.62/1.01      inference(renaming,[status(thm)],[c_943]) ).
% 2.62/1.01  
% 2.62/1.01  cnf(c_3360,plain,
% 2.62/1.01      ( k1_yellow_0(k2_yellow_1(X0),X1) = X2
% 2.62/1.01      | r2_lattice3(k2_yellow_1(X0),X1,X2) != iProver_top
% 2.62/1.01      | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 2.62/1.01      | m1_subset_1(sK2(k2_yellow_1(X0),X2,X1),u1_struct_0(k2_yellow_1(X0))) = iProver_top ),
% 2.62/1.01      inference(predicate_to_equality,[status(thm)],[c_944]) ).
% 2.62/1.01  
% 2.62/1.01  cnf(c_3455,plain,
% 2.62/1.01      ( k1_yellow_0(k2_yellow_1(X0),X1) = X2
% 2.62/1.01      | r2_lattice3(k2_yellow_1(X0),X1,X2) != iProver_top
% 2.62/1.01      | m1_subset_1(X2,X0) != iProver_top
% 2.62/1.01      | m1_subset_1(sK2(k2_yellow_1(X0),X2,X1),X0) = iProver_top ),
% 2.62/1.01      inference(light_normalisation,[status(thm)],[c_3360,c_25]) ).
% 2.62/1.01  
% 2.62/1.01  cnf(c_6482,plain,
% 2.62/1.01      ( m1_subset_1(X2,X0) != iProver_top
% 2.62/1.01      | r2_lattice3(k2_yellow_1(X0),X1,X2) != iProver_top
% 2.62/1.01      | k1_yellow_0(k2_yellow_1(X0),X1) = X2
% 2.62/1.01      | r1_tarski(X2,sK2(k2_yellow_1(X0),X2,X1)) != iProver_top
% 2.62/1.01      | v1_xboole_0(X0) = iProver_top ),
% 2.62/1.01      inference(global_propositional_subsumption,
% 2.62/1.01                [status(thm)],
% 2.62/1.01                [c_4362,c_3455]) ).
% 2.62/1.01  
% 2.62/1.01  cnf(c_6483,plain,
% 2.62/1.01      ( k1_yellow_0(k2_yellow_1(X0),X1) = X2
% 2.62/1.01      | r2_lattice3(k2_yellow_1(X0),X1,X2) != iProver_top
% 2.62/1.01      | m1_subset_1(X2,X0) != iProver_top
% 2.62/1.01      | r1_tarski(X2,sK2(k2_yellow_1(X0),X2,X1)) != iProver_top
% 2.62/1.01      | v1_xboole_0(X0) = iProver_top ),
% 2.62/1.01      inference(renaming,[status(thm)],[c_6482]) ).
% 2.62/1.01  
% 2.62/1.01  cnf(c_6491,plain,
% 2.62/1.01      ( k1_yellow_0(k2_yellow_1(X0),X1) = k1_xboole_0
% 2.62/1.01      | r2_lattice3(k2_yellow_1(X0),X1,k1_xboole_0) != iProver_top
% 2.62/1.01      | m1_subset_1(k1_xboole_0,X0) != iProver_top
% 2.62/1.01      | v1_xboole_0(X0) = iProver_top ),
% 2.62/1.01      inference(superposition,[status(thm)],[c_3368,c_6483]) ).
% 2.62/1.01  
% 2.62/1.01  cnf(c_6584,plain,
% 2.62/1.01      ( k1_yellow_0(k2_yellow_1(X0),X1) = k1_xboole_0
% 2.62/1.01      | m1_subset_1(k1_xboole_0,X0) != iProver_top
% 2.62/1.01      | v1_xboole_0(X1) != iProver_top
% 2.62/1.01      | v1_xboole_0(X0) = iProver_top ),
% 2.62/1.01      inference(superposition,[status(thm)],[c_3751,c_6491]) ).
% 2.62/1.01  
% 2.62/1.01  cnf(c_6591,plain,
% 2.62/1.01      ( k1_yellow_0(k2_yellow_1(sK3),X0) = k1_xboole_0
% 2.62/1.01      | v1_xboole_0(X0) != iProver_top
% 2.62/1.01      | v1_xboole_0(sK3) = iProver_top ),
% 2.62/1.01      inference(superposition,[status(thm)],[c_3676,c_6584]) ).
% 2.62/1.01  
% 2.62/1.01  cnf(c_6593,plain,
% 2.62/1.01      ( k1_yellow_0(k2_yellow_1(sK3),k1_xboole_0) = k1_xboole_0
% 2.62/1.01      | v1_xboole_0(sK3) = iProver_top
% 2.62/1.01      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.62/1.01      inference(instantiation,[status(thm)],[c_6591]) ).
% 2.62/1.01  
% 2.62/1.01  cnf(c_2929,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.62/1.01  
% 2.62/1.01  cnf(c_4463,plain,
% 2.62/1.01      ( k1_yellow_0(k2_yellow_1(sK3),k1_xboole_0) != X0
% 2.62/1.01      | k1_xboole_0 != X0
% 2.62/1.01      | k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK3),k1_xboole_0) ),
% 2.62/1.01      inference(instantiation,[status(thm)],[c_2929]) ).
% 2.62/1.01  
% 2.62/1.01  cnf(c_4464,plain,
% 2.62/1.01      ( k1_yellow_0(k2_yellow_1(sK3),k1_xboole_0) != k1_xboole_0
% 2.62/1.01      | k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK3),k1_xboole_0)
% 2.62/1.01      | k1_xboole_0 != k1_xboole_0 ),
% 2.62/1.01      inference(instantiation,[status(thm)],[c_4463]) ).
% 2.62/1.01  
% 2.62/1.01  cnf(c_3610,plain,
% 2.62/1.01      ( k3_yellow_0(k2_yellow_1(sK3)) != X0
% 2.62/1.01      | k1_xboole_0 != X0
% 2.62/1.01      | k1_xboole_0 = k3_yellow_0(k2_yellow_1(sK3)) ),
% 2.62/1.01      inference(instantiation,[status(thm)],[c_2929]) ).
% 2.62/1.01  
% 2.62/1.01  cnf(c_4134,plain,
% 2.62/1.01      ( k3_yellow_0(k2_yellow_1(sK3)) != k1_yellow_0(k2_yellow_1(sK3),k1_xboole_0)
% 2.62/1.01      | k1_xboole_0 != k1_yellow_0(k2_yellow_1(sK3),k1_xboole_0)
% 2.62/1.01      | k1_xboole_0 = k3_yellow_0(k2_yellow_1(sK3)) ),
% 2.62/1.01      inference(instantiation,[status(thm)],[c_3610]) ).
% 2.62/1.01  
% 2.62/1.01  cnf(c_11,plain,
% 2.62/1.01      ( ~ l1_orders_2(X0)
% 2.62/1.01      | k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0) ),
% 2.62/1.01      inference(cnf_transformation,[],[f58]) ).
% 2.62/1.01  
% 2.62/1.01  cnf(c_1122,plain,
% 2.62/1.01      ( k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0)
% 2.62/1.01      | k2_yellow_1(X1) != X0 ),
% 2.62/1.01      inference(resolution_lifted,[status(thm)],[c_11,c_20]) ).
% 2.62/1.01  
% 2.62/1.01  cnf(c_1123,plain,
% 2.62/1.01      ( k1_yellow_0(k2_yellow_1(X0),k1_xboole_0) = k3_yellow_0(k2_yellow_1(X0)) ),
% 2.62/1.01      inference(unflattening,[status(thm)],[c_1122]) ).
% 2.62/1.01  
% 2.62/1.01  cnf(c_3935,plain,
% 2.62/1.01      ( k1_yellow_0(k2_yellow_1(sK3),k1_xboole_0) = k3_yellow_0(k2_yellow_1(sK3)) ),
% 2.62/1.01      inference(instantiation,[status(thm)],[c_1123]) ).
% 2.62/1.01  
% 2.62/1.01  cnf(c_3657,plain,
% 2.62/1.01      ( X0 != X1
% 2.62/1.01      | k3_yellow_0(k2_yellow_1(sK3)) != X1
% 2.62/1.01      | k3_yellow_0(k2_yellow_1(sK3)) = X0 ),
% 2.62/1.01      inference(instantiation,[status(thm)],[c_2929]) ).
% 2.62/1.01  
% 2.62/1.01  cnf(c_3782,plain,
% 2.62/1.01      ( X0 != k3_yellow_0(k2_yellow_1(sK3))
% 2.62/1.01      | k3_yellow_0(k2_yellow_1(sK3)) = X0
% 2.62/1.01      | k3_yellow_0(k2_yellow_1(sK3)) != k3_yellow_0(k2_yellow_1(sK3)) ),
% 2.62/1.01      inference(instantiation,[status(thm)],[c_3657]) ).
% 2.62/1.01  
% 2.62/1.01  cnf(c_3934,plain,
% 2.62/1.01      ( k1_yellow_0(k2_yellow_1(sK3),k1_xboole_0) != k3_yellow_0(k2_yellow_1(sK3))
% 2.62/1.01      | k3_yellow_0(k2_yellow_1(sK3)) = k1_yellow_0(k2_yellow_1(sK3),k1_xboole_0)
% 2.62/1.01      | k3_yellow_0(k2_yellow_1(sK3)) != k3_yellow_0(k2_yellow_1(sK3)) ),
% 2.62/1.01      inference(instantiation,[status(thm)],[c_3782]) ).
% 2.62/1.01  
% 2.62/1.01  cnf(c_2928,plain,( X0 = X0 ),theory(equality) ).
% 2.62/1.01  
% 2.62/1.01  cnf(c_3783,plain,
% 2.62/1.01      ( k3_yellow_0(k2_yellow_1(sK3)) = k3_yellow_0(k2_yellow_1(sK3)) ),
% 2.62/1.01      inference(instantiation,[status(thm)],[c_2928]) ).
% 2.62/1.01  
% 2.62/1.01  cnf(c_2959,plain,
% 2.62/1.01      ( k1_xboole_0 = k1_xboole_0 ),
% 2.62/1.01      inference(instantiation,[status(thm)],[c_2928]) ).
% 2.62/1.01  
% 2.62/1.01  cnf(c_2,plain,
% 2.62/1.01      ( v1_xboole_0(k1_xboole_0) ),
% 2.62/1.01      inference(cnf_transformation,[],[f49]) ).
% 2.62/1.01  
% 2.62/1.01  cnf(c_104,plain,
% 2.62/1.01      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.62/1.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.62/1.01  
% 2.62/1.01  cnf(c_28,negated_conjecture,
% 2.62/1.01      ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK3)) ),
% 2.62/1.01      inference(cnf_transformation,[],[f77]) ).
% 2.62/1.01  
% 2.62/1.01  cnf(c_30,negated_conjecture,
% 2.62/1.01      ( ~ v1_xboole_0(sK3) ),
% 2.62/1.01      inference(cnf_transformation,[],[f75]) ).
% 2.62/1.01  
% 2.62/1.01  cnf(c_31,plain,
% 2.62/1.01      ( v1_xboole_0(sK3) != iProver_top ),
% 2.62/1.01      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.62/1.01  
% 2.62/1.01  cnf(contradiction,plain,
% 2.62/1.01      ( $false ),
% 2.62/1.01      inference(minisat,
% 2.62/1.01                [status(thm)],
% 2.62/1.01                [c_6593,c_4464,c_4134,c_3935,c_3934,c_3783,c_2959,c_104,
% 2.62/1.01                 c_28,c_31]) ).
% 2.62/1.01  
% 2.62/1.01  
% 2.62/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.62/1.01  
% 2.62/1.01  ------                               Statistics
% 2.62/1.01  
% 2.62/1.01  ------ General
% 2.62/1.01  
% 2.62/1.01  abstr_ref_over_cycles:                  0
% 2.62/1.01  abstr_ref_under_cycles:                 0
% 2.62/1.01  gc_basic_clause_elim:                   0
% 2.62/1.01  forced_gc_time:                         0
% 2.62/1.01  parsing_time:                           0.009
% 2.62/1.01  unif_index_cands_time:                  0.
% 2.62/1.01  unif_index_add_time:                    0.
% 2.62/1.01  orderings_time:                         0.
% 2.62/1.01  out_proof_time:                         0.008
% 2.62/1.01  total_time:                             0.188
% 2.62/1.01  num_of_symbols:                         54
% 2.62/1.01  num_of_terms:                           3972
% 2.62/1.01  
% 2.62/1.01  ------ Preprocessing
% 2.62/1.01  
% 2.62/1.01  num_of_splits:                          0
% 2.62/1.01  num_of_split_atoms:                     0
% 2.62/1.01  num_of_reused_defs:                     0
% 2.62/1.01  num_eq_ax_congr_red:                    35
% 2.62/1.01  num_of_sem_filtered_clauses:            1
% 2.62/1.01  num_of_subtypes:                        0
% 2.62/1.01  monotx_restored_types:                  0
% 2.62/1.01  sat_num_of_epr_types:                   0
% 2.62/1.01  sat_num_of_non_cyclic_types:            0
% 2.62/1.01  sat_guarded_non_collapsed_types:        0
% 2.62/1.01  num_pure_diseq_elim:                    0
% 2.62/1.01  simp_replaced_by:                       0
% 2.62/1.01  res_preprocessed:                       139
% 2.62/1.01  prep_upred:                             0
% 2.62/1.01  prep_unflattend:                        131
% 2.62/1.01  smt_new_axioms:                         0
% 2.62/1.01  pred_elim_cands:                        7
% 2.62/1.01  pred_elim:                              5
% 2.62/1.01  pred_elim_cl:                           6
% 2.62/1.01  pred_elim_cycles:                       17
% 2.62/1.01  merged_defs:                            0
% 2.62/1.01  merged_defs_ncl:                        0
% 2.62/1.01  bin_hyper_res:                          0
% 2.62/1.01  prep_cycles:                            4
% 2.62/1.01  pred_elim_time:                         0.042
% 2.62/1.01  splitting_time:                         0.
% 2.62/1.01  sem_filter_time:                        0.
% 2.62/1.01  monotx_time:                            0.
% 2.62/1.01  subtype_inf_time:                       0.
% 2.62/1.01  
% 2.62/1.01  ------ Problem properties
% 2.62/1.01  
% 2.62/1.01  clauses:                                25
% 2.62/1.01  conjectures:                            3
% 2.62/1.01  epr:                                    6
% 2.62/1.01  horn:                                   16
% 2.62/1.01  ground:                                 4
% 2.62/1.01  unary:                                  8
% 2.62/1.01  binary:                                 3
% 2.62/1.01  lits:                                   70
% 2.62/1.01  lits_eq:                                7
% 2.62/1.01  fd_pure:                                0
% 2.62/1.01  fd_pseudo:                              0
% 2.62/1.01  fd_cond:                                0
% 2.62/1.01  fd_pseudo_cond:                         3
% 2.62/1.01  ac_symbols:                             0
% 2.62/1.01  
% 2.62/1.01  ------ Propositional Solver
% 2.62/1.01  
% 2.62/1.01  prop_solver_calls:                      30
% 2.62/1.01  prop_fast_solver_calls:                 1666
% 2.62/1.01  smt_solver_calls:                       0
% 2.62/1.01  smt_fast_solver_calls:                  0
% 2.62/1.01  prop_num_of_clauses:                    1593
% 2.62/1.01  prop_preprocess_simplified:             5984
% 2.62/1.01  prop_fo_subsumed:                       16
% 2.62/1.01  prop_solver_time:                       0.
% 2.62/1.01  smt_solver_time:                        0.
% 2.62/1.01  smt_fast_solver_time:                   0.
% 2.62/1.01  prop_fast_solver_time:                  0.
% 2.62/1.01  prop_unsat_core_time:                   0.
% 2.62/1.01  
% 2.62/1.01  ------ QBF
% 2.62/1.01  
% 2.62/1.01  qbf_q_res:                              0
% 2.62/1.01  qbf_num_tautologies:                    0
% 2.62/1.01  qbf_prep_cycles:                        0
% 2.62/1.01  
% 2.62/1.01  ------ BMC1
% 2.62/1.01  
% 2.62/1.01  bmc1_current_bound:                     -1
% 2.62/1.01  bmc1_last_solved_bound:                 -1
% 2.62/1.01  bmc1_unsat_core_size:                   -1
% 2.62/1.01  bmc1_unsat_core_parents_size:           -1
% 2.62/1.01  bmc1_merge_next_fun:                    0
% 2.62/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.62/1.01  
% 2.62/1.01  ------ Instantiation
% 2.62/1.01  
% 2.62/1.01  inst_num_of_clauses:                    475
% 2.62/1.01  inst_num_in_passive:                    85
% 2.62/1.01  inst_num_in_active:                     265
% 2.62/1.01  inst_num_in_unprocessed:                125
% 2.62/1.01  inst_num_of_loops:                      290
% 2.62/1.01  inst_num_of_learning_restarts:          0
% 2.62/1.01  inst_num_moves_active_passive:          20
% 2.62/1.01  inst_lit_activity:                      0
% 2.62/1.01  inst_lit_activity_moves:                0
% 2.62/1.01  inst_num_tautologies:                   0
% 2.62/1.01  inst_num_prop_implied:                  0
% 2.62/1.01  inst_num_existing_simplified:           0
% 2.62/1.01  inst_num_eq_res_simplified:             0
% 2.62/1.01  inst_num_child_elim:                    0
% 2.62/1.01  inst_num_of_dismatching_blockings:      163
% 2.62/1.01  inst_num_of_non_proper_insts:           427
% 2.62/1.01  inst_num_of_duplicates:                 0
% 2.62/1.01  inst_inst_num_from_inst_to_res:         0
% 2.62/1.01  inst_dismatching_checking_time:         0.
% 2.62/1.01  
% 2.62/1.01  ------ Resolution
% 2.62/1.01  
% 2.62/1.01  res_num_of_clauses:                     0
% 2.62/1.01  res_num_in_passive:                     0
% 2.62/1.01  res_num_in_active:                      0
% 2.62/1.01  res_num_of_loops:                       143
% 2.62/1.01  res_forward_subset_subsumed:            75
% 2.62/1.01  res_backward_subset_subsumed:           2
% 2.62/1.01  res_forward_subsumed:                   0
% 2.62/1.01  res_backward_subsumed:                  0
% 2.62/1.01  res_forward_subsumption_resolution:     0
% 2.62/1.01  res_backward_subsumption_resolution:    0
% 2.62/1.01  res_clause_to_clause_subsumption:       296
% 2.62/1.01  res_orphan_elimination:                 0
% 2.62/1.01  res_tautology_del:                      43
% 2.62/1.01  res_num_eq_res_simplified:              0
% 2.62/1.01  res_num_sel_changes:                    0
% 2.62/1.01  res_moves_from_active_to_pass:          0
% 2.62/1.01  
% 2.62/1.01  ------ Superposition
% 2.62/1.01  
% 2.62/1.01  sup_time_total:                         0.
% 2.62/1.01  sup_time_generating:                    0.
% 2.62/1.01  sup_time_sim_full:                      0.
% 2.62/1.01  sup_time_sim_immed:                     0.
% 2.62/1.01  
% 2.62/1.01  sup_num_of_clauses:                     64
% 2.62/1.01  sup_num_in_active:                      58
% 2.62/1.01  sup_num_in_passive:                     6
% 2.62/1.01  sup_num_of_loops:                       57
% 2.62/1.01  sup_fw_superposition:                   48
% 2.62/1.01  sup_bw_superposition:                   23
% 2.62/1.01  sup_immediate_simplified:               18
% 2.62/1.01  sup_given_eliminated:                   0
% 2.62/1.01  comparisons_done:                       0
% 2.62/1.01  comparisons_avoided:                    0
% 2.62/1.01  
% 2.62/1.01  ------ Simplifications
% 2.62/1.01  
% 2.62/1.01  
% 2.62/1.01  sim_fw_subset_subsumed:                 5
% 2.62/1.01  sim_bw_subset_subsumed:                 0
% 2.62/1.01  sim_fw_subsumed:                        5
% 2.62/1.01  sim_bw_subsumed:                        0
% 2.62/1.01  sim_fw_subsumption_res:                 10
% 2.62/1.01  sim_bw_subsumption_res:                 0
% 2.62/1.01  sim_tautology_del:                      12
% 2.62/1.01  sim_eq_tautology_del:                   2
% 2.62/1.01  sim_eq_res_simp:                        0
% 2.62/1.01  sim_fw_demodulated:                     0
% 2.62/1.01  sim_bw_demodulated:                     0
% 2.62/1.01  sim_light_normalised:                   25
% 2.62/1.01  sim_joinable_taut:                      0
% 2.62/1.01  sim_joinable_simp:                      0
% 2.62/1.01  sim_ac_normalised:                      0
% 2.62/1.01  sim_smt_subsumption:                    0
% 2.62/1.01  
%------------------------------------------------------------------------------
