%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:20:13 EST 2020

% Result     : Theorem 2.82s
% Output     : CNFRefutation 2.82s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 184 expanded)
%              Number of clauses        :   69 (  77 expanded)
%              Number of leaves         :   20 (  35 expanded)
%              Depth                    :   21
%              Number of atoms          :  484 ( 659 expanded)
%              Number of equality atoms :  132 ( 168 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   15 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( r2_hidden(k1_xboole_0,X0)
       => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ( r2_hidden(k1_xboole_0,X0)
         => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f37,plain,(
    ? [X0] :
      ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0))
      & r2_hidden(k1_xboole_0,X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f38,plain,(
    ? [X0] :
      ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0))
      & r2_hidden(k1_xboole_0,X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f47,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0))
        & r2_hidden(k1_xboole_0,X0)
        & ~ v1_xboole_0(X0) )
   => ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK2))
      & r2_hidden(k1_xboole_0,sK2)
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK2))
    & r2_hidden(k1_xboole_0,sK2)
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f38,f47])).

fof(f78,plain,(
    r2_hidden(k1_xboole_0,sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( r1_lattice3(X0,k1_xboole_0,X1)
            & r2_lattice3(X0,k1_xboole_0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r2_lattice3(X0,k1_xboole_0,X1) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_lattice3(X0,k1_xboole_0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r2_lattice3(X0,k1_xboole_0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f69,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f14,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f39])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f40,f41])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f15,axiom,(
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
    inference(ennf_transformation,[],[f15])).

fof(f46,plain,(
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

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

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

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f12,axiom,(
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
    inference(pure_predicate_removal,[],[f12])).

fof(f20,plain,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f70,plain,(
    ! [X0] : v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f13,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_orders_2(k2_yellow_1(X0))
        & ~ v2_struct_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ~ v2_struct_0(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k2_yellow_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f72,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k2_yellow_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

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

fof(f18,plain,(
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

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f44,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X1,X3)
          & r2_lattice3(X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X1,sK1(X0,X1,X2))
        & r2_lattice3(X0,X2,sK1(X0,X1,X2))
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
                | ( ~ r1_orders_2(X0,X1,sK1(X0,X1,X2))
                  & r2_lattice3(X0,X2,sK1(X0,X1,X2))
                  & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f33,f44])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X2) = X1
      | ~ r1_orders_2(X0,X1,sK1(X0,X1,X2))
      | ~ r2_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f71,plain,(
    ! [X0] : v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X2) = X1
      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
      | ~ r2_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f59,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f79,plain,(
    k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK2)) ),
    inference(cnf_transformation,[],[f48])).

fof(f77,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_29,negated_conjecture,
    ( r2_hidden(k1_xboole_0,sK2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2678,plain,
    ( r2_hidden(k1_xboole_0,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_5,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2681,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3013,plain,
    ( m1_subset_1(k1_xboole_0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2678,c_2681])).

cnf(c_19,plain,
    ( r2_lattice3(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_20,plain,
    ( l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1127,plain,
    ( r2_lattice3(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | k2_yellow_1(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_20])).

cnf(c_1128,plain,
    ( r2_lattice3(k2_yellow_1(X0),k1_xboole_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) ),
    inference(unflattening,[status(thm)],[c_1127])).

cnf(c_2666,plain,
    ( r2_lattice3(k2_yellow_1(X0),k1_xboole_0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1128])).

cnf(c_25,plain,
    ( u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2715,plain,
    ( r2_lattice3(k2_yellow_1(X0),k1_xboole_0,X1) = iProver_top
    | m1_subset_1(X1,X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2666,c_25])).

cnf(c_3,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2683,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2685,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2682,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2679,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3006,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2682,c_2679])).

cnf(c_3258,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2685,c_3006])).

cnf(c_3373,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2683,c_3258])).

cnf(c_26,plain,
    ( r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ r1_tarski(X1,X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_9,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_22,plain,
    ( v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_328,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | k2_yellow_1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_22])).

cnf(c_329,plain,
    ( r1_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | v2_struct_0(k2_yellow_1(X0))
    | ~ l1_orders_2(k2_yellow_1(X0)) ),
    inference(unflattening,[status(thm)],[c_328])).

cnf(c_333,plain,
    ( v2_struct_0(k2_yellow_1(X0))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
    | r1_orders_2(k2_yellow_1(X0),X1,X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_329,c_20])).

cnf(c_334,plain,
    ( r1_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | v2_struct_0(k2_yellow_1(X0)) ),
    inference(renaming,[status(thm)],[c_333])).

cnf(c_23,plain,
    ( ~ v2_struct_0(k2_yellow_1(X0))
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_412,plain,
    ( r1_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | v1_xboole_0(X0) ),
    inference(resolution,[status(thm)],[c_334,c_23])).

cnf(c_603,plain,
    ( r1_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ r1_tarski(X1,X2)
    | v1_xboole_0(X0) ),
    inference(resolution,[status(thm)],[c_26,c_412])).

cnf(c_2675,plain,
    ( r1_orders_2(k2_yellow_1(X0),X1,X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_603])).

cnf(c_2799,plain,
    ( r1_orders_2(k2_yellow_1(X0),X1,X2) = iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2675,c_25])).

cnf(c_14,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK1(X0,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_21,plain,
    ( v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_991,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK1(X0,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2
    | k2_yellow_1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_21])).

cnf(c_992,plain,
    ( ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
    | ~ r1_orders_2(k2_yellow_1(X0),X2,sK1(k2_yellow_1(X0),X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ l1_orders_2(k2_yellow_1(X0))
    | k1_yellow_0(k2_yellow_1(X0),X1) = X2 ),
    inference(unflattening,[status(thm)],[c_991])).

cnf(c_996,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ r1_orders_2(k2_yellow_1(X0),X2,sK1(k2_yellow_1(X0),X2,X1))
    | ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
    | k1_yellow_0(k2_yellow_1(X0),X1) = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_992,c_20])).

cnf(c_997,plain,
    ( ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
    | ~ r1_orders_2(k2_yellow_1(X0),X2,sK1(k2_yellow_1(X0),X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | k1_yellow_0(k2_yellow_1(X0),X1) = X2 ),
    inference(renaming,[status(thm)],[c_996])).

cnf(c_2670,plain,
    ( k1_yellow_0(k2_yellow_1(X0),X1) = X2
    | r2_lattice3(k2_yellow_1(X0),X1,X2) != iProver_top
    | r1_orders_2(k2_yellow_1(X0),X2,sK1(k2_yellow_1(X0),X2,X1)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_997])).

cnf(c_2790,plain,
    ( k1_yellow_0(k2_yellow_1(X0),X1) = X2
    | r2_lattice3(k2_yellow_1(X0),X1,X2) != iProver_top
    | r1_orders_2(k2_yellow_1(X0),X2,sK1(k2_yellow_1(X0),X2,X1)) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2670,c_25])).

cnf(c_3902,plain,
    ( k1_yellow_0(k2_yellow_1(X0),X1) = X2
    | r2_lattice3(k2_yellow_1(X0),X1,X2) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(sK1(k2_yellow_1(X0),X2,X1),X0) != iProver_top
    | r1_tarski(X2,sK1(k2_yellow_1(X0),X2,X1)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2799,c_2790])).

cnf(c_16,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X2,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_943,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X2,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2
    | k2_yellow_1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_21])).

cnf(c_944,plain,
    ( ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | m1_subset_1(sK1(k2_yellow_1(X0),X2,X1),u1_struct_0(k2_yellow_1(X0)))
    | ~ l1_orders_2(k2_yellow_1(X0))
    | k1_yellow_0(k2_yellow_1(X0),X1) = X2 ),
    inference(unflattening,[status(thm)],[c_943])).

cnf(c_948,plain,
    ( m1_subset_1(sK1(k2_yellow_1(X0),X2,X1),u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
    | k1_yellow_0(k2_yellow_1(X0),X1) = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_944,c_20])).

cnf(c_949,plain,
    ( ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | m1_subset_1(sK1(k2_yellow_1(X0),X2,X1),u1_struct_0(k2_yellow_1(X0)))
    | k1_yellow_0(k2_yellow_1(X0),X1) = X2 ),
    inference(renaming,[status(thm)],[c_948])).

cnf(c_2672,plain,
    ( k1_yellow_0(k2_yellow_1(X0),X1) = X2
    | r2_lattice3(k2_yellow_1(X0),X1,X2) != iProver_top
    | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | m1_subset_1(sK1(k2_yellow_1(X0),X2,X1),u1_struct_0(k2_yellow_1(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_949])).

cnf(c_2772,plain,
    ( k1_yellow_0(k2_yellow_1(X0),X1) = X2
    | r2_lattice3(k2_yellow_1(X0),X1,X2) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(sK1(k2_yellow_1(X0),X2,X1),X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2672,c_25])).

cnf(c_5924,plain,
    ( m1_subset_1(X2,X0) != iProver_top
    | r2_lattice3(k2_yellow_1(X0),X1,X2) != iProver_top
    | k1_yellow_0(k2_yellow_1(X0),X1) = X2
    | r1_tarski(X2,sK1(k2_yellow_1(X0),X2,X1)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3902,c_2772])).

cnf(c_5925,plain,
    ( k1_yellow_0(k2_yellow_1(X0),X1) = X2
    | r2_lattice3(k2_yellow_1(X0),X1,X2) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | r1_tarski(X2,sK1(k2_yellow_1(X0),X2,X1)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_5924])).

cnf(c_5933,plain,
    ( k1_yellow_0(k2_yellow_1(X0),X1) = k1_xboole_0
    | r2_lattice3(k2_yellow_1(X0),X1,k1_xboole_0) != iProver_top
    | m1_subset_1(k1_xboole_0,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3373,c_5925])).

cnf(c_6413,plain,
    ( k1_yellow_0(k2_yellow_1(X0),k1_xboole_0) = k1_xboole_0
    | m1_subset_1(k1_xboole_0,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2715,c_5933])).

cnf(c_10,plain,
    ( ~ l1_orders_2(X0)
    | k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1139,plain,
    ( k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0)
    | k2_yellow_1(X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_20])).

cnf(c_1140,plain,
    ( k1_yellow_0(k2_yellow_1(X0),k1_xboole_0) = k3_yellow_0(k2_yellow_1(X0)) ),
    inference(unflattening,[status(thm)],[c_1139])).

cnf(c_6414,plain,
    ( k3_yellow_0(k2_yellow_1(X0)) = k1_xboole_0
    | m1_subset_1(k1_xboole_0,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6413,c_1140])).

cnf(c_6421,plain,
    ( k3_yellow_0(k2_yellow_1(sK2)) = k1_xboole_0
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3013,c_6414])).

cnf(c_2259,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2926,plain,
    ( k3_yellow_0(k2_yellow_1(sK2)) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k3_yellow_0(k2_yellow_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_2259])).

cnf(c_2927,plain,
    ( k3_yellow_0(k2_yellow_1(sK2)) != k1_xboole_0
    | k1_xboole_0 = k3_yellow_0(k2_yellow_1(sK2))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2926])).

cnf(c_2258,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2285,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2258])).

cnf(c_28,negated_conjecture,
    ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK2)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_30,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_31,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6421,c_2927,c_2285,c_28,c_31])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:29:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.82/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.82/1.00  
% 2.82/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.82/1.00  
% 2.82/1.00  ------  iProver source info
% 2.82/1.00  
% 2.82/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.82/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.82/1.00  git: non_committed_changes: false
% 2.82/1.00  git: last_make_outside_of_git: false
% 2.82/1.00  
% 2.82/1.00  ------ 
% 2.82/1.00  
% 2.82/1.00  ------ Input Options
% 2.82/1.00  
% 2.82/1.00  --out_options                           all
% 2.82/1.00  --tptp_safe_out                         true
% 2.82/1.00  --problem_path                          ""
% 2.82/1.00  --include_path                          ""
% 2.82/1.00  --clausifier                            res/vclausify_rel
% 2.82/1.00  --clausifier_options                    --mode clausify
% 2.82/1.00  --stdin                                 false
% 2.82/1.00  --stats_out                             all
% 2.82/1.00  
% 2.82/1.00  ------ General Options
% 2.82/1.00  
% 2.82/1.00  --fof                                   false
% 2.82/1.00  --time_out_real                         305.
% 2.82/1.00  --time_out_virtual                      -1.
% 2.82/1.00  --symbol_type_check                     false
% 2.82/1.00  --clausify_out                          false
% 2.82/1.00  --sig_cnt_out                           false
% 2.82/1.00  --trig_cnt_out                          false
% 2.82/1.00  --trig_cnt_out_tolerance                1.
% 2.82/1.00  --trig_cnt_out_sk_spl                   false
% 2.82/1.00  --abstr_cl_out                          false
% 2.82/1.00  
% 2.82/1.00  ------ Global Options
% 2.82/1.00  
% 2.82/1.00  --schedule                              default
% 2.82/1.00  --add_important_lit                     false
% 2.82/1.00  --prop_solver_per_cl                    1000
% 2.82/1.00  --min_unsat_core                        false
% 2.82/1.00  --soft_assumptions                      false
% 2.82/1.00  --soft_lemma_size                       3
% 2.82/1.00  --prop_impl_unit_size                   0
% 2.82/1.00  --prop_impl_unit                        []
% 2.82/1.00  --share_sel_clauses                     true
% 2.82/1.00  --reset_solvers                         false
% 2.82/1.00  --bc_imp_inh                            [conj_cone]
% 2.82/1.00  --conj_cone_tolerance                   3.
% 2.82/1.00  --extra_neg_conj                        none
% 2.82/1.00  --large_theory_mode                     true
% 2.82/1.00  --prolific_symb_bound                   200
% 2.82/1.00  --lt_threshold                          2000
% 2.82/1.00  --clause_weak_htbl                      true
% 2.82/1.00  --gc_record_bc_elim                     false
% 2.82/1.00  
% 2.82/1.00  ------ Preprocessing Options
% 2.82/1.00  
% 2.82/1.00  --preprocessing_flag                    true
% 2.82/1.00  --time_out_prep_mult                    0.1
% 2.82/1.00  --splitting_mode                        input
% 2.82/1.00  --splitting_grd                         true
% 2.82/1.00  --splitting_cvd                         false
% 2.82/1.00  --splitting_cvd_svl                     false
% 2.82/1.00  --splitting_nvd                         32
% 2.82/1.00  --sub_typing                            true
% 2.82/1.00  --prep_gs_sim                           true
% 2.82/1.00  --prep_unflatten                        true
% 2.82/1.00  --prep_res_sim                          true
% 2.82/1.00  --prep_upred                            true
% 2.82/1.00  --prep_sem_filter                       exhaustive
% 2.82/1.00  --prep_sem_filter_out                   false
% 2.82/1.00  --pred_elim                             true
% 2.82/1.00  --res_sim_input                         true
% 2.82/1.00  --eq_ax_congr_red                       true
% 2.82/1.00  --pure_diseq_elim                       true
% 2.82/1.00  --brand_transform                       false
% 2.82/1.00  --non_eq_to_eq                          false
% 2.82/1.00  --prep_def_merge                        true
% 2.82/1.00  --prep_def_merge_prop_impl              false
% 2.82/1.00  --prep_def_merge_mbd                    true
% 2.82/1.00  --prep_def_merge_tr_red                 false
% 2.82/1.00  --prep_def_merge_tr_cl                  false
% 2.82/1.00  --smt_preprocessing                     true
% 2.82/1.00  --smt_ac_axioms                         fast
% 2.82/1.00  --preprocessed_out                      false
% 2.82/1.00  --preprocessed_stats                    false
% 2.82/1.00  
% 2.82/1.00  ------ Abstraction refinement Options
% 2.82/1.00  
% 2.82/1.00  --abstr_ref                             []
% 2.82/1.00  --abstr_ref_prep                        false
% 2.82/1.00  --abstr_ref_until_sat                   false
% 2.82/1.00  --abstr_ref_sig_restrict                funpre
% 2.82/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.82/1.00  --abstr_ref_under                       []
% 2.82/1.00  
% 2.82/1.00  ------ SAT Options
% 2.82/1.00  
% 2.82/1.00  --sat_mode                              false
% 2.82/1.00  --sat_fm_restart_options                ""
% 2.82/1.00  --sat_gr_def                            false
% 2.82/1.00  --sat_epr_types                         true
% 2.82/1.00  --sat_non_cyclic_types                  false
% 2.82/1.00  --sat_finite_models                     false
% 2.82/1.00  --sat_fm_lemmas                         false
% 2.82/1.00  --sat_fm_prep                           false
% 2.82/1.00  --sat_fm_uc_incr                        true
% 2.82/1.00  --sat_out_model                         small
% 2.82/1.00  --sat_out_clauses                       false
% 2.82/1.00  
% 2.82/1.00  ------ QBF Options
% 2.82/1.00  
% 2.82/1.00  --qbf_mode                              false
% 2.82/1.00  --qbf_elim_univ                         false
% 2.82/1.00  --qbf_dom_inst                          none
% 2.82/1.00  --qbf_dom_pre_inst                      false
% 2.82/1.00  --qbf_sk_in                             false
% 2.82/1.00  --qbf_pred_elim                         true
% 2.82/1.00  --qbf_split                             512
% 2.82/1.00  
% 2.82/1.00  ------ BMC1 Options
% 2.82/1.00  
% 2.82/1.00  --bmc1_incremental                      false
% 2.82/1.00  --bmc1_axioms                           reachable_all
% 2.82/1.00  --bmc1_min_bound                        0
% 2.82/1.00  --bmc1_max_bound                        -1
% 2.82/1.00  --bmc1_max_bound_default                -1
% 2.82/1.00  --bmc1_symbol_reachability              true
% 2.82/1.00  --bmc1_property_lemmas                  false
% 2.82/1.00  --bmc1_k_induction                      false
% 2.82/1.00  --bmc1_non_equiv_states                 false
% 2.82/1.00  --bmc1_deadlock                         false
% 2.82/1.00  --bmc1_ucm                              false
% 2.82/1.00  --bmc1_add_unsat_core                   none
% 2.82/1.00  --bmc1_unsat_core_children              false
% 2.82/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.82/1.00  --bmc1_out_stat                         full
% 2.82/1.00  --bmc1_ground_init                      false
% 2.82/1.00  --bmc1_pre_inst_next_state              false
% 2.82/1.00  --bmc1_pre_inst_state                   false
% 2.82/1.00  --bmc1_pre_inst_reach_state             false
% 2.82/1.00  --bmc1_out_unsat_core                   false
% 2.82/1.00  --bmc1_aig_witness_out                  false
% 2.82/1.00  --bmc1_verbose                          false
% 2.82/1.00  --bmc1_dump_clauses_tptp                false
% 2.82/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.82/1.00  --bmc1_dump_file                        -
% 2.82/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.82/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.82/1.00  --bmc1_ucm_extend_mode                  1
% 2.82/1.00  --bmc1_ucm_init_mode                    2
% 2.82/1.00  --bmc1_ucm_cone_mode                    none
% 2.82/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.82/1.00  --bmc1_ucm_relax_model                  4
% 2.82/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.82/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.82/1.00  --bmc1_ucm_layered_model                none
% 2.82/1.00  --bmc1_ucm_max_lemma_size               10
% 2.82/1.00  
% 2.82/1.00  ------ AIG Options
% 2.82/1.00  
% 2.82/1.00  --aig_mode                              false
% 2.82/1.00  
% 2.82/1.00  ------ Instantiation Options
% 2.82/1.00  
% 2.82/1.00  --instantiation_flag                    true
% 2.82/1.00  --inst_sos_flag                         false
% 2.82/1.00  --inst_sos_phase                        true
% 2.82/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.82/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.82/1.00  --inst_lit_sel_side                     num_symb
% 2.82/1.00  --inst_solver_per_active                1400
% 2.82/1.00  --inst_solver_calls_frac                1.
% 2.82/1.00  --inst_passive_queue_type               priority_queues
% 2.82/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.82/1.00  --inst_passive_queues_freq              [25;2]
% 2.82/1.00  --inst_dismatching                      true
% 2.82/1.00  --inst_eager_unprocessed_to_passive     true
% 2.82/1.00  --inst_prop_sim_given                   true
% 2.82/1.00  --inst_prop_sim_new                     false
% 2.82/1.00  --inst_subs_new                         false
% 2.82/1.00  --inst_eq_res_simp                      false
% 2.82/1.00  --inst_subs_given                       false
% 2.82/1.00  --inst_orphan_elimination               true
% 2.82/1.00  --inst_learning_loop_flag               true
% 2.82/1.00  --inst_learning_start                   3000
% 2.82/1.00  --inst_learning_factor                  2
% 2.82/1.00  --inst_start_prop_sim_after_learn       3
% 2.82/1.00  --inst_sel_renew                        solver
% 2.82/1.00  --inst_lit_activity_flag                true
% 2.82/1.00  --inst_restr_to_given                   false
% 2.82/1.00  --inst_activity_threshold               500
% 2.82/1.00  --inst_out_proof                        true
% 2.82/1.00  
% 2.82/1.00  ------ Resolution Options
% 2.82/1.00  
% 2.82/1.00  --resolution_flag                       true
% 2.82/1.00  --res_lit_sel                           adaptive
% 2.82/1.00  --res_lit_sel_side                      none
% 2.82/1.00  --res_ordering                          kbo
% 2.82/1.00  --res_to_prop_solver                    active
% 2.82/1.00  --res_prop_simpl_new                    false
% 2.82/1.00  --res_prop_simpl_given                  true
% 2.82/1.00  --res_passive_queue_type                priority_queues
% 2.82/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.82/1.00  --res_passive_queues_freq               [15;5]
% 2.82/1.00  --res_forward_subs                      full
% 2.82/1.00  --res_backward_subs                     full
% 2.82/1.00  --res_forward_subs_resolution           true
% 2.82/1.00  --res_backward_subs_resolution          true
% 2.82/1.00  --res_orphan_elimination                true
% 2.82/1.00  --res_time_limit                        2.
% 2.82/1.00  --res_out_proof                         true
% 2.82/1.00  
% 2.82/1.00  ------ Superposition Options
% 2.82/1.00  
% 2.82/1.00  --superposition_flag                    true
% 2.82/1.00  --sup_passive_queue_type                priority_queues
% 2.82/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.82/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.82/1.00  --demod_completeness_check              fast
% 2.82/1.00  --demod_use_ground                      true
% 2.82/1.00  --sup_to_prop_solver                    passive
% 2.82/1.00  --sup_prop_simpl_new                    true
% 2.82/1.00  --sup_prop_simpl_given                  true
% 2.82/1.00  --sup_fun_splitting                     false
% 2.82/1.00  --sup_smt_interval                      50000
% 2.82/1.00  
% 2.82/1.00  ------ Superposition Simplification Setup
% 2.82/1.00  
% 2.82/1.00  --sup_indices_passive                   []
% 2.82/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.82/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.82/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.82/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.82/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.82/1.00  --sup_full_bw                           [BwDemod]
% 2.82/1.00  --sup_immed_triv                        [TrivRules]
% 2.82/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.82/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.82/1.00  --sup_immed_bw_main                     []
% 2.82/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.82/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.82/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.82/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.82/1.00  
% 2.82/1.00  ------ Combination Options
% 2.82/1.00  
% 2.82/1.00  --comb_res_mult                         3
% 2.82/1.00  --comb_sup_mult                         2
% 2.82/1.00  --comb_inst_mult                        10
% 2.82/1.00  
% 2.82/1.00  ------ Debug Options
% 2.82/1.00  
% 2.82/1.00  --dbg_backtrace                         false
% 2.82/1.00  --dbg_dump_prop_clauses                 false
% 2.82/1.00  --dbg_dump_prop_clauses_file            -
% 2.82/1.00  --dbg_out_stat                          false
% 2.82/1.00  ------ Parsing...
% 2.82/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.82/1.00  
% 2.82/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 2.82/1.00  
% 2.82/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.82/1.00  
% 2.82/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.82/1.00  ------ Proving...
% 2.82/1.00  ------ Problem Properties 
% 2.82/1.00  
% 2.82/1.00  
% 2.82/1.00  clauses                                 25
% 2.82/1.00  conjectures                             3
% 2.82/1.00  EPR                                     5
% 2.82/1.00  Horn                                    18
% 2.82/1.00  unary                                   8
% 2.82/1.00  binary                                  4
% 2.82/1.00  lits                                    67
% 2.82/1.00  lits eq                                 7
% 2.82/1.00  fd_pure                                 0
% 2.82/1.00  fd_pseudo                               0
% 2.82/1.00  fd_cond                                 0
% 2.82/1.00  fd_pseudo_cond                          3
% 2.82/1.00  AC symbols                              0
% 2.82/1.00  
% 2.82/1.00  ------ Schedule dynamic 5 is on 
% 2.82/1.00  
% 2.82/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.82/1.00  
% 2.82/1.00  
% 2.82/1.00  ------ 
% 2.82/1.00  Current options:
% 2.82/1.00  ------ 
% 2.82/1.00  
% 2.82/1.00  ------ Input Options
% 2.82/1.00  
% 2.82/1.00  --out_options                           all
% 2.82/1.00  --tptp_safe_out                         true
% 2.82/1.00  --problem_path                          ""
% 2.82/1.00  --include_path                          ""
% 2.82/1.00  --clausifier                            res/vclausify_rel
% 2.82/1.00  --clausifier_options                    --mode clausify
% 2.82/1.00  --stdin                                 false
% 2.82/1.00  --stats_out                             all
% 2.82/1.00  
% 2.82/1.00  ------ General Options
% 2.82/1.00  
% 2.82/1.00  --fof                                   false
% 2.82/1.00  --time_out_real                         305.
% 2.82/1.00  --time_out_virtual                      -1.
% 2.82/1.00  --symbol_type_check                     false
% 2.82/1.00  --clausify_out                          false
% 2.82/1.00  --sig_cnt_out                           false
% 2.82/1.00  --trig_cnt_out                          false
% 2.82/1.00  --trig_cnt_out_tolerance                1.
% 2.82/1.00  --trig_cnt_out_sk_spl                   false
% 2.82/1.00  --abstr_cl_out                          false
% 2.82/1.00  
% 2.82/1.00  ------ Global Options
% 2.82/1.00  
% 2.82/1.00  --schedule                              default
% 2.82/1.00  --add_important_lit                     false
% 2.82/1.00  --prop_solver_per_cl                    1000
% 2.82/1.00  --min_unsat_core                        false
% 2.82/1.00  --soft_assumptions                      false
% 2.82/1.00  --soft_lemma_size                       3
% 2.82/1.00  --prop_impl_unit_size                   0
% 2.82/1.00  --prop_impl_unit                        []
% 2.82/1.00  --share_sel_clauses                     true
% 2.82/1.00  --reset_solvers                         false
% 2.82/1.00  --bc_imp_inh                            [conj_cone]
% 2.82/1.00  --conj_cone_tolerance                   3.
% 2.82/1.00  --extra_neg_conj                        none
% 2.82/1.00  --large_theory_mode                     true
% 2.82/1.00  --prolific_symb_bound                   200
% 2.82/1.00  --lt_threshold                          2000
% 2.82/1.00  --clause_weak_htbl                      true
% 2.82/1.00  --gc_record_bc_elim                     false
% 2.82/1.00  
% 2.82/1.00  ------ Preprocessing Options
% 2.82/1.00  
% 2.82/1.00  --preprocessing_flag                    true
% 2.82/1.00  --time_out_prep_mult                    0.1
% 2.82/1.00  --splitting_mode                        input
% 2.82/1.00  --splitting_grd                         true
% 2.82/1.00  --splitting_cvd                         false
% 2.82/1.00  --splitting_cvd_svl                     false
% 2.82/1.00  --splitting_nvd                         32
% 2.82/1.00  --sub_typing                            true
% 2.82/1.00  --prep_gs_sim                           true
% 2.82/1.00  --prep_unflatten                        true
% 2.82/1.00  --prep_res_sim                          true
% 2.82/1.00  --prep_upred                            true
% 2.82/1.00  --prep_sem_filter                       exhaustive
% 2.82/1.00  --prep_sem_filter_out                   false
% 2.82/1.00  --pred_elim                             true
% 2.82/1.00  --res_sim_input                         true
% 2.82/1.00  --eq_ax_congr_red                       true
% 2.82/1.00  --pure_diseq_elim                       true
% 2.82/1.00  --brand_transform                       false
% 2.82/1.00  --non_eq_to_eq                          false
% 2.82/1.00  --prep_def_merge                        true
% 2.82/1.00  --prep_def_merge_prop_impl              false
% 2.82/1.00  --prep_def_merge_mbd                    true
% 2.82/1.00  --prep_def_merge_tr_red                 false
% 2.82/1.00  --prep_def_merge_tr_cl                  false
% 2.82/1.00  --smt_preprocessing                     true
% 2.82/1.00  --smt_ac_axioms                         fast
% 2.82/1.00  --preprocessed_out                      false
% 2.82/1.00  --preprocessed_stats                    false
% 2.82/1.00  
% 2.82/1.00  ------ Abstraction refinement Options
% 2.82/1.00  
% 2.82/1.00  --abstr_ref                             []
% 2.82/1.00  --abstr_ref_prep                        false
% 2.82/1.00  --abstr_ref_until_sat                   false
% 2.82/1.00  --abstr_ref_sig_restrict                funpre
% 2.82/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.82/1.00  --abstr_ref_under                       []
% 2.82/1.00  
% 2.82/1.00  ------ SAT Options
% 2.82/1.00  
% 2.82/1.00  --sat_mode                              false
% 2.82/1.00  --sat_fm_restart_options                ""
% 2.82/1.00  --sat_gr_def                            false
% 2.82/1.00  --sat_epr_types                         true
% 2.82/1.00  --sat_non_cyclic_types                  false
% 2.82/1.00  --sat_finite_models                     false
% 2.82/1.00  --sat_fm_lemmas                         false
% 2.82/1.00  --sat_fm_prep                           false
% 2.82/1.00  --sat_fm_uc_incr                        true
% 2.82/1.00  --sat_out_model                         small
% 2.82/1.00  --sat_out_clauses                       false
% 2.82/1.00  
% 2.82/1.00  ------ QBF Options
% 2.82/1.00  
% 2.82/1.00  --qbf_mode                              false
% 2.82/1.00  --qbf_elim_univ                         false
% 2.82/1.00  --qbf_dom_inst                          none
% 2.82/1.00  --qbf_dom_pre_inst                      false
% 2.82/1.00  --qbf_sk_in                             false
% 2.82/1.00  --qbf_pred_elim                         true
% 2.82/1.00  --qbf_split                             512
% 2.82/1.00  
% 2.82/1.00  ------ BMC1 Options
% 2.82/1.00  
% 2.82/1.00  --bmc1_incremental                      false
% 2.82/1.00  --bmc1_axioms                           reachable_all
% 2.82/1.00  --bmc1_min_bound                        0
% 2.82/1.00  --bmc1_max_bound                        -1
% 2.82/1.00  --bmc1_max_bound_default                -1
% 2.82/1.00  --bmc1_symbol_reachability              true
% 2.82/1.00  --bmc1_property_lemmas                  false
% 2.82/1.00  --bmc1_k_induction                      false
% 2.82/1.00  --bmc1_non_equiv_states                 false
% 2.82/1.00  --bmc1_deadlock                         false
% 2.82/1.00  --bmc1_ucm                              false
% 2.82/1.00  --bmc1_add_unsat_core                   none
% 2.82/1.00  --bmc1_unsat_core_children              false
% 2.82/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.82/1.00  --bmc1_out_stat                         full
% 2.82/1.00  --bmc1_ground_init                      false
% 2.82/1.00  --bmc1_pre_inst_next_state              false
% 2.82/1.00  --bmc1_pre_inst_state                   false
% 2.82/1.00  --bmc1_pre_inst_reach_state             false
% 2.82/1.00  --bmc1_out_unsat_core                   false
% 2.82/1.00  --bmc1_aig_witness_out                  false
% 2.82/1.00  --bmc1_verbose                          false
% 2.82/1.00  --bmc1_dump_clauses_tptp                false
% 2.82/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.82/1.00  --bmc1_dump_file                        -
% 2.82/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.82/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.82/1.00  --bmc1_ucm_extend_mode                  1
% 2.82/1.00  --bmc1_ucm_init_mode                    2
% 2.82/1.00  --bmc1_ucm_cone_mode                    none
% 2.82/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.82/1.00  --bmc1_ucm_relax_model                  4
% 2.82/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.82/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.82/1.00  --bmc1_ucm_layered_model                none
% 2.82/1.00  --bmc1_ucm_max_lemma_size               10
% 2.82/1.00  
% 2.82/1.00  ------ AIG Options
% 2.82/1.00  
% 2.82/1.00  --aig_mode                              false
% 2.82/1.00  
% 2.82/1.00  ------ Instantiation Options
% 2.82/1.00  
% 2.82/1.00  --instantiation_flag                    true
% 2.82/1.00  --inst_sos_flag                         false
% 2.82/1.00  --inst_sos_phase                        true
% 2.82/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.82/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.82/1.00  --inst_lit_sel_side                     none
% 2.82/1.00  --inst_solver_per_active                1400
% 2.82/1.00  --inst_solver_calls_frac                1.
% 2.82/1.00  --inst_passive_queue_type               priority_queues
% 2.82/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.82/1.00  --inst_passive_queues_freq              [25;2]
% 2.82/1.00  --inst_dismatching                      true
% 2.82/1.00  --inst_eager_unprocessed_to_passive     true
% 2.82/1.00  --inst_prop_sim_given                   true
% 2.82/1.00  --inst_prop_sim_new                     false
% 2.82/1.00  --inst_subs_new                         false
% 2.82/1.00  --inst_eq_res_simp                      false
% 2.82/1.00  --inst_subs_given                       false
% 2.82/1.00  --inst_orphan_elimination               true
% 2.82/1.00  --inst_learning_loop_flag               true
% 2.82/1.00  --inst_learning_start                   3000
% 2.82/1.00  --inst_learning_factor                  2
% 2.82/1.00  --inst_start_prop_sim_after_learn       3
% 2.82/1.00  --inst_sel_renew                        solver
% 2.82/1.00  --inst_lit_activity_flag                true
% 2.82/1.00  --inst_restr_to_given                   false
% 2.82/1.00  --inst_activity_threshold               500
% 2.82/1.00  --inst_out_proof                        true
% 2.82/1.00  
% 2.82/1.00  ------ Resolution Options
% 2.82/1.00  
% 2.82/1.00  --resolution_flag                       false
% 2.82/1.00  --res_lit_sel                           adaptive
% 2.82/1.00  --res_lit_sel_side                      none
% 2.82/1.00  --res_ordering                          kbo
% 2.82/1.00  --res_to_prop_solver                    active
% 2.82/1.00  --res_prop_simpl_new                    false
% 2.82/1.00  --res_prop_simpl_given                  true
% 2.82/1.00  --res_passive_queue_type                priority_queues
% 2.82/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.82/1.00  --res_passive_queues_freq               [15;5]
% 2.82/1.00  --res_forward_subs                      full
% 2.82/1.00  --res_backward_subs                     full
% 2.82/1.00  --res_forward_subs_resolution           true
% 2.82/1.00  --res_backward_subs_resolution          true
% 2.82/1.00  --res_orphan_elimination                true
% 2.82/1.00  --res_time_limit                        2.
% 2.82/1.00  --res_out_proof                         true
% 2.82/1.00  
% 2.82/1.00  ------ Superposition Options
% 2.82/1.00  
% 2.82/1.00  --superposition_flag                    true
% 2.82/1.00  --sup_passive_queue_type                priority_queues
% 2.82/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.82/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.82/1.00  --demod_completeness_check              fast
% 2.82/1.00  --demod_use_ground                      true
% 2.82/1.00  --sup_to_prop_solver                    passive
% 2.82/1.00  --sup_prop_simpl_new                    true
% 2.82/1.00  --sup_prop_simpl_given                  true
% 2.82/1.00  --sup_fun_splitting                     false
% 2.82/1.00  --sup_smt_interval                      50000
% 2.82/1.00  
% 2.82/1.00  ------ Superposition Simplification Setup
% 2.82/1.00  
% 2.82/1.00  --sup_indices_passive                   []
% 2.82/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.82/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.82/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.82/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.82/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.82/1.00  --sup_full_bw                           [BwDemod]
% 2.82/1.00  --sup_immed_triv                        [TrivRules]
% 2.82/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.82/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.82/1.00  --sup_immed_bw_main                     []
% 2.82/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.82/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.82/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.82/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.82/1.00  
% 2.82/1.00  ------ Combination Options
% 2.82/1.00  
% 2.82/1.00  --comb_res_mult                         3
% 2.82/1.00  --comb_sup_mult                         2
% 2.82/1.00  --comb_inst_mult                        10
% 2.82/1.00  
% 2.82/1.00  ------ Debug Options
% 2.82/1.00  
% 2.82/1.00  --dbg_backtrace                         false
% 2.82/1.00  --dbg_dump_prop_clauses                 false
% 2.82/1.00  --dbg_dump_prop_clauses_file            -
% 2.82/1.00  --dbg_out_stat                          false
% 2.82/1.00  
% 2.82/1.00  
% 2.82/1.00  
% 2.82/1.00  
% 2.82/1.00  ------ Proving...
% 2.82/1.00  
% 2.82/1.00  
% 2.82/1.00  % SZS status Theorem for theBenchmark.p
% 2.82/1.00  
% 2.82/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.82/1.00  
% 2.82/1.00  fof(f16,conjecture,(
% 2.82/1.00    ! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k1_xboole_0,X0) => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))))),
% 2.82/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.82/1.00  
% 2.82/1.00  fof(f17,negated_conjecture,(
% 2.82/1.00    ~! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k1_xboole_0,X0) => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))))),
% 2.82/1.00    inference(negated_conjecture,[],[f16])).
% 2.82/1.00  
% 2.82/1.00  fof(f37,plain,(
% 2.82/1.00    ? [X0] : ((k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0)) & r2_hidden(k1_xboole_0,X0)) & ~v1_xboole_0(X0))),
% 2.82/1.00    inference(ennf_transformation,[],[f17])).
% 2.82/1.00  
% 2.82/1.00  fof(f38,plain,(
% 2.82/1.00    ? [X0] : (k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0)) & r2_hidden(k1_xboole_0,X0) & ~v1_xboole_0(X0))),
% 2.82/1.00    inference(flattening,[],[f37])).
% 2.82/1.00  
% 2.82/1.00  fof(f47,plain,(
% 2.82/1.00    ? [X0] : (k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0)) & r2_hidden(k1_xboole_0,X0) & ~v1_xboole_0(X0)) => (k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK2)) & r2_hidden(k1_xboole_0,sK2) & ~v1_xboole_0(sK2))),
% 2.82/1.00    introduced(choice_axiom,[])).
% 2.82/1.00  
% 2.82/1.00  fof(f48,plain,(
% 2.82/1.00    k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK2)) & r2_hidden(k1_xboole_0,sK2) & ~v1_xboole_0(sK2)),
% 2.82/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f38,f47])).
% 2.82/1.00  
% 2.82/1.00  fof(f78,plain,(
% 2.82/1.00    r2_hidden(k1_xboole_0,sK2)),
% 2.82/1.00    inference(cnf_transformation,[],[f48])).
% 2.82/1.00  
% 2.82/1.00  fof(f4,axiom,(
% 2.82/1.00    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 2.82/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.82/1.00  
% 2.82/1.00  fof(f25,plain,(
% 2.82/1.00    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 2.82/1.00    inference(ennf_transformation,[],[f4])).
% 2.82/1.00  
% 2.82/1.00  fof(f54,plain,(
% 2.82/1.00    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 2.82/1.00    inference(cnf_transformation,[],[f25])).
% 2.82/1.00  
% 2.82/1.00  fof(f10,axiom,(
% 2.82/1.00    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (r1_lattice3(X0,k1_xboole_0,X1) & r2_lattice3(X0,k1_xboole_0,X1))))),
% 2.82/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.82/1.00  
% 2.82/1.00  fof(f23,plain,(
% 2.82/1.00    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r2_lattice3(X0,k1_xboole_0,X1)))),
% 2.82/1.00    inference(pure_predicate_removal,[],[f10])).
% 2.82/1.00  
% 2.82/1.00  fof(f34,plain,(
% 2.82/1.00    ! [X0] : (! [X1] : (r2_lattice3(X0,k1_xboole_0,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.82/1.00    inference(ennf_transformation,[],[f23])).
% 2.82/1.00  
% 2.82/1.00  fof(f68,plain,(
% 2.82/1.00    ( ! [X0,X1] : (r2_lattice3(X0,k1_xboole_0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.82/1.00    inference(cnf_transformation,[],[f34])).
% 2.82/1.00  
% 2.82/1.00  fof(f11,axiom,(
% 2.82/1.00    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 2.82/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.82/1.00  
% 2.82/1.00  fof(f22,plain,(
% 2.82/1.00    ! [X0] : l1_orders_2(k2_yellow_1(X0))),
% 2.82/1.00    inference(pure_predicate_removal,[],[f11])).
% 2.82/1.00  
% 2.82/1.00  fof(f69,plain,(
% 2.82/1.00    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 2.82/1.00    inference(cnf_transformation,[],[f22])).
% 2.82/1.00  
% 2.82/1.00  fof(f14,axiom,(
% 2.82/1.00    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 2.82/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.82/1.00  
% 2.82/1.00  fof(f73,plain,(
% 2.82/1.00    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 2.82/1.00    inference(cnf_transformation,[],[f14])).
% 2.82/1.00  
% 2.82/1.00  fof(f2,axiom,(
% 2.82/1.00    v1_xboole_0(k1_xboole_0)),
% 2.82/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.82/1.00  
% 2.82/1.00  fof(f52,plain,(
% 2.82/1.00    v1_xboole_0(k1_xboole_0)),
% 2.82/1.00    inference(cnf_transformation,[],[f2])).
% 2.82/1.00  
% 2.82/1.00  fof(f1,axiom,(
% 2.82/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.82/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.82/1.00  
% 2.82/1.00  fof(f24,plain,(
% 2.82/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.82/1.00    inference(ennf_transformation,[],[f1])).
% 2.82/1.00  
% 2.82/1.00  fof(f39,plain,(
% 2.82/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.82/1.00    inference(nnf_transformation,[],[f24])).
% 2.82/1.00  
% 2.82/1.00  fof(f40,plain,(
% 2.82/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.82/1.00    inference(rectify,[],[f39])).
% 2.82/1.00  
% 2.82/1.00  fof(f41,plain,(
% 2.82/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.82/1.00    introduced(choice_axiom,[])).
% 2.82/1.00  
% 2.82/1.00  fof(f42,plain,(
% 2.82/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.82/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f40,f41])).
% 2.82/1.00  
% 2.82/1.00  fof(f50,plain,(
% 2.82/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.82/1.00    inference(cnf_transformation,[],[f42])).
% 2.82/1.00  
% 2.82/1.00  fof(f3,axiom,(
% 2.82/1.00    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.82/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.82/1.00  
% 2.82/1.00  fof(f53,plain,(
% 2.82/1.00    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.82/1.00    inference(cnf_transformation,[],[f3])).
% 2.82/1.00  
% 2.82/1.00  fof(f6,axiom,(
% 2.82/1.00    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.82/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.82/1.00  
% 2.82/1.00  fof(f28,plain,(
% 2.82/1.00    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.82/1.00    inference(ennf_transformation,[],[f6])).
% 2.82/1.00  
% 2.82/1.00  fof(f56,plain,(
% 2.82/1.00    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.82/1.00    inference(cnf_transformation,[],[f28])).
% 2.82/1.00  
% 2.82/1.00  fof(f15,axiom,(
% 2.82/1.00    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)))))),
% 2.82/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.82/1.00  
% 2.82/1.00  fof(f36,plain,(
% 2.82/1.00    ! [X0] : (! [X1] : (! [X2] : ((r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 2.82/1.00    inference(ennf_transformation,[],[f15])).
% 2.82/1.00  
% 2.82/1.00  fof(f46,plain,(
% 2.82/1.00    ! [X0] : (! [X1] : (! [X2] : (((r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2)) & (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 2.82/1.00    inference(nnf_transformation,[],[f36])).
% 2.82/1.00  
% 2.82/1.00  fof(f76,plain,(
% 2.82/1.00    ( ! [X2,X0,X1] : (r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 2.82/1.00    inference(cnf_transformation,[],[f46])).
% 2.82/1.00  
% 2.82/1.00  fof(f7,axiom,(
% 2.82/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 2.82/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.82/1.00  
% 2.82/1.00  fof(f29,plain,(
% 2.82/1.00    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.82/1.00    inference(ennf_transformation,[],[f7])).
% 2.82/1.00  
% 2.82/1.00  fof(f30,plain,(
% 2.82/1.00    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.82/1.00    inference(flattening,[],[f29])).
% 2.82/1.00  
% 2.82/1.00  fof(f43,plain,(
% 2.82/1.00    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.82/1.00    inference(nnf_transformation,[],[f30])).
% 2.82/1.00  
% 2.82/1.00  fof(f57,plain,(
% 2.82/1.00    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.82/1.00    inference(cnf_transformation,[],[f43])).
% 2.82/1.00  
% 2.82/1.00  fof(f12,axiom,(
% 2.82/1.00    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v4_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 2.82/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.82/1.00  
% 2.82/1.00  fof(f19,plain,(
% 2.82/1.00    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 2.82/1.00    inference(pure_predicate_removal,[],[f12])).
% 2.82/1.00  
% 2.82/1.00  fof(f20,plain,(
% 2.82/1.00    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)))),
% 2.82/1.00    inference(pure_predicate_removal,[],[f19])).
% 2.82/1.00  
% 2.82/1.00  fof(f70,plain,(
% 2.82/1.00    ( ! [X0] : (v3_orders_2(k2_yellow_1(X0))) )),
% 2.82/1.00    inference(cnf_transformation,[],[f20])).
% 2.82/1.00  
% 2.82/1.00  fof(f13,axiom,(
% 2.82/1.00    ! [X0] : (~v1_xboole_0(X0) => (v1_orders_2(k2_yellow_1(X0)) & ~v2_struct_0(k2_yellow_1(X0))))),
% 2.82/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.82/1.00  
% 2.82/1.00  fof(f21,plain,(
% 2.82/1.00    ! [X0] : (~v1_xboole_0(X0) => ~v2_struct_0(k2_yellow_1(X0)))),
% 2.82/1.00    inference(pure_predicate_removal,[],[f13])).
% 2.82/1.00  
% 2.82/1.00  fof(f35,plain,(
% 2.82/1.00    ! [X0] : (~v2_struct_0(k2_yellow_1(X0)) | v1_xboole_0(X0))),
% 2.82/1.00    inference(ennf_transformation,[],[f21])).
% 2.82/1.00  
% 2.82/1.00  fof(f72,plain,(
% 2.82/1.00    ( ! [X0] : (~v2_struct_0(k2_yellow_1(X0)) | v1_xboole_0(X0)) )),
% 2.82/1.00    inference(cnf_transformation,[],[f35])).
% 2.82/1.00  
% 2.82/1.00  fof(f9,axiom,(
% 2.82/1.00    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1)) => (r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1)) & ((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1))))))),
% 2.82/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.82/1.00  
% 2.82/1.00  fof(f18,plain,(
% 2.82/1.00    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1)) => (r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1)) & ((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) => (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X4) => r1_orders_2(X0,X1,X4))) & r2_lattice3(X0,X2,X1))))))),
% 2.82/1.00    inference(rectify,[],[f9])).
% 2.82/1.00  
% 2.82/1.00  fof(f32,plain,(
% 2.82/1.00    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | (? [X3] : ((~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3)) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1))) & ((! [X4] : ((r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | (~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0)))),
% 2.82/1.00    inference(ennf_transformation,[],[f18])).
% 2.82/1.00  
% 2.82/1.00  fof(f33,plain,(
% 2.82/1.00    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | ? [X3] : (~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | ~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 2.82/1.00    inference(flattening,[],[f32])).
% 2.82/1.00  
% 2.82/1.00  fof(f44,plain,(
% 2.82/1.00    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X1,sK1(X0,X1,X2)) & r2_lattice3(X0,X2,sK1(X0,X1,X2)) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))))),
% 2.82/1.00    introduced(choice_axiom,[])).
% 2.82/1.00  
% 2.82/1.00  fof(f45,plain,(
% 2.82/1.00    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | (~r1_orders_2(X0,X1,sK1(X0,X1,X2)) & r2_lattice3(X0,X2,sK1(X0,X1,X2)) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | ~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 2.82/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f33,f44])).
% 2.82/1.00  
% 2.82/1.00  fof(f64,plain,(
% 2.82/1.00    ( ! [X2,X0,X1] : (k1_yellow_0(X0,X2) = X1 | ~r1_orders_2(X0,X1,sK1(X0,X1,X2)) | ~r2_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 2.82/1.00    inference(cnf_transformation,[],[f45])).
% 2.82/1.00  
% 2.82/1.00  fof(f71,plain,(
% 2.82/1.00    ( ! [X0] : (v5_orders_2(k2_yellow_1(X0))) )),
% 2.82/1.00    inference(cnf_transformation,[],[f20])).
% 2.82/1.00  
% 2.82/1.00  fof(f62,plain,(
% 2.82/1.00    ( ! [X2,X0,X1] : (k1_yellow_0(X0,X2) = X1 | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) | ~r2_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 2.82/1.00    inference(cnf_transformation,[],[f45])).
% 2.82/1.00  
% 2.82/1.00  fof(f8,axiom,(
% 2.82/1.00    ! [X0] : (l1_orders_2(X0) => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0))),
% 2.82/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.82/1.00  
% 2.82/1.00  fof(f31,plain,(
% 2.82/1.00    ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0))),
% 2.82/1.00    inference(ennf_transformation,[],[f8])).
% 2.82/1.00  
% 2.82/1.00  fof(f59,plain,(
% 2.82/1.00    ( ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0)) )),
% 2.82/1.00    inference(cnf_transformation,[],[f31])).
% 2.82/1.00  
% 2.82/1.00  fof(f79,plain,(
% 2.82/1.00    k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK2))),
% 2.82/1.00    inference(cnf_transformation,[],[f48])).
% 2.82/1.00  
% 2.82/1.00  fof(f77,plain,(
% 2.82/1.00    ~v1_xboole_0(sK2)),
% 2.82/1.00    inference(cnf_transformation,[],[f48])).
% 2.82/1.00  
% 2.82/1.00  cnf(c_29,negated_conjecture,
% 2.82/1.00      ( r2_hidden(k1_xboole_0,sK2) ),
% 2.82/1.00      inference(cnf_transformation,[],[f78]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_2678,plain,
% 2.82/1.00      ( r2_hidden(k1_xboole_0,sK2) = iProver_top ),
% 2.82/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_5,plain,
% 2.82/1.00      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 2.82/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_2681,plain,
% 2.82/1.00      ( m1_subset_1(X0,X1) = iProver_top
% 2.82/1.00      | r2_hidden(X0,X1) != iProver_top ),
% 2.82/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_3013,plain,
% 2.82/1.00      ( m1_subset_1(k1_xboole_0,sK2) = iProver_top ),
% 2.82/1.00      inference(superposition,[status(thm)],[c_2678,c_2681]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_19,plain,
% 2.82/1.00      ( r2_lattice3(X0,k1_xboole_0,X1)
% 2.82/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.82/1.00      | ~ l1_orders_2(X0) ),
% 2.82/1.00      inference(cnf_transformation,[],[f68]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_20,plain,
% 2.82/1.00      ( l1_orders_2(k2_yellow_1(X0)) ),
% 2.82/1.00      inference(cnf_transformation,[],[f69]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_1127,plain,
% 2.82/1.00      ( r2_lattice3(X0,k1_xboole_0,X1)
% 2.82/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.82/1.00      | k2_yellow_1(X2) != X0 ),
% 2.82/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_20]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_1128,plain,
% 2.82/1.00      ( r2_lattice3(k2_yellow_1(X0),k1_xboole_0,X1)
% 2.82/1.00      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) ),
% 2.82/1.00      inference(unflattening,[status(thm)],[c_1127]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_2666,plain,
% 2.82/1.00      ( r2_lattice3(k2_yellow_1(X0),k1_xboole_0,X1) = iProver_top
% 2.82/1.00      | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top ),
% 2.82/1.00      inference(predicate_to_equality,[status(thm)],[c_1128]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_25,plain,
% 2.82/1.00      ( u1_struct_0(k2_yellow_1(X0)) = X0 ),
% 2.82/1.00      inference(cnf_transformation,[],[f73]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_2715,plain,
% 2.82/1.00      ( r2_lattice3(k2_yellow_1(X0),k1_xboole_0,X1) = iProver_top
% 2.82/1.00      | m1_subset_1(X1,X0) != iProver_top ),
% 2.82/1.00      inference(light_normalisation,[status(thm)],[c_2666,c_25]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_3,plain,
% 2.82/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 2.82/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_2683,plain,
% 2.82/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.82/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_1,plain,
% 2.82/1.00      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 2.82/1.00      inference(cnf_transformation,[],[f50]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_2685,plain,
% 2.82/1.00      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 2.82/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 2.82/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_4,plain,
% 2.82/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.82/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_2682,plain,
% 2.82/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.82/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_7,plain,
% 2.82/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.82/1.00      | ~ r2_hidden(X2,X0)
% 2.82/1.00      | ~ v1_xboole_0(X1) ),
% 2.82/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_2679,plain,
% 2.82/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.82/1.00      | r2_hidden(X2,X0) != iProver_top
% 2.82/1.00      | v1_xboole_0(X1) != iProver_top ),
% 2.82/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_3006,plain,
% 2.82/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 2.82/1.00      | v1_xboole_0(X1) != iProver_top ),
% 2.82/1.00      inference(superposition,[status(thm)],[c_2682,c_2679]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_3258,plain,
% 2.82/1.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top
% 2.82/1.00      | v1_xboole_0(X1) != iProver_top ),
% 2.82/1.00      inference(superposition,[status(thm)],[c_2685,c_3006]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_3373,plain,
% 2.82/1.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.82/1.00      inference(superposition,[status(thm)],[c_2683,c_3258]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_26,plain,
% 2.82/1.00      ( r3_orders_2(k2_yellow_1(X0),X1,X2)
% 2.82/1.00      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.82/1.00      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.82/1.00      | ~ r1_tarski(X1,X2)
% 2.82/1.00      | v1_xboole_0(X0) ),
% 2.82/1.00      inference(cnf_transformation,[],[f76]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_9,plain,
% 2.82/1.00      ( r1_orders_2(X0,X1,X2)
% 2.82/1.00      | ~ r3_orders_2(X0,X1,X2)
% 2.82/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.82/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.82/1.00      | v2_struct_0(X0)
% 2.82/1.00      | ~ v3_orders_2(X0)
% 2.82/1.00      | ~ l1_orders_2(X0) ),
% 2.82/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_22,plain,
% 2.82/1.00      ( v3_orders_2(k2_yellow_1(X0)) ),
% 2.82/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_328,plain,
% 2.82/1.00      ( r1_orders_2(X0,X1,X2)
% 2.82/1.00      | ~ r3_orders_2(X0,X1,X2)
% 2.82/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.82/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.82/1.00      | v2_struct_0(X0)
% 2.82/1.00      | ~ l1_orders_2(X0)
% 2.82/1.00      | k2_yellow_1(X3) != X0 ),
% 2.82/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_22]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_329,plain,
% 2.82/1.00      ( r1_orders_2(k2_yellow_1(X0),X1,X2)
% 2.82/1.00      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
% 2.82/1.00      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.82/1.00      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.82/1.00      | v2_struct_0(k2_yellow_1(X0))
% 2.82/1.00      | ~ l1_orders_2(k2_yellow_1(X0)) ),
% 2.82/1.00      inference(unflattening,[status(thm)],[c_328]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_333,plain,
% 2.82/1.00      ( v2_struct_0(k2_yellow_1(X0))
% 2.82/1.00      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.82/1.00      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.82/1.00      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
% 2.82/1.00      | r1_orders_2(k2_yellow_1(X0),X1,X2) ),
% 2.82/1.00      inference(global_propositional_subsumption,
% 2.82/1.00                [status(thm)],
% 2.82/1.00                [c_329,c_20]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_334,plain,
% 2.82/1.00      ( r1_orders_2(k2_yellow_1(X0),X1,X2)
% 2.82/1.00      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
% 2.82/1.00      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.82/1.00      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.82/1.00      | v2_struct_0(k2_yellow_1(X0)) ),
% 2.82/1.00      inference(renaming,[status(thm)],[c_333]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_23,plain,
% 2.82/1.00      ( ~ v2_struct_0(k2_yellow_1(X0)) | v1_xboole_0(X0) ),
% 2.82/1.00      inference(cnf_transformation,[],[f72]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_412,plain,
% 2.82/1.00      ( r1_orders_2(k2_yellow_1(X0),X1,X2)
% 2.82/1.00      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
% 2.82/1.00      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.82/1.00      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.82/1.00      | v1_xboole_0(X0) ),
% 2.82/1.00      inference(resolution,[status(thm)],[c_334,c_23]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_603,plain,
% 2.82/1.00      ( r1_orders_2(k2_yellow_1(X0),X1,X2)
% 2.82/1.00      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.82/1.00      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.82/1.00      | ~ r1_tarski(X1,X2)
% 2.82/1.00      | v1_xboole_0(X0) ),
% 2.82/1.00      inference(resolution,[status(thm)],[c_26,c_412]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_2675,plain,
% 2.82/1.00      ( r1_orders_2(k2_yellow_1(X0),X1,X2) = iProver_top
% 2.82/1.00      | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 2.82/1.00      | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 2.82/1.00      | r1_tarski(X1,X2) != iProver_top
% 2.82/1.00      | v1_xboole_0(X0) = iProver_top ),
% 2.82/1.00      inference(predicate_to_equality,[status(thm)],[c_603]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_2799,plain,
% 2.82/1.00      ( r1_orders_2(k2_yellow_1(X0),X1,X2) = iProver_top
% 2.82/1.00      | m1_subset_1(X1,X0) != iProver_top
% 2.82/1.00      | m1_subset_1(X2,X0) != iProver_top
% 2.82/1.00      | r1_tarski(X1,X2) != iProver_top
% 2.82/1.00      | v1_xboole_0(X0) = iProver_top ),
% 2.82/1.00      inference(light_normalisation,[status(thm)],[c_2675,c_25]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_14,plain,
% 2.82/1.00      ( ~ r2_lattice3(X0,X1,X2)
% 2.82/1.00      | ~ r1_orders_2(X0,X2,sK1(X0,X2,X1))
% 2.82/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.82/1.00      | ~ v5_orders_2(X0)
% 2.82/1.00      | ~ l1_orders_2(X0)
% 2.82/1.00      | k1_yellow_0(X0,X1) = X2 ),
% 2.82/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_21,plain,
% 2.82/1.00      ( v5_orders_2(k2_yellow_1(X0)) ),
% 2.82/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_991,plain,
% 2.82/1.00      ( ~ r2_lattice3(X0,X1,X2)
% 2.82/1.00      | ~ r1_orders_2(X0,X2,sK1(X0,X2,X1))
% 2.82/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.82/1.00      | ~ l1_orders_2(X0)
% 2.82/1.00      | k1_yellow_0(X0,X1) = X2
% 2.82/1.00      | k2_yellow_1(X3) != X0 ),
% 2.82/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_21]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_992,plain,
% 2.82/1.00      ( ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
% 2.82/1.00      | ~ r1_orders_2(k2_yellow_1(X0),X2,sK1(k2_yellow_1(X0),X2,X1))
% 2.82/1.00      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.82/1.00      | ~ l1_orders_2(k2_yellow_1(X0))
% 2.82/1.00      | k1_yellow_0(k2_yellow_1(X0),X1) = X2 ),
% 2.82/1.00      inference(unflattening,[status(thm)],[c_991]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_996,plain,
% 2.82/1.00      ( ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.82/1.00      | ~ r1_orders_2(k2_yellow_1(X0),X2,sK1(k2_yellow_1(X0),X2,X1))
% 2.82/1.00      | ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
% 2.82/1.00      | k1_yellow_0(k2_yellow_1(X0),X1) = X2 ),
% 2.82/1.00      inference(global_propositional_subsumption,
% 2.82/1.00                [status(thm)],
% 2.82/1.00                [c_992,c_20]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_997,plain,
% 2.82/1.00      ( ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
% 2.82/1.00      | ~ r1_orders_2(k2_yellow_1(X0),X2,sK1(k2_yellow_1(X0),X2,X1))
% 2.82/1.00      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.82/1.00      | k1_yellow_0(k2_yellow_1(X0),X1) = X2 ),
% 2.82/1.00      inference(renaming,[status(thm)],[c_996]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_2670,plain,
% 2.82/1.00      ( k1_yellow_0(k2_yellow_1(X0),X1) = X2
% 2.82/1.00      | r2_lattice3(k2_yellow_1(X0),X1,X2) != iProver_top
% 2.82/1.00      | r1_orders_2(k2_yellow_1(X0),X2,sK1(k2_yellow_1(X0),X2,X1)) != iProver_top
% 2.82/1.00      | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top ),
% 2.82/1.00      inference(predicate_to_equality,[status(thm)],[c_997]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_2790,plain,
% 2.82/1.00      ( k1_yellow_0(k2_yellow_1(X0),X1) = X2
% 2.82/1.00      | r2_lattice3(k2_yellow_1(X0),X1,X2) != iProver_top
% 2.82/1.00      | r1_orders_2(k2_yellow_1(X0),X2,sK1(k2_yellow_1(X0),X2,X1)) != iProver_top
% 2.82/1.00      | m1_subset_1(X2,X0) != iProver_top ),
% 2.82/1.00      inference(light_normalisation,[status(thm)],[c_2670,c_25]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_3902,plain,
% 2.82/1.00      ( k1_yellow_0(k2_yellow_1(X0),X1) = X2
% 2.82/1.00      | r2_lattice3(k2_yellow_1(X0),X1,X2) != iProver_top
% 2.82/1.00      | m1_subset_1(X2,X0) != iProver_top
% 2.82/1.00      | m1_subset_1(sK1(k2_yellow_1(X0),X2,X1),X0) != iProver_top
% 2.82/1.00      | r1_tarski(X2,sK1(k2_yellow_1(X0),X2,X1)) != iProver_top
% 2.82/1.00      | v1_xboole_0(X0) = iProver_top ),
% 2.82/1.00      inference(superposition,[status(thm)],[c_2799,c_2790]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_16,plain,
% 2.82/1.00      ( ~ r2_lattice3(X0,X1,X2)
% 2.82/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.82/1.00      | m1_subset_1(sK1(X0,X2,X1),u1_struct_0(X0))
% 2.82/1.00      | ~ v5_orders_2(X0)
% 2.82/1.00      | ~ l1_orders_2(X0)
% 2.82/1.00      | k1_yellow_0(X0,X1) = X2 ),
% 2.82/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_943,plain,
% 2.82/1.00      ( ~ r2_lattice3(X0,X1,X2)
% 2.82/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.82/1.00      | m1_subset_1(sK1(X0,X2,X1),u1_struct_0(X0))
% 2.82/1.00      | ~ l1_orders_2(X0)
% 2.82/1.00      | k1_yellow_0(X0,X1) = X2
% 2.82/1.00      | k2_yellow_1(X3) != X0 ),
% 2.82/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_21]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_944,plain,
% 2.82/1.00      ( ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
% 2.82/1.00      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.82/1.00      | m1_subset_1(sK1(k2_yellow_1(X0),X2,X1),u1_struct_0(k2_yellow_1(X0)))
% 2.82/1.00      | ~ l1_orders_2(k2_yellow_1(X0))
% 2.82/1.00      | k1_yellow_0(k2_yellow_1(X0),X1) = X2 ),
% 2.82/1.00      inference(unflattening,[status(thm)],[c_943]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_948,plain,
% 2.82/1.00      ( m1_subset_1(sK1(k2_yellow_1(X0),X2,X1),u1_struct_0(k2_yellow_1(X0)))
% 2.82/1.00      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.82/1.00      | ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
% 2.82/1.00      | k1_yellow_0(k2_yellow_1(X0),X1) = X2 ),
% 2.82/1.00      inference(global_propositional_subsumption,
% 2.82/1.00                [status(thm)],
% 2.82/1.00                [c_944,c_20]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_949,plain,
% 2.82/1.00      ( ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
% 2.82/1.00      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.82/1.00      | m1_subset_1(sK1(k2_yellow_1(X0),X2,X1),u1_struct_0(k2_yellow_1(X0)))
% 2.82/1.00      | k1_yellow_0(k2_yellow_1(X0),X1) = X2 ),
% 2.82/1.00      inference(renaming,[status(thm)],[c_948]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_2672,plain,
% 2.82/1.00      ( k1_yellow_0(k2_yellow_1(X0),X1) = X2
% 2.82/1.00      | r2_lattice3(k2_yellow_1(X0),X1,X2) != iProver_top
% 2.82/1.00      | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 2.82/1.00      | m1_subset_1(sK1(k2_yellow_1(X0),X2,X1),u1_struct_0(k2_yellow_1(X0))) = iProver_top ),
% 2.82/1.00      inference(predicate_to_equality,[status(thm)],[c_949]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_2772,plain,
% 2.82/1.00      ( k1_yellow_0(k2_yellow_1(X0),X1) = X2
% 2.82/1.00      | r2_lattice3(k2_yellow_1(X0),X1,X2) != iProver_top
% 2.82/1.00      | m1_subset_1(X2,X0) != iProver_top
% 2.82/1.00      | m1_subset_1(sK1(k2_yellow_1(X0),X2,X1),X0) = iProver_top ),
% 2.82/1.00      inference(light_normalisation,[status(thm)],[c_2672,c_25]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_5924,plain,
% 2.82/1.00      ( m1_subset_1(X2,X0) != iProver_top
% 2.82/1.00      | r2_lattice3(k2_yellow_1(X0),X1,X2) != iProver_top
% 2.82/1.00      | k1_yellow_0(k2_yellow_1(X0),X1) = X2
% 2.82/1.00      | r1_tarski(X2,sK1(k2_yellow_1(X0),X2,X1)) != iProver_top
% 2.82/1.00      | v1_xboole_0(X0) = iProver_top ),
% 2.82/1.00      inference(global_propositional_subsumption,
% 2.82/1.00                [status(thm)],
% 2.82/1.00                [c_3902,c_2772]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_5925,plain,
% 2.82/1.00      ( k1_yellow_0(k2_yellow_1(X0),X1) = X2
% 2.82/1.00      | r2_lattice3(k2_yellow_1(X0),X1,X2) != iProver_top
% 2.82/1.00      | m1_subset_1(X2,X0) != iProver_top
% 2.82/1.00      | r1_tarski(X2,sK1(k2_yellow_1(X0),X2,X1)) != iProver_top
% 2.82/1.00      | v1_xboole_0(X0) = iProver_top ),
% 2.82/1.00      inference(renaming,[status(thm)],[c_5924]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_5933,plain,
% 2.82/1.00      ( k1_yellow_0(k2_yellow_1(X0),X1) = k1_xboole_0
% 2.82/1.00      | r2_lattice3(k2_yellow_1(X0),X1,k1_xboole_0) != iProver_top
% 2.82/1.00      | m1_subset_1(k1_xboole_0,X0) != iProver_top
% 2.82/1.00      | v1_xboole_0(X0) = iProver_top ),
% 2.82/1.00      inference(superposition,[status(thm)],[c_3373,c_5925]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_6413,plain,
% 2.82/1.00      ( k1_yellow_0(k2_yellow_1(X0),k1_xboole_0) = k1_xboole_0
% 2.82/1.00      | m1_subset_1(k1_xboole_0,X0) != iProver_top
% 2.82/1.00      | v1_xboole_0(X0) = iProver_top ),
% 2.82/1.00      inference(superposition,[status(thm)],[c_2715,c_5933]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_10,plain,
% 2.82/1.00      ( ~ l1_orders_2(X0)
% 2.82/1.00      | k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0) ),
% 2.82/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_1139,plain,
% 2.82/1.00      ( k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0)
% 2.82/1.00      | k2_yellow_1(X1) != X0 ),
% 2.82/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_20]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_1140,plain,
% 2.82/1.00      ( k1_yellow_0(k2_yellow_1(X0),k1_xboole_0) = k3_yellow_0(k2_yellow_1(X0)) ),
% 2.82/1.00      inference(unflattening,[status(thm)],[c_1139]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_6414,plain,
% 2.82/1.00      ( k3_yellow_0(k2_yellow_1(X0)) = k1_xboole_0
% 2.82/1.00      | m1_subset_1(k1_xboole_0,X0) != iProver_top
% 2.82/1.00      | v1_xboole_0(X0) = iProver_top ),
% 2.82/1.00      inference(demodulation,[status(thm)],[c_6413,c_1140]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_6421,plain,
% 2.82/1.00      ( k3_yellow_0(k2_yellow_1(sK2)) = k1_xboole_0
% 2.82/1.00      | v1_xboole_0(sK2) = iProver_top ),
% 2.82/1.00      inference(superposition,[status(thm)],[c_3013,c_6414]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_2259,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_2926,plain,
% 2.82/1.00      ( k3_yellow_0(k2_yellow_1(sK2)) != X0
% 2.82/1.00      | k1_xboole_0 != X0
% 2.82/1.00      | k1_xboole_0 = k3_yellow_0(k2_yellow_1(sK2)) ),
% 2.82/1.00      inference(instantiation,[status(thm)],[c_2259]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_2927,plain,
% 2.82/1.00      ( k3_yellow_0(k2_yellow_1(sK2)) != k1_xboole_0
% 2.82/1.00      | k1_xboole_0 = k3_yellow_0(k2_yellow_1(sK2))
% 2.82/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 2.82/1.00      inference(instantiation,[status(thm)],[c_2926]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_2258,plain,( X0 = X0 ),theory(equality) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_2285,plain,
% 2.82/1.00      ( k1_xboole_0 = k1_xboole_0 ),
% 2.82/1.00      inference(instantiation,[status(thm)],[c_2258]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_28,negated_conjecture,
% 2.82/1.00      ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK2)) ),
% 2.82/1.00      inference(cnf_transformation,[],[f79]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_30,negated_conjecture,
% 2.82/1.00      ( ~ v1_xboole_0(sK2) ),
% 2.82/1.00      inference(cnf_transformation,[],[f77]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_31,plain,
% 2.82/1.00      ( v1_xboole_0(sK2) != iProver_top ),
% 2.82/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(contradiction,plain,
% 2.82/1.00      ( $false ),
% 2.82/1.00      inference(minisat,[status(thm)],[c_6421,c_2927,c_2285,c_28,c_31]) ).
% 2.82/1.00  
% 2.82/1.00  
% 2.82/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.82/1.00  
% 2.82/1.00  ------                               Statistics
% 2.82/1.00  
% 2.82/1.00  ------ General
% 2.82/1.00  
% 2.82/1.00  abstr_ref_over_cycles:                  0
% 2.82/1.00  abstr_ref_under_cycles:                 0
% 2.82/1.00  gc_basic_clause_elim:                   0
% 2.82/1.00  forced_gc_time:                         0
% 2.82/1.00  parsing_time:                           0.011
% 2.82/1.00  unif_index_cands_time:                  0.
% 2.82/1.00  unif_index_add_time:                    0.
% 2.82/1.00  orderings_time:                         0.
% 2.82/1.00  out_proof_time:                         0.01
% 2.82/1.00  total_time:                             0.242
% 2.82/1.00  num_of_symbols:                         54
% 2.82/1.00  num_of_terms:                           4854
% 2.82/1.00  
% 2.82/1.00  ------ Preprocessing
% 2.82/1.00  
% 2.82/1.00  num_of_splits:                          0
% 2.82/1.00  num_of_split_atoms:                     0
% 2.82/1.00  num_of_reused_defs:                     0
% 2.82/1.00  num_eq_ax_congr_red:                    34
% 2.82/1.00  num_of_sem_filtered_clauses:            1
% 2.82/1.00  num_of_subtypes:                        0
% 2.82/1.00  monotx_restored_types:                  0
% 2.82/1.00  sat_num_of_epr_types:                   0
% 2.82/1.00  sat_num_of_non_cyclic_types:            0
% 2.82/1.00  sat_guarded_non_collapsed_types:        0
% 2.82/1.00  num_pure_diseq_elim:                    0
% 2.82/1.00  simp_replaced_by:                       0
% 2.82/1.00  res_preprocessed:                       135
% 2.82/1.00  prep_upred:                             0
% 2.82/1.00  prep_unflattend:                        66
% 2.82/1.00  smt_new_axioms:                         0
% 2.82/1.00  pred_elim_cands:                        7
% 2.82/1.00  pred_elim:                              5
% 2.82/1.00  pred_elim_cl:                           6
% 2.82/1.00  pred_elim_cycles:                       14
% 2.82/1.00  merged_defs:                            0
% 2.82/1.00  merged_defs_ncl:                        0
% 2.82/1.00  bin_hyper_res:                          0
% 2.82/1.00  prep_cycles:                            4
% 2.82/1.00  pred_elim_time:                         0.056
% 2.82/1.00  splitting_time:                         0.
% 2.82/1.00  sem_filter_time:                        0.
% 2.82/1.00  monotx_time:                            0.
% 2.82/1.00  subtype_inf_time:                       0.
% 2.82/1.00  
% 2.82/1.00  ------ Problem properties
% 2.82/1.00  
% 2.82/1.00  clauses:                                25
% 2.82/1.00  conjectures:                            3
% 2.82/1.00  epr:                                    5
% 2.82/1.00  horn:                                   18
% 2.82/1.00  ground:                                 4
% 2.82/1.00  unary:                                  8
% 2.82/1.00  binary:                                 4
% 2.82/1.00  lits:                                   67
% 2.82/1.00  lits_eq:                                7
% 2.82/1.00  fd_pure:                                0
% 2.82/1.00  fd_pseudo:                              0
% 2.82/1.00  fd_cond:                                0
% 2.82/1.00  fd_pseudo_cond:                         3
% 2.82/1.00  ac_symbols:                             0
% 2.82/1.00  
% 2.82/1.00  ------ Propositional Solver
% 2.82/1.00  
% 2.82/1.00  prop_solver_calls:                      29
% 2.82/1.00  prop_fast_solver_calls:                 1447
% 2.82/1.00  smt_solver_calls:                       0
% 2.82/1.00  smt_fast_solver_calls:                  0
% 2.82/1.00  prop_num_of_clauses:                    1931
% 2.82/1.00  prop_preprocess_simplified:             6057
% 2.82/1.00  prop_fo_subsumed:                       13
% 2.82/1.00  prop_solver_time:                       0.
% 2.82/1.00  smt_solver_time:                        0.
% 2.82/1.00  smt_fast_solver_time:                   0.
% 2.82/1.00  prop_fast_solver_time:                  0.
% 2.82/1.00  prop_unsat_core_time:                   0.
% 2.82/1.00  
% 2.82/1.00  ------ QBF
% 2.82/1.00  
% 2.82/1.00  qbf_q_res:                              0
% 2.82/1.00  qbf_num_tautologies:                    0
% 2.82/1.00  qbf_prep_cycles:                        0
% 2.82/1.00  
% 2.82/1.00  ------ BMC1
% 2.82/1.00  
% 2.82/1.00  bmc1_current_bound:                     -1
% 2.82/1.00  bmc1_last_solved_bound:                 -1
% 2.82/1.00  bmc1_unsat_core_size:                   -1
% 2.82/1.00  bmc1_unsat_core_parents_size:           -1
% 2.82/1.00  bmc1_merge_next_fun:                    0
% 2.82/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.82/1.00  
% 2.82/1.00  ------ Instantiation
% 2.82/1.00  
% 2.82/1.00  inst_num_of_clauses:                    550
% 2.82/1.00  inst_num_in_passive:                    17
% 2.82/1.00  inst_num_in_active:                     322
% 2.82/1.00  inst_num_in_unprocessed:                211
% 2.82/1.00  inst_num_of_loops:                      330
% 2.82/1.00  inst_num_of_learning_restarts:          0
% 2.82/1.00  inst_num_moves_active_passive:          4
% 2.82/1.00  inst_lit_activity:                      0
% 2.82/1.00  inst_lit_activity_moves:                0
% 2.82/1.00  inst_num_tautologies:                   0
% 2.82/1.00  inst_num_prop_implied:                  0
% 2.82/1.00  inst_num_existing_simplified:           0
% 2.82/1.00  inst_num_eq_res_simplified:             0
% 2.82/1.00  inst_num_child_elim:                    0
% 2.82/1.00  inst_num_of_dismatching_blockings:      79
% 2.82/1.00  inst_num_of_non_proper_insts:           498
% 2.82/1.00  inst_num_of_duplicates:                 0
% 2.82/1.00  inst_inst_num_from_inst_to_res:         0
% 2.82/1.00  inst_dismatching_checking_time:         0.
% 2.82/1.00  
% 2.82/1.00  ------ Resolution
% 2.82/1.00  
% 2.82/1.00  res_num_of_clauses:                     0
% 2.82/1.00  res_num_in_passive:                     0
% 2.82/1.00  res_num_in_active:                      0
% 2.82/1.00  res_num_of_loops:                       139
% 2.82/1.00  res_forward_subset_subsumed:            58
% 2.82/1.00  res_backward_subset_subsumed:           0
% 2.82/1.00  res_forward_subsumed:                   0
% 2.82/1.00  res_backward_subsumed:                  0
% 2.82/1.00  res_forward_subsumption_resolution:     0
% 2.82/1.00  res_backward_subsumption_resolution:    0
% 2.82/1.00  res_clause_to_clause_subsumption:       504
% 2.82/1.00  res_orphan_elimination:                 0
% 2.82/1.00  res_tautology_del:                      45
% 2.82/1.00  res_num_eq_res_simplified:              0
% 2.82/1.00  res_num_sel_changes:                    0
% 2.82/1.00  res_moves_from_active_to_pass:          0
% 2.82/1.00  
% 2.82/1.00  ------ Superposition
% 2.82/1.00  
% 2.82/1.00  sup_time_total:                         0.
% 2.82/1.00  sup_time_generating:                    0.
% 2.82/1.00  sup_time_sim_full:                      0.
% 2.82/1.00  sup_time_sim_immed:                     0.
% 2.82/1.00  
% 2.82/1.00  sup_num_of_clauses:                     85
% 2.82/1.00  sup_num_in_active:                      65
% 2.82/1.00  sup_num_in_passive:                     20
% 2.82/1.00  sup_num_of_loops:                       65
% 2.82/1.00  sup_fw_superposition:                   51
% 2.82/1.00  sup_bw_superposition:                   28
% 2.82/1.00  sup_immediate_simplified:               16
% 2.82/1.00  sup_given_eliminated:                   0
% 2.82/1.00  comparisons_done:                       0
% 2.82/1.00  comparisons_avoided:                    0
% 2.82/1.00  
% 2.82/1.00  ------ Simplifications
% 2.82/1.00  
% 2.82/1.00  
% 2.82/1.00  sim_fw_subset_subsumed:                 3
% 2.82/1.00  sim_bw_subset_subsumed:                 2
% 2.82/1.00  sim_fw_subsumed:                        8
% 2.82/1.00  sim_bw_subsumed:                        0
% 2.82/1.00  sim_fw_subsumption_res:                 4
% 2.82/1.00  sim_bw_subsumption_res:                 0
% 2.82/1.00  sim_tautology_del:                      6
% 2.82/1.00  sim_eq_tautology_del:                   1
% 2.82/1.00  sim_eq_res_simp:                        0
% 2.82/1.00  sim_fw_demodulated:                     1
% 2.82/1.00  sim_bw_demodulated:                     0
% 2.82/1.00  sim_light_normalised:                   18
% 2.82/1.00  sim_joinable_taut:                      0
% 2.82/1.00  sim_joinable_simp:                      0
% 2.82/1.00  sim_ac_normalised:                      0
% 2.82/1.00  sim_smt_subsumption:                    0
% 2.82/1.00  
%------------------------------------------------------------------------------
