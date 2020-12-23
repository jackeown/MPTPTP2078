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
% DateTime   : Thu Dec  3 12:20:14 EST 2020

% Result     : Theorem 3.28s
% Output     : CNFRefutation 3.28s
% Verified   : 
% Statistics : Number of formulae       :  180 ( 392 expanded)
%              Number of clauses        :  104 ( 158 expanded)
%              Number of leaves         :   23 (  74 expanded)
%              Depth                    :   30
%              Number of atoms          :  707 (1444 expanded)
%              Number of equality atoms :  205 ( 351 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   15 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
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

fof(f36,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f35])).

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f51,plain,(
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
    inference(rectify,[],[f50])).

fof(f52,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
        & r2_hidden(sK0(X0,X1,X2),X1)
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f51,f52])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f99,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f17,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f103,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f13,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
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
    inference(rectify,[],[f13])).

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f63,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X1)
          & r1_lattice3(X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK3(X0,X1,X2),X1)
        & r1_lattice3(X0,X2,sK3(X0,X1,X2))
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
                | ( ~ r1_orders_2(X0,sK3(X0,X1,X2),X1)
                  & r1_lattice3(X0,X2,sK3(X0,X1,X2))
                  & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f44,f63])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( k2_yellow_0(X0,X2) = X1
      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | ~ r1_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f15,axiom,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v4_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f24,plain,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f22])).

fof(f101,plain,(
    ! [X0] : v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f19,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( r2_hidden(k3_tarski(X0),X0)
       => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ( r2_hidden(k3_tarski(X0),X0)
         => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f47,plain,(
    ? [X0] :
      ( k3_tarski(X0) != k4_yellow_0(k2_yellow_1(X0))
      & r2_hidden(k3_tarski(X0),X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f48,plain,(
    ? [X0] :
      ( k3_tarski(X0) != k4_yellow_0(k2_yellow_1(X0))
      & r2_hidden(k3_tarski(X0),X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f66,plain,
    ( ? [X0] :
        ( k3_tarski(X0) != k4_yellow_0(k2_yellow_1(X0))
        & r2_hidden(k3_tarski(X0),X0)
        & ~ v1_xboole_0(X0) )
   => ( k3_tarski(sK4) != k4_yellow_0(k2_yellow_1(sK4))
      & r2_hidden(k3_tarski(sK4),sK4)
      & ~ v1_xboole_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,
    ( k3_tarski(sK4) != k4_yellow_0(k2_yellow_1(sK4))
    & r2_hidden(k3_tarski(sK4),sK4)
    & ~ v1_xboole_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f48,f66])).

fof(f107,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f67])).

fof(f9,axiom,(
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
    inference(ennf_transformation,[],[f9])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f37])).

fof(f54,plain,(
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
    inference(nnf_transformation,[],[f38])).

fof(f55,plain,(
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
    inference(rectify,[],[f54])).

fof(f56,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK1(X0,X1,X2),X2)
        & r2_hidden(sK1(X0,X1,X2),X1)
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f55,f56])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f18,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
             => ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f65,plain,(
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
    inference(nnf_transformation,[],[f46])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f65])).

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

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f49,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f100,plain,(
    ! [X0] : v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f16,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_orders_2(k2_yellow_1(X0))
        & ~ v2_struct_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ~ v2_struct_0(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k2_yellow_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f102,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k2_yellow_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,sK1(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f108,plain,(
    r2_hidden(k3_tarski(sK4),sK4) ),
    inference(cnf_transformation,[],[f67])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f80,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( k2_yellow_0(X0,X2) = X1
      | ~ r1_orders_2(X0,sK3(X0,X1,X2),X1)
      | ~ r1_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k2_yellow_0(X0,k1_xboole_0) = k4_yellow_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( k2_yellow_0(X0,k1_xboole_0) = k4_yellow_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f89,plain,(
    ! [X0] :
      ( k2_yellow_0(X0,k1_xboole_0) = k4_yellow_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f109,plain,(
    k3_tarski(sK4) != k4_yellow_0(k2_yellow_1(sK4)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_9,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK0(X0,X1,X2),X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_31,plain,
    ( l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1359,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK0(X0,X1,X2),X1)
    | k2_yellow_1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_31])).

cnf(c_1360,plain,
    ( r1_lattice3(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | r2_hidden(sK0(k2_yellow_1(X0),X1,X2),X1) ),
    inference(unflattening,[status(thm)],[c_1359])).

cnf(c_3465,plain,
    ( r1_lattice3(k2_yellow_1(X0),X1,X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | r2_hidden(sK0(k2_yellow_1(X0),X1,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1360])).

cnf(c_36,plain,
    ( u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_3532,plain,
    ( r1_lattice3(k2_yellow_1(X0),X1,X2) = iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | r2_hidden(sK0(k2_yellow_1(X0),X1,X2),X1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3465,c_36])).

cnf(c_0,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_643,plain,
    ( ~ r2_hidden(X0,X1)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_4])).

cnf(c_644,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_643])).

cnf(c_3489,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_644])).

cnf(c_4333,plain,
    ( r1_lattice3(k2_yellow_1(X0),k1_xboole_0,X1) = iProver_top
    | m1_subset_1(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3532,c_3489])).

cnf(c_28,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK3(X0,X2,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k2_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_32,plain,
    ( v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_821,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK3(X0,X2,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | k2_yellow_0(X0,X1) = X2
    | k2_yellow_1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_32])).

cnf(c_822,plain,
    ( ~ r1_lattice3(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | m1_subset_1(sK3(k2_yellow_1(X0),X2,X1),u1_struct_0(k2_yellow_1(X0)))
    | ~ l1_orders_2(k2_yellow_1(X0))
    | k2_yellow_0(k2_yellow_1(X0),X1) = X2 ),
    inference(unflattening,[status(thm)],[c_821])).

cnf(c_826,plain,
    ( m1_subset_1(sK3(k2_yellow_1(X0),X2,X1),u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ r1_lattice3(k2_yellow_1(X0),X1,X2)
    | k2_yellow_0(k2_yellow_1(X0),X1) = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_822,c_31])).

cnf(c_827,plain,
    ( ~ r1_lattice3(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | m1_subset_1(sK3(k2_yellow_1(X0),X2,X1),u1_struct_0(k2_yellow_1(X0)))
    | k2_yellow_0(k2_yellow_1(X0),X1) = X2 ),
    inference(renaming,[status(thm)],[c_826])).

cnf(c_3484,plain,
    ( k2_yellow_0(k2_yellow_1(X0),X1) = X2
    | r1_lattice3(k2_yellow_1(X0),X1,X2) != iProver_top
    | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | m1_subset_1(sK3(k2_yellow_1(X0),X2,X1),u1_struct_0(k2_yellow_1(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_827])).

cnf(c_3626,plain,
    ( k2_yellow_0(k2_yellow_1(X0),X1) = X2
    | r1_lattice3(k2_yellow_1(X0),X1,X2) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(sK3(k2_yellow_1(X0),X2,X1),X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3484,c_36])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_41,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_456,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_41])).

cnf(c_457,plain,
    ( ~ m1_subset_1(X0,sK4)
    | r2_hidden(X0,sK4) ),
    inference(unflattening,[status(thm)],[c_456])).

cnf(c_3493,plain,
    ( m1_subset_1(X0,sK4) != iProver_top
    | r2_hidden(X0,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_457])).

cnf(c_5459,plain,
    ( k2_yellow_0(k2_yellow_1(sK4),X0) = X1
    | r1_lattice3(k2_yellow_1(sK4),X0,X1) != iProver_top
    | m1_subset_1(X1,sK4) != iProver_top
    | r2_hidden(sK3(k2_yellow_1(sK4),X1,X0),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3626,c_3493])).

cnf(c_14,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1278,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
    | k2_yellow_1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_31])).

cnf(c_1279,plain,
    ( r2_lattice3(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | m1_subset_1(sK1(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0))) ),
    inference(unflattening,[status(thm)],[c_1278])).

cnf(c_3470,plain,
    ( r2_lattice3(k2_yellow_1(X0),X1,X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | m1_subset_1(sK1(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1279])).

cnf(c_3553,plain,
    ( r2_lattice3(k2_yellow_1(X0),X1,X2) = iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(sK1(k2_yellow_1(X0),X1,X2),X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3470,c_36])).

cnf(c_4643,plain,
    ( r2_lattice3(k2_yellow_1(sK4),X0,X1) = iProver_top
    | m1_subset_1(X1,sK4) != iProver_top
    | r2_hidden(sK1(k2_yellow_1(sK4),X0,X1),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3553,c_3493])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(X0,k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_37,plain,
    ( r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ r1_tarski(X1,X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_486,plain,
    ( r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ r1_tarski(X1,X2)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_37,c_41])).

cnf(c_487,plain,
    ( r3_orders_2(k2_yellow_1(sK4),X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK4)))
    | ~ r1_tarski(X0,X1) ),
    inference(unflattening,[status(thm)],[c_486])).

cnf(c_679,plain,
    ( r3_orders_2(k2_yellow_1(sK4),X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK4)))
    | ~ r2_hidden(X2,X3)
    | X0 != X2
    | k3_tarski(X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_487])).

cnf(c_680,plain,
    ( r3_orders_2(k2_yellow_1(sK4),X0,k3_tarski(X1))
    | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK4)))
    | ~ m1_subset_1(k3_tarski(X1),u1_struct_0(k2_yellow_1(sK4)))
    | ~ r2_hidden(X0,X1) ),
    inference(unflattening,[status(thm)],[c_679])).

cnf(c_3486,plain,
    ( r3_orders_2(k2_yellow_1(sK4),X0,k3_tarski(X1)) = iProver_top
    | m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK4))) != iProver_top
    | m1_subset_1(k3_tarski(X1),u1_struct_0(k2_yellow_1(sK4))) != iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_680])).

cnf(c_3590,plain,
    ( r3_orders_2(k2_yellow_1(sK4),X0,k3_tarski(X1)) = iProver_top
    | m1_subset_1(X0,sK4) != iProver_top
    | m1_subset_1(k3_tarski(X1),sK4) != iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3486,c_36])).

cnf(c_6,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_33,plain,
    ( v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_526,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | k2_yellow_1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_33])).

cnf(c_527,plain,
    ( r1_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | v2_struct_0(k2_yellow_1(X0))
    | ~ l1_orders_2(k2_yellow_1(X0)) ),
    inference(unflattening,[status(thm)],[c_526])).

cnf(c_531,plain,
    ( v2_struct_0(k2_yellow_1(X0))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
    | r1_orders_2(k2_yellow_1(X0),X1,X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_527,c_31])).

cnf(c_532,plain,
    ( r1_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | v2_struct_0(k2_yellow_1(X0)) ),
    inference(renaming,[status(thm)],[c_531])).

cnf(c_3491,plain,
    ( r1_orders_2(k2_yellow_1(X0),X1,X2) = iProver_top
    | r3_orders_2(k2_yellow_1(X0),X1,X2) != iProver_top
    | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | v2_struct_0(k2_yellow_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_532])).

cnf(c_3675,plain,
    ( r1_orders_2(k2_yellow_1(X0),X1,X2) = iProver_top
    | r3_orders_2(k2_yellow_1(X0),X1,X2) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | v2_struct_0(k2_yellow_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3491,c_36])).

cnf(c_5557,plain,
    ( r1_orders_2(k2_yellow_1(sK4),X0,k3_tarski(X1)) = iProver_top
    | m1_subset_1(X0,sK4) != iProver_top
    | m1_subset_1(k3_tarski(X1),sK4) != iProver_top
    | r2_hidden(X0,X1) != iProver_top
    | v2_struct_0(k2_yellow_1(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3590,c_3675])).

cnf(c_42,plain,
    ( v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_34,plain,
    ( ~ v2_struct_0(k2_yellow_1(X0))
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_52,plain,
    ( v2_struct_0(k2_yellow_1(X0)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_54,plain,
    ( v2_struct_0(k2_yellow_1(sK4)) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_52])).

cnf(c_5650,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(k3_tarski(X1),sK4) != iProver_top
    | m1_subset_1(X0,sK4) != iProver_top
    | r1_orders_2(k2_yellow_1(sK4),X0,k3_tarski(X1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5557,c_42,c_54])).

cnf(c_5651,plain,
    ( r1_orders_2(k2_yellow_1(sK4),X0,k3_tarski(X1)) = iProver_top
    | m1_subset_1(X0,sK4) != iProver_top
    | m1_subset_1(k3_tarski(X1),sK4) != iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_5650])).

cnf(c_12,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK1(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1308,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK1(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | k2_yellow_1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_31])).

cnf(c_1309,plain,
    ( r2_lattice3(k2_yellow_1(X0),X1,X2)
    | ~ r1_orders_2(k2_yellow_1(X0),sK1(k2_yellow_1(X0),X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) ),
    inference(unflattening,[status(thm)],[c_1308])).

cnf(c_3468,plain,
    ( r2_lattice3(k2_yellow_1(X0),X1,X2) = iProver_top
    | r1_orders_2(k2_yellow_1(X0),sK1(k2_yellow_1(X0),X1,X2),X2) != iProver_top
    | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1309])).

cnf(c_3567,plain,
    ( r2_lattice3(k2_yellow_1(X0),X1,X2) = iProver_top
    | r1_orders_2(k2_yellow_1(X0),sK1(k2_yellow_1(X0),X1,X2),X2) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3468,c_36])).

cnf(c_5662,plain,
    ( r2_lattice3(k2_yellow_1(sK4),X0,k3_tarski(X1)) = iProver_top
    | m1_subset_1(sK1(k2_yellow_1(sK4),X0,k3_tarski(X1)),sK4) != iProver_top
    | m1_subset_1(k3_tarski(X1),sK4) != iProver_top
    | r2_hidden(sK1(k2_yellow_1(sK4),X0,k3_tarski(X1)),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5651,c_3567])).

cnf(c_7373,plain,
    ( r2_lattice3(k2_yellow_1(sK4),X0,k3_tarski(X1)) = iProver_top
    | m1_subset_1(k3_tarski(X1),sK4) != iProver_top
    | r2_hidden(sK1(k2_yellow_1(sK4),X0,k3_tarski(X1)),X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5662,c_3553])).

cnf(c_7378,plain,
    ( r2_lattice3(k2_yellow_1(sK4),X0,k3_tarski(sK4)) = iProver_top
    | m1_subset_1(k3_tarski(sK4),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4643,c_7373])).

cnf(c_40,negated_conjecture,
    ( r2_hidden(k3_tarski(sK4),sK4) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_43,plain,
    ( r2_hidden(k3_tarski(sK4),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_2,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_3886,plain,
    ( m1_subset_1(k3_tarski(sK4),sK4)
    | ~ r2_hidden(k3_tarski(sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_3887,plain,
    ( m1_subset_1(k3_tarski(sK4),sK4) = iProver_top
    | r2_hidden(k3_tarski(sK4),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3886])).

cnf(c_7392,plain,
    ( r2_lattice3(k2_yellow_1(sK4),X0,k3_tarski(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7378,c_43,c_3887])).

cnf(c_15,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r2_hidden(X3,X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1257,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r2_hidden(X3,X1)
    | k2_yellow_1(X4) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_31])).

cnf(c_1258,plain,
    ( ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
    | r1_orders_2(k2_yellow_1(X0),X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ r2_hidden(X3,X1) ),
    inference(unflattening,[status(thm)],[c_1257])).

cnf(c_3471,plain,
    ( r2_lattice3(k2_yellow_1(X0),X1,X2) != iProver_top
    | r1_orders_2(k2_yellow_1(X0),X3,X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | m1_subset_1(X3,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | r2_hidden(X3,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1258])).

cnf(c_3697,plain,
    ( r2_lattice3(k2_yellow_1(X0),X1,X2) != iProver_top
    | r1_orders_2(k2_yellow_1(X0),X3,X2) = iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X3,X0) != iProver_top
    | r2_hidden(X3,X1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3471,c_36])).

cnf(c_7399,plain,
    ( r1_orders_2(k2_yellow_1(sK4),X0,k3_tarski(sK4)) = iProver_top
    | m1_subset_1(X0,sK4) != iProver_top
    | m1_subset_1(k3_tarski(sK4),sK4) != iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_7392,c_3697])).

cnf(c_7611,plain,
    ( m1_subset_1(X0,sK4) != iProver_top
    | r1_orders_2(k2_yellow_1(sK4),X0,k3_tarski(sK4)) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7399,c_43,c_3887])).

cnf(c_7612,plain,
    ( r1_orders_2(k2_yellow_1(sK4),X0,k3_tarski(sK4)) = iProver_top
    | m1_subset_1(X0,sK4) != iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_7611])).

cnf(c_7624,plain,
    ( k2_yellow_0(k2_yellow_1(sK4),X0) = X1
    | r1_lattice3(k2_yellow_1(sK4),X0,X1) != iProver_top
    | r1_orders_2(k2_yellow_1(sK4),sK3(k2_yellow_1(sK4),X1,X0),k3_tarski(sK4)) = iProver_top
    | m1_subset_1(X1,sK4) != iProver_top
    | m1_subset_1(sK3(k2_yellow_1(sK4),X1,X0),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5459,c_7612])).

cnf(c_8955,plain,
    ( k2_yellow_0(k2_yellow_1(sK4),X0) = X1
    | r1_lattice3(k2_yellow_1(sK4),X0,X1) != iProver_top
    | r1_orders_2(k2_yellow_1(sK4),sK3(k2_yellow_1(sK4),X1,X0),k3_tarski(sK4)) = iProver_top
    | m1_subset_1(X1,sK4) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7624,c_3626])).

cnf(c_26,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK3(X0,X2,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k2_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_869,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK3(X0,X2,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | k2_yellow_0(X0,X1) = X2
    | k2_yellow_1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_32])).

cnf(c_870,plain,
    ( ~ r1_lattice3(k2_yellow_1(X0),X1,X2)
    | ~ r1_orders_2(k2_yellow_1(X0),sK3(k2_yellow_1(X0),X2,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ l1_orders_2(k2_yellow_1(X0))
    | k2_yellow_0(k2_yellow_1(X0),X1) = X2 ),
    inference(unflattening,[status(thm)],[c_869])).

cnf(c_874,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ r1_orders_2(k2_yellow_1(X0),sK3(k2_yellow_1(X0),X2,X1),X2)
    | ~ r1_lattice3(k2_yellow_1(X0),X1,X2)
    | k2_yellow_0(k2_yellow_1(X0),X1) = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_870,c_31])).

cnf(c_875,plain,
    ( ~ r1_lattice3(k2_yellow_1(X0),X1,X2)
    | ~ r1_orders_2(k2_yellow_1(X0),sK3(k2_yellow_1(X0),X2,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | k2_yellow_0(k2_yellow_1(X0),X1) = X2 ),
    inference(renaming,[status(thm)],[c_874])).

cnf(c_3482,plain,
    ( k2_yellow_0(k2_yellow_1(X0),X1) = X2
    | r1_lattice3(k2_yellow_1(X0),X1,X2) != iProver_top
    | r1_orders_2(k2_yellow_1(X0),sK3(k2_yellow_1(X0),X2,X1),X2) != iProver_top
    | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_875])).

cnf(c_3644,plain,
    ( k2_yellow_0(k2_yellow_1(X0),X1) = X2
    | r1_lattice3(k2_yellow_1(X0),X1,X2) != iProver_top
    | r1_orders_2(k2_yellow_1(X0),sK3(k2_yellow_1(X0),X2,X1),X2) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3482,c_36])).

cnf(c_8960,plain,
    ( k2_yellow_0(k2_yellow_1(sK4),X0) = k3_tarski(sK4)
    | r1_lattice3(k2_yellow_1(sK4),X0,k3_tarski(sK4)) != iProver_top
    | m1_subset_1(k3_tarski(sK4),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_8955,c_3644])).

cnf(c_9691,plain,
    ( r1_lattice3(k2_yellow_1(sK4),X0,k3_tarski(sK4)) != iProver_top
    | k2_yellow_0(k2_yellow_1(sK4),X0) = k3_tarski(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8960,c_43,c_3887])).

cnf(c_9692,plain,
    ( k2_yellow_0(k2_yellow_1(sK4),X0) = k3_tarski(sK4)
    | r1_lattice3(k2_yellow_1(sK4),X0,k3_tarski(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_9691])).

cnf(c_9699,plain,
    ( k2_yellow_0(k2_yellow_1(sK4),k1_xboole_0) = k3_tarski(sK4)
    | m1_subset_1(k3_tarski(sK4),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4333,c_9692])).

cnf(c_21,plain,
    ( ~ l1_orders_2(X0)
    | k2_yellow_0(X0,k1_xboole_0) = k4_yellow_0(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1152,plain,
    ( k2_yellow_0(X0,k1_xboole_0) = k4_yellow_0(X0)
    | k2_yellow_1(X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_31])).

cnf(c_1153,plain,
    ( k2_yellow_0(k2_yellow_1(X0),k1_xboole_0) = k4_yellow_0(k2_yellow_1(X0)) ),
    inference(unflattening,[status(thm)],[c_1152])).

cnf(c_9700,plain,
    ( k4_yellow_0(k2_yellow_1(sK4)) = k3_tarski(sK4)
    | m1_subset_1(k3_tarski(sK4),sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9699,c_1153])).

cnf(c_2867,plain,
    ( X0 != X1
    | X2 != X1
    | X0 = X2 ),
    theory(equality)).

cnf(c_3897,plain,
    ( k4_yellow_0(k2_yellow_1(sK4)) != X0
    | k3_tarski(sK4) != X0
    | k3_tarski(sK4) = k4_yellow_0(k2_yellow_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_2867])).

cnf(c_4024,plain,
    ( k4_yellow_0(k2_yellow_1(sK4)) != k3_tarski(sK4)
    | k3_tarski(sK4) = k4_yellow_0(k2_yellow_1(sK4))
    | k3_tarski(sK4) != k3_tarski(sK4) ),
    inference(instantiation,[status(thm)],[c_3897])).

cnf(c_2866,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2905,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_2866])).

cnf(c_2868,plain,
    ( X0 != X1
    | k3_tarski(X0) = k3_tarski(X1) ),
    theory(equality)).

cnf(c_2886,plain,
    ( k3_tarski(sK4) = k3_tarski(sK4)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2868])).

cnf(c_39,negated_conjecture,
    ( k3_tarski(sK4) != k4_yellow_0(k2_yellow_1(sK4)) ),
    inference(cnf_transformation,[],[f109])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9700,c_4024,c_3887,c_2905,c_2886,c_39,c_43])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:20:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.28/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.28/0.98  
% 3.28/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.28/0.98  
% 3.28/0.98  ------  iProver source info
% 3.28/0.98  
% 3.28/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.28/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.28/0.98  git: non_committed_changes: false
% 3.28/0.98  git: last_make_outside_of_git: false
% 3.28/0.98  
% 3.28/0.98  ------ 
% 3.28/0.98  
% 3.28/0.98  ------ Input Options
% 3.28/0.98  
% 3.28/0.98  --out_options                           all
% 3.28/0.98  --tptp_safe_out                         true
% 3.28/0.98  --problem_path                          ""
% 3.28/0.98  --include_path                          ""
% 3.28/0.98  --clausifier                            res/vclausify_rel
% 3.28/0.98  --clausifier_options                    --mode clausify
% 3.28/0.98  --stdin                                 false
% 3.28/0.98  --stats_out                             all
% 3.28/0.98  
% 3.28/0.98  ------ General Options
% 3.28/0.98  
% 3.28/0.98  --fof                                   false
% 3.28/0.98  --time_out_real                         305.
% 3.28/0.98  --time_out_virtual                      -1.
% 3.28/0.98  --symbol_type_check                     false
% 3.28/0.98  --clausify_out                          false
% 3.28/0.98  --sig_cnt_out                           false
% 3.28/0.98  --trig_cnt_out                          false
% 3.28/0.98  --trig_cnt_out_tolerance                1.
% 3.28/0.98  --trig_cnt_out_sk_spl                   false
% 3.28/0.98  --abstr_cl_out                          false
% 3.28/0.98  
% 3.28/0.98  ------ Global Options
% 3.28/0.98  
% 3.28/0.98  --schedule                              default
% 3.28/0.98  --add_important_lit                     false
% 3.28/0.98  --prop_solver_per_cl                    1000
% 3.28/0.98  --min_unsat_core                        false
% 3.28/0.98  --soft_assumptions                      false
% 3.28/0.98  --soft_lemma_size                       3
% 3.28/0.98  --prop_impl_unit_size                   0
% 3.28/0.98  --prop_impl_unit                        []
% 3.28/0.98  --share_sel_clauses                     true
% 3.28/0.98  --reset_solvers                         false
% 3.28/0.98  --bc_imp_inh                            [conj_cone]
% 3.28/0.98  --conj_cone_tolerance                   3.
% 3.28/0.98  --extra_neg_conj                        none
% 3.28/0.98  --large_theory_mode                     true
% 3.28/0.98  --prolific_symb_bound                   200
% 3.28/0.98  --lt_threshold                          2000
% 3.28/0.98  --clause_weak_htbl                      true
% 3.28/0.98  --gc_record_bc_elim                     false
% 3.28/0.98  
% 3.28/0.98  ------ Preprocessing Options
% 3.28/0.98  
% 3.28/0.98  --preprocessing_flag                    true
% 3.28/0.98  --time_out_prep_mult                    0.1
% 3.28/0.98  --splitting_mode                        input
% 3.28/0.98  --splitting_grd                         true
% 3.28/0.98  --splitting_cvd                         false
% 3.28/0.98  --splitting_cvd_svl                     false
% 3.28/0.98  --splitting_nvd                         32
% 3.28/0.98  --sub_typing                            true
% 3.28/0.98  --prep_gs_sim                           true
% 3.28/0.98  --prep_unflatten                        true
% 3.28/0.98  --prep_res_sim                          true
% 3.28/0.98  --prep_upred                            true
% 3.28/0.98  --prep_sem_filter                       exhaustive
% 3.28/0.98  --prep_sem_filter_out                   false
% 3.28/0.98  --pred_elim                             true
% 3.28/0.98  --res_sim_input                         true
% 3.28/0.98  --eq_ax_congr_red                       true
% 3.28/0.98  --pure_diseq_elim                       true
% 3.28/0.98  --brand_transform                       false
% 3.28/0.98  --non_eq_to_eq                          false
% 3.28/0.98  --prep_def_merge                        true
% 3.28/0.98  --prep_def_merge_prop_impl              false
% 3.28/0.98  --prep_def_merge_mbd                    true
% 3.28/0.98  --prep_def_merge_tr_red                 false
% 3.28/0.98  --prep_def_merge_tr_cl                  false
% 3.28/0.98  --smt_preprocessing                     true
% 3.28/0.98  --smt_ac_axioms                         fast
% 3.28/0.98  --preprocessed_out                      false
% 3.28/0.98  --preprocessed_stats                    false
% 3.28/0.98  
% 3.28/0.98  ------ Abstraction refinement Options
% 3.28/0.98  
% 3.28/0.98  --abstr_ref                             []
% 3.28/0.98  --abstr_ref_prep                        false
% 3.28/0.98  --abstr_ref_until_sat                   false
% 3.28/0.98  --abstr_ref_sig_restrict                funpre
% 3.28/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.28/0.98  --abstr_ref_under                       []
% 3.28/0.98  
% 3.28/0.98  ------ SAT Options
% 3.28/0.98  
% 3.28/0.98  --sat_mode                              false
% 3.28/0.98  --sat_fm_restart_options                ""
% 3.28/0.98  --sat_gr_def                            false
% 3.28/0.98  --sat_epr_types                         true
% 3.28/0.98  --sat_non_cyclic_types                  false
% 3.28/0.98  --sat_finite_models                     false
% 3.28/0.98  --sat_fm_lemmas                         false
% 3.28/0.98  --sat_fm_prep                           false
% 3.28/0.98  --sat_fm_uc_incr                        true
% 3.28/0.98  --sat_out_model                         small
% 3.28/0.98  --sat_out_clauses                       false
% 3.28/0.98  
% 3.28/0.98  ------ QBF Options
% 3.28/0.98  
% 3.28/0.98  --qbf_mode                              false
% 3.28/0.98  --qbf_elim_univ                         false
% 3.28/0.98  --qbf_dom_inst                          none
% 3.28/0.98  --qbf_dom_pre_inst                      false
% 3.28/0.98  --qbf_sk_in                             false
% 3.28/0.98  --qbf_pred_elim                         true
% 3.28/0.98  --qbf_split                             512
% 3.28/0.98  
% 3.28/0.98  ------ BMC1 Options
% 3.28/0.98  
% 3.28/0.98  --bmc1_incremental                      false
% 3.28/0.98  --bmc1_axioms                           reachable_all
% 3.28/0.98  --bmc1_min_bound                        0
% 3.28/0.98  --bmc1_max_bound                        -1
% 3.28/0.98  --bmc1_max_bound_default                -1
% 3.28/0.98  --bmc1_symbol_reachability              true
% 3.28/0.98  --bmc1_property_lemmas                  false
% 3.28/0.98  --bmc1_k_induction                      false
% 3.28/0.98  --bmc1_non_equiv_states                 false
% 3.28/0.98  --bmc1_deadlock                         false
% 3.28/0.98  --bmc1_ucm                              false
% 3.28/0.98  --bmc1_add_unsat_core                   none
% 3.28/0.98  --bmc1_unsat_core_children              false
% 3.28/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.28/0.98  --bmc1_out_stat                         full
% 3.28/0.98  --bmc1_ground_init                      false
% 3.28/0.98  --bmc1_pre_inst_next_state              false
% 3.28/0.98  --bmc1_pre_inst_state                   false
% 3.28/0.98  --bmc1_pre_inst_reach_state             false
% 3.28/0.98  --bmc1_out_unsat_core                   false
% 3.28/0.98  --bmc1_aig_witness_out                  false
% 3.28/0.98  --bmc1_verbose                          false
% 3.28/0.98  --bmc1_dump_clauses_tptp                false
% 3.28/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.28/0.98  --bmc1_dump_file                        -
% 3.28/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.28/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.28/0.98  --bmc1_ucm_extend_mode                  1
% 3.28/0.98  --bmc1_ucm_init_mode                    2
% 3.28/0.98  --bmc1_ucm_cone_mode                    none
% 3.28/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.28/0.98  --bmc1_ucm_relax_model                  4
% 3.28/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.28/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.28/0.98  --bmc1_ucm_layered_model                none
% 3.28/0.98  --bmc1_ucm_max_lemma_size               10
% 3.28/0.98  
% 3.28/0.98  ------ AIG Options
% 3.28/0.98  
% 3.28/0.98  --aig_mode                              false
% 3.28/0.98  
% 3.28/0.98  ------ Instantiation Options
% 3.28/0.98  
% 3.28/0.98  --instantiation_flag                    true
% 3.28/0.98  --inst_sos_flag                         false
% 3.28/0.98  --inst_sos_phase                        true
% 3.28/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.28/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.28/0.98  --inst_lit_sel_side                     num_symb
% 3.28/0.98  --inst_solver_per_active                1400
% 3.28/0.98  --inst_solver_calls_frac                1.
% 3.28/0.98  --inst_passive_queue_type               priority_queues
% 3.28/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.28/0.98  --inst_passive_queues_freq              [25;2]
% 3.28/0.98  --inst_dismatching                      true
% 3.28/0.98  --inst_eager_unprocessed_to_passive     true
% 3.28/0.98  --inst_prop_sim_given                   true
% 3.28/0.98  --inst_prop_sim_new                     false
% 3.28/0.98  --inst_subs_new                         false
% 3.28/0.98  --inst_eq_res_simp                      false
% 3.28/0.98  --inst_subs_given                       false
% 3.28/0.98  --inst_orphan_elimination               true
% 3.28/0.98  --inst_learning_loop_flag               true
% 3.28/0.98  --inst_learning_start                   3000
% 3.28/0.98  --inst_learning_factor                  2
% 3.28/0.98  --inst_start_prop_sim_after_learn       3
% 3.28/0.98  --inst_sel_renew                        solver
% 3.28/0.98  --inst_lit_activity_flag                true
% 3.28/0.98  --inst_restr_to_given                   false
% 3.28/0.98  --inst_activity_threshold               500
% 3.28/0.98  --inst_out_proof                        true
% 3.28/0.98  
% 3.28/0.98  ------ Resolution Options
% 3.28/0.98  
% 3.28/0.98  --resolution_flag                       true
% 3.28/0.98  --res_lit_sel                           adaptive
% 3.28/0.98  --res_lit_sel_side                      none
% 3.28/0.98  --res_ordering                          kbo
% 3.28/0.98  --res_to_prop_solver                    active
% 3.28/0.98  --res_prop_simpl_new                    false
% 3.28/0.98  --res_prop_simpl_given                  true
% 3.28/0.98  --res_passive_queue_type                priority_queues
% 3.28/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.28/0.98  --res_passive_queues_freq               [15;5]
% 3.28/0.98  --res_forward_subs                      full
% 3.28/0.98  --res_backward_subs                     full
% 3.28/0.98  --res_forward_subs_resolution           true
% 3.28/0.98  --res_backward_subs_resolution          true
% 3.28/0.98  --res_orphan_elimination                true
% 3.28/0.98  --res_time_limit                        2.
% 3.28/0.98  --res_out_proof                         true
% 3.28/0.98  
% 3.28/0.98  ------ Superposition Options
% 3.28/0.98  
% 3.28/0.98  --superposition_flag                    true
% 3.28/0.98  --sup_passive_queue_type                priority_queues
% 3.28/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.28/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.28/0.98  --demod_completeness_check              fast
% 3.28/0.98  --demod_use_ground                      true
% 3.28/0.98  --sup_to_prop_solver                    passive
% 3.28/0.98  --sup_prop_simpl_new                    true
% 3.28/0.98  --sup_prop_simpl_given                  true
% 3.28/0.98  --sup_fun_splitting                     false
% 3.28/0.98  --sup_smt_interval                      50000
% 3.28/0.98  
% 3.28/0.98  ------ Superposition Simplification Setup
% 3.28/0.98  
% 3.28/0.98  --sup_indices_passive                   []
% 3.28/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.28/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.28/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.28/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.28/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.28/0.98  --sup_full_bw                           [BwDemod]
% 3.28/0.98  --sup_immed_triv                        [TrivRules]
% 3.28/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.28/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.28/0.98  --sup_immed_bw_main                     []
% 3.28/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.28/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.28/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.28/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.28/0.98  
% 3.28/0.98  ------ Combination Options
% 3.28/0.98  
% 3.28/0.98  --comb_res_mult                         3
% 3.28/0.98  --comb_sup_mult                         2
% 3.28/0.98  --comb_inst_mult                        10
% 3.28/0.98  
% 3.28/0.98  ------ Debug Options
% 3.28/0.98  
% 3.28/0.98  --dbg_backtrace                         false
% 3.28/0.98  --dbg_dump_prop_clauses                 false
% 3.28/0.98  --dbg_dump_prop_clauses_file            -
% 3.28/0.98  --dbg_out_stat                          false
% 3.28/0.98  ------ Parsing...
% 3.28/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.28/0.98  
% 3.28/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 3.28/0.98  
% 3.28/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.28/0.98  
% 3.28/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.28/0.98  ------ Proving...
% 3.28/0.98  ------ Problem Properties 
% 3.28/0.98  
% 3.28/0.98  
% 3.28/0.98  clauses                                 36
% 3.28/0.98  conjectures                             2
% 3.28/0.98  EPR                                     3
% 3.28/0.98  Horn                                    24
% 3.28/0.98  unary                                   8
% 3.28/0.98  binary                                  3
% 3.28/0.98  lits                                    115
% 3.28/0.98  lits eq                                 11
% 3.28/0.98  fd_pure                                 0
% 3.28/0.98  fd_pseudo                               0
% 3.28/0.98  fd_cond                                 0
% 3.28/0.98  fd_pseudo_cond                          7
% 3.28/0.98  AC symbols                              0
% 3.28/0.98  
% 3.28/0.98  ------ Schedule dynamic 5 is on 
% 3.28/0.98  
% 3.28/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.28/0.98  
% 3.28/0.98  
% 3.28/0.98  ------ 
% 3.28/0.98  Current options:
% 3.28/0.98  ------ 
% 3.28/0.98  
% 3.28/0.98  ------ Input Options
% 3.28/0.98  
% 3.28/0.98  --out_options                           all
% 3.28/0.98  --tptp_safe_out                         true
% 3.28/0.98  --problem_path                          ""
% 3.28/0.98  --include_path                          ""
% 3.28/0.98  --clausifier                            res/vclausify_rel
% 3.28/0.98  --clausifier_options                    --mode clausify
% 3.28/0.98  --stdin                                 false
% 3.28/0.98  --stats_out                             all
% 3.28/0.98  
% 3.28/0.98  ------ General Options
% 3.28/0.98  
% 3.28/0.98  --fof                                   false
% 3.28/0.98  --time_out_real                         305.
% 3.28/0.98  --time_out_virtual                      -1.
% 3.28/0.98  --symbol_type_check                     false
% 3.28/0.98  --clausify_out                          false
% 3.28/0.98  --sig_cnt_out                           false
% 3.28/0.98  --trig_cnt_out                          false
% 3.28/0.98  --trig_cnt_out_tolerance                1.
% 3.28/0.98  --trig_cnt_out_sk_spl                   false
% 3.28/0.98  --abstr_cl_out                          false
% 3.28/0.98  
% 3.28/0.98  ------ Global Options
% 3.28/0.98  
% 3.28/0.98  --schedule                              default
% 3.28/0.98  --add_important_lit                     false
% 3.28/0.98  --prop_solver_per_cl                    1000
% 3.28/0.98  --min_unsat_core                        false
% 3.28/0.98  --soft_assumptions                      false
% 3.28/0.98  --soft_lemma_size                       3
% 3.28/0.98  --prop_impl_unit_size                   0
% 3.28/0.98  --prop_impl_unit                        []
% 3.28/0.98  --share_sel_clauses                     true
% 3.28/0.98  --reset_solvers                         false
% 3.28/0.98  --bc_imp_inh                            [conj_cone]
% 3.28/0.98  --conj_cone_tolerance                   3.
% 3.28/0.98  --extra_neg_conj                        none
% 3.28/0.98  --large_theory_mode                     true
% 3.28/0.98  --prolific_symb_bound                   200
% 3.28/0.98  --lt_threshold                          2000
% 3.28/0.98  --clause_weak_htbl                      true
% 3.28/0.98  --gc_record_bc_elim                     false
% 3.28/0.98  
% 3.28/0.98  ------ Preprocessing Options
% 3.28/0.98  
% 3.28/0.98  --preprocessing_flag                    true
% 3.28/0.98  --time_out_prep_mult                    0.1
% 3.28/0.98  --splitting_mode                        input
% 3.28/0.98  --splitting_grd                         true
% 3.28/0.98  --splitting_cvd                         false
% 3.28/0.98  --splitting_cvd_svl                     false
% 3.28/0.98  --splitting_nvd                         32
% 3.28/0.98  --sub_typing                            true
% 3.28/0.98  --prep_gs_sim                           true
% 3.28/0.98  --prep_unflatten                        true
% 3.28/0.98  --prep_res_sim                          true
% 3.28/0.98  --prep_upred                            true
% 3.28/0.98  --prep_sem_filter                       exhaustive
% 3.28/0.98  --prep_sem_filter_out                   false
% 3.28/0.98  --pred_elim                             true
% 3.28/0.98  --res_sim_input                         true
% 3.28/0.98  --eq_ax_congr_red                       true
% 3.28/0.98  --pure_diseq_elim                       true
% 3.28/0.98  --brand_transform                       false
% 3.28/0.98  --non_eq_to_eq                          false
% 3.28/0.98  --prep_def_merge                        true
% 3.28/0.98  --prep_def_merge_prop_impl              false
% 3.28/0.98  --prep_def_merge_mbd                    true
% 3.28/0.98  --prep_def_merge_tr_red                 false
% 3.28/0.98  --prep_def_merge_tr_cl                  false
% 3.28/0.98  --smt_preprocessing                     true
% 3.28/0.98  --smt_ac_axioms                         fast
% 3.28/0.98  --preprocessed_out                      false
% 3.28/0.98  --preprocessed_stats                    false
% 3.28/0.98  
% 3.28/0.98  ------ Abstraction refinement Options
% 3.28/0.98  
% 3.28/0.98  --abstr_ref                             []
% 3.28/0.98  --abstr_ref_prep                        false
% 3.28/0.98  --abstr_ref_until_sat                   false
% 3.28/0.98  --abstr_ref_sig_restrict                funpre
% 3.28/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.28/0.98  --abstr_ref_under                       []
% 3.28/0.98  
% 3.28/0.98  ------ SAT Options
% 3.28/0.98  
% 3.28/0.98  --sat_mode                              false
% 3.28/0.98  --sat_fm_restart_options                ""
% 3.28/0.98  --sat_gr_def                            false
% 3.28/0.98  --sat_epr_types                         true
% 3.28/0.98  --sat_non_cyclic_types                  false
% 3.28/0.98  --sat_finite_models                     false
% 3.28/0.98  --sat_fm_lemmas                         false
% 3.28/0.98  --sat_fm_prep                           false
% 3.28/0.98  --sat_fm_uc_incr                        true
% 3.28/0.98  --sat_out_model                         small
% 3.28/0.98  --sat_out_clauses                       false
% 3.28/0.98  
% 3.28/0.98  ------ QBF Options
% 3.28/0.98  
% 3.28/0.98  --qbf_mode                              false
% 3.28/0.98  --qbf_elim_univ                         false
% 3.28/0.98  --qbf_dom_inst                          none
% 3.28/0.98  --qbf_dom_pre_inst                      false
% 3.28/0.98  --qbf_sk_in                             false
% 3.28/0.98  --qbf_pred_elim                         true
% 3.28/0.98  --qbf_split                             512
% 3.28/0.98  
% 3.28/0.98  ------ BMC1 Options
% 3.28/0.98  
% 3.28/0.98  --bmc1_incremental                      false
% 3.28/0.98  --bmc1_axioms                           reachable_all
% 3.28/0.98  --bmc1_min_bound                        0
% 3.28/0.98  --bmc1_max_bound                        -1
% 3.28/0.98  --bmc1_max_bound_default                -1
% 3.28/0.98  --bmc1_symbol_reachability              true
% 3.28/0.98  --bmc1_property_lemmas                  false
% 3.28/0.98  --bmc1_k_induction                      false
% 3.28/0.98  --bmc1_non_equiv_states                 false
% 3.28/0.98  --bmc1_deadlock                         false
% 3.28/0.98  --bmc1_ucm                              false
% 3.28/0.98  --bmc1_add_unsat_core                   none
% 3.28/0.98  --bmc1_unsat_core_children              false
% 3.28/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.28/0.98  --bmc1_out_stat                         full
% 3.28/0.98  --bmc1_ground_init                      false
% 3.28/0.98  --bmc1_pre_inst_next_state              false
% 3.28/0.98  --bmc1_pre_inst_state                   false
% 3.28/0.98  --bmc1_pre_inst_reach_state             false
% 3.28/0.98  --bmc1_out_unsat_core                   false
% 3.28/0.98  --bmc1_aig_witness_out                  false
% 3.28/0.98  --bmc1_verbose                          false
% 3.28/0.98  --bmc1_dump_clauses_tptp                false
% 3.28/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.28/0.98  --bmc1_dump_file                        -
% 3.28/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.28/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.28/0.98  --bmc1_ucm_extend_mode                  1
% 3.28/0.98  --bmc1_ucm_init_mode                    2
% 3.28/0.98  --bmc1_ucm_cone_mode                    none
% 3.28/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.28/0.98  --bmc1_ucm_relax_model                  4
% 3.28/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.28/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.28/0.98  --bmc1_ucm_layered_model                none
% 3.28/0.98  --bmc1_ucm_max_lemma_size               10
% 3.28/0.98  
% 3.28/0.98  ------ AIG Options
% 3.28/0.98  
% 3.28/0.98  --aig_mode                              false
% 3.28/0.98  
% 3.28/0.98  ------ Instantiation Options
% 3.28/0.98  
% 3.28/0.98  --instantiation_flag                    true
% 3.28/0.98  --inst_sos_flag                         false
% 3.28/0.98  --inst_sos_phase                        true
% 3.28/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.28/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.28/0.98  --inst_lit_sel_side                     none
% 3.28/0.98  --inst_solver_per_active                1400
% 3.28/0.98  --inst_solver_calls_frac                1.
% 3.28/0.98  --inst_passive_queue_type               priority_queues
% 3.28/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.28/0.98  --inst_passive_queues_freq              [25;2]
% 3.28/0.98  --inst_dismatching                      true
% 3.28/0.98  --inst_eager_unprocessed_to_passive     true
% 3.28/0.98  --inst_prop_sim_given                   true
% 3.28/0.98  --inst_prop_sim_new                     false
% 3.28/0.98  --inst_subs_new                         false
% 3.28/0.98  --inst_eq_res_simp                      false
% 3.28/0.98  --inst_subs_given                       false
% 3.28/0.98  --inst_orphan_elimination               true
% 3.28/0.98  --inst_learning_loop_flag               true
% 3.28/0.98  --inst_learning_start                   3000
% 3.28/0.98  --inst_learning_factor                  2
% 3.28/0.98  --inst_start_prop_sim_after_learn       3
% 3.28/0.98  --inst_sel_renew                        solver
% 3.28/0.98  --inst_lit_activity_flag                true
% 3.28/0.98  --inst_restr_to_given                   false
% 3.28/0.98  --inst_activity_threshold               500
% 3.28/0.98  --inst_out_proof                        true
% 3.28/0.98  
% 3.28/0.98  ------ Resolution Options
% 3.28/0.98  
% 3.28/0.98  --resolution_flag                       false
% 3.28/0.98  --res_lit_sel                           adaptive
% 3.28/0.98  --res_lit_sel_side                      none
% 3.28/0.98  --res_ordering                          kbo
% 3.28/0.98  --res_to_prop_solver                    active
% 3.28/0.98  --res_prop_simpl_new                    false
% 3.28/0.98  --res_prop_simpl_given                  true
% 3.28/0.98  --res_passive_queue_type                priority_queues
% 3.28/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.28/0.98  --res_passive_queues_freq               [15;5]
% 3.28/0.98  --res_forward_subs                      full
% 3.28/0.98  --res_backward_subs                     full
% 3.28/0.98  --res_forward_subs_resolution           true
% 3.28/0.98  --res_backward_subs_resolution          true
% 3.28/0.98  --res_orphan_elimination                true
% 3.28/0.98  --res_time_limit                        2.
% 3.28/0.98  --res_out_proof                         true
% 3.28/0.98  
% 3.28/0.98  ------ Superposition Options
% 3.28/0.98  
% 3.28/0.98  --superposition_flag                    true
% 3.28/0.98  --sup_passive_queue_type                priority_queues
% 3.28/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.28/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.28/0.98  --demod_completeness_check              fast
% 3.28/0.98  --demod_use_ground                      true
% 3.28/0.98  --sup_to_prop_solver                    passive
% 3.28/0.98  --sup_prop_simpl_new                    true
% 3.28/0.98  --sup_prop_simpl_given                  true
% 3.28/0.98  --sup_fun_splitting                     false
% 3.28/0.98  --sup_smt_interval                      50000
% 3.28/0.98  
% 3.28/0.98  ------ Superposition Simplification Setup
% 3.28/0.98  
% 3.28/0.98  --sup_indices_passive                   []
% 3.28/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.28/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.28/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.28/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.28/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.28/0.98  --sup_full_bw                           [BwDemod]
% 3.28/0.98  --sup_immed_triv                        [TrivRules]
% 3.28/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.28/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.28/0.98  --sup_immed_bw_main                     []
% 3.28/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.28/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.28/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.28/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.28/0.98  
% 3.28/0.98  ------ Combination Options
% 3.28/0.98  
% 3.28/0.98  --comb_res_mult                         3
% 3.28/0.98  --comb_sup_mult                         2
% 3.28/0.98  --comb_inst_mult                        10
% 3.28/0.98  
% 3.28/0.98  ------ Debug Options
% 3.28/0.98  
% 3.28/0.98  --dbg_backtrace                         false
% 3.28/0.98  --dbg_dump_prop_clauses                 false
% 3.28/0.98  --dbg_dump_prop_clauses_file            -
% 3.28/0.98  --dbg_out_stat                          false
% 3.28/0.98  
% 3.28/0.98  
% 3.28/0.98  
% 3.28/0.98  
% 3.28/0.98  ------ Proving...
% 3.28/0.98  
% 3.28/0.98  
% 3.28/0.98  % SZS status Theorem for theBenchmark.p
% 3.28/0.98  
% 3.28/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.28/0.98  
% 3.28/0.98  fof(f8,axiom,(
% 3.28/0.98    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X2,X3))))))),
% 3.28/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/0.98  
% 3.28/0.98  fof(f35,plain,(
% 3.28/0.98    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.28/0.98    inference(ennf_transformation,[],[f8])).
% 3.28/0.98  
% 3.28/0.98  fof(f36,plain,(
% 3.28/0.98    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.28/0.98    inference(flattening,[],[f35])).
% 3.28/0.98  
% 3.28/0.98  fof(f50,plain,(
% 3.28/0.98    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.28/0.98    inference(nnf_transformation,[],[f36])).
% 3.28/0.98  
% 3.28/0.98  fof(f51,plain,(
% 3.28/0.98    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.28/0.98    inference(rectify,[],[f50])).
% 3.28/0.98  
% 3.28/0.98  fof(f52,plain,(
% 3.28/0.98    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X2,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 3.28/0.98    introduced(choice_axiom,[])).
% 3.28/0.98  
% 3.28/0.98  fof(f53,plain,(
% 3.28/0.98    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | (~r1_orders_2(X0,X2,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.28/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f51,f52])).
% 3.28/0.98  
% 3.28/0.98  fof(f78,plain,(
% 3.28/0.98    ( ! [X2,X0,X1] : (r1_lattice3(X0,X1,X2) | r2_hidden(sK0(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.28/0.98    inference(cnf_transformation,[],[f53])).
% 3.28/0.98  
% 3.28/0.98  fof(f14,axiom,(
% 3.28/0.98    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 3.28/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/0.98  
% 3.28/0.98  fof(f23,plain,(
% 3.28/0.98    ! [X0] : l1_orders_2(k2_yellow_1(X0))),
% 3.28/0.98    inference(pure_predicate_removal,[],[f14])).
% 3.28/0.98  
% 3.28/0.98  fof(f99,plain,(
% 3.28/0.98    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 3.28/0.98    inference(cnf_transformation,[],[f23])).
% 3.28/0.98  
% 3.28/0.98  fof(f17,axiom,(
% 3.28/0.98    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 3.28/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/0.98  
% 3.28/0.98  fof(f103,plain,(
% 3.28/0.98    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 3.28/0.98    inference(cnf_transformation,[],[f17])).
% 3.28/0.98  
% 3.28/0.98  fof(f1,axiom,(
% 3.28/0.98    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.28/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/0.98  
% 3.28/0.98  fof(f68,plain,(
% 3.28/0.98    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.28/0.98    inference(cnf_transformation,[],[f1])).
% 3.28/0.98  
% 3.28/0.98  fof(f5,axiom,(
% 3.28/0.98    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.28/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/0.98  
% 3.28/0.98  fof(f30,plain,(
% 3.28/0.98    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.28/0.98    inference(ennf_transformation,[],[f5])).
% 3.28/0.98  
% 3.28/0.98  fof(f72,plain,(
% 3.28/0.98    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.28/0.98    inference(cnf_transformation,[],[f30])).
% 3.28/0.98  
% 3.28/0.98  fof(f13,axiom,(
% 3.28/0.98    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X2,X3) => r1_orders_2(X0,X3,X1))) & r1_lattice3(X0,X2,X1)) => (r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1)) & ((r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X2,X3) => r1_orders_2(X0,X3,X1))) & r1_lattice3(X0,X2,X1))))))),
% 3.28/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/0.98  
% 3.28/0.98  fof(f21,plain,(
% 3.28/0.98    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X2,X3) => r1_orders_2(X0,X3,X1))) & r1_lattice3(X0,X2,X1)) => (r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1)) & ((r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1) => (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r1_lattice3(X0,X2,X4) => r1_orders_2(X0,X4,X1))) & r1_lattice3(X0,X2,X1))))))),
% 3.28/0.98    inference(rectify,[],[f13])).
% 3.28/0.98  
% 3.28/0.98  fof(f43,plain,(
% 3.28/0.98    ! [X0] : (! [X1] : (! [X2] : (((r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1) | (? [X3] : ((~r1_orders_2(X0,X3,X1) & r1_lattice3(X0,X2,X3)) & m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X2,X1))) & ((! [X4] : ((r1_orders_2(X0,X4,X1) | ~r1_lattice3(X0,X2,X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_lattice3(X0,X2,X1)) | (~r2_yellow_0(X0,X2) | k2_yellow_0(X0,X2) != X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0)))),
% 3.28/0.98    inference(ennf_transformation,[],[f21])).
% 3.28/0.98  
% 3.28/0.98  fof(f44,plain,(
% 3.28/0.98    ! [X0] : (! [X1] : (! [X2] : (((r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1) | ? [X3] : (~r1_orders_2(X0,X3,X1) & r1_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X4,X1) | ~r1_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_lattice3(X0,X2,X1)) | ~r2_yellow_0(X0,X2) | k2_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 3.28/0.98    inference(flattening,[],[f43])).
% 3.28/0.98  
% 3.28/0.98  fof(f63,plain,(
% 3.28/0.98    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X1) & r1_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK3(X0,X1,X2),X1) & r1_lattice3(X0,X2,sK3(X0,X1,X2)) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))))),
% 3.28/0.98    introduced(choice_axiom,[])).
% 3.28/0.98  
% 3.28/0.98  fof(f64,plain,(
% 3.28/0.98    ! [X0] : (! [X1] : (! [X2] : (((r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1) | (~r1_orders_2(X0,sK3(X0,X1,X2),X1) & r1_lattice3(X0,X2,sK3(X0,X1,X2)) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))) | ~r1_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X4,X1) | ~r1_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_lattice3(X0,X2,X1)) | ~r2_yellow_0(X0,X2) | k2_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 3.28/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f44,f63])).
% 3.28/0.98  
% 3.28/0.98  fof(f93,plain,(
% 3.28/0.98    ( ! [X2,X0,X1] : (k2_yellow_0(X0,X2) = X1 | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) | ~r1_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 3.28/0.98    inference(cnf_transformation,[],[f64])).
% 3.28/0.98  
% 3.28/0.98  fof(f15,axiom,(
% 3.28/0.98    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v4_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 3.28/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/0.98  
% 3.28/0.98  fof(f22,plain,(
% 3.28/0.98    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 3.28/0.98    inference(pure_predicate_removal,[],[f15])).
% 3.28/0.98  
% 3.28/0.98  fof(f24,plain,(
% 3.28/0.98    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)))),
% 3.28/0.98    inference(pure_predicate_removal,[],[f22])).
% 3.28/0.98  
% 3.28/0.98  fof(f101,plain,(
% 3.28/0.98    ( ! [X0] : (v5_orders_2(k2_yellow_1(X0))) )),
% 3.28/0.98    inference(cnf_transformation,[],[f24])).
% 3.28/0.98  
% 3.28/0.98  fof(f4,axiom,(
% 3.28/0.98    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.28/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/0.98  
% 3.28/0.98  fof(f28,plain,(
% 3.28/0.98    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.28/0.98    inference(ennf_transformation,[],[f4])).
% 3.28/0.98  
% 3.28/0.98  fof(f29,plain,(
% 3.28/0.98    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.28/0.98    inference(flattening,[],[f28])).
% 3.28/0.98  
% 3.28/0.98  fof(f71,plain,(
% 3.28/0.98    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.28/0.98    inference(cnf_transformation,[],[f29])).
% 3.28/0.98  
% 3.28/0.98  fof(f19,conjecture,(
% 3.28/0.98    ! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k3_tarski(X0),X0) => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))))),
% 3.28/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/0.98  
% 3.28/0.98  fof(f20,negated_conjecture,(
% 3.28/0.98    ~! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k3_tarski(X0),X0) => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))))),
% 3.28/0.98    inference(negated_conjecture,[],[f19])).
% 3.28/0.98  
% 3.28/0.98  fof(f47,plain,(
% 3.28/0.98    ? [X0] : ((k3_tarski(X0) != k4_yellow_0(k2_yellow_1(X0)) & r2_hidden(k3_tarski(X0),X0)) & ~v1_xboole_0(X0))),
% 3.28/0.98    inference(ennf_transformation,[],[f20])).
% 3.28/0.98  
% 3.28/0.98  fof(f48,plain,(
% 3.28/0.98    ? [X0] : (k3_tarski(X0) != k4_yellow_0(k2_yellow_1(X0)) & r2_hidden(k3_tarski(X0),X0) & ~v1_xboole_0(X0))),
% 3.28/0.98    inference(flattening,[],[f47])).
% 3.28/0.98  
% 3.28/0.98  fof(f66,plain,(
% 3.28/0.98    ? [X0] : (k3_tarski(X0) != k4_yellow_0(k2_yellow_1(X0)) & r2_hidden(k3_tarski(X0),X0) & ~v1_xboole_0(X0)) => (k3_tarski(sK4) != k4_yellow_0(k2_yellow_1(sK4)) & r2_hidden(k3_tarski(sK4),sK4) & ~v1_xboole_0(sK4))),
% 3.28/0.98    introduced(choice_axiom,[])).
% 3.28/0.98  
% 3.28/0.98  fof(f67,plain,(
% 3.28/0.98    k3_tarski(sK4) != k4_yellow_0(k2_yellow_1(sK4)) & r2_hidden(k3_tarski(sK4),sK4) & ~v1_xboole_0(sK4)),
% 3.28/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f48,f66])).
% 3.28/0.98  
% 3.28/0.98  fof(f107,plain,(
% 3.28/0.98    ~v1_xboole_0(sK4)),
% 3.28/0.98    inference(cnf_transformation,[],[f67])).
% 3.28/0.98  
% 3.28/0.98  fof(f9,axiom,(
% 3.28/0.98    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X3,X2))))))),
% 3.28/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/0.98  
% 3.28/0.98  fof(f37,plain,(
% 3.28/0.98    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.28/0.98    inference(ennf_transformation,[],[f9])).
% 3.28/0.98  
% 3.28/0.98  fof(f38,plain,(
% 3.28/0.98    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.28/0.98    inference(flattening,[],[f37])).
% 3.28/0.98  
% 3.28/0.98  fof(f54,plain,(
% 3.28/0.98    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.28/0.98    inference(nnf_transformation,[],[f38])).
% 3.28/0.98  
% 3.28/0.98  fof(f55,plain,(
% 3.28/0.98    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.28/0.98    inference(rectify,[],[f54])).
% 3.28/0.98  
% 3.28/0.98  fof(f56,plain,(
% 3.28/0.98    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK1(X0,X1,X2),X2) & r2_hidden(sK1(X0,X1,X2),X1) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))))),
% 3.28/0.98    introduced(choice_axiom,[])).
% 3.28/0.98  
% 3.28/0.98  fof(f57,plain,(
% 3.28/0.98    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | (~r1_orders_2(X0,sK1(X0,X1,X2),X2) & r2_hidden(sK1(X0,X1,X2),X1) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.28/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f55,f56])).
% 3.28/0.98  
% 3.28/0.98  fof(f81,plain,(
% 3.28/0.98    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.28/0.98    inference(cnf_transformation,[],[f57])).
% 3.28/0.98  
% 3.28/0.98  fof(f2,axiom,(
% 3.28/0.98    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 3.28/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/0.98  
% 3.28/0.98  fof(f26,plain,(
% 3.28/0.98    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 3.28/0.98    inference(ennf_transformation,[],[f2])).
% 3.28/0.98  
% 3.28/0.98  fof(f69,plain,(
% 3.28/0.98    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 3.28/0.98    inference(cnf_transformation,[],[f26])).
% 3.28/0.98  
% 3.28/0.98  fof(f18,axiom,(
% 3.28/0.98    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)))))),
% 3.28/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/0.98  
% 3.28/0.98  fof(f46,plain,(
% 3.28/0.98    ! [X0] : (! [X1] : (! [X2] : ((r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 3.28/0.98    inference(ennf_transformation,[],[f18])).
% 3.28/0.98  
% 3.28/0.98  fof(f65,plain,(
% 3.28/0.98    ! [X0] : (! [X1] : (! [X2] : (((r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2)) & (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 3.28/0.98    inference(nnf_transformation,[],[f46])).
% 3.28/0.98  
% 3.28/0.98  fof(f106,plain,(
% 3.28/0.98    ( ! [X2,X0,X1] : (r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 3.28/0.98    inference(cnf_transformation,[],[f65])).
% 3.28/0.98  
% 3.28/0.98  fof(f6,axiom,(
% 3.28/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 3.28/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/0.98  
% 3.28/0.98  fof(f31,plain,(
% 3.28/0.98    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 3.28/0.98    inference(ennf_transformation,[],[f6])).
% 3.28/0.98  
% 3.28/0.98  fof(f32,plain,(
% 3.28/0.98    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.28/0.98    inference(flattening,[],[f31])).
% 3.28/0.98  
% 3.28/0.98  fof(f49,plain,(
% 3.28/0.98    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.28/0.98    inference(nnf_transformation,[],[f32])).
% 3.28/0.98  
% 3.28/0.98  fof(f73,plain,(
% 3.28/0.98    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.28/0.98    inference(cnf_transformation,[],[f49])).
% 3.28/0.98  
% 3.28/0.98  fof(f100,plain,(
% 3.28/0.98    ( ! [X0] : (v3_orders_2(k2_yellow_1(X0))) )),
% 3.28/0.98    inference(cnf_transformation,[],[f24])).
% 3.28/0.98  
% 3.28/0.98  fof(f16,axiom,(
% 3.28/0.98    ! [X0] : (~v1_xboole_0(X0) => (v1_orders_2(k2_yellow_1(X0)) & ~v2_struct_0(k2_yellow_1(X0))))),
% 3.28/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/0.98  
% 3.28/0.98  fof(f25,plain,(
% 3.28/0.98    ! [X0] : (~v1_xboole_0(X0) => ~v2_struct_0(k2_yellow_1(X0)))),
% 3.28/0.98    inference(pure_predicate_removal,[],[f16])).
% 3.28/0.98  
% 3.28/0.98  fof(f45,plain,(
% 3.28/0.98    ! [X0] : (~v2_struct_0(k2_yellow_1(X0)) | v1_xboole_0(X0))),
% 3.28/0.98    inference(ennf_transformation,[],[f25])).
% 3.28/0.98  
% 3.28/0.98  fof(f102,plain,(
% 3.28/0.98    ( ! [X0] : (~v2_struct_0(k2_yellow_1(X0)) | v1_xboole_0(X0)) )),
% 3.28/0.98    inference(cnf_transformation,[],[f45])).
% 3.28/0.98  
% 3.28/0.98  fof(f83,plain,(
% 3.28/0.98    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | ~r1_orders_2(X0,sK1(X0,X1,X2),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.28/0.98    inference(cnf_transformation,[],[f57])).
% 3.28/0.98  
% 3.28/0.98  fof(f108,plain,(
% 3.28/0.98    r2_hidden(k3_tarski(sK4),sK4)),
% 3.28/0.98    inference(cnf_transformation,[],[f67])).
% 3.28/0.98  
% 3.28/0.98  fof(f3,axiom,(
% 3.28/0.98    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 3.28/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/0.98  
% 3.28/0.98  fof(f27,plain,(
% 3.28/0.98    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 3.28/0.98    inference(ennf_transformation,[],[f3])).
% 3.28/0.98  
% 3.28/0.98  fof(f70,plain,(
% 3.28/0.98    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 3.28/0.98    inference(cnf_transformation,[],[f27])).
% 3.28/0.98  
% 3.28/0.98  fof(f80,plain,(
% 3.28/0.98    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.28/0.98    inference(cnf_transformation,[],[f57])).
% 3.28/0.98  
% 3.28/0.98  fof(f95,plain,(
% 3.28/0.98    ( ! [X2,X0,X1] : (k2_yellow_0(X0,X2) = X1 | ~r1_orders_2(X0,sK3(X0,X1,X2),X1) | ~r1_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 3.28/0.98    inference(cnf_transformation,[],[f64])).
% 3.28/0.98  
% 3.28/0.98  fof(f11,axiom,(
% 3.28/0.98    ! [X0] : (l1_orders_2(X0) => k2_yellow_0(X0,k1_xboole_0) = k4_yellow_0(X0))),
% 3.28/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/0.98  
% 3.28/0.98  fof(f41,plain,(
% 3.28/0.98    ! [X0] : (k2_yellow_0(X0,k1_xboole_0) = k4_yellow_0(X0) | ~l1_orders_2(X0))),
% 3.28/0.98    inference(ennf_transformation,[],[f11])).
% 3.28/0.98  
% 3.28/0.98  fof(f89,plain,(
% 3.28/0.98    ( ! [X0] : (k2_yellow_0(X0,k1_xboole_0) = k4_yellow_0(X0) | ~l1_orders_2(X0)) )),
% 3.28/0.98    inference(cnf_transformation,[],[f41])).
% 3.28/0.98  
% 3.28/0.98  fof(f109,plain,(
% 3.28/0.98    k3_tarski(sK4) != k4_yellow_0(k2_yellow_1(sK4))),
% 3.28/0.98    inference(cnf_transformation,[],[f67])).
% 3.28/0.98  
% 3.28/0.98  cnf(c_9,plain,
% 3.28/0.98      ( r1_lattice3(X0,X1,X2)
% 3.28/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.28/0.98      | r2_hidden(sK0(X0,X1,X2),X1)
% 3.28/0.98      | ~ l1_orders_2(X0) ),
% 3.28/0.98      inference(cnf_transformation,[],[f78]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_31,plain,
% 3.28/0.98      ( l1_orders_2(k2_yellow_1(X0)) ),
% 3.28/0.98      inference(cnf_transformation,[],[f99]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_1359,plain,
% 3.28/0.98      ( r1_lattice3(X0,X1,X2)
% 3.28/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.28/0.98      | r2_hidden(sK0(X0,X1,X2),X1)
% 3.28/0.98      | k2_yellow_1(X3) != X0 ),
% 3.28/0.98      inference(resolution_lifted,[status(thm)],[c_9,c_31]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_1360,plain,
% 3.28/0.98      ( r1_lattice3(k2_yellow_1(X0),X1,X2)
% 3.28/0.98      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.28/0.98      | r2_hidden(sK0(k2_yellow_1(X0),X1,X2),X1) ),
% 3.28/0.98      inference(unflattening,[status(thm)],[c_1359]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_3465,plain,
% 3.28/0.98      ( r1_lattice3(k2_yellow_1(X0),X1,X2) = iProver_top
% 3.28/0.98      | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 3.28/0.98      | r2_hidden(sK0(k2_yellow_1(X0),X1,X2),X1) = iProver_top ),
% 3.28/0.98      inference(predicate_to_equality,[status(thm)],[c_1360]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_36,plain,
% 3.28/0.98      ( u1_struct_0(k2_yellow_1(X0)) = X0 ),
% 3.28/0.98      inference(cnf_transformation,[],[f103]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_3532,plain,
% 3.28/0.98      ( r1_lattice3(k2_yellow_1(X0),X1,X2) = iProver_top
% 3.28/0.98      | m1_subset_1(X2,X0) != iProver_top
% 3.28/0.98      | r2_hidden(sK0(k2_yellow_1(X0),X1,X2),X1) = iProver_top ),
% 3.28/0.98      inference(light_normalisation,[status(thm)],[c_3465,c_36]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_0,plain,
% 3.28/0.98      ( r1_tarski(k1_xboole_0,X0) ),
% 3.28/0.98      inference(cnf_transformation,[],[f68]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_4,plain,
% 3.28/0.98      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 3.28/0.98      inference(cnf_transformation,[],[f72]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_643,plain,
% 3.28/0.98      ( ~ r2_hidden(X0,X1) | X0 != X2 | k1_xboole_0 != X1 ),
% 3.28/0.98      inference(resolution_lifted,[status(thm)],[c_0,c_4]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_644,plain,
% 3.28/0.98      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 3.28/0.98      inference(unflattening,[status(thm)],[c_643]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_3489,plain,
% 3.28/0.98      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.28/0.98      inference(predicate_to_equality,[status(thm)],[c_644]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_4333,plain,
% 3.28/0.98      ( r1_lattice3(k2_yellow_1(X0),k1_xboole_0,X1) = iProver_top
% 3.28/0.98      | m1_subset_1(X1,X0) != iProver_top ),
% 3.28/0.98      inference(superposition,[status(thm)],[c_3532,c_3489]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_28,plain,
% 3.28/0.98      ( ~ r1_lattice3(X0,X1,X2)
% 3.28/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.28/0.98      | m1_subset_1(sK3(X0,X2,X1),u1_struct_0(X0))
% 3.28/0.98      | ~ v5_orders_2(X0)
% 3.28/0.98      | ~ l1_orders_2(X0)
% 3.28/0.98      | k2_yellow_0(X0,X1) = X2 ),
% 3.28/0.98      inference(cnf_transformation,[],[f93]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_32,plain,
% 3.28/0.98      ( v5_orders_2(k2_yellow_1(X0)) ),
% 3.28/0.98      inference(cnf_transformation,[],[f101]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_821,plain,
% 3.28/0.98      ( ~ r1_lattice3(X0,X1,X2)
% 3.28/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.28/0.98      | m1_subset_1(sK3(X0,X2,X1),u1_struct_0(X0))
% 3.28/0.98      | ~ l1_orders_2(X0)
% 3.28/0.98      | k2_yellow_0(X0,X1) = X2
% 3.28/0.98      | k2_yellow_1(X3) != X0 ),
% 3.28/0.98      inference(resolution_lifted,[status(thm)],[c_28,c_32]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_822,plain,
% 3.28/0.98      ( ~ r1_lattice3(k2_yellow_1(X0),X1,X2)
% 3.28/0.98      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.28/0.98      | m1_subset_1(sK3(k2_yellow_1(X0),X2,X1),u1_struct_0(k2_yellow_1(X0)))
% 3.28/0.98      | ~ l1_orders_2(k2_yellow_1(X0))
% 3.28/0.98      | k2_yellow_0(k2_yellow_1(X0),X1) = X2 ),
% 3.28/0.98      inference(unflattening,[status(thm)],[c_821]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_826,plain,
% 3.28/0.98      ( m1_subset_1(sK3(k2_yellow_1(X0),X2,X1),u1_struct_0(k2_yellow_1(X0)))
% 3.28/0.98      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.28/0.98      | ~ r1_lattice3(k2_yellow_1(X0),X1,X2)
% 3.28/0.98      | k2_yellow_0(k2_yellow_1(X0),X1) = X2 ),
% 3.28/0.98      inference(global_propositional_subsumption,
% 3.28/0.98                [status(thm)],
% 3.28/0.98                [c_822,c_31]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_827,plain,
% 3.28/0.98      ( ~ r1_lattice3(k2_yellow_1(X0),X1,X2)
% 3.28/0.98      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.28/0.98      | m1_subset_1(sK3(k2_yellow_1(X0),X2,X1),u1_struct_0(k2_yellow_1(X0)))
% 3.28/0.98      | k2_yellow_0(k2_yellow_1(X0),X1) = X2 ),
% 3.28/0.98      inference(renaming,[status(thm)],[c_826]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_3484,plain,
% 3.28/0.98      ( k2_yellow_0(k2_yellow_1(X0),X1) = X2
% 3.28/0.98      | r1_lattice3(k2_yellow_1(X0),X1,X2) != iProver_top
% 3.28/0.98      | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 3.28/0.98      | m1_subset_1(sK3(k2_yellow_1(X0),X2,X1),u1_struct_0(k2_yellow_1(X0))) = iProver_top ),
% 3.28/0.98      inference(predicate_to_equality,[status(thm)],[c_827]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_3626,plain,
% 3.28/0.98      ( k2_yellow_0(k2_yellow_1(X0),X1) = X2
% 3.28/0.98      | r1_lattice3(k2_yellow_1(X0),X1,X2) != iProver_top
% 3.28/0.98      | m1_subset_1(X2,X0) != iProver_top
% 3.28/0.98      | m1_subset_1(sK3(k2_yellow_1(X0),X2,X1),X0) = iProver_top ),
% 3.28/0.98      inference(light_normalisation,[status(thm)],[c_3484,c_36]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_3,plain,
% 3.28/0.98      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.28/0.98      inference(cnf_transformation,[],[f71]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_41,negated_conjecture,
% 3.28/0.98      ( ~ v1_xboole_0(sK4) ),
% 3.28/0.98      inference(cnf_transformation,[],[f107]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_456,plain,
% 3.28/0.98      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | sK4 != X1 ),
% 3.28/0.98      inference(resolution_lifted,[status(thm)],[c_3,c_41]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_457,plain,
% 3.28/0.98      ( ~ m1_subset_1(X0,sK4) | r2_hidden(X0,sK4) ),
% 3.28/0.98      inference(unflattening,[status(thm)],[c_456]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_3493,plain,
% 3.28/0.98      ( m1_subset_1(X0,sK4) != iProver_top
% 3.28/0.98      | r2_hidden(X0,sK4) = iProver_top ),
% 3.28/0.98      inference(predicate_to_equality,[status(thm)],[c_457]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_5459,plain,
% 3.28/0.98      ( k2_yellow_0(k2_yellow_1(sK4),X0) = X1
% 3.28/0.98      | r1_lattice3(k2_yellow_1(sK4),X0,X1) != iProver_top
% 3.28/0.98      | m1_subset_1(X1,sK4) != iProver_top
% 3.28/0.98      | r2_hidden(sK3(k2_yellow_1(sK4),X1,X0),sK4) = iProver_top ),
% 3.28/0.98      inference(superposition,[status(thm)],[c_3626,c_3493]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_14,plain,
% 3.28/0.98      ( r2_lattice3(X0,X1,X2)
% 3.28/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.28/0.98      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
% 3.28/0.98      | ~ l1_orders_2(X0) ),
% 3.28/0.98      inference(cnf_transformation,[],[f81]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_1278,plain,
% 3.28/0.98      ( r2_lattice3(X0,X1,X2)
% 3.28/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.28/0.98      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
% 3.28/0.98      | k2_yellow_1(X3) != X0 ),
% 3.28/0.98      inference(resolution_lifted,[status(thm)],[c_14,c_31]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_1279,plain,
% 3.28/0.98      ( r2_lattice3(k2_yellow_1(X0),X1,X2)
% 3.28/0.98      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.28/0.98      | m1_subset_1(sK1(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0))) ),
% 3.28/0.98      inference(unflattening,[status(thm)],[c_1278]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_3470,plain,
% 3.28/0.98      ( r2_lattice3(k2_yellow_1(X0),X1,X2) = iProver_top
% 3.28/0.98      | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 3.28/0.98      | m1_subset_1(sK1(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0))) = iProver_top ),
% 3.28/0.98      inference(predicate_to_equality,[status(thm)],[c_1279]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_3553,plain,
% 3.28/0.98      ( r2_lattice3(k2_yellow_1(X0),X1,X2) = iProver_top
% 3.28/0.98      | m1_subset_1(X2,X0) != iProver_top
% 3.28/0.98      | m1_subset_1(sK1(k2_yellow_1(X0),X1,X2),X0) = iProver_top ),
% 3.28/0.98      inference(light_normalisation,[status(thm)],[c_3470,c_36]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_4643,plain,
% 3.28/0.98      ( r2_lattice3(k2_yellow_1(sK4),X0,X1) = iProver_top
% 3.28/0.98      | m1_subset_1(X1,sK4) != iProver_top
% 3.28/0.98      | r2_hidden(sK1(k2_yellow_1(sK4),X0,X1),sK4) = iProver_top ),
% 3.28/0.98      inference(superposition,[status(thm)],[c_3553,c_3493]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_1,plain,
% 3.28/0.98      ( ~ r2_hidden(X0,X1) | r1_tarski(X0,k3_tarski(X1)) ),
% 3.28/0.98      inference(cnf_transformation,[],[f69]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_37,plain,
% 3.28/0.98      ( r3_orders_2(k2_yellow_1(X0),X1,X2)
% 3.28/0.98      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.28/0.98      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.28/0.98      | ~ r1_tarski(X1,X2)
% 3.28/0.98      | v1_xboole_0(X0) ),
% 3.28/0.98      inference(cnf_transformation,[],[f106]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_486,plain,
% 3.28/0.98      ( r3_orders_2(k2_yellow_1(X0),X1,X2)
% 3.28/0.98      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.28/0.98      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.28/0.98      | ~ r1_tarski(X1,X2)
% 3.28/0.98      | sK4 != X0 ),
% 3.28/0.98      inference(resolution_lifted,[status(thm)],[c_37,c_41]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_487,plain,
% 3.28/0.98      ( r3_orders_2(k2_yellow_1(sK4),X0,X1)
% 3.28/0.98      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK4)))
% 3.28/0.98      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK4)))
% 3.28/0.98      | ~ r1_tarski(X0,X1) ),
% 3.28/0.98      inference(unflattening,[status(thm)],[c_486]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_679,plain,
% 3.28/0.98      ( r3_orders_2(k2_yellow_1(sK4),X0,X1)
% 3.28/0.98      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK4)))
% 3.28/0.98      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK4)))
% 3.28/0.98      | ~ r2_hidden(X2,X3)
% 3.28/0.98      | X0 != X2
% 3.28/0.98      | k3_tarski(X3) != X1 ),
% 3.28/0.98      inference(resolution_lifted,[status(thm)],[c_1,c_487]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_680,plain,
% 3.28/0.98      ( r3_orders_2(k2_yellow_1(sK4),X0,k3_tarski(X1))
% 3.28/0.98      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK4)))
% 3.28/0.98      | ~ m1_subset_1(k3_tarski(X1),u1_struct_0(k2_yellow_1(sK4)))
% 3.28/0.98      | ~ r2_hidden(X0,X1) ),
% 3.28/0.98      inference(unflattening,[status(thm)],[c_679]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_3486,plain,
% 3.28/0.98      ( r3_orders_2(k2_yellow_1(sK4),X0,k3_tarski(X1)) = iProver_top
% 3.28/0.98      | m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK4))) != iProver_top
% 3.28/0.98      | m1_subset_1(k3_tarski(X1),u1_struct_0(k2_yellow_1(sK4))) != iProver_top
% 3.28/0.98      | r2_hidden(X0,X1) != iProver_top ),
% 3.28/0.98      inference(predicate_to_equality,[status(thm)],[c_680]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_3590,plain,
% 3.28/0.98      ( r3_orders_2(k2_yellow_1(sK4),X0,k3_tarski(X1)) = iProver_top
% 3.28/0.98      | m1_subset_1(X0,sK4) != iProver_top
% 3.28/0.98      | m1_subset_1(k3_tarski(X1),sK4) != iProver_top
% 3.28/0.98      | r2_hidden(X0,X1) != iProver_top ),
% 3.28/0.98      inference(demodulation,[status(thm)],[c_3486,c_36]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_6,plain,
% 3.28/0.98      ( r1_orders_2(X0,X1,X2)
% 3.28/0.98      | ~ r3_orders_2(X0,X1,X2)
% 3.28/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.28/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.28/0.98      | v2_struct_0(X0)
% 3.28/0.98      | ~ v3_orders_2(X0)
% 3.28/0.98      | ~ l1_orders_2(X0) ),
% 3.28/0.98      inference(cnf_transformation,[],[f73]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_33,plain,
% 3.28/0.98      ( v3_orders_2(k2_yellow_1(X0)) ),
% 3.28/0.98      inference(cnf_transformation,[],[f100]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_526,plain,
% 3.28/0.98      ( r1_orders_2(X0,X1,X2)
% 3.28/0.98      | ~ r3_orders_2(X0,X1,X2)
% 3.28/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.28/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.28/0.98      | v2_struct_0(X0)
% 3.28/0.98      | ~ l1_orders_2(X0)
% 3.28/0.98      | k2_yellow_1(X3) != X0 ),
% 3.28/0.98      inference(resolution_lifted,[status(thm)],[c_6,c_33]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_527,plain,
% 3.28/0.98      ( r1_orders_2(k2_yellow_1(X0),X1,X2)
% 3.28/0.98      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
% 3.28/0.98      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.28/0.98      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.28/0.98      | v2_struct_0(k2_yellow_1(X0))
% 3.28/0.98      | ~ l1_orders_2(k2_yellow_1(X0)) ),
% 3.28/0.98      inference(unflattening,[status(thm)],[c_526]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_531,plain,
% 3.28/0.98      ( v2_struct_0(k2_yellow_1(X0))
% 3.28/0.98      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.28/0.98      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.28/0.98      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
% 3.28/0.98      | r1_orders_2(k2_yellow_1(X0),X1,X2) ),
% 3.28/0.98      inference(global_propositional_subsumption,
% 3.28/0.98                [status(thm)],
% 3.28/0.98                [c_527,c_31]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_532,plain,
% 3.28/0.98      ( r1_orders_2(k2_yellow_1(X0),X1,X2)
% 3.28/0.98      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
% 3.28/0.98      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.28/0.98      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.28/0.98      | v2_struct_0(k2_yellow_1(X0)) ),
% 3.28/0.98      inference(renaming,[status(thm)],[c_531]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_3491,plain,
% 3.28/0.98      ( r1_orders_2(k2_yellow_1(X0),X1,X2) = iProver_top
% 3.28/0.98      | r3_orders_2(k2_yellow_1(X0),X1,X2) != iProver_top
% 3.28/0.98      | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 3.28/0.98      | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 3.28/0.98      | v2_struct_0(k2_yellow_1(X0)) = iProver_top ),
% 3.28/0.98      inference(predicate_to_equality,[status(thm)],[c_532]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_3675,plain,
% 3.28/0.98      ( r1_orders_2(k2_yellow_1(X0),X1,X2) = iProver_top
% 3.28/0.98      | r3_orders_2(k2_yellow_1(X0),X1,X2) != iProver_top
% 3.28/0.98      | m1_subset_1(X2,X0) != iProver_top
% 3.28/0.98      | m1_subset_1(X1,X0) != iProver_top
% 3.28/0.98      | v2_struct_0(k2_yellow_1(X0)) = iProver_top ),
% 3.28/0.98      inference(light_normalisation,[status(thm)],[c_3491,c_36]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_5557,plain,
% 3.28/0.98      ( r1_orders_2(k2_yellow_1(sK4),X0,k3_tarski(X1)) = iProver_top
% 3.28/0.98      | m1_subset_1(X0,sK4) != iProver_top
% 3.28/0.98      | m1_subset_1(k3_tarski(X1),sK4) != iProver_top
% 3.28/0.98      | r2_hidden(X0,X1) != iProver_top
% 3.28/0.98      | v2_struct_0(k2_yellow_1(sK4)) = iProver_top ),
% 3.28/0.98      inference(superposition,[status(thm)],[c_3590,c_3675]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_42,plain,
% 3.28/0.98      ( v1_xboole_0(sK4) != iProver_top ),
% 3.28/0.98      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_34,plain,
% 3.28/0.98      ( ~ v2_struct_0(k2_yellow_1(X0)) | v1_xboole_0(X0) ),
% 3.28/0.98      inference(cnf_transformation,[],[f102]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_52,plain,
% 3.28/0.98      ( v2_struct_0(k2_yellow_1(X0)) != iProver_top
% 3.28/0.98      | v1_xboole_0(X0) = iProver_top ),
% 3.28/0.98      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_54,plain,
% 3.28/0.98      ( v2_struct_0(k2_yellow_1(sK4)) != iProver_top
% 3.28/0.98      | v1_xboole_0(sK4) = iProver_top ),
% 3.28/0.98      inference(instantiation,[status(thm)],[c_52]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_5650,plain,
% 3.28/0.98      ( r2_hidden(X0,X1) != iProver_top
% 3.28/0.98      | m1_subset_1(k3_tarski(X1),sK4) != iProver_top
% 3.28/0.98      | m1_subset_1(X0,sK4) != iProver_top
% 3.28/0.98      | r1_orders_2(k2_yellow_1(sK4),X0,k3_tarski(X1)) = iProver_top ),
% 3.28/0.98      inference(global_propositional_subsumption,
% 3.28/0.98                [status(thm)],
% 3.28/0.98                [c_5557,c_42,c_54]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_5651,plain,
% 3.28/0.98      ( r1_orders_2(k2_yellow_1(sK4),X0,k3_tarski(X1)) = iProver_top
% 3.28/0.98      | m1_subset_1(X0,sK4) != iProver_top
% 3.28/0.98      | m1_subset_1(k3_tarski(X1),sK4) != iProver_top
% 3.28/0.98      | r2_hidden(X0,X1) != iProver_top ),
% 3.28/0.98      inference(renaming,[status(thm)],[c_5650]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_12,plain,
% 3.28/0.98      ( r2_lattice3(X0,X1,X2)
% 3.28/0.98      | ~ r1_orders_2(X0,sK1(X0,X1,X2),X2)
% 3.28/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.28/0.98      | ~ l1_orders_2(X0) ),
% 3.28/0.98      inference(cnf_transformation,[],[f83]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_1308,plain,
% 3.28/0.98      ( r2_lattice3(X0,X1,X2)
% 3.28/0.98      | ~ r1_orders_2(X0,sK1(X0,X1,X2),X2)
% 3.28/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.28/0.98      | k2_yellow_1(X3) != X0 ),
% 3.28/0.98      inference(resolution_lifted,[status(thm)],[c_12,c_31]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_1309,plain,
% 3.28/0.98      ( r2_lattice3(k2_yellow_1(X0),X1,X2)
% 3.28/0.98      | ~ r1_orders_2(k2_yellow_1(X0),sK1(k2_yellow_1(X0),X1,X2),X2)
% 3.28/0.98      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) ),
% 3.28/0.98      inference(unflattening,[status(thm)],[c_1308]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_3468,plain,
% 3.28/0.98      ( r2_lattice3(k2_yellow_1(X0),X1,X2) = iProver_top
% 3.28/0.98      | r1_orders_2(k2_yellow_1(X0),sK1(k2_yellow_1(X0),X1,X2),X2) != iProver_top
% 3.28/0.98      | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top ),
% 3.28/0.98      inference(predicate_to_equality,[status(thm)],[c_1309]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_3567,plain,
% 3.28/0.98      ( r2_lattice3(k2_yellow_1(X0),X1,X2) = iProver_top
% 3.28/0.98      | r1_orders_2(k2_yellow_1(X0),sK1(k2_yellow_1(X0),X1,X2),X2) != iProver_top
% 3.28/0.98      | m1_subset_1(X2,X0) != iProver_top ),
% 3.28/0.98      inference(light_normalisation,[status(thm)],[c_3468,c_36]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_5662,plain,
% 3.28/0.98      ( r2_lattice3(k2_yellow_1(sK4),X0,k3_tarski(X1)) = iProver_top
% 3.28/0.98      | m1_subset_1(sK1(k2_yellow_1(sK4),X0,k3_tarski(X1)),sK4) != iProver_top
% 3.28/0.98      | m1_subset_1(k3_tarski(X1),sK4) != iProver_top
% 3.28/0.98      | r2_hidden(sK1(k2_yellow_1(sK4),X0,k3_tarski(X1)),X1) != iProver_top ),
% 3.28/0.98      inference(superposition,[status(thm)],[c_5651,c_3567]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_7373,plain,
% 3.28/0.98      ( r2_lattice3(k2_yellow_1(sK4),X0,k3_tarski(X1)) = iProver_top
% 3.28/0.98      | m1_subset_1(k3_tarski(X1),sK4) != iProver_top
% 3.28/0.98      | r2_hidden(sK1(k2_yellow_1(sK4),X0,k3_tarski(X1)),X1) != iProver_top ),
% 3.28/0.98      inference(forward_subsumption_resolution,
% 3.28/0.98                [status(thm)],
% 3.28/0.98                [c_5662,c_3553]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_7378,plain,
% 3.28/0.98      ( r2_lattice3(k2_yellow_1(sK4),X0,k3_tarski(sK4)) = iProver_top
% 3.28/0.98      | m1_subset_1(k3_tarski(sK4),sK4) != iProver_top ),
% 3.28/0.98      inference(superposition,[status(thm)],[c_4643,c_7373]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_40,negated_conjecture,
% 3.28/0.98      ( r2_hidden(k3_tarski(sK4),sK4) ),
% 3.28/0.98      inference(cnf_transformation,[],[f108]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_43,plain,
% 3.28/0.98      ( r2_hidden(k3_tarski(sK4),sK4) = iProver_top ),
% 3.28/0.98      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_2,plain,
% 3.28/0.98      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 3.28/0.98      inference(cnf_transformation,[],[f70]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_3886,plain,
% 3.28/0.98      ( m1_subset_1(k3_tarski(sK4),sK4)
% 3.28/0.98      | ~ r2_hidden(k3_tarski(sK4),sK4) ),
% 3.28/0.98      inference(instantiation,[status(thm)],[c_2]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_3887,plain,
% 3.28/0.98      ( m1_subset_1(k3_tarski(sK4),sK4) = iProver_top
% 3.28/0.98      | r2_hidden(k3_tarski(sK4),sK4) != iProver_top ),
% 3.28/0.98      inference(predicate_to_equality,[status(thm)],[c_3886]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_7392,plain,
% 3.28/0.98      ( r2_lattice3(k2_yellow_1(sK4),X0,k3_tarski(sK4)) = iProver_top ),
% 3.28/0.98      inference(global_propositional_subsumption,
% 3.28/0.98                [status(thm)],
% 3.28/0.98                [c_7378,c_43,c_3887]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_15,plain,
% 3.28/0.98      ( ~ r2_lattice3(X0,X1,X2)
% 3.28/0.98      | r1_orders_2(X0,X3,X2)
% 3.28/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.28/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.28/0.98      | ~ r2_hidden(X3,X1)
% 3.28/0.98      | ~ l1_orders_2(X0) ),
% 3.28/0.98      inference(cnf_transformation,[],[f80]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_1257,plain,
% 3.28/0.98      ( ~ r2_lattice3(X0,X1,X2)
% 3.28/0.98      | r1_orders_2(X0,X3,X2)
% 3.28/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.28/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.28/0.98      | ~ r2_hidden(X3,X1)
% 3.28/0.98      | k2_yellow_1(X4) != X0 ),
% 3.28/0.98      inference(resolution_lifted,[status(thm)],[c_15,c_31]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_1258,plain,
% 3.28/0.98      ( ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
% 3.28/0.98      | r1_orders_2(k2_yellow_1(X0),X3,X2)
% 3.28/0.98      | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(X0)))
% 3.28/0.98      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.28/0.98      | ~ r2_hidden(X3,X1) ),
% 3.28/0.98      inference(unflattening,[status(thm)],[c_1257]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_3471,plain,
% 3.28/0.98      ( r2_lattice3(k2_yellow_1(X0),X1,X2) != iProver_top
% 3.28/0.98      | r1_orders_2(k2_yellow_1(X0),X3,X2) = iProver_top
% 3.28/0.98      | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 3.28/0.98      | m1_subset_1(X3,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 3.28/0.98      | r2_hidden(X3,X1) != iProver_top ),
% 3.28/0.98      inference(predicate_to_equality,[status(thm)],[c_1258]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_3697,plain,
% 3.28/0.98      ( r2_lattice3(k2_yellow_1(X0),X1,X2) != iProver_top
% 3.28/0.98      | r1_orders_2(k2_yellow_1(X0),X3,X2) = iProver_top
% 3.28/0.98      | m1_subset_1(X2,X0) != iProver_top
% 3.28/0.98      | m1_subset_1(X3,X0) != iProver_top
% 3.28/0.98      | r2_hidden(X3,X1) != iProver_top ),
% 3.28/0.98      inference(light_normalisation,[status(thm)],[c_3471,c_36]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_7399,plain,
% 3.28/0.98      ( r1_orders_2(k2_yellow_1(sK4),X0,k3_tarski(sK4)) = iProver_top
% 3.28/0.98      | m1_subset_1(X0,sK4) != iProver_top
% 3.28/0.98      | m1_subset_1(k3_tarski(sK4),sK4) != iProver_top
% 3.28/0.98      | r2_hidden(X0,X1) != iProver_top ),
% 3.28/0.98      inference(superposition,[status(thm)],[c_7392,c_3697]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_7611,plain,
% 3.28/0.98      ( m1_subset_1(X0,sK4) != iProver_top
% 3.28/0.98      | r1_orders_2(k2_yellow_1(sK4),X0,k3_tarski(sK4)) = iProver_top
% 3.28/0.98      | r2_hidden(X0,X1) != iProver_top ),
% 3.28/0.98      inference(global_propositional_subsumption,
% 3.28/0.98                [status(thm)],
% 3.28/0.98                [c_7399,c_43,c_3887]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_7612,plain,
% 3.28/0.98      ( r1_orders_2(k2_yellow_1(sK4),X0,k3_tarski(sK4)) = iProver_top
% 3.28/0.98      | m1_subset_1(X0,sK4) != iProver_top
% 3.28/0.98      | r2_hidden(X0,X1) != iProver_top ),
% 3.28/0.98      inference(renaming,[status(thm)],[c_7611]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_7624,plain,
% 3.28/0.98      ( k2_yellow_0(k2_yellow_1(sK4),X0) = X1
% 3.28/0.98      | r1_lattice3(k2_yellow_1(sK4),X0,X1) != iProver_top
% 3.28/0.98      | r1_orders_2(k2_yellow_1(sK4),sK3(k2_yellow_1(sK4),X1,X0),k3_tarski(sK4)) = iProver_top
% 3.28/0.98      | m1_subset_1(X1,sK4) != iProver_top
% 3.28/0.98      | m1_subset_1(sK3(k2_yellow_1(sK4),X1,X0),sK4) != iProver_top ),
% 3.28/0.98      inference(superposition,[status(thm)],[c_5459,c_7612]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_8955,plain,
% 3.28/0.98      ( k2_yellow_0(k2_yellow_1(sK4),X0) = X1
% 3.28/0.98      | r1_lattice3(k2_yellow_1(sK4),X0,X1) != iProver_top
% 3.28/0.98      | r1_orders_2(k2_yellow_1(sK4),sK3(k2_yellow_1(sK4),X1,X0),k3_tarski(sK4)) = iProver_top
% 3.28/0.98      | m1_subset_1(X1,sK4) != iProver_top ),
% 3.28/0.98      inference(forward_subsumption_resolution,
% 3.28/0.98                [status(thm)],
% 3.28/0.98                [c_7624,c_3626]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_26,plain,
% 3.28/0.98      ( ~ r1_lattice3(X0,X1,X2)
% 3.28/0.98      | ~ r1_orders_2(X0,sK3(X0,X2,X1),X2)
% 3.28/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.28/0.98      | ~ v5_orders_2(X0)
% 3.28/0.98      | ~ l1_orders_2(X0)
% 3.28/0.98      | k2_yellow_0(X0,X1) = X2 ),
% 3.28/0.98      inference(cnf_transformation,[],[f95]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_869,plain,
% 3.28/0.98      ( ~ r1_lattice3(X0,X1,X2)
% 3.28/0.98      | ~ r1_orders_2(X0,sK3(X0,X2,X1),X2)
% 3.28/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.28/0.98      | ~ l1_orders_2(X0)
% 3.28/0.98      | k2_yellow_0(X0,X1) = X2
% 3.28/0.98      | k2_yellow_1(X3) != X0 ),
% 3.28/0.98      inference(resolution_lifted,[status(thm)],[c_26,c_32]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_870,plain,
% 3.28/0.98      ( ~ r1_lattice3(k2_yellow_1(X0),X1,X2)
% 3.28/0.98      | ~ r1_orders_2(k2_yellow_1(X0),sK3(k2_yellow_1(X0),X2,X1),X2)
% 3.28/0.98      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.28/0.98      | ~ l1_orders_2(k2_yellow_1(X0))
% 3.28/0.98      | k2_yellow_0(k2_yellow_1(X0),X1) = X2 ),
% 3.28/0.98      inference(unflattening,[status(thm)],[c_869]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_874,plain,
% 3.28/0.98      ( ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.28/0.98      | ~ r1_orders_2(k2_yellow_1(X0),sK3(k2_yellow_1(X0),X2,X1),X2)
% 3.28/0.98      | ~ r1_lattice3(k2_yellow_1(X0),X1,X2)
% 3.28/0.98      | k2_yellow_0(k2_yellow_1(X0),X1) = X2 ),
% 3.28/0.98      inference(global_propositional_subsumption,
% 3.28/0.98                [status(thm)],
% 3.28/0.98                [c_870,c_31]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_875,plain,
% 3.28/0.98      ( ~ r1_lattice3(k2_yellow_1(X0),X1,X2)
% 3.28/0.98      | ~ r1_orders_2(k2_yellow_1(X0),sK3(k2_yellow_1(X0),X2,X1),X2)
% 3.28/0.98      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.28/0.98      | k2_yellow_0(k2_yellow_1(X0),X1) = X2 ),
% 3.28/0.98      inference(renaming,[status(thm)],[c_874]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_3482,plain,
% 3.28/0.98      ( k2_yellow_0(k2_yellow_1(X0),X1) = X2
% 3.28/0.98      | r1_lattice3(k2_yellow_1(X0),X1,X2) != iProver_top
% 3.28/0.98      | r1_orders_2(k2_yellow_1(X0),sK3(k2_yellow_1(X0),X2,X1),X2) != iProver_top
% 3.28/0.98      | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top ),
% 3.28/0.98      inference(predicate_to_equality,[status(thm)],[c_875]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_3644,plain,
% 3.28/0.98      ( k2_yellow_0(k2_yellow_1(X0),X1) = X2
% 3.28/0.98      | r1_lattice3(k2_yellow_1(X0),X1,X2) != iProver_top
% 3.28/0.98      | r1_orders_2(k2_yellow_1(X0),sK3(k2_yellow_1(X0),X2,X1),X2) != iProver_top
% 3.28/0.98      | m1_subset_1(X2,X0) != iProver_top ),
% 3.28/0.98      inference(light_normalisation,[status(thm)],[c_3482,c_36]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_8960,plain,
% 3.28/0.98      ( k2_yellow_0(k2_yellow_1(sK4),X0) = k3_tarski(sK4)
% 3.28/0.98      | r1_lattice3(k2_yellow_1(sK4),X0,k3_tarski(sK4)) != iProver_top
% 3.28/0.98      | m1_subset_1(k3_tarski(sK4),sK4) != iProver_top ),
% 3.28/0.98      inference(superposition,[status(thm)],[c_8955,c_3644]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_9691,plain,
% 3.28/0.98      ( r1_lattice3(k2_yellow_1(sK4),X0,k3_tarski(sK4)) != iProver_top
% 3.28/0.98      | k2_yellow_0(k2_yellow_1(sK4),X0) = k3_tarski(sK4) ),
% 3.28/0.98      inference(global_propositional_subsumption,
% 3.28/0.98                [status(thm)],
% 3.28/0.98                [c_8960,c_43,c_3887]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_9692,plain,
% 3.28/0.98      ( k2_yellow_0(k2_yellow_1(sK4),X0) = k3_tarski(sK4)
% 3.28/0.98      | r1_lattice3(k2_yellow_1(sK4),X0,k3_tarski(sK4)) != iProver_top ),
% 3.28/0.98      inference(renaming,[status(thm)],[c_9691]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_9699,plain,
% 3.28/0.98      ( k2_yellow_0(k2_yellow_1(sK4),k1_xboole_0) = k3_tarski(sK4)
% 3.28/0.98      | m1_subset_1(k3_tarski(sK4),sK4) != iProver_top ),
% 3.28/0.98      inference(superposition,[status(thm)],[c_4333,c_9692]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_21,plain,
% 3.28/0.98      ( ~ l1_orders_2(X0)
% 3.28/0.98      | k2_yellow_0(X0,k1_xboole_0) = k4_yellow_0(X0) ),
% 3.28/0.98      inference(cnf_transformation,[],[f89]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_1152,plain,
% 3.28/0.98      ( k2_yellow_0(X0,k1_xboole_0) = k4_yellow_0(X0)
% 3.28/0.98      | k2_yellow_1(X1) != X0 ),
% 3.28/0.98      inference(resolution_lifted,[status(thm)],[c_21,c_31]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_1153,plain,
% 3.28/0.98      ( k2_yellow_0(k2_yellow_1(X0),k1_xboole_0) = k4_yellow_0(k2_yellow_1(X0)) ),
% 3.28/0.98      inference(unflattening,[status(thm)],[c_1152]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_9700,plain,
% 3.28/0.98      ( k4_yellow_0(k2_yellow_1(sK4)) = k3_tarski(sK4)
% 3.28/0.98      | m1_subset_1(k3_tarski(sK4),sK4) != iProver_top ),
% 3.28/0.98      inference(demodulation,[status(thm)],[c_9699,c_1153]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_2867,plain,( X0 != X1 | X2 != X1 | X0 = X2 ),theory(equality) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_3897,plain,
% 3.28/0.98      ( k4_yellow_0(k2_yellow_1(sK4)) != X0
% 3.28/0.98      | k3_tarski(sK4) != X0
% 3.28/0.98      | k3_tarski(sK4) = k4_yellow_0(k2_yellow_1(sK4)) ),
% 3.28/0.98      inference(instantiation,[status(thm)],[c_2867]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_4024,plain,
% 3.28/0.98      ( k4_yellow_0(k2_yellow_1(sK4)) != k3_tarski(sK4)
% 3.28/0.98      | k3_tarski(sK4) = k4_yellow_0(k2_yellow_1(sK4))
% 3.28/0.98      | k3_tarski(sK4) != k3_tarski(sK4) ),
% 3.28/0.98      inference(instantiation,[status(thm)],[c_3897]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_2866,plain,( X0 = X0 ),theory(equality) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_2905,plain,
% 3.28/0.98      ( sK4 = sK4 ),
% 3.28/0.98      inference(instantiation,[status(thm)],[c_2866]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_2868,plain,
% 3.28/0.98      ( X0 != X1 | k3_tarski(X0) = k3_tarski(X1) ),
% 3.28/0.98      theory(equality) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_2886,plain,
% 3.28/0.98      ( k3_tarski(sK4) = k3_tarski(sK4) | sK4 != sK4 ),
% 3.28/0.98      inference(instantiation,[status(thm)],[c_2868]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_39,negated_conjecture,
% 3.28/0.98      ( k3_tarski(sK4) != k4_yellow_0(k2_yellow_1(sK4)) ),
% 3.28/0.98      inference(cnf_transformation,[],[f109]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(contradiction,plain,
% 3.28/0.98      ( $false ),
% 3.28/0.98      inference(minisat,
% 3.28/0.98                [status(thm)],
% 3.28/0.98                [c_9700,c_4024,c_3887,c_2905,c_2886,c_39,c_43]) ).
% 3.28/0.98  
% 3.28/0.98  
% 3.28/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.28/0.98  
% 3.28/0.98  ------                               Statistics
% 3.28/0.98  
% 3.28/0.98  ------ General
% 3.28/0.98  
% 3.28/0.98  abstr_ref_over_cycles:                  0
% 3.28/0.98  abstr_ref_under_cycles:                 0
% 3.28/0.98  gc_basic_clause_elim:                   0
% 3.28/0.98  forced_gc_time:                         0
% 3.28/0.98  parsing_time:                           0.012
% 3.28/0.98  unif_index_cands_time:                  0.
% 3.28/0.98  unif_index_add_time:                    0.
% 3.28/0.98  orderings_time:                         0.
% 3.28/0.98  out_proof_time:                         0.011
% 3.28/0.98  total_time:                             0.288
% 3.28/0.98  num_of_symbols:                         57
% 3.28/0.98  num_of_terms:                           7989
% 3.28/0.98  
% 3.28/0.98  ------ Preprocessing
% 3.28/0.98  
% 3.28/0.98  num_of_splits:                          0
% 3.28/0.98  num_of_split_atoms:                     0
% 3.28/0.98  num_of_reused_defs:                     0
% 3.28/0.98  num_eq_ax_congr_red:                    50
% 3.28/0.98  num_of_sem_filtered_clauses:            1
% 3.28/0.98  num_of_subtypes:                        0
% 3.28/0.98  monotx_restored_types:                  0
% 3.28/0.98  sat_num_of_epr_types:                   0
% 3.28/0.98  sat_num_of_non_cyclic_types:            0
% 3.28/0.98  sat_guarded_non_collapsed_types:        0
% 3.28/0.98  num_pure_diseq_elim:                    0
% 3.28/0.98  simp_replaced_by:                       0
% 3.28/0.98  res_preprocessed:                       189
% 3.28/0.98  prep_upred:                             0
% 3.28/0.98  prep_unflattend:                        58
% 3.28/0.98  smt_new_axioms:                         0
% 3.28/0.98  pred_elim_cands:                        8
% 3.28/0.98  pred_elim:                              5
% 3.28/0.98  pred_elim_cl:                           4
% 3.28/0.98  pred_elim_cycles:                       14
% 3.28/0.98  merged_defs:                            0
% 3.28/0.98  merged_defs_ncl:                        0
% 3.28/0.98  bin_hyper_res:                          0
% 3.28/0.98  prep_cycles:                            4
% 3.28/0.98  pred_elim_time:                         0.043
% 3.28/0.98  splitting_time:                         0.
% 3.28/0.98  sem_filter_time:                        0.
% 3.28/0.98  monotx_time:                            0.001
% 3.28/0.98  subtype_inf_time:                       0.
% 3.28/0.98  
% 3.28/0.98  ------ Problem properties
% 3.28/0.98  
% 3.28/0.98  clauses:                                36
% 3.28/0.98  conjectures:                            2
% 3.28/0.98  epr:                                    3
% 3.28/0.98  horn:                                   24
% 3.28/0.98  ground:                                 3
% 3.28/0.98  unary:                                  8
% 3.28/0.98  binary:                                 3
% 3.28/0.98  lits:                                   115
% 3.28/0.98  lits_eq:                                11
% 3.28/0.98  fd_pure:                                0
% 3.28/0.98  fd_pseudo:                              0
% 3.28/0.98  fd_cond:                                0
% 3.28/0.98  fd_pseudo_cond:                         7
% 3.28/0.98  ac_symbols:                             0
% 3.28/0.98  
% 3.28/0.98  ------ Propositional Solver
% 3.28/0.98  
% 3.28/0.98  prop_solver_calls:                      27
% 3.28/0.98  prop_fast_solver_calls:                 2005
% 3.28/0.98  smt_solver_calls:                       0
% 3.28/0.98  smt_fast_solver_calls:                  0
% 3.28/0.98  prop_num_of_clauses:                    3290
% 3.28/0.98  prop_preprocess_simplified:             10242
% 3.28/0.98  prop_fo_subsumed:                       30
% 3.28/0.98  prop_solver_time:                       0.
% 3.28/0.98  smt_solver_time:                        0.
% 3.28/0.98  smt_fast_solver_time:                   0.
% 3.28/0.98  prop_fast_solver_time:                  0.
% 3.28/0.98  prop_unsat_core_time:                   0.
% 3.28/0.98  
% 3.28/0.98  ------ QBF
% 3.28/0.98  
% 3.28/0.98  qbf_q_res:                              0
% 3.28/0.98  qbf_num_tautologies:                    0
% 3.28/0.98  qbf_prep_cycles:                        0
% 3.28/0.98  
% 3.28/0.98  ------ BMC1
% 3.28/0.98  
% 3.28/0.98  bmc1_current_bound:                     -1
% 3.28/0.98  bmc1_last_solved_bound:                 -1
% 3.28/0.98  bmc1_unsat_core_size:                   -1
% 3.28/0.98  bmc1_unsat_core_parents_size:           -1
% 3.28/0.98  bmc1_merge_next_fun:                    0
% 3.28/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.28/0.98  
% 3.28/0.98  ------ Instantiation
% 3.28/0.98  
% 3.28/0.98  inst_num_of_clauses:                    845
% 3.28/0.98  inst_num_in_passive:                    206
% 3.28/0.98  inst_num_in_active:                     290
% 3.28/0.98  inst_num_in_unprocessed:                349
% 3.28/0.98  inst_num_of_loops:                      370
% 3.28/0.98  inst_num_of_learning_restarts:          0
% 3.28/0.98  inst_num_moves_active_passive:          78
% 3.28/0.98  inst_lit_activity:                      0
% 3.28/0.98  inst_lit_activity_moves:                0
% 3.28/0.98  inst_num_tautologies:                   0
% 3.28/0.98  inst_num_prop_implied:                  0
% 3.28/0.98  inst_num_existing_simplified:           0
% 3.28/0.98  inst_num_eq_res_simplified:             0
% 3.28/0.98  inst_num_child_elim:                    0
% 3.28/0.98  inst_num_of_dismatching_blockings:      357
% 3.28/0.98  inst_num_of_non_proper_insts:           530
% 3.28/0.98  inst_num_of_duplicates:                 0
% 3.28/0.98  inst_inst_num_from_inst_to_res:         0
% 3.28/0.98  inst_dismatching_checking_time:         0.
% 3.28/0.98  
% 3.28/0.98  ------ Resolution
% 3.28/0.98  
% 3.28/0.98  res_num_of_clauses:                     0
% 3.28/0.98  res_num_in_passive:                     0
% 3.28/0.98  res_num_in_active:                      0
% 3.28/0.98  res_num_of_loops:                       193
% 3.28/0.98  res_forward_subset_subsumed:            40
% 3.28/0.98  res_backward_subset_subsumed:           0
% 3.28/0.98  res_forward_subsumed:                   0
% 3.28/0.98  res_backward_subsumed:                  0
% 3.28/0.98  res_forward_subsumption_resolution:     0
% 3.28/0.98  res_backward_subsumption_resolution:    0
% 3.28/0.98  res_clause_to_clause_subsumption:       575
% 3.28/0.98  res_orphan_elimination:                 0
% 3.28/0.98  res_tautology_del:                      24
% 3.28/0.98  res_num_eq_res_simplified:              0
% 3.28/0.98  res_num_sel_changes:                    0
% 3.28/0.98  res_moves_from_active_to_pass:          0
% 3.28/0.98  
% 3.28/0.98  ------ Superposition
% 3.28/0.98  
% 3.28/0.98  sup_time_total:                         0.
% 3.28/0.98  sup_time_generating:                    0.
% 3.28/0.98  sup_time_sim_full:                      0.
% 3.28/0.98  sup_time_sim_immed:                     0.
% 3.28/0.98  
% 3.28/0.98  sup_num_of_clauses:                     105
% 3.28/0.98  sup_num_in_active:                      73
% 3.28/0.98  sup_num_in_passive:                     32
% 3.28/0.98  sup_num_of_loops:                       72
% 3.28/0.98  sup_fw_superposition:                   29
% 3.28/0.98  sup_bw_superposition:                   69
% 3.28/0.98  sup_immediate_simplified:               25
% 3.28/0.98  sup_given_eliminated:                   0
% 3.28/0.98  comparisons_done:                       0
% 3.28/0.98  comparisons_avoided:                    0
% 3.28/0.98  
% 3.28/0.98  ------ Simplifications
% 3.28/0.98  
% 3.28/0.98  
% 3.28/0.98  sim_fw_subset_subsumed:                 8
% 3.28/0.98  sim_bw_subset_subsumed:                 1
% 3.28/0.98  sim_fw_subsumed:                        12
% 3.28/0.98  sim_bw_subsumed:                        3
% 3.28/0.98  sim_fw_subsumption_res:                 5
% 3.28/0.98  sim_bw_subsumption_res:                 0
% 3.28/0.98  sim_tautology_del:                      0
% 3.28/0.98  sim_eq_tautology_del:                   3
% 3.28/0.98  sim_eq_res_simp:                        0
% 3.28/0.98  sim_fw_demodulated:                     5
% 3.28/0.98  sim_bw_demodulated:                     0
% 3.28/0.98  sim_light_normalised:                   25
% 3.28/0.98  sim_joinable_taut:                      0
% 3.28/0.98  sim_joinable_simp:                      0
% 3.28/0.98  sim_ac_normalised:                      0
% 3.28/0.98  sim_smt_subsumption:                    0
% 3.28/0.98  
%------------------------------------------------------------------------------
