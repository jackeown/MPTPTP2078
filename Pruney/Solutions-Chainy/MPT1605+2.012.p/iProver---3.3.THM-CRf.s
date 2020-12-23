%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:20:14 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 247 expanded)
%              Number of clauses        :   86 ( 113 expanded)
%              Number of leaves         :   18 (  48 expanded)
%              Depth                    :   26
%              Number of atoms          :  512 ( 828 expanded)
%              Number of equality atoms :  174 ( 257 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   15 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
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

fof(f14,plain,(
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
    inference(rectify,[],[f5])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X1,X3)
          & r2_lattice3(X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X1,sK0(X0,X1,X2))
        & r2_lattice3(X0,X2,sK0(X0,X1,X2))
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f32])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X2) = X1
      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
      | ~ r2_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f8,axiom,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v4_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f17,plain,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f53,plain,(
    ! [X0] : v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f51,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f10,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

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

fof(f31,plain,(
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

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f52,plain,(
    ! [X0] : v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f11,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
             => ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f12,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( r2_hidden(k1_xboole_0,X0)
       => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ( r2_hidden(k1_xboole_0,X0)
         => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f29,plain,(
    ? [X0] :
      ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0))
      & r2_hidden(k1_xboole_0,X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f30,plain,(
    ? [X0] :
      ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0))
      & r2_hidden(k1_xboole_0,X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f35,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0))
        & r2_hidden(k1_xboole_0,X0)
        & ~ v1_xboole_0(X0) )
   => ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK1))
      & r2_hidden(k1_xboole_0,sK1)
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK1))
    & r2_hidden(k1_xboole_0,sK1)
    & ~ v1_xboole_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f35])).

fof(f59,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f9,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_orders_2(k2_yellow_1(X0))
        & ~ v2_struct_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ~ v2_struct_0(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k2_yellow_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k2_yellow_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

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

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f60,plain,(
    r2_hidden(k1_xboole_0,sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X2) = X1
      | ~ r1_orders_2(X0,X1,sK0(X0,X1,X2))
      | ~ r2_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f41,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( r1_lattice3(X0,k1_xboole_0,X1)
            & r2_lattice3(X0,k1_xboole_0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r2_lattice3(X0,k1_xboole_0,X1) ) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_lattice3(X0,k1_xboole_0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_lattice3(X0,k1_xboole_0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f61,plain,(
    k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK1)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_10,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X2,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_15,plain,
    ( v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_577,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X2,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2
    | k2_yellow_1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_15])).

cnf(c_578,plain,
    ( ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | m1_subset_1(sK0(k2_yellow_1(X0),X2,X1),u1_struct_0(k2_yellow_1(X0)))
    | ~ l1_orders_2(k2_yellow_1(X0))
    | k1_yellow_0(k2_yellow_1(X0),X1) = X2 ),
    inference(unflattening,[status(thm)],[c_577])).

cnf(c_14,plain,
    ( l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_582,plain,
    ( m1_subset_1(sK0(k2_yellow_1(X0),X2,X1),u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
    | k1_yellow_0(k2_yellow_1(X0),X1) = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_578,c_14])).

cnf(c_583,plain,
    ( ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | m1_subset_1(sK0(k2_yellow_1(X0),X2,X1),u1_struct_0(k2_yellow_1(X0)))
    | k1_yellow_0(k2_yellow_1(X0),X1) = X2 ),
    inference(renaming,[status(thm)],[c_582])).

cnf(c_1748,plain,
    ( k1_yellow_0(k2_yellow_1(X0),X1) = X2
    | r2_lattice3(k2_yellow_1(X0),X1,X2) != iProver_top
    | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | m1_subset_1(sK0(k2_yellow_1(X0),X2,X1),u1_struct_0(k2_yellow_1(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_583])).

cnf(c_19,plain,
    ( u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1802,plain,
    ( k1_yellow_0(k2_yellow_1(X0),X1) = X2
    | r2_lattice3(k2_yellow_1(X0),X1,X2) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(sK0(k2_yellow_1(X0),X2,X1),X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1748,c_19])).

cnf(c_3,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_16,plain,
    ( v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_347,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | k2_yellow_1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_16])).

cnf(c_348,plain,
    ( r1_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | v2_struct_0(k2_yellow_1(X0))
    | ~ l1_orders_2(k2_yellow_1(X0)) ),
    inference(unflattening,[status(thm)],[c_347])).

cnf(c_352,plain,
    ( v2_struct_0(k2_yellow_1(X0))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
    | r1_orders_2(k2_yellow_1(X0),X1,X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_348,c_14])).

cnf(c_353,plain,
    ( r1_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | v2_struct_0(k2_yellow_1(X0)) ),
    inference(renaming,[status(thm)],[c_352])).

cnf(c_0,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_20,plain,
    ( r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ r1_tarski(X1,X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_24,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_290,plain,
    ( r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ r1_tarski(X1,X2)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_24])).

cnf(c_291,plain,
    ( r3_orders_2(k2_yellow_1(sK1),X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))
    | ~ r1_tarski(X0,X1) ),
    inference(unflattening,[status(thm)],[c_290])).

cnf(c_328,plain,
    ( r3_orders_2(k2_yellow_1(sK1),X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))
    | X1 != X2
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_291])).

cnf(c_329,plain,
    ( r3_orders_2(k2_yellow_1(sK1),k1_xboole_0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK1))) ),
    inference(unflattening,[status(thm)],[c_328])).

cnf(c_464,plain,
    ( r1_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK1)))
    | v2_struct_0(k2_yellow_1(X0))
    | X3 != X2
    | k2_yellow_1(X0) != k2_yellow_1(sK1)
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_353,c_329])).

cnf(c_465,plain,
    ( r1_orders_2(k2_yellow_1(X0),k1_xboole_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK1)))
    | v2_struct_0(k2_yellow_1(X0))
    | k2_yellow_1(X0) != k2_yellow_1(sK1) ),
    inference(unflattening,[status(thm)],[c_464])).

cnf(c_17,plain,
    ( v1_xboole_0(X0)
    | ~ v2_struct_0(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_308,plain,
    ( ~ v2_struct_0(k2_yellow_1(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_24])).

cnf(c_309,plain,
    ( ~ v2_struct_0(k2_yellow_1(sK1)) ),
    inference(unflattening,[status(thm)],[c_308])).

cnf(c_499,plain,
    ( r1_orders_2(k2_yellow_1(X0),k1_xboole_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK1)))
    | k2_yellow_1(X0) != k2_yellow_1(sK1) ),
    inference(resolution_lifted,[status(thm)],[c_465,c_309])).

cnf(c_1751,plain,
    ( k2_yellow_1(X0) != k2_yellow_1(sK1)
    | r1_orders_2(k2_yellow_1(X0),k1_xboole_0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_499])).

cnf(c_1840,plain,
    ( k2_yellow_1(X0) != k2_yellow_1(sK1)
    | r1_orders_2(k2_yellow_1(X0),k1_xboole_0,X1) = iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,X0) != iProver_top
    | m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1751,c_19])).

cnf(c_1841,plain,
    ( k2_yellow_1(X0) != k2_yellow_1(sK1)
    | r1_orders_2(k2_yellow_1(X0),k1_xboole_0,X1) = iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(X1,sK1) != iProver_top
    | m1_subset_1(k1_xboole_0,X0) != iProver_top
    | m1_subset_1(k1_xboole_0,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1840,c_19])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_23,negated_conjecture,
    ( r2_hidden(k1_xboole_0,sK1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_265,plain,
    ( m1_subset_1(X0,X1)
    | sK1 != X1
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_23])).

cnf(c_266,plain,
    ( m1_subset_1(k1_xboole_0,sK1) ),
    inference(unflattening,[status(thm)],[c_265])).

cnf(c_1752,plain,
    ( m1_subset_1(k1_xboole_0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_266])).

cnf(c_1848,plain,
    ( k2_yellow_1(X0) != k2_yellow_1(sK1)
    | r1_orders_2(k2_yellow_1(X0),k1_xboole_0,X1) = iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(X1,sK1) != iProver_top
    | m1_subset_1(k1_xboole_0,X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1841,c_1752])).

cnf(c_1916,plain,
    ( r1_orders_2(k2_yellow_1(sK1),k1_xboole_0,X0) = iProver_top
    | m1_subset_1(X0,sK1) != iProver_top
    | m1_subset_1(k1_xboole_0,sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1848])).

cnf(c_267,plain,
    ( m1_subset_1(k1_xboole_0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_266])).

cnf(c_1921,plain,
    ( m1_subset_1(X0,sK1) != iProver_top
    | r1_orders_2(k2_yellow_1(sK1),k1_xboole_0,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1916,c_267])).

cnf(c_1922,plain,
    ( r1_orders_2(k2_yellow_1(sK1),k1_xboole_0,X0) = iProver_top
    | m1_subset_1(X0,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_1921])).

cnf(c_8,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK0(X0,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_625,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK0(X0,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2
    | k2_yellow_1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_15])).

cnf(c_626,plain,
    ( ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
    | ~ r1_orders_2(k2_yellow_1(X0),X2,sK0(k2_yellow_1(X0),X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ l1_orders_2(k2_yellow_1(X0))
    | k1_yellow_0(k2_yellow_1(X0),X1) = X2 ),
    inference(unflattening,[status(thm)],[c_625])).

cnf(c_630,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ r1_orders_2(k2_yellow_1(X0),X2,sK0(k2_yellow_1(X0),X2,X1))
    | ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
    | k1_yellow_0(k2_yellow_1(X0),X1) = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_626,c_14])).

cnf(c_631,plain,
    ( ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
    | ~ r1_orders_2(k2_yellow_1(X0),X2,sK0(k2_yellow_1(X0),X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | k1_yellow_0(k2_yellow_1(X0),X1) = X2 ),
    inference(renaming,[status(thm)],[c_630])).

cnf(c_1746,plain,
    ( k1_yellow_0(k2_yellow_1(X0),X1) = X2
    | r2_lattice3(k2_yellow_1(X0),X1,X2) != iProver_top
    | r1_orders_2(k2_yellow_1(X0),X2,sK0(k2_yellow_1(X0),X2,X1)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_631])).

cnf(c_1820,plain,
    ( k1_yellow_0(k2_yellow_1(X0),X1) = X2
    | r2_lattice3(k2_yellow_1(X0),X1,X2) != iProver_top
    | r1_orders_2(k2_yellow_1(X0),X2,sK0(k2_yellow_1(X0),X2,X1)) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1746,c_19])).

cnf(c_2458,plain,
    ( k1_yellow_0(k2_yellow_1(sK1),X0) = k1_xboole_0
    | r2_lattice3(k2_yellow_1(sK1),X0,k1_xboole_0) != iProver_top
    | m1_subset_1(sK0(k2_yellow_1(sK1),k1_xboole_0,X0),sK1) != iProver_top
    | m1_subset_1(k1_xboole_0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1922,c_1820])).

cnf(c_2518,plain,
    ( m1_subset_1(sK0(k2_yellow_1(sK1),k1_xboole_0,X0),sK1) != iProver_top
    | r2_lattice3(k2_yellow_1(sK1),X0,k1_xboole_0) != iProver_top
    | k1_yellow_0(k2_yellow_1(sK1),X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2458,c_267])).

cnf(c_2519,plain,
    ( k1_yellow_0(k2_yellow_1(sK1),X0) = k1_xboole_0
    | r2_lattice3(k2_yellow_1(sK1),X0,k1_xboole_0) != iProver_top
    | m1_subset_1(sK0(k2_yellow_1(sK1),k1_xboole_0,X0),sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_2518])).

cnf(c_2527,plain,
    ( k1_yellow_0(k2_yellow_1(sK1),X0) = k1_xboole_0
    | r2_lattice3(k2_yellow_1(sK1),X0,k1_xboole_0) != iProver_top
    | m1_subset_1(k1_xboole_0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1802,c_2519])).

cnf(c_2536,plain,
    ( k1_yellow_0(k2_yellow_1(sK1),k1_xboole_0) = k1_xboole_0
    | r2_lattice3(k2_yellow_1(sK1),k1_xboole_0,k1_xboole_0) != iProver_top
    | m1_subset_1(k1_xboole_0,sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2527])).

cnf(c_1511,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2398,plain,
    ( k1_yellow_0(k2_yellow_1(sK1),k1_xboole_0) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK1),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1511])).

cnf(c_2399,plain,
    ( k1_yellow_0(k2_yellow_1(sK1),k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK1),k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2398])).

cnf(c_1903,plain,
    ( k3_yellow_0(k2_yellow_1(sK1)) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k3_yellow_0(k2_yellow_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_1511])).

cnf(c_2210,plain,
    ( k3_yellow_0(k2_yellow_1(sK1)) != k1_yellow_0(k2_yellow_1(sK1),k1_xboole_0)
    | k1_xboole_0 != k1_yellow_0(k2_yellow_1(sK1),k1_xboole_0)
    | k1_xboole_0 = k3_yellow_0(k2_yellow_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_1903])).

cnf(c_4,plain,
    ( ~ l1_orders_2(X0)
    | k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_773,plain,
    ( k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0)
    | k2_yellow_1(X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_14])).

cnf(c_774,plain,
    ( k1_yellow_0(k2_yellow_1(X0),k1_xboole_0) = k3_yellow_0(k2_yellow_1(X0)) ),
    inference(unflattening,[status(thm)],[c_773])).

cnf(c_2059,plain,
    ( k1_yellow_0(k2_yellow_1(sK1),k1_xboole_0) = k3_yellow_0(k2_yellow_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_774])).

cnf(c_1928,plain,
    ( X0 != X1
    | k3_yellow_0(k2_yellow_1(sK1)) != X1
    | k3_yellow_0(k2_yellow_1(sK1)) = X0 ),
    inference(instantiation,[status(thm)],[c_1511])).

cnf(c_1956,plain,
    ( X0 != k3_yellow_0(k2_yellow_1(sK1))
    | k3_yellow_0(k2_yellow_1(sK1)) = X0
    | k3_yellow_0(k2_yellow_1(sK1)) != k3_yellow_0(k2_yellow_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_1928])).

cnf(c_2058,plain,
    ( k1_yellow_0(k2_yellow_1(sK1),k1_xboole_0) != k3_yellow_0(k2_yellow_1(sK1))
    | k3_yellow_0(k2_yellow_1(sK1)) = k1_yellow_0(k2_yellow_1(sK1),k1_xboole_0)
    | k3_yellow_0(k2_yellow_1(sK1)) != k3_yellow_0(k2_yellow_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_1956])).

cnf(c_13,plain,
    ( r2_lattice3(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_761,plain,
    ( r2_lattice3(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | k2_yellow_1(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_14])).

cnf(c_762,plain,
    ( r2_lattice3(k2_yellow_1(X0),k1_xboole_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) ),
    inference(unflattening,[status(thm)],[c_761])).

cnf(c_1993,plain,
    ( r2_lattice3(k2_yellow_1(sK1),k1_xboole_0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1))) ),
    inference(instantiation,[status(thm)],[c_762])).

cnf(c_1994,plain,
    ( r2_lattice3(k2_yellow_1(sK1),k1_xboole_0,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1993])).

cnf(c_1996,plain,
    ( r2_lattice3(k2_yellow_1(sK1),k1_xboole_0,k1_xboole_0) = iProver_top
    | m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK1))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1994])).

cnf(c_1510,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1950,plain,
    ( k2_yellow_1(sK1) = k2_yellow_1(sK1) ),
    inference(instantiation,[status(thm)],[c_1510])).

cnf(c_1515,plain,
    ( X0 != X1
    | k3_yellow_0(X0) = k3_yellow_0(X1) ),
    theory(equality)).

cnf(c_1930,plain,
    ( k2_yellow_1(sK1) != X0
    | k3_yellow_0(k2_yellow_1(sK1)) = k3_yellow_0(X0) ),
    inference(instantiation,[status(thm)],[c_1515])).

cnf(c_1949,plain,
    ( k2_yellow_1(sK1) != k2_yellow_1(sK1)
    | k3_yellow_0(k2_yellow_1(sK1)) = k3_yellow_0(k2_yellow_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_1930])).

cnf(c_1934,plain,
    ( u1_struct_0(k2_yellow_1(sK1)) = sK1 ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_1512,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1905,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(k1_xboole_0,sK1)
    | X1 != sK1
    | X0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1512])).

cnf(c_1933,plain,
    ( m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(k1_xboole_0,sK1)
    | X0 != k1_xboole_0
    | u1_struct_0(k2_yellow_1(sK1)) != sK1 ),
    inference(instantiation,[status(thm)],[c_1905])).

cnf(c_1935,plain,
    ( X0 != k1_xboole_0
    | u1_struct_0(k2_yellow_1(sK1)) != sK1
    | m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1))) = iProver_top
    | m1_subset_1(k1_xboole_0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1933])).

cnf(c_1937,plain,
    ( u1_struct_0(k2_yellow_1(sK1)) != sK1
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK1))) = iProver_top
    | m1_subset_1(k1_xboole_0,sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1935])).

cnf(c_1533,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1510])).

cnf(c_22,negated_conjecture,
    ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK1)) ),
    inference(cnf_transformation,[],[f61])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2536,c_2399,c_2210,c_2059,c_2058,c_1996,c_1950,c_1949,c_1934,c_1937,c_1533,c_267,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:23:08 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.66/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.00  
% 1.66/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.66/1.00  
% 1.66/1.00  ------  iProver source info
% 1.66/1.00  
% 1.66/1.00  git: date: 2020-06-30 10:37:57 +0100
% 1.66/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.66/1.00  git: non_committed_changes: false
% 1.66/1.00  git: last_make_outside_of_git: false
% 1.66/1.00  
% 1.66/1.00  ------ 
% 1.66/1.00  
% 1.66/1.00  ------ Input Options
% 1.66/1.00  
% 1.66/1.00  --out_options                           all
% 1.66/1.00  --tptp_safe_out                         true
% 1.66/1.00  --problem_path                          ""
% 1.66/1.00  --include_path                          ""
% 1.66/1.00  --clausifier                            res/vclausify_rel
% 1.66/1.00  --clausifier_options                    --mode clausify
% 1.66/1.00  --stdin                                 false
% 1.66/1.00  --stats_out                             all
% 1.66/1.00  
% 1.66/1.00  ------ General Options
% 1.66/1.00  
% 1.66/1.00  --fof                                   false
% 1.66/1.00  --time_out_real                         305.
% 1.66/1.00  --time_out_virtual                      -1.
% 1.66/1.00  --symbol_type_check                     false
% 1.66/1.00  --clausify_out                          false
% 1.66/1.00  --sig_cnt_out                           false
% 1.66/1.00  --trig_cnt_out                          false
% 1.66/1.00  --trig_cnt_out_tolerance                1.
% 1.66/1.00  --trig_cnt_out_sk_spl                   false
% 1.66/1.00  --abstr_cl_out                          false
% 1.66/1.00  
% 1.66/1.00  ------ Global Options
% 1.66/1.00  
% 1.66/1.00  --schedule                              default
% 1.66/1.00  --add_important_lit                     false
% 1.66/1.00  --prop_solver_per_cl                    1000
% 1.66/1.00  --min_unsat_core                        false
% 1.66/1.00  --soft_assumptions                      false
% 1.66/1.00  --soft_lemma_size                       3
% 1.66/1.00  --prop_impl_unit_size                   0
% 1.66/1.00  --prop_impl_unit                        []
% 1.66/1.00  --share_sel_clauses                     true
% 1.66/1.00  --reset_solvers                         false
% 1.66/1.00  --bc_imp_inh                            [conj_cone]
% 1.66/1.00  --conj_cone_tolerance                   3.
% 1.66/1.00  --extra_neg_conj                        none
% 1.66/1.00  --large_theory_mode                     true
% 1.66/1.00  --prolific_symb_bound                   200
% 1.66/1.00  --lt_threshold                          2000
% 1.66/1.00  --clause_weak_htbl                      true
% 1.66/1.00  --gc_record_bc_elim                     false
% 1.66/1.00  
% 1.66/1.00  ------ Preprocessing Options
% 1.66/1.00  
% 1.66/1.00  --preprocessing_flag                    true
% 1.66/1.00  --time_out_prep_mult                    0.1
% 1.66/1.00  --splitting_mode                        input
% 1.66/1.00  --splitting_grd                         true
% 1.66/1.00  --splitting_cvd                         false
% 1.66/1.00  --splitting_cvd_svl                     false
% 1.66/1.00  --splitting_nvd                         32
% 1.66/1.00  --sub_typing                            true
% 1.66/1.00  --prep_gs_sim                           true
% 1.66/1.00  --prep_unflatten                        true
% 1.66/1.00  --prep_res_sim                          true
% 1.66/1.00  --prep_upred                            true
% 1.66/1.00  --prep_sem_filter                       exhaustive
% 1.66/1.00  --prep_sem_filter_out                   false
% 1.66/1.00  --pred_elim                             true
% 1.66/1.00  --res_sim_input                         true
% 1.66/1.00  --eq_ax_congr_red                       true
% 1.66/1.00  --pure_diseq_elim                       true
% 1.66/1.00  --brand_transform                       false
% 1.66/1.00  --non_eq_to_eq                          false
% 1.66/1.00  --prep_def_merge                        true
% 1.66/1.00  --prep_def_merge_prop_impl              false
% 1.66/1.00  --prep_def_merge_mbd                    true
% 1.66/1.00  --prep_def_merge_tr_red                 false
% 1.66/1.00  --prep_def_merge_tr_cl                  false
% 1.66/1.00  --smt_preprocessing                     true
% 1.66/1.00  --smt_ac_axioms                         fast
% 1.66/1.00  --preprocessed_out                      false
% 1.66/1.00  --preprocessed_stats                    false
% 1.66/1.00  
% 1.66/1.00  ------ Abstraction refinement Options
% 1.66/1.00  
% 1.66/1.00  --abstr_ref                             []
% 1.66/1.00  --abstr_ref_prep                        false
% 1.66/1.00  --abstr_ref_until_sat                   false
% 1.66/1.00  --abstr_ref_sig_restrict                funpre
% 1.66/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.66/1.00  --abstr_ref_under                       []
% 1.66/1.00  
% 1.66/1.00  ------ SAT Options
% 1.66/1.00  
% 1.66/1.00  --sat_mode                              false
% 1.66/1.00  --sat_fm_restart_options                ""
% 1.66/1.00  --sat_gr_def                            false
% 1.66/1.00  --sat_epr_types                         true
% 1.66/1.00  --sat_non_cyclic_types                  false
% 1.66/1.00  --sat_finite_models                     false
% 1.66/1.00  --sat_fm_lemmas                         false
% 1.66/1.00  --sat_fm_prep                           false
% 1.66/1.00  --sat_fm_uc_incr                        true
% 1.66/1.00  --sat_out_model                         small
% 1.66/1.00  --sat_out_clauses                       false
% 1.66/1.00  
% 1.66/1.00  ------ QBF Options
% 1.66/1.00  
% 1.66/1.00  --qbf_mode                              false
% 1.66/1.00  --qbf_elim_univ                         false
% 1.66/1.00  --qbf_dom_inst                          none
% 1.66/1.00  --qbf_dom_pre_inst                      false
% 1.66/1.00  --qbf_sk_in                             false
% 1.66/1.00  --qbf_pred_elim                         true
% 1.66/1.00  --qbf_split                             512
% 1.66/1.00  
% 1.66/1.00  ------ BMC1 Options
% 1.66/1.00  
% 1.66/1.00  --bmc1_incremental                      false
% 1.66/1.00  --bmc1_axioms                           reachable_all
% 1.66/1.00  --bmc1_min_bound                        0
% 1.66/1.00  --bmc1_max_bound                        -1
% 1.66/1.00  --bmc1_max_bound_default                -1
% 1.66/1.00  --bmc1_symbol_reachability              true
% 1.66/1.00  --bmc1_property_lemmas                  false
% 1.66/1.00  --bmc1_k_induction                      false
% 1.66/1.00  --bmc1_non_equiv_states                 false
% 1.66/1.00  --bmc1_deadlock                         false
% 1.66/1.00  --bmc1_ucm                              false
% 1.66/1.00  --bmc1_add_unsat_core                   none
% 1.66/1.00  --bmc1_unsat_core_children              false
% 1.66/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.66/1.00  --bmc1_out_stat                         full
% 1.66/1.00  --bmc1_ground_init                      false
% 1.66/1.00  --bmc1_pre_inst_next_state              false
% 1.66/1.00  --bmc1_pre_inst_state                   false
% 1.66/1.00  --bmc1_pre_inst_reach_state             false
% 1.66/1.00  --bmc1_out_unsat_core                   false
% 1.66/1.00  --bmc1_aig_witness_out                  false
% 1.66/1.00  --bmc1_verbose                          false
% 1.66/1.00  --bmc1_dump_clauses_tptp                false
% 1.66/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.66/1.00  --bmc1_dump_file                        -
% 1.66/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.66/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.66/1.00  --bmc1_ucm_extend_mode                  1
% 1.66/1.00  --bmc1_ucm_init_mode                    2
% 1.66/1.00  --bmc1_ucm_cone_mode                    none
% 1.66/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.66/1.00  --bmc1_ucm_relax_model                  4
% 1.66/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.66/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.66/1.00  --bmc1_ucm_layered_model                none
% 1.66/1.00  --bmc1_ucm_max_lemma_size               10
% 1.66/1.00  
% 1.66/1.00  ------ AIG Options
% 1.66/1.00  
% 1.66/1.00  --aig_mode                              false
% 1.66/1.00  
% 1.66/1.00  ------ Instantiation Options
% 1.66/1.00  
% 1.66/1.00  --instantiation_flag                    true
% 1.66/1.00  --inst_sos_flag                         false
% 1.66/1.00  --inst_sos_phase                        true
% 1.66/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.66/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.66/1.00  --inst_lit_sel_side                     num_symb
% 1.66/1.00  --inst_solver_per_active                1400
% 1.66/1.00  --inst_solver_calls_frac                1.
% 1.66/1.00  --inst_passive_queue_type               priority_queues
% 1.66/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.66/1.00  --inst_passive_queues_freq              [25;2]
% 1.66/1.00  --inst_dismatching                      true
% 1.66/1.00  --inst_eager_unprocessed_to_passive     true
% 1.66/1.00  --inst_prop_sim_given                   true
% 1.66/1.00  --inst_prop_sim_new                     false
% 1.66/1.00  --inst_subs_new                         false
% 1.66/1.00  --inst_eq_res_simp                      false
% 1.66/1.00  --inst_subs_given                       false
% 1.66/1.00  --inst_orphan_elimination               true
% 1.66/1.00  --inst_learning_loop_flag               true
% 1.66/1.00  --inst_learning_start                   3000
% 1.66/1.00  --inst_learning_factor                  2
% 1.66/1.00  --inst_start_prop_sim_after_learn       3
% 1.66/1.00  --inst_sel_renew                        solver
% 1.66/1.00  --inst_lit_activity_flag                true
% 1.66/1.00  --inst_restr_to_given                   false
% 1.66/1.00  --inst_activity_threshold               500
% 1.66/1.00  --inst_out_proof                        true
% 1.66/1.00  
% 1.66/1.00  ------ Resolution Options
% 1.66/1.00  
% 1.66/1.00  --resolution_flag                       true
% 1.66/1.00  --res_lit_sel                           adaptive
% 1.66/1.00  --res_lit_sel_side                      none
% 1.66/1.00  --res_ordering                          kbo
% 1.66/1.00  --res_to_prop_solver                    active
% 1.66/1.00  --res_prop_simpl_new                    false
% 1.66/1.00  --res_prop_simpl_given                  true
% 1.66/1.00  --res_passive_queue_type                priority_queues
% 1.66/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.66/1.00  --res_passive_queues_freq               [15;5]
% 1.66/1.00  --res_forward_subs                      full
% 1.66/1.00  --res_backward_subs                     full
% 1.66/1.00  --res_forward_subs_resolution           true
% 1.66/1.00  --res_backward_subs_resolution          true
% 1.66/1.00  --res_orphan_elimination                true
% 1.66/1.00  --res_time_limit                        2.
% 1.66/1.00  --res_out_proof                         true
% 1.66/1.00  
% 1.66/1.00  ------ Superposition Options
% 1.66/1.00  
% 1.66/1.00  --superposition_flag                    true
% 1.66/1.00  --sup_passive_queue_type                priority_queues
% 1.66/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.66/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.66/1.00  --demod_completeness_check              fast
% 1.66/1.00  --demod_use_ground                      true
% 1.66/1.00  --sup_to_prop_solver                    passive
% 1.66/1.00  --sup_prop_simpl_new                    true
% 1.66/1.00  --sup_prop_simpl_given                  true
% 1.66/1.00  --sup_fun_splitting                     false
% 1.66/1.00  --sup_smt_interval                      50000
% 1.66/1.00  
% 1.66/1.00  ------ Superposition Simplification Setup
% 1.66/1.00  
% 1.66/1.00  --sup_indices_passive                   []
% 1.66/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.66/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.66/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.66/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.66/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.66/1.00  --sup_full_bw                           [BwDemod]
% 1.66/1.00  --sup_immed_triv                        [TrivRules]
% 1.66/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.66/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.66/1.00  --sup_immed_bw_main                     []
% 1.66/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.66/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.66/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.66/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.66/1.00  
% 1.66/1.00  ------ Combination Options
% 1.66/1.00  
% 1.66/1.00  --comb_res_mult                         3
% 1.66/1.00  --comb_sup_mult                         2
% 1.66/1.00  --comb_inst_mult                        10
% 1.66/1.00  
% 1.66/1.00  ------ Debug Options
% 1.66/1.00  
% 1.66/1.00  --dbg_backtrace                         false
% 1.66/1.00  --dbg_dump_prop_clauses                 false
% 1.66/1.00  --dbg_dump_prop_clauses_file            -
% 1.66/1.00  --dbg_out_stat                          false
% 1.66/1.00  ------ Parsing...
% 1.66/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.66/1.00  
% 1.66/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 9 0s  sf_e  pe_s  pe_e 
% 1.66/1.00  
% 1.66/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.66/1.00  
% 1.66/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.66/1.00  ------ Proving...
% 1.66/1.00  ------ Problem Properties 
% 1.66/1.00  
% 1.66/1.00  
% 1.66/1.00  clauses                                 15
% 1.66/1.00  conjectures                             1
% 1.66/1.00  EPR                                     1
% 1.66/1.00  Horn                                    11
% 1.66/1.00  unary                                   5
% 1.66/1.00  binary                                  1
% 1.66/1.00  lits                                    45
% 1.66/1.00  lits eq                                 8
% 1.66/1.00  fd_pure                                 0
% 1.66/1.00  fd_pseudo                               0
% 1.66/1.00  fd_cond                                 0
% 1.66/1.00  fd_pseudo_cond                          3
% 1.66/1.00  AC symbols                              0
% 1.66/1.00  
% 1.66/1.00  ------ Schedule dynamic 5 is on 
% 1.66/1.00  
% 1.66/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.66/1.00  
% 1.66/1.00  
% 1.66/1.00  ------ 
% 1.66/1.00  Current options:
% 1.66/1.00  ------ 
% 1.66/1.00  
% 1.66/1.00  ------ Input Options
% 1.66/1.00  
% 1.66/1.00  --out_options                           all
% 1.66/1.00  --tptp_safe_out                         true
% 1.66/1.00  --problem_path                          ""
% 1.66/1.00  --include_path                          ""
% 1.66/1.00  --clausifier                            res/vclausify_rel
% 1.66/1.00  --clausifier_options                    --mode clausify
% 1.66/1.00  --stdin                                 false
% 1.66/1.00  --stats_out                             all
% 1.66/1.00  
% 1.66/1.00  ------ General Options
% 1.66/1.00  
% 1.66/1.00  --fof                                   false
% 1.66/1.00  --time_out_real                         305.
% 1.66/1.00  --time_out_virtual                      -1.
% 1.66/1.00  --symbol_type_check                     false
% 1.66/1.00  --clausify_out                          false
% 1.66/1.00  --sig_cnt_out                           false
% 1.66/1.00  --trig_cnt_out                          false
% 1.66/1.00  --trig_cnt_out_tolerance                1.
% 1.66/1.00  --trig_cnt_out_sk_spl                   false
% 1.66/1.00  --abstr_cl_out                          false
% 1.66/1.00  
% 1.66/1.00  ------ Global Options
% 1.66/1.00  
% 1.66/1.00  --schedule                              default
% 1.66/1.00  --add_important_lit                     false
% 1.66/1.00  --prop_solver_per_cl                    1000
% 1.66/1.00  --min_unsat_core                        false
% 1.66/1.00  --soft_assumptions                      false
% 1.66/1.00  --soft_lemma_size                       3
% 1.66/1.00  --prop_impl_unit_size                   0
% 1.66/1.00  --prop_impl_unit                        []
% 1.66/1.00  --share_sel_clauses                     true
% 1.66/1.00  --reset_solvers                         false
% 1.66/1.00  --bc_imp_inh                            [conj_cone]
% 1.66/1.00  --conj_cone_tolerance                   3.
% 1.66/1.00  --extra_neg_conj                        none
% 1.66/1.00  --large_theory_mode                     true
% 1.66/1.00  --prolific_symb_bound                   200
% 1.66/1.00  --lt_threshold                          2000
% 1.66/1.00  --clause_weak_htbl                      true
% 1.66/1.00  --gc_record_bc_elim                     false
% 1.66/1.00  
% 1.66/1.00  ------ Preprocessing Options
% 1.66/1.00  
% 1.66/1.00  --preprocessing_flag                    true
% 1.66/1.00  --time_out_prep_mult                    0.1
% 1.66/1.00  --splitting_mode                        input
% 1.66/1.00  --splitting_grd                         true
% 1.66/1.00  --splitting_cvd                         false
% 1.66/1.00  --splitting_cvd_svl                     false
% 1.66/1.00  --splitting_nvd                         32
% 1.66/1.00  --sub_typing                            true
% 1.66/1.00  --prep_gs_sim                           true
% 1.66/1.00  --prep_unflatten                        true
% 1.66/1.00  --prep_res_sim                          true
% 1.66/1.00  --prep_upred                            true
% 1.66/1.00  --prep_sem_filter                       exhaustive
% 1.66/1.00  --prep_sem_filter_out                   false
% 1.66/1.00  --pred_elim                             true
% 1.66/1.00  --res_sim_input                         true
% 1.66/1.00  --eq_ax_congr_red                       true
% 1.66/1.00  --pure_diseq_elim                       true
% 1.66/1.00  --brand_transform                       false
% 1.66/1.00  --non_eq_to_eq                          false
% 1.66/1.00  --prep_def_merge                        true
% 1.66/1.00  --prep_def_merge_prop_impl              false
% 1.66/1.00  --prep_def_merge_mbd                    true
% 1.66/1.00  --prep_def_merge_tr_red                 false
% 1.66/1.00  --prep_def_merge_tr_cl                  false
% 1.66/1.00  --smt_preprocessing                     true
% 1.66/1.00  --smt_ac_axioms                         fast
% 1.66/1.00  --preprocessed_out                      false
% 1.66/1.00  --preprocessed_stats                    false
% 1.66/1.00  
% 1.66/1.00  ------ Abstraction refinement Options
% 1.66/1.00  
% 1.66/1.00  --abstr_ref                             []
% 1.66/1.00  --abstr_ref_prep                        false
% 1.66/1.00  --abstr_ref_until_sat                   false
% 1.66/1.00  --abstr_ref_sig_restrict                funpre
% 1.66/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.66/1.00  --abstr_ref_under                       []
% 1.66/1.00  
% 1.66/1.00  ------ SAT Options
% 1.66/1.00  
% 1.66/1.00  --sat_mode                              false
% 1.66/1.00  --sat_fm_restart_options                ""
% 1.66/1.00  --sat_gr_def                            false
% 1.66/1.00  --sat_epr_types                         true
% 1.66/1.00  --sat_non_cyclic_types                  false
% 1.66/1.00  --sat_finite_models                     false
% 1.66/1.00  --sat_fm_lemmas                         false
% 1.66/1.00  --sat_fm_prep                           false
% 1.66/1.00  --sat_fm_uc_incr                        true
% 1.66/1.00  --sat_out_model                         small
% 1.66/1.00  --sat_out_clauses                       false
% 1.66/1.00  
% 1.66/1.00  ------ QBF Options
% 1.66/1.00  
% 1.66/1.00  --qbf_mode                              false
% 1.66/1.00  --qbf_elim_univ                         false
% 1.66/1.00  --qbf_dom_inst                          none
% 1.66/1.00  --qbf_dom_pre_inst                      false
% 1.66/1.00  --qbf_sk_in                             false
% 1.66/1.00  --qbf_pred_elim                         true
% 1.66/1.00  --qbf_split                             512
% 1.66/1.00  
% 1.66/1.00  ------ BMC1 Options
% 1.66/1.00  
% 1.66/1.00  --bmc1_incremental                      false
% 1.66/1.00  --bmc1_axioms                           reachable_all
% 1.66/1.00  --bmc1_min_bound                        0
% 1.66/1.00  --bmc1_max_bound                        -1
% 1.66/1.00  --bmc1_max_bound_default                -1
% 1.66/1.00  --bmc1_symbol_reachability              true
% 1.66/1.00  --bmc1_property_lemmas                  false
% 1.66/1.00  --bmc1_k_induction                      false
% 1.66/1.00  --bmc1_non_equiv_states                 false
% 1.66/1.00  --bmc1_deadlock                         false
% 1.66/1.00  --bmc1_ucm                              false
% 1.66/1.00  --bmc1_add_unsat_core                   none
% 1.66/1.00  --bmc1_unsat_core_children              false
% 1.66/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.66/1.00  --bmc1_out_stat                         full
% 1.66/1.00  --bmc1_ground_init                      false
% 1.66/1.00  --bmc1_pre_inst_next_state              false
% 1.66/1.00  --bmc1_pre_inst_state                   false
% 1.66/1.00  --bmc1_pre_inst_reach_state             false
% 1.66/1.00  --bmc1_out_unsat_core                   false
% 1.66/1.00  --bmc1_aig_witness_out                  false
% 1.66/1.00  --bmc1_verbose                          false
% 1.66/1.00  --bmc1_dump_clauses_tptp                false
% 1.66/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.66/1.00  --bmc1_dump_file                        -
% 1.66/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.66/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.66/1.00  --bmc1_ucm_extend_mode                  1
% 1.66/1.00  --bmc1_ucm_init_mode                    2
% 1.66/1.00  --bmc1_ucm_cone_mode                    none
% 1.66/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.66/1.00  --bmc1_ucm_relax_model                  4
% 1.66/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.66/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.66/1.00  --bmc1_ucm_layered_model                none
% 1.66/1.00  --bmc1_ucm_max_lemma_size               10
% 1.66/1.00  
% 1.66/1.00  ------ AIG Options
% 1.66/1.00  
% 1.66/1.00  --aig_mode                              false
% 1.66/1.00  
% 1.66/1.00  ------ Instantiation Options
% 1.66/1.00  
% 1.66/1.00  --instantiation_flag                    true
% 1.66/1.00  --inst_sos_flag                         false
% 1.66/1.00  --inst_sos_phase                        true
% 1.66/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.66/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.66/1.00  --inst_lit_sel_side                     none
% 1.66/1.00  --inst_solver_per_active                1400
% 1.66/1.00  --inst_solver_calls_frac                1.
% 1.66/1.00  --inst_passive_queue_type               priority_queues
% 1.66/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.66/1.00  --inst_passive_queues_freq              [25;2]
% 1.66/1.00  --inst_dismatching                      true
% 1.66/1.00  --inst_eager_unprocessed_to_passive     true
% 1.66/1.00  --inst_prop_sim_given                   true
% 1.66/1.00  --inst_prop_sim_new                     false
% 1.66/1.00  --inst_subs_new                         false
% 1.66/1.00  --inst_eq_res_simp                      false
% 1.66/1.00  --inst_subs_given                       false
% 1.66/1.00  --inst_orphan_elimination               true
% 1.66/1.00  --inst_learning_loop_flag               true
% 1.66/1.00  --inst_learning_start                   3000
% 1.66/1.00  --inst_learning_factor                  2
% 1.66/1.00  --inst_start_prop_sim_after_learn       3
% 1.66/1.00  --inst_sel_renew                        solver
% 1.66/1.00  --inst_lit_activity_flag                true
% 1.66/1.00  --inst_restr_to_given                   false
% 1.66/1.00  --inst_activity_threshold               500
% 1.66/1.00  --inst_out_proof                        true
% 1.66/1.00  
% 1.66/1.00  ------ Resolution Options
% 1.66/1.00  
% 1.66/1.00  --resolution_flag                       false
% 1.66/1.00  --res_lit_sel                           adaptive
% 1.66/1.00  --res_lit_sel_side                      none
% 1.66/1.00  --res_ordering                          kbo
% 1.66/1.00  --res_to_prop_solver                    active
% 1.66/1.00  --res_prop_simpl_new                    false
% 1.66/1.00  --res_prop_simpl_given                  true
% 1.66/1.00  --res_passive_queue_type                priority_queues
% 1.66/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.66/1.00  --res_passive_queues_freq               [15;5]
% 1.66/1.00  --res_forward_subs                      full
% 1.66/1.00  --res_backward_subs                     full
% 1.66/1.00  --res_forward_subs_resolution           true
% 1.66/1.00  --res_backward_subs_resolution          true
% 1.66/1.00  --res_orphan_elimination                true
% 1.66/1.00  --res_time_limit                        2.
% 1.66/1.00  --res_out_proof                         true
% 1.66/1.00  
% 1.66/1.00  ------ Superposition Options
% 1.66/1.00  
% 1.66/1.00  --superposition_flag                    true
% 1.66/1.00  --sup_passive_queue_type                priority_queues
% 1.66/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.66/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.66/1.00  --demod_completeness_check              fast
% 1.66/1.00  --demod_use_ground                      true
% 1.66/1.00  --sup_to_prop_solver                    passive
% 1.66/1.00  --sup_prop_simpl_new                    true
% 1.66/1.00  --sup_prop_simpl_given                  true
% 1.66/1.00  --sup_fun_splitting                     false
% 1.66/1.00  --sup_smt_interval                      50000
% 1.66/1.00  
% 1.66/1.00  ------ Superposition Simplification Setup
% 1.66/1.00  
% 1.66/1.00  --sup_indices_passive                   []
% 1.66/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.66/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.66/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.66/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.66/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.66/1.00  --sup_full_bw                           [BwDemod]
% 1.66/1.00  --sup_immed_triv                        [TrivRules]
% 1.66/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.66/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.66/1.00  --sup_immed_bw_main                     []
% 1.66/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.66/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.66/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.66/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.66/1.00  
% 1.66/1.00  ------ Combination Options
% 1.66/1.00  
% 1.66/1.00  --comb_res_mult                         3
% 1.66/1.00  --comb_sup_mult                         2
% 1.66/1.00  --comb_inst_mult                        10
% 1.66/1.00  
% 1.66/1.00  ------ Debug Options
% 1.66/1.00  
% 1.66/1.00  --dbg_backtrace                         false
% 1.66/1.00  --dbg_dump_prop_clauses                 false
% 1.66/1.00  --dbg_dump_prop_clauses_file            -
% 1.66/1.00  --dbg_out_stat                          false
% 1.66/1.00  
% 1.66/1.00  
% 1.66/1.00  
% 1.66/1.00  
% 1.66/1.00  ------ Proving...
% 1.66/1.00  
% 1.66/1.00  
% 1.66/1.00  % SZS status Theorem for theBenchmark.p
% 1.66/1.00  
% 1.66/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 1.66/1.00  
% 1.66/1.00  fof(f5,axiom,(
% 1.66/1.00    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1)) => (r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1)) & ((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1))))))),
% 1.66/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.66/1.00  
% 1.66/1.00  fof(f14,plain,(
% 1.66/1.00    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1)) => (r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1)) & ((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) => (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X4) => r1_orders_2(X0,X1,X4))) & r2_lattice3(X0,X2,X1))))))),
% 1.66/1.00    inference(rectify,[],[f5])).
% 1.66/1.00  
% 1.66/1.00  fof(f24,plain,(
% 1.66/1.00    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | (? [X3] : ((~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3)) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1))) & ((! [X4] : ((r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | (~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0)))),
% 1.66/1.00    inference(ennf_transformation,[],[f14])).
% 1.66/1.00  
% 1.66/1.00  fof(f25,plain,(
% 1.66/1.00    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | ? [X3] : (~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | ~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 1.66/1.00    inference(flattening,[],[f24])).
% 1.66/1.00  
% 1.66/1.00  fof(f32,plain,(
% 1.66/1.00    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X1,sK0(X0,X1,X2)) & r2_lattice3(X0,X2,sK0(X0,X1,X2)) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 1.66/1.00    introduced(choice_axiom,[])).
% 1.66/1.00  
% 1.66/1.00  fof(f33,plain,(
% 1.66/1.00    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | (~r1_orders_2(X0,X1,sK0(X0,X1,X2)) & r2_lattice3(X0,X2,sK0(X0,X1,X2)) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | ~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 1.66/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f32])).
% 1.66/1.00  
% 1.66/1.00  fof(f44,plain,(
% 1.66/1.00    ( ! [X2,X0,X1] : (k1_yellow_0(X0,X2) = X1 | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) | ~r2_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 1.66/1.00    inference(cnf_transformation,[],[f33])).
% 1.66/1.00  
% 1.66/1.00  fof(f8,axiom,(
% 1.66/1.00    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v4_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 1.66/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.66/1.00  
% 1.66/1.00  fof(f15,plain,(
% 1.66/1.00    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 1.66/1.00    inference(pure_predicate_removal,[],[f8])).
% 1.66/1.00  
% 1.66/1.00  fof(f17,plain,(
% 1.66/1.00    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)))),
% 1.66/1.00    inference(pure_predicate_removal,[],[f15])).
% 1.66/1.00  
% 1.66/1.00  fof(f53,plain,(
% 1.66/1.00    ( ! [X0] : (v5_orders_2(k2_yellow_1(X0))) )),
% 1.66/1.00    inference(cnf_transformation,[],[f17])).
% 1.66/1.00  
% 1.66/1.00  fof(f7,axiom,(
% 1.66/1.00    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 1.66/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.66/1.00  
% 1.66/1.00  fof(f16,plain,(
% 1.66/1.00    ! [X0] : l1_orders_2(k2_yellow_1(X0))),
% 1.66/1.00    inference(pure_predicate_removal,[],[f7])).
% 1.66/1.00  
% 1.66/1.00  fof(f51,plain,(
% 1.66/1.00    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 1.66/1.00    inference(cnf_transformation,[],[f16])).
% 1.66/1.00  
% 1.66/1.00  fof(f10,axiom,(
% 1.66/1.00    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 1.66/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.66/1.00  
% 1.66/1.00  fof(f55,plain,(
% 1.66/1.00    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 1.66/1.00    inference(cnf_transformation,[],[f10])).
% 1.66/1.00  
% 1.66/1.00  fof(f3,axiom,(
% 1.66/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 1.66/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.66/1.00  
% 1.66/1.00  fof(f21,plain,(
% 1.66/1.00    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.66/1.00    inference(ennf_transformation,[],[f3])).
% 1.66/1.00  
% 1.66/1.00  fof(f22,plain,(
% 1.66/1.00    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.66/1.00    inference(flattening,[],[f21])).
% 1.66/1.00  
% 1.66/1.00  fof(f31,plain,(
% 1.66/1.00    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.66/1.00    inference(nnf_transformation,[],[f22])).
% 1.66/1.00  
% 1.66/1.00  fof(f39,plain,(
% 1.66/1.00    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.66/1.00    inference(cnf_transformation,[],[f31])).
% 1.66/1.00  
% 1.66/1.00  fof(f52,plain,(
% 1.66/1.00    ( ! [X0] : (v3_orders_2(k2_yellow_1(X0))) )),
% 1.66/1.00    inference(cnf_transformation,[],[f17])).
% 1.66/1.00  
% 1.66/1.00  fof(f1,axiom,(
% 1.66/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.66/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.66/1.00  
% 1.66/1.00  fof(f37,plain,(
% 1.66/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.66/1.00    inference(cnf_transformation,[],[f1])).
% 1.66/1.00  
% 1.66/1.00  fof(f11,axiom,(
% 1.66/1.00    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)))))),
% 1.66/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.66/1.00  
% 1.66/1.00  fof(f28,plain,(
% 1.66/1.00    ! [X0] : (! [X1] : (! [X2] : ((r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 1.66/1.00    inference(ennf_transformation,[],[f11])).
% 1.66/1.00  
% 1.66/1.00  fof(f34,plain,(
% 1.66/1.00    ! [X0] : (! [X1] : (! [X2] : (((r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2)) & (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 1.66/1.00    inference(nnf_transformation,[],[f28])).
% 1.66/1.00  
% 1.66/1.00  fof(f58,plain,(
% 1.66/1.00    ( ! [X2,X0,X1] : (r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 1.66/1.00    inference(cnf_transformation,[],[f34])).
% 1.66/1.00  
% 1.66/1.00  fof(f12,conjecture,(
% 1.66/1.00    ! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k1_xboole_0,X0) => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))))),
% 1.66/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.66/1.00  
% 1.66/1.00  fof(f13,negated_conjecture,(
% 1.66/1.00    ~! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k1_xboole_0,X0) => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))))),
% 1.66/1.00    inference(negated_conjecture,[],[f12])).
% 1.66/1.00  
% 1.66/1.00  fof(f29,plain,(
% 1.66/1.00    ? [X0] : ((k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0)) & r2_hidden(k1_xboole_0,X0)) & ~v1_xboole_0(X0))),
% 1.66/1.00    inference(ennf_transformation,[],[f13])).
% 1.66/1.00  
% 1.66/1.00  fof(f30,plain,(
% 1.66/1.00    ? [X0] : (k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0)) & r2_hidden(k1_xboole_0,X0) & ~v1_xboole_0(X0))),
% 1.66/1.00    inference(flattening,[],[f29])).
% 1.66/1.00  
% 1.66/1.00  fof(f35,plain,(
% 1.66/1.00    ? [X0] : (k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0)) & r2_hidden(k1_xboole_0,X0) & ~v1_xboole_0(X0)) => (k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK1)) & r2_hidden(k1_xboole_0,sK1) & ~v1_xboole_0(sK1))),
% 1.66/1.00    introduced(choice_axiom,[])).
% 1.66/1.00  
% 1.66/1.00  fof(f36,plain,(
% 1.66/1.00    k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK1)) & r2_hidden(k1_xboole_0,sK1) & ~v1_xboole_0(sK1)),
% 1.66/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f35])).
% 1.66/1.00  
% 1.66/1.00  fof(f59,plain,(
% 1.66/1.00    ~v1_xboole_0(sK1)),
% 1.66/1.00    inference(cnf_transformation,[],[f36])).
% 1.66/1.00  
% 1.66/1.00  fof(f9,axiom,(
% 1.66/1.00    ! [X0] : (~v1_xboole_0(X0) => (v1_orders_2(k2_yellow_1(X0)) & ~v2_struct_0(k2_yellow_1(X0))))),
% 1.66/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.66/1.00  
% 1.66/1.00  fof(f18,plain,(
% 1.66/1.00    ! [X0] : (~v1_xboole_0(X0) => ~v2_struct_0(k2_yellow_1(X0)))),
% 1.66/1.00    inference(pure_predicate_removal,[],[f9])).
% 1.66/1.00  
% 1.66/1.00  fof(f27,plain,(
% 1.66/1.00    ! [X0] : (~v2_struct_0(k2_yellow_1(X0)) | v1_xboole_0(X0))),
% 1.66/1.00    inference(ennf_transformation,[],[f18])).
% 1.66/1.00  
% 1.66/1.00  fof(f54,plain,(
% 1.66/1.00    ( ! [X0] : (~v2_struct_0(k2_yellow_1(X0)) | v1_xboole_0(X0)) )),
% 1.66/1.00    inference(cnf_transformation,[],[f27])).
% 1.66/1.00  
% 1.66/1.00  fof(f2,axiom,(
% 1.66/1.00    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.66/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.66/1.00  
% 1.66/1.00  fof(f20,plain,(
% 1.66/1.00    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.66/1.00    inference(ennf_transformation,[],[f2])).
% 1.66/1.00  
% 1.66/1.00  fof(f38,plain,(
% 1.66/1.00    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 1.66/1.00    inference(cnf_transformation,[],[f20])).
% 1.66/1.00  
% 1.66/1.00  fof(f60,plain,(
% 1.66/1.00    r2_hidden(k1_xboole_0,sK1)),
% 1.66/1.00    inference(cnf_transformation,[],[f36])).
% 1.66/1.00  
% 1.66/1.00  fof(f46,plain,(
% 1.66/1.00    ( ! [X2,X0,X1] : (k1_yellow_0(X0,X2) = X1 | ~r1_orders_2(X0,X1,sK0(X0,X1,X2)) | ~r2_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 1.66/1.00    inference(cnf_transformation,[],[f33])).
% 1.66/1.00  
% 1.66/1.00  fof(f4,axiom,(
% 1.66/1.00    ! [X0] : (l1_orders_2(X0) => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0))),
% 1.66/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.66/1.00  
% 1.66/1.00  fof(f23,plain,(
% 1.66/1.00    ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0))),
% 1.66/1.00    inference(ennf_transformation,[],[f4])).
% 1.66/1.00  
% 1.66/1.00  fof(f41,plain,(
% 1.66/1.00    ( ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0)) )),
% 1.66/1.00    inference(cnf_transformation,[],[f23])).
% 1.66/1.00  
% 1.66/1.00  fof(f6,axiom,(
% 1.66/1.00    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (r1_lattice3(X0,k1_xboole_0,X1) & r2_lattice3(X0,k1_xboole_0,X1))))),
% 1.66/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.66/1.00  
% 1.66/1.00  fof(f19,plain,(
% 1.66/1.00    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r2_lattice3(X0,k1_xboole_0,X1)))),
% 1.66/1.00    inference(pure_predicate_removal,[],[f6])).
% 1.66/1.00  
% 1.66/1.00  fof(f26,plain,(
% 1.66/1.00    ! [X0] : (! [X1] : (r2_lattice3(X0,k1_xboole_0,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.66/1.00    inference(ennf_transformation,[],[f19])).
% 1.66/1.00  
% 1.66/1.00  fof(f50,plain,(
% 1.66/1.00    ( ! [X0,X1] : (r2_lattice3(X0,k1_xboole_0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.66/1.00    inference(cnf_transformation,[],[f26])).
% 1.66/1.00  
% 1.66/1.00  fof(f61,plain,(
% 1.66/1.00    k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK1))),
% 1.66/1.00    inference(cnf_transformation,[],[f36])).
% 1.66/1.00  
% 1.66/1.00  cnf(c_10,plain,
% 1.66/1.00      ( ~ r2_lattice3(X0,X1,X2)
% 1.66/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.66/1.00      | m1_subset_1(sK0(X0,X2,X1),u1_struct_0(X0))
% 1.66/1.00      | ~ v5_orders_2(X0)
% 1.66/1.00      | ~ l1_orders_2(X0)
% 1.66/1.00      | k1_yellow_0(X0,X1) = X2 ),
% 1.66/1.00      inference(cnf_transformation,[],[f44]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_15,plain,
% 1.66/1.00      ( v5_orders_2(k2_yellow_1(X0)) ),
% 1.66/1.00      inference(cnf_transformation,[],[f53]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_577,plain,
% 1.66/1.00      ( ~ r2_lattice3(X0,X1,X2)
% 1.66/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.66/1.00      | m1_subset_1(sK0(X0,X2,X1),u1_struct_0(X0))
% 1.66/1.00      | ~ l1_orders_2(X0)
% 1.66/1.00      | k1_yellow_0(X0,X1) = X2
% 1.66/1.00      | k2_yellow_1(X3) != X0 ),
% 1.66/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_15]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_578,plain,
% 1.66/1.00      ( ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
% 1.66/1.00      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 1.66/1.00      | m1_subset_1(sK0(k2_yellow_1(X0),X2,X1),u1_struct_0(k2_yellow_1(X0)))
% 1.66/1.00      | ~ l1_orders_2(k2_yellow_1(X0))
% 1.66/1.00      | k1_yellow_0(k2_yellow_1(X0),X1) = X2 ),
% 1.66/1.00      inference(unflattening,[status(thm)],[c_577]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_14,plain,
% 1.66/1.00      ( l1_orders_2(k2_yellow_1(X0)) ),
% 1.66/1.00      inference(cnf_transformation,[],[f51]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_582,plain,
% 1.66/1.00      ( m1_subset_1(sK0(k2_yellow_1(X0),X2,X1),u1_struct_0(k2_yellow_1(X0)))
% 1.66/1.00      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 1.66/1.00      | ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
% 1.66/1.00      | k1_yellow_0(k2_yellow_1(X0),X1) = X2 ),
% 1.66/1.00      inference(global_propositional_subsumption,
% 1.66/1.00                [status(thm)],
% 1.66/1.00                [c_578,c_14]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_583,plain,
% 1.66/1.00      ( ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
% 1.66/1.00      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 1.66/1.00      | m1_subset_1(sK0(k2_yellow_1(X0),X2,X1),u1_struct_0(k2_yellow_1(X0)))
% 1.66/1.00      | k1_yellow_0(k2_yellow_1(X0),X1) = X2 ),
% 1.66/1.00      inference(renaming,[status(thm)],[c_582]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_1748,plain,
% 1.66/1.00      ( k1_yellow_0(k2_yellow_1(X0),X1) = X2
% 1.66/1.00      | r2_lattice3(k2_yellow_1(X0),X1,X2) != iProver_top
% 1.66/1.00      | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 1.66/1.00      | m1_subset_1(sK0(k2_yellow_1(X0),X2,X1),u1_struct_0(k2_yellow_1(X0))) = iProver_top ),
% 1.66/1.00      inference(predicate_to_equality,[status(thm)],[c_583]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_19,plain,
% 1.66/1.00      ( u1_struct_0(k2_yellow_1(X0)) = X0 ),
% 1.66/1.00      inference(cnf_transformation,[],[f55]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_1802,plain,
% 1.66/1.00      ( k1_yellow_0(k2_yellow_1(X0),X1) = X2
% 1.66/1.00      | r2_lattice3(k2_yellow_1(X0),X1,X2) != iProver_top
% 1.66/1.00      | m1_subset_1(X2,X0) != iProver_top
% 1.66/1.00      | m1_subset_1(sK0(k2_yellow_1(X0),X2,X1),X0) = iProver_top ),
% 1.66/1.00      inference(light_normalisation,[status(thm)],[c_1748,c_19]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_3,plain,
% 1.66/1.00      ( r1_orders_2(X0,X1,X2)
% 1.66/1.00      | ~ r3_orders_2(X0,X1,X2)
% 1.66/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.66/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.66/1.00      | v2_struct_0(X0)
% 1.66/1.00      | ~ v3_orders_2(X0)
% 1.66/1.00      | ~ l1_orders_2(X0) ),
% 1.66/1.00      inference(cnf_transformation,[],[f39]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_16,plain,
% 1.66/1.00      ( v3_orders_2(k2_yellow_1(X0)) ),
% 1.66/1.00      inference(cnf_transformation,[],[f52]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_347,plain,
% 1.66/1.00      ( r1_orders_2(X0,X1,X2)
% 1.66/1.00      | ~ r3_orders_2(X0,X1,X2)
% 1.66/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.66/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.66/1.00      | v2_struct_0(X0)
% 1.66/1.00      | ~ l1_orders_2(X0)
% 1.66/1.00      | k2_yellow_1(X3) != X0 ),
% 1.66/1.00      inference(resolution_lifted,[status(thm)],[c_3,c_16]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_348,plain,
% 1.66/1.00      ( r1_orders_2(k2_yellow_1(X0),X1,X2)
% 1.66/1.00      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
% 1.66/1.00      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 1.66/1.00      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 1.66/1.00      | v2_struct_0(k2_yellow_1(X0))
% 1.66/1.00      | ~ l1_orders_2(k2_yellow_1(X0)) ),
% 1.66/1.00      inference(unflattening,[status(thm)],[c_347]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_352,plain,
% 1.66/1.00      ( v2_struct_0(k2_yellow_1(X0))
% 1.66/1.00      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 1.66/1.00      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 1.66/1.00      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
% 1.66/1.00      | r1_orders_2(k2_yellow_1(X0),X1,X2) ),
% 1.66/1.00      inference(global_propositional_subsumption,
% 1.66/1.00                [status(thm)],
% 1.66/1.00                [c_348,c_14]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_353,plain,
% 1.66/1.00      ( r1_orders_2(k2_yellow_1(X0),X1,X2)
% 1.66/1.00      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
% 1.66/1.00      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 1.66/1.00      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 1.66/1.00      | v2_struct_0(k2_yellow_1(X0)) ),
% 1.66/1.00      inference(renaming,[status(thm)],[c_352]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_0,plain,
% 1.66/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 1.66/1.00      inference(cnf_transformation,[],[f37]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_20,plain,
% 1.66/1.00      ( r3_orders_2(k2_yellow_1(X0),X1,X2)
% 1.66/1.00      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 1.66/1.00      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 1.66/1.00      | ~ r1_tarski(X1,X2)
% 1.66/1.00      | v1_xboole_0(X0) ),
% 1.66/1.00      inference(cnf_transformation,[],[f58]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_24,negated_conjecture,
% 1.66/1.00      ( ~ v1_xboole_0(sK1) ),
% 1.66/1.00      inference(cnf_transformation,[],[f59]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_290,plain,
% 1.66/1.00      ( r3_orders_2(k2_yellow_1(X0),X1,X2)
% 1.66/1.00      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 1.66/1.00      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 1.66/1.00      | ~ r1_tarski(X1,X2)
% 1.66/1.00      | sK1 != X0 ),
% 1.66/1.00      inference(resolution_lifted,[status(thm)],[c_20,c_24]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_291,plain,
% 1.66/1.00      ( r3_orders_2(k2_yellow_1(sK1),X0,X1)
% 1.66/1.00      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
% 1.66/1.00      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))
% 1.66/1.00      | ~ r1_tarski(X0,X1) ),
% 1.66/1.00      inference(unflattening,[status(thm)],[c_290]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_328,plain,
% 1.66/1.00      ( r3_orders_2(k2_yellow_1(sK1),X0,X1)
% 1.66/1.00      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
% 1.66/1.00      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))
% 1.66/1.00      | X1 != X2
% 1.66/1.00      | k1_xboole_0 != X0 ),
% 1.66/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_291]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_329,plain,
% 1.66/1.00      ( r3_orders_2(k2_yellow_1(sK1),k1_xboole_0,X0)
% 1.66/1.00      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
% 1.66/1.00      | ~ m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK1))) ),
% 1.66/1.00      inference(unflattening,[status(thm)],[c_328]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_464,plain,
% 1.66/1.00      ( r1_orders_2(k2_yellow_1(X0),X1,X2)
% 1.66/1.00      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 1.66/1.00      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 1.66/1.00      | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(sK1)))
% 1.66/1.00      | ~ m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK1)))
% 1.66/1.00      | v2_struct_0(k2_yellow_1(X0))
% 1.66/1.00      | X3 != X2
% 1.66/1.00      | k2_yellow_1(X0) != k2_yellow_1(sK1)
% 1.66/1.00      | k1_xboole_0 != X1 ),
% 1.66/1.00      inference(resolution_lifted,[status(thm)],[c_353,c_329]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_465,plain,
% 1.66/1.00      ( r1_orders_2(k2_yellow_1(X0),k1_xboole_0,X1)
% 1.66/1.00      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 1.66/1.00      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))
% 1.66/1.00      | ~ m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(X0)))
% 1.66/1.00      | ~ m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK1)))
% 1.66/1.00      | v2_struct_0(k2_yellow_1(X0))
% 1.66/1.00      | k2_yellow_1(X0) != k2_yellow_1(sK1) ),
% 1.66/1.00      inference(unflattening,[status(thm)],[c_464]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_17,plain,
% 1.66/1.00      ( v1_xboole_0(X0) | ~ v2_struct_0(k2_yellow_1(X0)) ),
% 1.66/1.00      inference(cnf_transformation,[],[f54]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_308,plain,
% 1.66/1.00      ( ~ v2_struct_0(k2_yellow_1(X0)) | sK1 != X0 ),
% 1.66/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_24]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_309,plain,
% 1.66/1.00      ( ~ v2_struct_0(k2_yellow_1(sK1)) ),
% 1.66/1.00      inference(unflattening,[status(thm)],[c_308]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_499,plain,
% 1.66/1.00      ( r1_orders_2(k2_yellow_1(X0),k1_xboole_0,X1)
% 1.66/1.00      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 1.66/1.00      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))
% 1.66/1.00      | ~ m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(X0)))
% 1.66/1.00      | ~ m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK1)))
% 1.66/1.00      | k2_yellow_1(X0) != k2_yellow_1(sK1) ),
% 1.66/1.00      inference(resolution_lifted,[status(thm)],[c_465,c_309]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_1751,plain,
% 1.66/1.00      ( k2_yellow_1(X0) != k2_yellow_1(sK1)
% 1.66/1.00      | r1_orders_2(k2_yellow_1(X0),k1_xboole_0,X1) = iProver_top
% 1.66/1.00      | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 1.66/1.00      | m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1))) != iProver_top
% 1.66/1.00      | m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 1.66/1.00      | m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK1))) != iProver_top ),
% 1.66/1.00      inference(predicate_to_equality,[status(thm)],[c_499]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_1840,plain,
% 1.66/1.00      ( k2_yellow_1(X0) != k2_yellow_1(sK1)
% 1.66/1.00      | r1_orders_2(k2_yellow_1(X0),k1_xboole_0,X1) = iProver_top
% 1.66/1.00      | m1_subset_1(X1,X0) != iProver_top
% 1.66/1.00      | m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1))) != iProver_top
% 1.66/1.00      | m1_subset_1(k1_xboole_0,X0) != iProver_top
% 1.66/1.00      | m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK1))) != iProver_top ),
% 1.66/1.00      inference(light_normalisation,[status(thm)],[c_1751,c_19]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_1841,plain,
% 1.66/1.00      ( k2_yellow_1(X0) != k2_yellow_1(sK1)
% 1.66/1.00      | r1_orders_2(k2_yellow_1(X0),k1_xboole_0,X1) = iProver_top
% 1.66/1.00      | m1_subset_1(X1,X0) != iProver_top
% 1.66/1.00      | m1_subset_1(X1,sK1) != iProver_top
% 1.66/1.00      | m1_subset_1(k1_xboole_0,X0) != iProver_top
% 1.66/1.00      | m1_subset_1(k1_xboole_0,sK1) != iProver_top ),
% 1.66/1.00      inference(demodulation,[status(thm)],[c_1840,c_19]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_1,plain,
% 1.66/1.00      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 1.66/1.00      inference(cnf_transformation,[],[f38]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_23,negated_conjecture,
% 1.66/1.00      ( r2_hidden(k1_xboole_0,sK1) ),
% 1.66/1.00      inference(cnf_transformation,[],[f60]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_265,plain,
% 1.66/1.00      ( m1_subset_1(X0,X1) | sK1 != X1 | k1_xboole_0 != X0 ),
% 1.66/1.00      inference(resolution_lifted,[status(thm)],[c_1,c_23]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_266,plain,
% 1.66/1.00      ( m1_subset_1(k1_xboole_0,sK1) ),
% 1.66/1.00      inference(unflattening,[status(thm)],[c_265]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_1752,plain,
% 1.66/1.00      ( m1_subset_1(k1_xboole_0,sK1) = iProver_top ),
% 1.66/1.00      inference(predicate_to_equality,[status(thm)],[c_266]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_1848,plain,
% 1.66/1.00      ( k2_yellow_1(X0) != k2_yellow_1(sK1)
% 1.66/1.00      | r1_orders_2(k2_yellow_1(X0),k1_xboole_0,X1) = iProver_top
% 1.66/1.00      | m1_subset_1(X1,X0) != iProver_top
% 1.66/1.00      | m1_subset_1(X1,sK1) != iProver_top
% 1.66/1.00      | m1_subset_1(k1_xboole_0,X0) != iProver_top ),
% 1.66/1.00      inference(forward_subsumption_resolution,
% 1.66/1.00                [status(thm)],
% 1.66/1.00                [c_1841,c_1752]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_1916,plain,
% 1.66/1.00      ( r1_orders_2(k2_yellow_1(sK1),k1_xboole_0,X0) = iProver_top
% 1.66/1.00      | m1_subset_1(X0,sK1) != iProver_top
% 1.66/1.00      | m1_subset_1(k1_xboole_0,sK1) != iProver_top ),
% 1.66/1.00      inference(equality_resolution,[status(thm)],[c_1848]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_267,plain,
% 1.66/1.00      ( m1_subset_1(k1_xboole_0,sK1) = iProver_top ),
% 1.66/1.00      inference(predicate_to_equality,[status(thm)],[c_266]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_1921,plain,
% 1.66/1.00      ( m1_subset_1(X0,sK1) != iProver_top
% 1.66/1.00      | r1_orders_2(k2_yellow_1(sK1),k1_xboole_0,X0) = iProver_top ),
% 1.66/1.00      inference(global_propositional_subsumption,
% 1.66/1.00                [status(thm)],
% 1.66/1.00                [c_1916,c_267]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_1922,plain,
% 1.66/1.00      ( r1_orders_2(k2_yellow_1(sK1),k1_xboole_0,X0) = iProver_top
% 1.66/1.00      | m1_subset_1(X0,sK1) != iProver_top ),
% 1.66/1.00      inference(renaming,[status(thm)],[c_1921]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_8,plain,
% 1.66/1.00      ( ~ r2_lattice3(X0,X1,X2)
% 1.66/1.00      | ~ r1_orders_2(X0,X2,sK0(X0,X2,X1))
% 1.66/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.66/1.00      | ~ v5_orders_2(X0)
% 1.66/1.00      | ~ l1_orders_2(X0)
% 1.66/1.00      | k1_yellow_0(X0,X1) = X2 ),
% 1.66/1.00      inference(cnf_transformation,[],[f46]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_625,plain,
% 1.66/1.00      ( ~ r2_lattice3(X0,X1,X2)
% 1.66/1.00      | ~ r1_orders_2(X0,X2,sK0(X0,X2,X1))
% 1.66/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.66/1.00      | ~ l1_orders_2(X0)
% 1.66/1.00      | k1_yellow_0(X0,X1) = X2
% 1.66/1.00      | k2_yellow_1(X3) != X0 ),
% 1.66/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_15]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_626,plain,
% 1.66/1.00      ( ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
% 1.66/1.00      | ~ r1_orders_2(k2_yellow_1(X0),X2,sK0(k2_yellow_1(X0),X2,X1))
% 1.66/1.00      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 1.66/1.00      | ~ l1_orders_2(k2_yellow_1(X0))
% 1.66/1.00      | k1_yellow_0(k2_yellow_1(X0),X1) = X2 ),
% 1.66/1.00      inference(unflattening,[status(thm)],[c_625]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_630,plain,
% 1.66/1.00      ( ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 1.66/1.00      | ~ r1_orders_2(k2_yellow_1(X0),X2,sK0(k2_yellow_1(X0),X2,X1))
% 1.66/1.00      | ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
% 1.66/1.00      | k1_yellow_0(k2_yellow_1(X0),X1) = X2 ),
% 1.66/1.00      inference(global_propositional_subsumption,
% 1.66/1.00                [status(thm)],
% 1.66/1.00                [c_626,c_14]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_631,plain,
% 1.66/1.00      ( ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
% 1.66/1.00      | ~ r1_orders_2(k2_yellow_1(X0),X2,sK0(k2_yellow_1(X0),X2,X1))
% 1.66/1.00      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 1.66/1.00      | k1_yellow_0(k2_yellow_1(X0),X1) = X2 ),
% 1.66/1.00      inference(renaming,[status(thm)],[c_630]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_1746,plain,
% 1.66/1.00      ( k1_yellow_0(k2_yellow_1(X0),X1) = X2
% 1.66/1.00      | r2_lattice3(k2_yellow_1(X0),X1,X2) != iProver_top
% 1.66/1.00      | r1_orders_2(k2_yellow_1(X0),X2,sK0(k2_yellow_1(X0),X2,X1)) != iProver_top
% 1.66/1.00      | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top ),
% 1.66/1.00      inference(predicate_to_equality,[status(thm)],[c_631]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_1820,plain,
% 1.66/1.00      ( k1_yellow_0(k2_yellow_1(X0),X1) = X2
% 1.66/1.00      | r2_lattice3(k2_yellow_1(X0),X1,X2) != iProver_top
% 1.66/1.00      | r1_orders_2(k2_yellow_1(X0),X2,sK0(k2_yellow_1(X0),X2,X1)) != iProver_top
% 1.66/1.00      | m1_subset_1(X2,X0) != iProver_top ),
% 1.66/1.00      inference(light_normalisation,[status(thm)],[c_1746,c_19]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_2458,plain,
% 1.66/1.00      ( k1_yellow_0(k2_yellow_1(sK1),X0) = k1_xboole_0
% 1.66/1.00      | r2_lattice3(k2_yellow_1(sK1),X0,k1_xboole_0) != iProver_top
% 1.66/1.00      | m1_subset_1(sK0(k2_yellow_1(sK1),k1_xboole_0,X0),sK1) != iProver_top
% 1.66/1.00      | m1_subset_1(k1_xboole_0,sK1) != iProver_top ),
% 1.66/1.00      inference(superposition,[status(thm)],[c_1922,c_1820]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_2518,plain,
% 1.66/1.00      ( m1_subset_1(sK0(k2_yellow_1(sK1),k1_xboole_0,X0),sK1) != iProver_top
% 1.66/1.00      | r2_lattice3(k2_yellow_1(sK1),X0,k1_xboole_0) != iProver_top
% 1.66/1.00      | k1_yellow_0(k2_yellow_1(sK1),X0) = k1_xboole_0 ),
% 1.66/1.00      inference(global_propositional_subsumption,
% 1.66/1.00                [status(thm)],
% 1.66/1.00                [c_2458,c_267]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_2519,plain,
% 1.66/1.00      ( k1_yellow_0(k2_yellow_1(sK1),X0) = k1_xboole_0
% 1.66/1.00      | r2_lattice3(k2_yellow_1(sK1),X0,k1_xboole_0) != iProver_top
% 1.66/1.00      | m1_subset_1(sK0(k2_yellow_1(sK1),k1_xboole_0,X0),sK1) != iProver_top ),
% 1.66/1.00      inference(renaming,[status(thm)],[c_2518]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_2527,plain,
% 1.66/1.00      ( k1_yellow_0(k2_yellow_1(sK1),X0) = k1_xboole_0
% 1.66/1.00      | r2_lattice3(k2_yellow_1(sK1),X0,k1_xboole_0) != iProver_top
% 1.66/1.00      | m1_subset_1(k1_xboole_0,sK1) != iProver_top ),
% 1.66/1.00      inference(superposition,[status(thm)],[c_1802,c_2519]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_2536,plain,
% 1.66/1.00      ( k1_yellow_0(k2_yellow_1(sK1),k1_xboole_0) = k1_xboole_0
% 1.66/1.00      | r2_lattice3(k2_yellow_1(sK1),k1_xboole_0,k1_xboole_0) != iProver_top
% 1.66/1.00      | m1_subset_1(k1_xboole_0,sK1) != iProver_top ),
% 1.66/1.00      inference(instantiation,[status(thm)],[c_2527]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_1511,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_2398,plain,
% 1.66/1.00      ( k1_yellow_0(k2_yellow_1(sK1),k1_xboole_0) != X0
% 1.66/1.00      | k1_xboole_0 != X0
% 1.66/1.00      | k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK1),k1_xboole_0) ),
% 1.66/1.00      inference(instantiation,[status(thm)],[c_1511]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_2399,plain,
% 1.66/1.00      ( k1_yellow_0(k2_yellow_1(sK1),k1_xboole_0) != k1_xboole_0
% 1.66/1.00      | k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK1),k1_xboole_0)
% 1.66/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 1.66/1.00      inference(instantiation,[status(thm)],[c_2398]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_1903,plain,
% 1.66/1.00      ( k3_yellow_0(k2_yellow_1(sK1)) != X0
% 1.66/1.00      | k1_xboole_0 != X0
% 1.66/1.00      | k1_xboole_0 = k3_yellow_0(k2_yellow_1(sK1)) ),
% 1.66/1.00      inference(instantiation,[status(thm)],[c_1511]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_2210,plain,
% 1.66/1.00      ( k3_yellow_0(k2_yellow_1(sK1)) != k1_yellow_0(k2_yellow_1(sK1),k1_xboole_0)
% 1.66/1.00      | k1_xboole_0 != k1_yellow_0(k2_yellow_1(sK1),k1_xboole_0)
% 1.66/1.00      | k1_xboole_0 = k3_yellow_0(k2_yellow_1(sK1)) ),
% 1.66/1.00      inference(instantiation,[status(thm)],[c_1903]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_4,plain,
% 1.66/1.00      ( ~ l1_orders_2(X0)
% 1.66/1.00      | k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0) ),
% 1.66/1.00      inference(cnf_transformation,[],[f41]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_773,plain,
% 1.66/1.00      ( k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0)
% 1.66/1.00      | k2_yellow_1(X1) != X0 ),
% 1.66/1.00      inference(resolution_lifted,[status(thm)],[c_4,c_14]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_774,plain,
% 1.66/1.00      ( k1_yellow_0(k2_yellow_1(X0),k1_xboole_0) = k3_yellow_0(k2_yellow_1(X0)) ),
% 1.66/1.00      inference(unflattening,[status(thm)],[c_773]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_2059,plain,
% 1.66/1.00      ( k1_yellow_0(k2_yellow_1(sK1),k1_xboole_0) = k3_yellow_0(k2_yellow_1(sK1)) ),
% 1.66/1.00      inference(instantiation,[status(thm)],[c_774]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_1928,plain,
% 1.66/1.00      ( X0 != X1
% 1.66/1.00      | k3_yellow_0(k2_yellow_1(sK1)) != X1
% 1.66/1.00      | k3_yellow_0(k2_yellow_1(sK1)) = X0 ),
% 1.66/1.00      inference(instantiation,[status(thm)],[c_1511]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_1956,plain,
% 1.66/1.00      ( X0 != k3_yellow_0(k2_yellow_1(sK1))
% 1.66/1.00      | k3_yellow_0(k2_yellow_1(sK1)) = X0
% 1.66/1.00      | k3_yellow_0(k2_yellow_1(sK1)) != k3_yellow_0(k2_yellow_1(sK1)) ),
% 1.66/1.00      inference(instantiation,[status(thm)],[c_1928]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_2058,plain,
% 1.66/1.00      ( k1_yellow_0(k2_yellow_1(sK1),k1_xboole_0) != k3_yellow_0(k2_yellow_1(sK1))
% 1.66/1.00      | k3_yellow_0(k2_yellow_1(sK1)) = k1_yellow_0(k2_yellow_1(sK1),k1_xboole_0)
% 1.66/1.00      | k3_yellow_0(k2_yellow_1(sK1)) != k3_yellow_0(k2_yellow_1(sK1)) ),
% 1.66/1.00      inference(instantiation,[status(thm)],[c_1956]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_13,plain,
% 1.66/1.00      ( r2_lattice3(X0,k1_xboole_0,X1)
% 1.66/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.66/1.00      | ~ l1_orders_2(X0) ),
% 1.66/1.00      inference(cnf_transformation,[],[f50]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_761,plain,
% 1.66/1.00      ( r2_lattice3(X0,k1_xboole_0,X1)
% 1.66/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.66/1.00      | k2_yellow_1(X2) != X0 ),
% 1.66/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_14]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_762,plain,
% 1.66/1.00      ( r2_lattice3(k2_yellow_1(X0),k1_xboole_0,X1)
% 1.66/1.00      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) ),
% 1.66/1.00      inference(unflattening,[status(thm)],[c_761]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_1993,plain,
% 1.66/1.00      ( r2_lattice3(k2_yellow_1(sK1),k1_xboole_0,X0)
% 1.66/1.00      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1))) ),
% 1.66/1.00      inference(instantiation,[status(thm)],[c_762]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_1994,plain,
% 1.66/1.00      ( r2_lattice3(k2_yellow_1(sK1),k1_xboole_0,X0) = iProver_top
% 1.66/1.00      | m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1))) != iProver_top ),
% 1.66/1.00      inference(predicate_to_equality,[status(thm)],[c_1993]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_1996,plain,
% 1.66/1.00      ( r2_lattice3(k2_yellow_1(sK1),k1_xboole_0,k1_xboole_0) = iProver_top
% 1.66/1.00      | m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK1))) != iProver_top ),
% 1.66/1.00      inference(instantiation,[status(thm)],[c_1994]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_1510,plain,( X0 = X0 ),theory(equality) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_1950,plain,
% 1.66/1.00      ( k2_yellow_1(sK1) = k2_yellow_1(sK1) ),
% 1.66/1.00      inference(instantiation,[status(thm)],[c_1510]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_1515,plain,
% 1.66/1.00      ( X0 != X1 | k3_yellow_0(X0) = k3_yellow_0(X1) ),
% 1.66/1.00      theory(equality) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_1930,plain,
% 1.66/1.00      ( k2_yellow_1(sK1) != X0
% 1.66/1.00      | k3_yellow_0(k2_yellow_1(sK1)) = k3_yellow_0(X0) ),
% 1.66/1.00      inference(instantiation,[status(thm)],[c_1515]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_1949,plain,
% 1.66/1.00      ( k2_yellow_1(sK1) != k2_yellow_1(sK1)
% 1.66/1.00      | k3_yellow_0(k2_yellow_1(sK1)) = k3_yellow_0(k2_yellow_1(sK1)) ),
% 1.66/1.00      inference(instantiation,[status(thm)],[c_1930]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_1934,plain,
% 1.66/1.00      ( u1_struct_0(k2_yellow_1(sK1)) = sK1 ),
% 1.66/1.00      inference(instantiation,[status(thm)],[c_19]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_1512,plain,
% 1.66/1.00      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 1.66/1.00      theory(equality) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_1905,plain,
% 1.66/1.00      ( m1_subset_1(X0,X1)
% 1.66/1.00      | ~ m1_subset_1(k1_xboole_0,sK1)
% 1.66/1.00      | X1 != sK1
% 1.66/1.00      | X0 != k1_xboole_0 ),
% 1.66/1.00      inference(instantiation,[status(thm)],[c_1512]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_1933,plain,
% 1.66/1.00      ( m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
% 1.66/1.00      | ~ m1_subset_1(k1_xboole_0,sK1)
% 1.66/1.00      | X0 != k1_xboole_0
% 1.66/1.00      | u1_struct_0(k2_yellow_1(sK1)) != sK1 ),
% 1.66/1.00      inference(instantiation,[status(thm)],[c_1905]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_1935,plain,
% 1.66/1.00      ( X0 != k1_xboole_0
% 1.66/1.00      | u1_struct_0(k2_yellow_1(sK1)) != sK1
% 1.66/1.00      | m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1))) = iProver_top
% 1.66/1.00      | m1_subset_1(k1_xboole_0,sK1) != iProver_top ),
% 1.66/1.00      inference(predicate_to_equality,[status(thm)],[c_1933]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_1937,plain,
% 1.66/1.00      ( u1_struct_0(k2_yellow_1(sK1)) != sK1
% 1.66/1.00      | k1_xboole_0 != k1_xboole_0
% 1.66/1.00      | m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK1))) = iProver_top
% 1.66/1.00      | m1_subset_1(k1_xboole_0,sK1) != iProver_top ),
% 1.66/1.00      inference(instantiation,[status(thm)],[c_1935]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_1533,plain,
% 1.66/1.00      ( k1_xboole_0 = k1_xboole_0 ),
% 1.66/1.00      inference(instantiation,[status(thm)],[c_1510]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_22,negated_conjecture,
% 1.66/1.00      ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK1)) ),
% 1.66/1.00      inference(cnf_transformation,[],[f61]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(contradiction,plain,
% 1.66/1.00      ( $false ),
% 1.66/1.00      inference(minisat,
% 1.66/1.00                [status(thm)],
% 1.66/1.00                [c_2536,c_2399,c_2210,c_2059,c_2058,c_1996,c_1950,c_1949,
% 1.66/1.00                 c_1934,c_1937,c_1533,c_267,c_22]) ).
% 1.66/1.00  
% 1.66/1.00  
% 1.66/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 1.66/1.00  
% 1.66/1.00  ------                               Statistics
% 1.66/1.00  
% 1.66/1.00  ------ General
% 1.66/1.00  
% 1.66/1.00  abstr_ref_over_cycles:                  0
% 1.66/1.00  abstr_ref_under_cycles:                 0
% 1.66/1.00  gc_basic_clause_elim:                   0
% 1.66/1.00  forced_gc_time:                         0
% 1.66/1.00  parsing_time:                           0.008
% 1.66/1.00  unif_index_cands_time:                  0.
% 1.66/1.00  unif_index_add_time:                    0.
% 1.66/1.00  orderings_time:                         0.
% 1.66/1.00  out_proof_time:                         0.008
% 1.66/1.00  total_time:                             0.142
% 1.66/1.00  num_of_symbols:                         52
% 1.66/1.00  num_of_terms:                           1616
% 1.66/1.00  
% 1.66/1.00  ------ Preprocessing
% 1.66/1.00  
% 1.66/1.00  num_of_splits:                          0
% 1.66/1.00  num_of_split_atoms:                     0
% 1.66/1.00  num_of_reused_defs:                     0
% 1.66/1.00  num_eq_ax_congr_red:                    20
% 1.66/1.00  num_of_sem_filtered_clauses:            1
% 1.66/1.00  num_of_subtypes:                        0
% 1.66/1.00  monotx_restored_types:                  0
% 1.66/1.00  sat_num_of_epr_types:                   0
% 1.66/1.00  sat_num_of_non_cyclic_types:            0
% 1.66/1.00  sat_guarded_non_collapsed_types:        0
% 1.66/1.00  num_pure_diseq_elim:                    0
% 1.66/1.00  simp_replaced_by:                       0
% 1.66/1.00  res_preprocessed:                       95
% 1.66/1.00  prep_upred:                             0
% 1.66/1.00  prep_unflattend:                        37
% 1.66/1.00  smt_new_axioms:                         0
% 1.66/1.00  pred_elim_cands:                        4
% 1.66/1.00  pred_elim:                              8
% 1.66/1.00  pred_elim_cl:                           10
% 1.66/1.00  pred_elim_cycles:                       13
% 1.66/1.00  merged_defs:                            0
% 1.66/1.00  merged_defs_ncl:                        0
% 1.66/1.00  bin_hyper_res:                          0
% 1.66/1.00  prep_cycles:                            4
% 1.66/1.00  pred_elim_time:                         0.036
% 1.66/1.00  splitting_time:                         0.
% 1.66/1.00  sem_filter_time:                        0.
% 1.66/1.00  monotx_time:                            0.001
% 1.66/1.00  subtype_inf_time:                       0.
% 1.66/1.00  
% 1.66/1.00  ------ Problem properties
% 1.66/1.00  
% 1.66/1.00  clauses:                                15
% 1.66/1.00  conjectures:                            1
% 1.66/1.00  epr:                                    1
% 1.66/1.00  horn:                                   11
% 1.66/1.00  ground:                                 2
% 1.66/1.00  unary:                                  5
% 1.66/1.00  binary:                                 1
% 1.66/1.00  lits:                                   45
% 1.66/1.00  lits_eq:                                8
% 1.66/1.00  fd_pure:                                0
% 1.66/1.00  fd_pseudo:                              0
% 1.66/1.00  fd_cond:                                0
% 1.66/1.00  fd_pseudo_cond:                         3
% 1.66/1.00  ac_symbols:                             0
% 1.66/1.00  
% 1.66/1.00  ------ Propositional Solver
% 1.66/1.00  
% 1.66/1.00  prop_solver_calls:                      27
% 1.66/1.00  prop_fast_solver_calls:                 927
% 1.66/1.00  smt_solver_calls:                       0
% 1.66/1.00  smt_fast_solver_calls:                  0
% 1.66/1.00  prop_num_of_clauses:                    602
% 1.66/1.00  prop_preprocess_simplified:             3035
% 1.66/1.00  prop_fo_subsumed:                       15
% 1.66/1.00  prop_solver_time:                       0.
% 1.66/1.00  smt_solver_time:                        0.
% 1.66/1.00  smt_fast_solver_time:                   0.
% 1.66/1.00  prop_fast_solver_time:                  0.
% 1.66/1.00  prop_unsat_core_time:                   0.
% 1.66/1.00  
% 1.66/1.00  ------ QBF
% 1.66/1.00  
% 1.66/1.00  qbf_q_res:                              0
% 1.66/1.00  qbf_num_tautologies:                    0
% 1.66/1.00  qbf_prep_cycles:                        0
% 1.66/1.00  
% 1.66/1.00  ------ BMC1
% 1.66/1.00  
% 1.66/1.00  bmc1_current_bound:                     -1
% 1.66/1.00  bmc1_last_solved_bound:                 -1
% 1.66/1.00  bmc1_unsat_core_size:                   -1
% 1.66/1.00  bmc1_unsat_core_parents_size:           -1
% 1.66/1.00  bmc1_merge_next_fun:                    0
% 1.66/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.66/1.00  
% 1.66/1.00  ------ Instantiation
% 1.66/1.00  
% 1.66/1.00  inst_num_of_clauses:                    149
% 1.66/1.00  inst_num_in_passive:                    20
% 1.66/1.00  inst_num_in_active:                     94
% 1.66/1.00  inst_num_in_unprocessed:                35
% 1.66/1.00  inst_num_of_loops:                      100
% 1.66/1.00  inst_num_of_learning_restarts:          0
% 1.66/1.00  inst_num_moves_active_passive:          3
% 1.66/1.00  inst_lit_activity:                      0
% 1.66/1.00  inst_lit_activity_moves:                0
% 1.66/1.00  inst_num_tautologies:                   0
% 1.66/1.00  inst_num_prop_implied:                  0
% 1.66/1.00  inst_num_existing_simplified:           0
% 1.66/1.00  inst_num_eq_res_simplified:             0
% 1.66/1.00  inst_num_child_elim:                    0
% 1.66/1.00  inst_num_of_dismatching_blockings:      17
% 1.66/1.00  inst_num_of_non_proper_insts:           106
% 1.66/1.00  inst_num_of_duplicates:                 0
% 1.66/1.00  inst_inst_num_from_inst_to_res:         0
% 1.66/1.00  inst_dismatching_checking_time:         0.
% 1.66/1.00  
% 1.66/1.00  ------ Resolution
% 1.66/1.00  
% 1.66/1.00  res_num_of_clauses:                     0
% 1.66/1.00  res_num_in_passive:                     0
% 1.66/1.00  res_num_in_active:                      0
% 1.66/1.00  res_num_of_loops:                       99
% 1.66/1.00  res_forward_subset_subsumed:            24
% 1.66/1.00  res_backward_subset_subsumed:           0
% 1.66/1.00  res_forward_subsumed:                   0
% 1.66/1.00  res_backward_subsumed:                  0
% 1.66/1.00  res_forward_subsumption_resolution:     0
% 1.66/1.00  res_backward_subsumption_resolution:    0
% 1.66/1.00  res_clause_to_clause_subsumption:       74
% 1.66/1.00  res_orphan_elimination:                 0
% 1.66/1.00  res_tautology_del:                      11
% 1.66/1.00  res_num_eq_res_simplified:              0
% 1.66/1.00  res_num_sel_changes:                    0
% 1.66/1.00  res_moves_from_active_to_pass:          0
% 1.66/1.00  
% 1.66/1.00  ------ Superposition
% 1.66/1.00  
% 1.66/1.00  sup_time_total:                         0.
% 1.66/1.00  sup_time_generating:                    0.
% 1.66/1.00  sup_time_sim_full:                      0.
% 1.66/1.00  sup_time_sim_immed:                     0.
% 1.66/1.00  
% 1.66/1.00  sup_num_of_clauses:                     20
% 1.66/1.00  sup_num_in_active:                      18
% 1.66/1.00  sup_num_in_passive:                     2
% 1.66/1.00  sup_num_of_loops:                       18
% 1.66/1.00  sup_fw_superposition:                   8
% 1.66/1.00  sup_bw_superposition:                   0
% 1.66/1.00  sup_immediate_simplified:               2
% 1.66/1.00  sup_given_eliminated:                   0
% 1.66/1.00  comparisons_done:                       0
% 1.66/1.00  comparisons_avoided:                    0
% 1.66/1.00  
% 1.66/1.00  ------ Simplifications
% 1.66/1.00  
% 1.66/1.00  
% 1.66/1.00  sim_fw_subset_subsumed:                 1
% 1.66/1.00  sim_bw_subset_subsumed:                 1
% 1.66/1.00  sim_fw_subsumed:                        1
% 1.66/1.00  sim_bw_subsumed:                        0
% 1.66/1.00  sim_fw_subsumption_res:                 1
% 1.66/1.00  sim_bw_subsumption_res:                 0
% 1.66/1.00  sim_tautology_del:                      0
% 1.66/1.00  sim_eq_tautology_del:                   0
% 1.66/1.00  sim_eq_res_simp:                        0
% 1.66/1.00  sim_fw_demodulated:                     1
% 1.66/1.00  sim_bw_demodulated:                     0
% 1.66/1.00  sim_light_normalised:                   11
% 1.66/1.00  sim_joinable_taut:                      0
% 1.66/1.00  sim_joinable_simp:                      0
% 1.66/1.00  sim_ac_normalised:                      0
% 1.66/1.00  sim_smt_subsumption:                    0
% 1.66/1.00  
%------------------------------------------------------------------------------
