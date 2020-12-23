%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1573+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:55 EST 2020

% Result     : Theorem 1.25s
% Output     : CNFRefutation 1.25s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 355 expanded)
%              Number of clauses        :   65 ( 115 expanded)
%              Number of leaves         :    9 (  85 expanded)
%              Depth                    :   16
%              Number of atoms          :  391 (1838 expanded)
%              Number of equality atoms :  127 ( 379 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   11 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( ( r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
             => r1_lattice3(X0,X1,X2) )
            & ( r1_lattice3(X0,X1,X2)
             => r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2) )
            & ( r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
             => r2_lattice3(X0,X1,X2) )
            & ( r2_lattice3(X0,X1,X2)
             => r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ~ r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2) )
            & ( r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
              | ~ r1_lattice3(X0,X1,X2) )
            & ( r2_lattice3(X0,X1,X2)
              | ~ r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2) )
            & ( r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ~ r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2) )
            & ( r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
              | ~ r1_lattice3(X0,X1,X2) )
            & ( r2_lattice3(X0,X1,X2)
              | ~ r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2) )
            & ( r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
            | r1_yellow_0(X0,X1) )
         => k1_yellow_0(X0,X1) = k1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
              | r1_yellow_0(X0,X1) )
           => k1_yellow_0(X0,X1) = k1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_yellow_0(X0,X1) != k1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
          & ( r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
            | r1_yellow_0(X0,X1) ) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_yellow_0(X0,X1) != k1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
          & ( r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
            | r1_yellow_0(X0,X1) ) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f17,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k1_yellow_0(X0,X1) != k1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
          & ( r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
            | r1_yellow_0(X0,X1) ) )
     => ( k1_yellow_0(X0,sK2) != k1_yellow_0(X0,k3_xboole_0(sK2,u1_struct_0(X0)))
        & ( r1_yellow_0(X0,k3_xboole_0(sK2,u1_struct_0(X0)))
          | r1_yellow_0(X0,sK2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k1_yellow_0(X0,X1) != k1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
            & ( r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
              | r1_yellow_0(X0,X1) ) )
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k1_yellow_0(sK1,X1) != k1_yellow_0(sK1,k3_xboole_0(X1,u1_struct_0(sK1)))
          & ( r1_yellow_0(sK1,k3_xboole_0(X1,u1_struct_0(sK1)))
            | r1_yellow_0(sK1,X1) ) )
      & l1_orders_2(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( k1_yellow_0(sK1,sK2) != k1_yellow_0(sK1,k3_xboole_0(sK2,u1_struct_0(sK1)))
    & ( r1_yellow_0(sK1,k3_xboole_0(sK2,u1_struct_0(sK1)))
      | r1_yellow_0(sK1,sK2) )
    & l1_orders_2(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f11,f17,f16])).

fof(f28,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f27,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( ( ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_lattice3(X0,X1,X3)
                <=> r2_lattice3(X0,X2,X3) ) )
            & r1_yellow_0(X0,X1) )
         => k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2)
          | ? [X3] :
              ( ( r2_lattice3(X0,X1,X3)
              <~> r2_lattice3(X0,X2,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r1_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2)
          | ? [X3] :
              ( ( r2_lattice3(X0,X1,X3)
              <~> r2_lattice3(X0,X2,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r1_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f6])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2)
          | ? [X3] :
              ( ( ~ r2_lattice3(X0,X2,X3)
                | ~ r2_lattice3(X0,X1,X3) )
              & ( r2_lattice3(X0,X2,X3)
                | r2_lattice3(X0,X1,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r1_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2)
          | ? [X3] :
              ( ( ~ r2_lattice3(X0,X2,X3)
                | ~ r2_lattice3(X0,X1,X3) )
              & ( r2_lattice3(X0,X2,X3)
                | r2_lattice3(X0,X1,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r1_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f14,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_lattice3(X0,X2,X3)
            | ~ r2_lattice3(X0,X1,X3) )
          & ( r2_lattice3(X0,X2,X3)
            | r2_lattice3(X0,X1,X3) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ( ~ r2_lattice3(X0,X2,sK0(X0,X1,X2))
          | ~ r2_lattice3(X0,X1,sK0(X0,X1,X2)) )
        & ( r2_lattice3(X0,X2,sK0(X0,X1,X2))
          | r2_lattice3(X0,X1,sK0(X0,X1,X2)) )
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2)
          | ( ( ~ r2_lattice3(X0,X2,sK0(X0,X1,X2))
              | ~ r2_lattice3(X0,X1,sK0(X0,X1,X2)) )
            & ( r2_lattice3(X0,X2,sK0(X0,X1,X2))
              | r2_lattice3(X0,X1,sK0(X0,X1,X2)) )
            & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) )
          | ~ r1_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f14])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2)
      | r2_lattice3(X0,X2,sK0(X0,X1,X2))
      | r2_lattice3(X0,X1,sK0(X0,X1,X2))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | ~ r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2)
      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2)
      | ~ r2_lattice3(X0,X2,sK0(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,sK0(X0,X1,X2))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f30,plain,(
    k1_yellow_0(sK1,sK2) != k1_yellow_0(sK1,k3_xboole_0(sK2,u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f18])).

fof(f29,plain,
    ( r1_yellow_0(sK1,k3_xboole_0(sK2,u1_struct_0(sK1)))
    | r1_yellow_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_7,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_10,negated_conjecture,
    ( l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_198,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_10])).

cnf(c_199,plain,
    ( ~ r2_lattice3(sK1,X0,X1)
    | r2_lattice3(sK1,k3_xboole_0(X0,u1_struct_0(sK1)),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | v2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_198])).

cnf(c_11,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_203,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK1))
    | r2_lattice3(sK1,k3_xboole_0(X0,u1_struct_0(sK1)),X1)
    | ~ r2_lattice3(sK1,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_199,c_11])).

cnf(c_204,plain,
    ( ~ r2_lattice3(sK1,X0,X1)
    | r2_lattice3(sK1,k3_xboole_0(X0,u1_struct_0(sK1)),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_203])).

cnf(c_462,plain,
    ( ~ r2_lattice3(sK1,X0_41,X0_42)
    | r2_lattice3(sK1,k3_xboole_0(X0_41,u1_struct_0(sK1)),X0_42)
    | ~ m1_subset_1(X0_42,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_204])).

cnf(c_917,plain,
    ( ~ r2_lattice3(sK1,X0_41,sK0(sK1,X1_41,k3_xboole_0(sK2,u1_struct_0(sK1))))
    | r2_lattice3(sK1,k3_xboole_0(X0_41,u1_struct_0(sK1)),sK0(sK1,X1_41,k3_xboole_0(sK2,u1_struct_0(sK1))))
    | ~ m1_subset_1(sK0(sK1,X1_41,k3_xboole_0(sK2,u1_struct_0(sK1))),u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_462])).

cnf(c_923,plain,
    ( r2_lattice3(sK1,X0_41,sK0(sK1,X1_41,k3_xboole_0(sK2,u1_struct_0(sK1)))) != iProver_top
    | r2_lattice3(sK1,k3_xboole_0(X0_41,u1_struct_0(sK1)),sK0(sK1,X1_41,k3_xboole_0(sK2,u1_struct_0(sK1)))) = iProver_top
    | m1_subset_1(sK0(sK1,X1_41,k3_xboole_0(sK2,u1_struct_0(sK1))),u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_917])).

cnf(c_925,plain,
    ( r2_lattice3(sK1,k3_xboole_0(sK2,u1_struct_0(sK1)),sK0(sK1,sK2,k3_xboole_0(sK2,u1_struct_0(sK1)))) = iProver_top
    | r2_lattice3(sK1,sK2,sK0(sK1,sK2,k3_xboole_0(sK2,u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,k3_xboole_0(sK2,u1_struct_0(sK1))),u1_struct_0(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_923])).

cnf(c_2,plain,
    ( r2_lattice3(X0,X1,sK0(X0,X2,X1))
    | r2_lattice3(X0,X2,sK0(X0,X2,X1))
    | ~ r1_yellow_0(X0,X2)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_261,plain,
    ( r2_lattice3(X0,X1,sK0(X0,X2,X1))
    | r2_lattice3(X0,X2,sK0(X0,X2,X1))
    | ~ r1_yellow_0(X0,X2)
    | v2_struct_0(X0)
    | k1_yellow_0(X0,X2) = k1_yellow_0(X0,X1)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_10])).

cnf(c_262,plain,
    ( r2_lattice3(sK1,X0,sK0(sK1,X0,X1))
    | r2_lattice3(sK1,X1,sK0(sK1,X0,X1))
    | ~ r1_yellow_0(sK1,X0)
    | v2_struct_0(sK1)
    | k1_yellow_0(sK1,X0) = k1_yellow_0(sK1,X1) ),
    inference(unflattening,[status(thm)],[c_261])).

cnf(c_266,plain,
    ( ~ r1_yellow_0(sK1,X0)
    | r2_lattice3(sK1,X1,sK0(sK1,X0,X1))
    | r2_lattice3(sK1,X0,sK0(sK1,X0,X1))
    | k1_yellow_0(sK1,X0) = k1_yellow_0(sK1,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_262,c_11])).

cnf(c_267,plain,
    ( r2_lattice3(sK1,X0,sK0(sK1,X0,X1))
    | r2_lattice3(sK1,X1,sK0(sK1,X0,X1))
    | ~ r1_yellow_0(sK1,X0)
    | k1_yellow_0(sK1,X0) = k1_yellow_0(sK1,X1) ),
    inference(renaming,[status(thm)],[c_266])).

cnf(c_459,plain,
    ( r2_lattice3(sK1,X0_41,sK0(sK1,X0_41,X1_41))
    | r2_lattice3(sK1,X1_41,sK0(sK1,X0_41,X1_41))
    | ~ r1_yellow_0(sK1,X0_41)
    | k1_yellow_0(sK1,X0_41) = k1_yellow_0(sK1,X1_41) ),
    inference(subtyping,[status(esa)],[c_267])).

cnf(c_626,plain,
    ( k1_yellow_0(sK1,X0_41) = k1_yellow_0(sK1,X1_41)
    | r2_lattice3(sK1,X0_41,sK0(sK1,X0_41,X1_41)) = iProver_top
    | r2_lattice3(sK1,X1_41,sK0(sK1,X0_41,X1_41)) = iProver_top
    | r1_yellow_0(sK1,X0_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_459])).

cnf(c_6,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_219,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_10])).

cnf(c_220,plain,
    ( r2_lattice3(sK1,X0,X1)
    | ~ r2_lattice3(sK1,k3_xboole_0(X0,u1_struct_0(sK1)),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | v2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_219])).

cnf(c_224,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ r2_lattice3(sK1,k3_xboole_0(X0,u1_struct_0(sK1)),X1)
    | r2_lattice3(sK1,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_220,c_11])).

cnf(c_225,plain,
    ( r2_lattice3(sK1,X0,X1)
    | ~ r2_lattice3(sK1,k3_xboole_0(X0,u1_struct_0(sK1)),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_224])).

cnf(c_461,plain,
    ( r2_lattice3(sK1,X0_41,X0_42)
    | ~ r2_lattice3(sK1,k3_xboole_0(X0_41,u1_struct_0(sK1)),X0_42)
    | ~ m1_subset_1(X0_42,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_225])).

cnf(c_624,plain,
    ( r2_lattice3(sK1,X0_41,X0_42) = iProver_top
    | r2_lattice3(sK1,k3_xboole_0(X0_41,u1_struct_0(sK1)),X0_42) != iProver_top
    | m1_subset_1(X0_42,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_461])).

cnf(c_855,plain,
    ( k1_yellow_0(sK1,k3_xboole_0(X0_41,u1_struct_0(sK1))) = k1_yellow_0(sK1,X1_41)
    | r2_lattice3(sK1,X0_41,sK0(sK1,k3_xboole_0(X0_41,u1_struct_0(sK1)),X1_41)) = iProver_top
    | r2_lattice3(sK1,X1_41,sK0(sK1,k3_xboole_0(X0_41,u1_struct_0(sK1)),X1_41)) = iProver_top
    | m1_subset_1(sK0(sK1,k3_xboole_0(X0_41,u1_struct_0(sK1)),X1_41),u1_struct_0(sK1)) != iProver_top
    | r1_yellow_0(sK1,k3_xboole_0(X0_41,u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_626,c_624])).

cnf(c_882,plain,
    ( k1_yellow_0(sK1,k3_xboole_0(sK2,u1_struct_0(sK1))) = k1_yellow_0(sK1,sK2)
    | r2_lattice3(sK1,sK2,sK0(sK1,k3_xboole_0(sK2,u1_struct_0(sK1)),sK2)) = iProver_top
    | m1_subset_1(sK0(sK1,k3_xboole_0(sK2,u1_struct_0(sK1)),sK2),u1_struct_0(sK1)) != iProver_top
    | r1_yellow_0(sK1,k3_xboole_0(sK2,u1_struct_0(sK1))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_855])).

cnf(c_853,plain,
    ( k1_yellow_0(sK1,k3_xboole_0(X0_41,u1_struct_0(sK1))) = k1_yellow_0(sK1,X1_41)
    | r2_lattice3(sK1,X1_41,sK0(sK1,X1_41,k3_xboole_0(X0_41,u1_struct_0(sK1)))) = iProver_top
    | r2_lattice3(sK1,X0_41,sK0(sK1,X1_41,k3_xboole_0(X0_41,u1_struct_0(sK1)))) = iProver_top
    | m1_subset_1(sK0(sK1,X1_41,k3_xboole_0(X0_41,u1_struct_0(sK1))),u1_struct_0(sK1)) != iProver_top
    | r1_yellow_0(sK1,X1_41) != iProver_top ),
    inference(superposition,[status(thm)],[c_626,c_624])).

cnf(c_879,plain,
    ( k1_yellow_0(sK1,k3_xboole_0(sK2,u1_struct_0(sK1))) = k1_yellow_0(sK1,sK2)
    | r2_lattice3(sK1,sK2,sK0(sK1,sK2,k3_xboole_0(sK2,u1_struct_0(sK1)))) = iProver_top
    | m1_subset_1(sK0(sK1,sK2,k3_xboole_0(sK2,u1_struct_0(sK1))),u1_struct_0(sK1)) != iProver_top
    | r1_yellow_0(sK1,sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_853])).

cnf(c_3,plain,
    ( m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | ~ r1_yellow_0(X0,X1)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X2) = k1_yellow_0(X0,X1) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_240,plain,
    ( m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | ~ r1_yellow_0(X0,X1)
    | v2_struct_0(X0)
    | k1_yellow_0(X0,X2) = k1_yellow_0(X0,X1)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_10])).

cnf(c_241,plain,
    ( m1_subset_1(sK0(sK1,X0,X1),u1_struct_0(sK1))
    | ~ r1_yellow_0(sK1,X0)
    | v2_struct_0(sK1)
    | k1_yellow_0(sK1,X1) = k1_yellow_0(sK1,X0) ),
    inference(unflattening,[status(thm)],[c_240])).

cnf(c_245,plain,
    ( ~ r1_yellow_0(sK1,X0)
    | m1_subset_1(sK0(sK1,X0,X1),u1_struct_0(sK1))
    | k1_yellow_0(sK1,X1) = k1_yellow_0(sK1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_241,c_11])).

cnf(c_246,plain,
    ( m1_subset_1(sK0(sK1,X0,X1),u1_struct_0(sK1))
    | ~ r1_yellow_0(sK1,X0)
    | k1_yellow_0(sK1,X1) = k1_yellow_0(sK1,X0) ),
    inference(renaming,[status(thm)],[c_245])).

cnf(c_460,plain,
    ( m1_subset_1(sK0(sK1,X0_41,X1_41),u1_struct_0(sK1))
    | ~ r1_yellow_0(sK1,X0_41)
    | k1_yellow_0(sK1,X1_41) = k1_yellow_0(sK1,X0_41) ),
    inference(subtyping,[status(esa)],[c_246])).

cnf(c_813,plain,
    ( m1_subset_1(sK0(sK1,X0_41,k3_xboole_0(sK2,u1_struct_0(sK1))),u1_struct_0(sK1))
    | ~ r1_yellow_0(sK1,X0_41)
    | k1_yellow_0(sK1,k3_xboole_0(sK2,u1_struct_0(sK1))) = k1_yellow_0(sK1,X0_41) ),
    inference(instantiation,[status(thm)],[c_460])).

cnf(c_814,plain,
    ( k1_yellow_0(sK1,k3_xboole_0(sK2,u1_struct_0(sK1))) = k1_yellow_0(sK1,X0_41)
    | m1_subset_1(sK0(sK1,X0_41,k3_xboole_0(sK2,u1_struct_0(sK1))),u1_struct_0(sK1)) = iProver_top
    | r1_yellow_0(sK1,X0_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_813])).

cnf(c_816,plain,
    ( k1_yellow_0(sK1,k3_xboole_0(sK2,u1_struct_0(sK1))) = k1_yellow_0(sK1,sK2)
    | m1_subset_1(sK0(sK1,sK2,k3_xboole_0(sK2,u1_struct_0(sK1))),u1_struct_0(sK1)) = iProver_top
    | r1_yellow_0(sK1,sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_814])).

cnf(c_623,plain,
    ( r2_lattice3(sK1,X0_41,X0_42) != iProver_top
    | r2_lattice3(sK1,k3_xboole_0(X0_41,u1_struct_0(sK1)),X0_42) = iProver_top
    | m1_subset_1(X0_42,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_462])).

cnf(c_1,plain,
    ( ~ r2_lattice3(X0,X1,sK0(X0,X2,X1))
    | ~ r2_lattice3(X0,X2,sK0(X0,X2,X1))
    | ~ r1_yellow_0(X0,X2)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_285,plain,
    ( ~ r2_lattice3(X0,X1,sK0(X0,X2,X1))
    | ~ r2_lattice3(X0,X2,sK0(X0,X2,X1))
    | ~ r1_yellow_0(X0,X2)
    | v2_struct_0(X0)
    | k1_yellow_0(X0,X2) = k1_yellow_0(X0,X1)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_10])).

cnf(c_286,plain,
    ( ~ r2_lattice3(sK1,X0,sK0(sK1,X0,X1))
    | ~ r2_lattice3(sK1,X1,sK0(sK1,X0,X1))
    | ~ r1_yellow_0(sK1,X0)
    | v2_struct_0(sK1)
    | k1_yellow_0(sK1,X0) = k1_yellow_0(sK1,X1) ),
    inference(unflattening,[status(thm)],[c_285])).

cnf(c_290,plain,
    ( ~ r1_yellow_0(sK1,X0)
    | ~ r2_lattice3(sK1,X1,sK0(sK1,X0,X1))
    | ~ r2_lattice3(sK1,X0,sK0(sK1,X0,X1))
    | k1_yellow_0(sK1,X0) = k1_yellow_0(sK1,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_286,c_11])).

cnf(c_291,plain,
    ( ~ r2_lattice3(sK1,X0,sK0(sK1,X0,X1))
    | ~ r2_lattice3(sK1,X1,sK0(sK1,X0,X1))
    | ~ r1_yellow_0(sK1,X0)
    | k1_yellow_0(sK1,X0) = k1_yellow_0(sK1,X1) ),
    inference(renaming,[status(thm)],[c_290])).

cnf(c_458,plain,
    ( ~ r2_lattice3(sK1,X0_41,sK0(sK1,X0_41,X1_41))
    | ~ r2_lattice3(sK1,X1_41,sK0(sK1,X0_41,X1_41))
    | ~ r1_yellow_0(sK1,X0_41)
    | k1_yellow_0(sK1,X0_41) = k1_yellow_0(sK1,X1_41) ),
    inference(subtyping,[status(esa)],[c_291])).

cnf(c_627,plain,
    ( k1_yellow_0(sK1,X0_41) = k1_yellow_0(sK1,X1_41)
    | r2_lattice3(sK1,X0_41,sK0(sK1,X0_41,X1_41)) != iProver_top
    | r2_lattice3(sK1,X1_41,sK0(sK1,X0_41,X1_41)) != iProver_top
    | r1_yellow_0(sK1,X0_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_458])).

cnf(c_786,plain,
    ( k1_yellow_0(sK1,k3_xboole_0(X0_41,u1_struct_0(sK1))) = k1_yellow_0(sK1,X1_41)
    | r2_lattice3(sK1,X0_41,sK0(sK1,k3_xboole_0(X0_41,u1_struct_0(sK1)),X1_41)) != iProver_top
    | r2_lattice3(sK1,X1_41,sK0(sK1,k3_xboole_0(X0_41,u1_struct_0(sK1)),X1_41)) != iProver_top
    | m1_subset_1(sK0(sK1,k3_xboole_0(X0_41,u1_struct_0(sK1)),X1_41),u1_struct_0(sK1)) != iProver_top
    | r1_yellow_0(sK1,k3_xboole_0(X0_41,u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_623,c_627])).

cnf(c_788,plain,
    ( k1_yellow_0(sK1,k3_xboole_0(sK2,u1_struct_0(sK1))) = k1_yellow_0(sK1,sK2)
    | r2_lattice3(sK1,sK2,sK0(sK1,k3_xboole_0(sK2,u1_struct_0(sK1)),sK2)) != iProver_top
    | m1_subset_1(sK0(sK1,k3_xboole_0(sK2,u1_struct_0(sK1)),sK2),u1_struct_0(sK1)) != iProver_top
    | r1_yellow_0(sK1,k3_xboole_0(sK2,u1_struct_0(sK1))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_786])).

cnf(c_471,plain,
    ( X0_43 != X1_43
    | X2_43 != X1_43
    | X2_43 = X0_43 ),
    theory(equality)).

cnf(c_698,plain,
    ( k1_yellow_0(sK1,k3_xboole_0(sK2,u1_struct_0(sK1))) != X0_43
    | k1_yellow_0(sK1,sK2) != X0_43
    | k1_yellow_0(sK1,sK2) = k1_yellow_0(sK1,k3_xboole_0(sK2,u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_471])).

cnf(c_738,plain,
    ( k1_yellow_0(sK1,k3_xboole_0(sK2,u1_struct_0(sK1))) != k1_yellow_0(sK1,X0_41)
    | k1_yellow_0(sK1,sK2) != k1_yellow_0(sK1,X0_41)
    | k1_yellow_0(sK1,sK2) = k1_yellow_0(sK1,k3_xboole_0(sK2,u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_698])).

cnf(c_741,plain,
    ( k1_yellow_0(sK1,k3_xboole_0(sK2,u1_struct_0(sK1))) != k1_yellow_0(sK1,sK2)
    | k1_yellow_0(sK1,sK2) = k1_yellow_0(sK1,k3_xboole_0(sK2,u1_struct_0(sK1)))
    | k1_yellow_0(sK1,sK2) != k1_yellow_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_738])).

cnf(c_688,plain,
    ( ~ r2_lattice3(sK1,k3_xboole_0(sK2,u1_struct_0(sK1)),sK0(sK1,sK2,k3_xboole_0(sK2,u1_struct_0(sK1))))
    | ~ r2_lattice3(sK1,sK2,sK0(sK1,sK2,k3_xboole_0(sK2,u1_struct_0(sK1))))
    | ~ r1_yellow_0(sK1,sK2)
    | k1_yellow_0(sK1,sK2) = k1_yellow_0(sK1,k3_xboole_0(sK2,u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_458])).

cnf(c_689,plain,
    ( k1_yellow_0(sK1,sK2) = k1_yellow_0(sK1,k3_xboole_0(sK2,u1_struct_0(sK1)))
    | r2_lattice3(sK1,k3_xboole_0(sK2,u1_struct_0(sK1)),sK0(sK1,sK2,k3_xboole_0(sK2,u1_struct_0(sK1)))) != iProver_top
    | r2_lattice3(sK1,sK2,sK0(sK1,sK2,k3_xboole_0(sK2,u1_struct_0(sK1)))) != iProver_top
    | r1_yellow_0(sK1,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_688])).

cnf(c_685,plain,
    ( m1_subset_1(sK0(sK1,k3_xboole_0(sK2,u1_struct_0(sK1)),sK2),u1_struct_0(sK1))
    | ~ r1_yellow_0(sK1,k3_xboole_0(sK2,u1_struct_0(sK1)))
    | k1_yellow_0(sK1,sK2) = k1_yellow_0(sK1,k3_xboole_0(sK2,u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_460])).

cnf(c_686,plain,
    ( k1_yellow_0(sK1,sK2) = k1_yellow_0(sK1,k3_xboole_0(sK2,u1_struct_0(sK1)))
    | m1_subset_1(sK0(sK1,k3_xboole_0(sK2,u1_struct_0(sK1)),sK2),u1_struct_0(sK1)) = iProver_top
    | r1_yellow_0(sK1,k3_xboole_0(sK2,u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_685])).

cnf(c_8,negated_conjecture,
    ( k1_yellow_0(sK1,sK2) != k1_yellow_0(sK1,k3_xboole_0(sK2,u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_464,negated_conjecture,
    ( k1_yellow_0(sK1,sK2) != k1_yellow_0(sK1,k3_xboole_0(sK2,u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_467,plain,
    ( X0_41 = X0_41 ),
    theory(equality)).

cnf(c_483,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_467])).

cnf(c_473,plain,
    ( k1_yellow_0(X0_40,X0_41) = k1_yellow_0(X0_40,X1_41)
    | X0_41 != X1_41 ),
    theory(equality)).

cnf(c_478,plain,
    ( k1_yellow_0(sK1,sK2) = k1_yellow_0(sK1,sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_473])).

cnf(c_9,negated_conjecture,
    ( r1_yellow_0(sK1,k3_xboole_0(sK2,u1_struct_0(sK1)))
    | r1_yellow_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_14,plain,
    ( r1_yellow_0(sK1,k3_xboole_0(sK2,u1_struct_0(sK1))) = iProver_top
    | r1_yellow_0(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_925,c_882,c_879,c_816,c_788,c_741,c_689,c_686,c_464,c_483,c_478,c_14])).


%------------------------------------------------------------------------------
