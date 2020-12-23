%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1498+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:44 EST 2020

% Result     : Theorem 0.94s
% Output     : CNFRefutation 0.94s
% Verified   : 
% Statistics : Number of formulae       :  106 (1087 expanded)
%              Number of clauses        :   73 ( 262 expanded)
%              Number of leaves         :   11 ( 253 expanded)
%              Depth                    :   19
%              Number of atoms          :  386 (6687 expanded)
%              Number of equality atoms :   91 ( 239 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,conjecture,(
    ! [X0,X1] :
      ( ( l3_lattices(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(k3_lattice3(X1)))
         => ( r2_lattice3(k3_lattice3(X1),X0,X2)
          <=> r4_lattice3(X1,k5_lattice3(X1,X2),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( l3_lattices(X1)
          & v10_lattices(X1)
          & ~ v2_struct_0(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(k3_lattice3(X1)))
           => ( r2_lattice3(k3_lattice3(X1),X0,X2)
            <=> r4_lattice3(X1,k5_lattice3(X1,X2),X0) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r2_lattice3(k3_lattice3(X1),X0,X2)
          <~> r4_lattice3(X1,k5_lattice3(X1,X2),X0) )
          & m1_subset_1(X2,u1_struct_0(k3_lattice3(X1))) )
      & l3_lattices(X1)
      & v10_lattices(X1)
      & ~ v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r2_lattice3(k3_lattice3(X1),X0,X2)
          <~> r4_lattice3(X1,k5_lattice3(X1,X2),X0) )
          & m1_subset_1(X2,u1_struct_0(k3_lattice3(X1))) )
      & l3_lattices(X1)
      & v10_lattices(X1)
      & ~ v2_struct_0(X1) ) ),
    inference(flattening,[],[f15])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r4_lattice3(X1,k5_lattice3(X1,X2),X0)
            | ~ r2_lattice3(k3_lattice3(X1),X0,X2) )
          & ( r4_lattice3(X1,k5_lattice3(X1,X2),X0)
            | r2_lattice3(k3_lattice3(X1),X0,X2) )
          & m1_subset_1(X2,u1_struct_0(k3_lattice3(X1))) )
      & l3_lattices(X1)
      & v10_lattices(X1)
      & ~ v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r4_lattice3(X1,k5_lattice3(X1,X2),X0)
            | ~ r2_lattice3(k3_lattice3(X1),X0,X2) )
          & ( r4_lattice3(X1,k5_lattice3(X1,X2),X0)
            | r2_lattice3(k3_lattice3(X1),X0,X2) )
          & m1_subset_1(X2,u1_struct_0(k3_lattice3(X1))) )
      & l3_lattices(X1)
      & v10_lattices(X1)
      & ~ v2_struct_0(X1) ) ),
    inference(flattening,[],[f18])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ r4_lattice3(X1,k5_lattice3(X1,X2),X0)
            | ~ r2_lattice3(k3_lattice3(X1),X0,X2) )
          & ( r4_lattice3(X1,k5_lattice3(X1,X2),X0)
            | r2_lattice3(k3_lattice3(X1),X0,X2) )
          & m1_subset_1(X2,u1_struct_0(k3_lattice3(X1))) )
     => ( ( ~ r4_lattice3(X1,k5_lattice3(X1,sK2),X0)
          | ~ r2_lattice3(k3_lattice3(X1),X0,sK2) )
        & ( r4_lattice3(X1,k5_lattice3(X1,sK2),X0)
          | r2_lattice3(k3_lattice3(X1),X0,sK2) )
        & m1_subset_1(sK2,u1_struct_0(k3_lattice3(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r4_lattice3(X1,k5_lattice3(X1,X2),X0)
              | ~ r2_lattice3(k3_lattice3(X1),X0,X2) )
            & ( r4_lattice3(X1,k5_lattice3(X1,X2),X0)
              | r2_lattice3(k3_lattice3(X1),X0,X2) )
            & m1_subset_1(X2,u1_struct_0(k3_lattice3(X1))) )
        & l3_lattices(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ( ~ r4_lattice3(sK1,k5_lattice3(sK1,X2),sK0)
            | ~ r2_lattice3(k3_lattice3(sK1),sK0,X2) )
          & ( r4_lattice3(sK1,k5_lattice3(sK1,X2),sK0)
            | r2_lattice3(k3_lattice3(sK1),sK0,X2) )
          & m1_subset_1(X2,u1_struct_0(k3_lattice3(sK1))) )
      & l3_lattices(sK1)
      & v10_lattices(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ( ~ r4_lattice3(sK1,k5_lattice3(sK1,sK2),sK0)
      | ~ r2_lattice3(k3_lattice3(sK1),sK0,sK2) )
    & ( r4_lattice3(sK1,k5_lattice3(sK1,sK2),sK0)
      | r2_lattice3(k3_lattice3(sK1),sK0,sK2) )
    & m1_subset_1(sK2,u1_struct_0(k3_lattice3(sK1)))
    & l3_lattices(sK1)
    & v10_lattices(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f21,f20])).

fof(f32,plain,
    ( r4_lattice3(sK1,k5_lattice3(sK1,sK2),sK0)
    | r2_lattice3(k3_lattice3(sK1),sK0,sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( r4_lattice3(X1,X2,X0)
          <=> r2_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r4_lattice3(X1,X2,X0)
          <=> r2_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2)) )
          | ~ m1_subset_1(X2,u1_struct_0(X1)) )
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r4_lattice3(X1,X2,X0)
          <=> r2_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2)) )
          | ~ m1_subset_1(X2,u1_struct_0(X1)) )
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f13])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r4_lattice3(X1,X2,X0)
              | ~ r2_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2)) )
            & ( r2_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2))
              | ~ r4_lattice3(X1,X2,X0) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X1)) )
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2))
      | ~ r4_lattice3(X1,X2,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f30,plain,(
    l3_lattices(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f28,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f29,plain,(
    v10_lattices(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f31,plain,(
    m1_subset_1(sK2,u1_struct_0(k3_lattice3(sK1))) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(k3_lattice3(X0)))
        & l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_lattice3(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(X0)))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_lattice3(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(X0)))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_lattice3(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(X0)))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k3_lattice3(X0)))
         => k5_lattice3(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_lattice3(X0,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(X0))) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_lattice3(X0,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(X0))) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k5_lattice3(X0,X1) = X1
      | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(X0)))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k4_lattice3(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattice3(X0,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattice3(X0,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k4_lattice3(X0,X1) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f33,plain,
    ( ~ r4_lattice3(sK1,k5_lattice3(sK1,sK2),sK0)
    | ~ r2_lattice3(k3_lattice3(sK1),sK0,sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X1,X2,X0)
      | ~ r2_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_6,negated_conjecture,
    ( r2_lattice3(k3_lattice3(sK1),sK0,sK2)
    | r4_lattice3(sK1,k5_lattice3(sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_80,plain,
    ( r2_lattice3(k3_lattice3(sK1),sK0,sK2)
    | r4_lattice3(sK1,k5_lattice3(sK1,sK2),sK0) ),
    inference(prop_impl,[status(thm)],[c_6])).

cnf(c_4,plain,
    ( r2_lattice3(k3_lattice3(X0),X1,k4_lattice3(X0,X2))
    | ~ r4_lattice3(X0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_8,negated_conjecture,
    ( l3_lattices(sK1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_153,plain,
    ( r2_lattice3(k3_lattice3(X0),X1,k4_lattice3(X0,X2))
    | ~ r4_lattice3(X0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_8])).

cnf(c_154,plain,
    ( r2_lattice3(k3_lattice3(sK1),X0,k4_lattice3(sK1,X1))
    | ~ r4_lattice3(sK1,X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1) ),
    inference(unflattening,[status(thm)],[c_153])).

cnf(c_10,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_9,negated_conjecture,
    ( v10_lattices(sK1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_158,plain,
    ( r2_lattice3(k3_lattice3(sK1),X0,k4_lattice3(sK1,X1))
    | ~ r4_lattice3(sK1,X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_154,c_10,c_9])).

cnf(c_268,plain,
    ( r2_lattice3(k3_lattice3(sK1),X0,k4_lattice3(sK1,X1))
    | r2_lattice3(k3_lattice3(sK1),sK0,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | k5_lattice3(sK1,sK2) != X1
    | sK0 != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_80,c_158])).

cnf(c_269,plain,
    ( r2_lattice3(k3_lattice3(sK1),sK0,k4_lattice3(sK1,k5_lattice3(sK1,sK2)))
    | r2_lattice3(k3_lattice3(sK1),sK0,sK2)
    | ~ m1_subset_1(k5_lattice3(sK1,sK2),u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_268])).

cnf(c_351,plain,
    ( r2_lattice3(k3_lattice3(sK1),sK0,k4_lattice3(sK1,k5_lattice3(sK1,sK2)))
    | r2_lattice3(k3_lattice3(sK1),sK0,sK2)
    | ~ m1_subset_1(k5_lattice3(sK1,sK2),u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_269])).

cnf(c_562,plain,
    ( r2_lattice3(k3_lattice3(sK1),sK0,k4_lattice3(sK1,k5_lattice3(sK1,sK2))) = iProver_top
    | r2_lattice3(k3_lattice3(sK1),sK0,sK2) = iProver_top
    | m1_subset_1(k5_lattice3(sK1,sK2),u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_351])).

cnf(c_7,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(k3_lattice3(sK1))) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_14,plain,
    ( m1_subset_1(sK2,u1_struct_0(k3_lattice3(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_270,plain,
    ( r2_lattice3(k3_lattice3(sK1),sK0,k4_lattice3(sK1,k5_lattice3(sK1,sK2))) = iProver_top
    | r2_lattice3(k3_lattice3(sK1),sK0,sK2) = iProver_top
    | m1_subset_1(k5_lattice3(sK1,sK2),u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_269])).

cnf(c_357,plain,
    ( X0_43 = X0_43 ),
    theory(equality)).

cnf(c_368,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_357])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(X1)))
    | m1_subset_1(k5_lattice3(X1,X0),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_195,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(X1)))
    | m1_subset_1(k5_lattice3(X1,X0),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_8])).

cnf(c_196,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(sK1)))
    | m1_subset_1(k5_lattice3(sK1,X0),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1) ),
    inference(unflattening,[status(thm)],[c_195])).

cnf(c_200,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(sK1)))
    | m1_subset_1(k5_lattice3(sK1,X0),u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_196,c_10,c_9])).

cnf(c_354,plain,
    ( ~ m1_subset_1(X0_43,u1_struct_0(k3_lattice3(sK1)))
    | m1_subset_1(k5_lattice3(sK1,X0_43),u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_200])).

cnf(c_371,plain,
    ( m1_subset_1(k5_lattice3(sK1,sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(k3_lattice3(sK1))) ),
    inference(instantiation,[status(thm)],[c_354])).

cnf(c_370,plain,
    ( m1_subset_1(X0_43,u1_struct_0(k3_lattice3(sK1))) != iProver_top
    | m1_subset_1(k5_lattice3(sK1,X0_43),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_354])).

cnf(c_372,plain,
    ( m1_subset_1(k5_lattice3(sK1,sK2),u1_struct_0(sK1)) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(k3_lattice3(sK1))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_370])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(X1)))
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | k5_lattice3(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_213,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(X1)))
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k5_lattice3(X1,X0) = X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_8])).

cnf(c_214,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(sK1)))
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | k5_lattice3(sK1,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_213])).

cnf(c_218,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(sK1)))
    | k5_lattice3(sK1,X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_214,c_10,c_9])).

cnf(c_353,plain,
    ( ~ m1_subset_1(X0_43,u1_struct_0(k3_lattice3(sK1)))
    | k5_lattice3(sK1,X0_43) = X0_43 ),
    inference(subtyping,[status(esa)],[c_218])).

cnf(c_374,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(k3_lattice3(sK1)))
    | k5_lattice3(sK1,sK2) = sK2 ),
    inference(instantiation,[status(thm)],[c_353])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | k4_lattice3(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_231,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k4_lattice3(X1,X0) = X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_8])).

cnf(c_232,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | k4_lattice3(sK1,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_231])).

cnf(c_236,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | k4_lattice3(sK1,X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_232,c_10,c_9])).

cnf(c_352,plain,
    ( ~ m1_subset_1(X0_43,u1_struct_0(sK1))
    | k4_lattice3(sK1,X0_43) = X0_43 ),
    inference(subtyping,[status(esa)],[c_236])).

cnf(c_604,plain,
    ( ~ m1_subset_1(k5_lattice3(sK1,X0_43),u1_struct_0(sK1))
    | k4_lattice3(sK1,k5_lattice3(sK1,X0_43)) = k5_lattice3(sK1,X0_43) ),
    inference(instantiation,[status(thm)],[c_352])).

cnf(c_606,plain,
    ( ~ m1_subset_1(k5_lattice3(sK1,sK2),u1_struct_0(sK1))
    | k4_lattice3(sK1,k5_lattice3(sK1,sK2)) = k5_lattice3(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_604])).

cnf(c_358,plain,
    ( X0_43 != X1_43
    | X2_43 != X1_43
    | X2_43 = X0_43 ),
    theory(equality)).

cnf(c_639,plain,
    ( X0_43 != X1_43
    | X0_43 = k5_lattice3(sK1,X2_43)
    | k5_lattice3(sK1,X2_43) != X1_43 ),
    inference(instantiation,[status(thm)],[c_358])).

cnf(c_640,plain,
    ( k5_lattice3(sK1,sK2) != sK2
    | sK2 = k5_lattice3(sK1,sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_639])).

cnf(c_362,plain,
    ( ~ r2_lattice3(X0_41,X0_42,X0_43)
    | r2_lattice3(X0_41,X0_42,X1_43)
    | X1_43 != X0_43 ),
    theory(equality)).

cnf(c_617,plain,
    ( r2_lattice3(k3_lattice3(sK1),sK0,X0_43)
    | ~ r2_lattice3(k3_lattice3(sK1),sK0,sK2)
    | X0_43 != sK2 ),
    inference(instantiation,[status(thm)],[c_362])).

cnf(c_650,plain,
    ( r2_lattice3(k3_lattice3(sK1),sK0,k4_lattice3(sK1,k5_lattice3(sK1,sK2)))
    | ~ r2_lattice3(k3_lattice3(sK1),sK0,sK2)
    | k4_lattice3(sK1,k5_lattice3(sK1,sK2)) != sK2 ),
    inference(instantiation,[status(thm)],[c_617])).

cnf(c_651,plain,
    ( k4_lattice3(sK1,k5_lattice3(sK1,sK2)) != sK2
    | r2_lattice3(k3_lattice3(sK1),sK0,k4_lattice3(sK1,k5_lattice3(sK1,sK2))) = iProver_top
    | r2_lattice3(k3_lattice3(sK1),sK0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_650])).

cnf(c_687,plain,
    ( k4_lattice3(sK1,k5_lattice3(sK1,sK2)) != X0_43
    | k4_lattice3(sK1,k5_lattice3(sK1,sK2)) = sK2
    | sK2 != X0_43 ),
    inference(instantiation,[status(thm)],[c_358])).

cnf(c_753,plain,
    ( k4_lattice3(sK1,k5_lattice3(sK1,sK2)) != k5_lattice3(sK1,sK2)
    | k4_lattice3(sK1,k5_lattice3(sK1,sK2)) = sK2
    | sK2 != k5_lattice3(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_687])).

cnf(c_800,plain,
    ( r2_lattice3(k3_lattice3(sK1),sK0,k4_lattice3(sK1,k5_lattice3(sK1,sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_562,c_7,c_14,c_270,c_368,c_371,c_372,c_374,c_606,c_640,c_651,c_753])).

cnf(c_355,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(k3_lattice3(sK1))) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_558,plain,
    ( m1_subset_1(sK2,u1_struct_0(k3_lattice3(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_355])).

cnf(c_560,plain,
    ( k5_lattice3(sK1,X0_43) = X0_43
    | m1_subset_1(X0_43,u1_struct_0(k3_lattice3(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_353])).

cnf(c_661,plain,
    ( k5_lattice3(sK1,sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_558,c_560])).

cnf(c_559,plain,
    ( m1_subset_1(X0_43,u1_struct_0(k3_lattice3(sK1))) != iProver_top
    | m1_subset_1(k5_lattice3(sK1,X0_43),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_354])).

cnf(c_691,plain,
    ( m1_subset_1(sK2,u1_struct_0(k3_lattice3(sK1))) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_661,c_559])).

cnf(c_360,plain,
    ( ~ m1_subset_1(X0_43,X0_44)
    | m1_subset_1(X1_43,X0_44)
    | X1_43 != X0_43 ),
    theory(equality)).

cnf(c_612,plain,
    ( m1_subset_1(X0_43,u1_struct_0(sK1))
    | ~ m1_subset_1(k5_lattice3(sK1,X1_43),u1_struct_0(sK1))
    | X0_43 != k5_lattice3(sK1,X1_43) ),
    inference(instantiation,[status(thm)],[c_360])).

cnf(c_613,plain,
    ( X0_43 != k5_lattice3(sK1,X1_43)
    | m1_subset_1(X0_43,u1_struct_0(sK1)) = iProver_top
    | m1_subset_1(k5_lattice3(sK1,X1_43),u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_612])).

cnf(c_615,plain,
    ( sK2 != k5_lattice3(sK1,sK2)
    | m1_subset_1(k5_lattice3(sK1,sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_613])).

cnf(c_706,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_691,c_7,c_14,c_368,c_372,c_374,c_615,c_640])).

cnf(c_561,plain,
    ( k4_lattice3(sK1,X0_43) = X0_43
    | m1_subset_1(X0_43,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_352])).

cnf(c_711,plain,
    ( k4_lattice3(sK1,sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_706,c_561])).

cnf(c_804,plain,
    ( r2_lattice3(k3_lattice3(sK1),sK0,sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_800,c_661,c_711])).

cnf(c_5,negated_conjecture,
    ( ~ r2_lattice3(k3_lattice3(sK1),sK0,sK2)
    | ~ r4_lattice3(sK1,k5_lattice3(sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_78,plain,
    ( ~ r2_lattice3(k3_lattice3(sK1),sK0,sK2)
    | ~ r4_lattice3(sK1,k5_lattice3(sK1,sK2),sK0) ),
    inference(prop_impl,[status(thm)],[c_5])).

cnf(c_3,plain,
    ( ~ r2_lattice3(k3_lattice3(X0),X1,k4_lattice3(X0,X2))
    | r4_lattice3(X0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_174,plain,
    ( ~ r2_lattice3(k3_lattice3(X0),X1,k4_lattice3(X0,X2))
    | r4_lattice3(X0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_8])).

cnf(c_175,plain,
    ( ~ r2_lattice3(k3_lattice3(sK1),X0,k4_lattice3(sK1,X1))
    | r4_lattice3(sK1,X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1) ),
    inference(unflattening,[status(thm)],[c_174])).

cnf(c_179,plain,
    ( ~ r2_lattice3(k3_lattice3(sK1),X0,k4_lattice3(sK1,X1))
    | r4_lattice3(sK1,X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_175,c_10,c_9])).

cnf(c_281,plain,
    ( ~ r2_lattice3(k3_lattice3(sK1),X0,k4_lattice3(sK1,X1))
    | ~ r2_lattice3(k3_lattice3(sK1),sK0,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | k5_lattice3(sK1,sK2) != X1
    | sK0 != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_78,c_179])).

cnf(c_282,plain,
    ( ~ r2_lattice3(k3_lattice3(sK1),sK0,k4_lattice3(sK1,k5_lattice3(sK1,sK2)))
    | ~ r2_lattice3(k3_lattice3(sK1),sK0,sK2)
    | ~ m1_subset_1(k5_lattice3(sK1,sK2),u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_281])).

cnf(c_283,plain,
    ( r2_lattice3(k3_lattice3(sK1),sK0,k4_lattice3(sK1,k5_lattice3(sK1,sK2))) != iProver_top
    | r2_lattice3(k3_lattice3(sK1),sK0,sK2) != iProver_top
    | m1_subset_1(k5_lattice3(sK1,sK2),u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_282])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_804,c_800,c_372,c_283,c_14])).


%------------------------------------------------------------------------------
