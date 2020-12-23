%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:18:59 EST 2020

% Result     : Theorem 1.08s
% Output     : CNFRefutation 1.08s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 491 expanded)
%              Number of clauses        :   87 ( 216 expanded)
%              Number of leaves         :   15 (  95 expanded)
%              Depth                    :   21
%              Number of atoms          :  385 (1888 expanded)
%              Number of equality atoms :  167 ( 371 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,u1_struct_0(k1_lattice3(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))
         => ( r1_lattices(k1_lattice3(X0),X1,X2)
          <=> r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,u1_struct_0(k1_lattice3(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))
           => ( r1_lattices(k1_lattice3(X0),X1,X2)
            <=> r1_tarski(X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_lattices(k1_lattice3(X0),X1,X2)
          <~> r1_tarski(X1,X2) )
          & m1_subset_1(X2,u1_struct_0(k1_lattice3(X0))) )
      & m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,X2)
            | ~ r1_lattices(k1_lattice3(X0),X1,X2) )
          & ( r1_tarski(X1,X2)
            | r1_lattices(k1_lattice3(X0),X1,X2) )
          & m1_subset_1(X2,u1_struct_0(k1_lattice3(X0))) )
      & m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,X2)
            | ~ r1_lattices(k1_lattice3(X0),X1,X2) )
          & ( r1_tarski(X1,X2)
            | r1_lattices(k1_lattice3(X0),X1,X2) )
          & m1_subset_1(X2,u1_struct_0(k1_lattice3(X0))) )
      & m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))) ) ),
    inference(flattening,[],[f20])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,X2)
            | ~ r1_lattices(k1_lattice3(X0),X1,X2) )
          & ( r1_tarski(X1,X2)
            | r1_lattices(k1_lattice3(X0),X1,X2) )
          & m1_subset_1(X2,u1_struct_0(k1_lattice3(X0))) )
     => ( ( ~ r1_tarski(X1,sK2)
          | ~ r1_lattices(k1_lattice3(X0),X1,sK2) )
        & ( r1_tarski(X1,sK2)
          | r1_lattices(k1_lattice3(X0),X1,sK2) )
        & m1_subset_1(sK2,u1_struct_0(k1_lattice3(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r1_tarski(X1,X2)
              | ~ r1_lattices(k1_lattice3(X0),X1,X2) )
            & ( r1_tarski(X1,X2)
              | r1_lattices(k1_lattice3(X0),X1,X2) )
            & m1_subset_1(X2,u1_struct_0(k1_lattice3(X0))) )
        & m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))) )
   => ( ? [X2] :
          ( ( ~ r1_tarski(sK1,X2)
            | ~ r1_lattices(k1_lattice3(sK0),sK1,X2) )
          & ( r1_tarski(sK1,X2)
            | r1_lattices(k1_lattice3(sK0),sK1,X2) )
          & m1_subset_1(X2,u1_struct_0(k1_lattice3(sK0))) )
      & m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ( ~ r1_tarski(sK1,sK2)
      | ~ r1_lattices(k1_lattice3(sK0),sK1,sK2) )
    & ( r1_tarski(sK1,sK2)
      | r1_lattices(k1_lattice3(sK0),sK1,sK2) )
    & m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0)))
    & m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f23,f22])).

fof(f36,plain,
    ( r1_tarski(sK1,sK2)
    | r1_lattices(k1_lattice3(sK0),sK1,sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_lattices(X0,X1,X2)
                  | k1_lattices(X0,X1,X2) != X2 )
                & ( k1_lattices(X0,X1,X2) = X2
                  | ~ r1_lattices(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k1_lattices(X0,X1,X2) = X2
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f4,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => l2_lattices(X0) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f16,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f29,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f5,axiom,(
    ! [X0] :
      ( l3_lattices(k1_lattice3(X0))
      & v3_lattices(k1_lattice3(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] : l3_lattices(k1_lattice3(X0)) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f30,plain,(
    ! [X0] : l3_lattices(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f6,axiom,(
    ! [X0] :
      ( v3_lattices(k1_lattice3(X0))
      & ~ v2_struct_0(k1_lattice3(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] : ~ v2_struct_0(k1_lattice3(X0)) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f31,plain,(
    ! [X0] : ~ v2_struct_0(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f35,plain,(
    m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,u1_struct_0(k1_lattice3(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))
         => ( k2_lattices(k1_lattice3(X0),X1,X2) = k3_xboole_0(X1,X2)
            & k2_xboole_0(X1,X2) = k1_lattices(k1_lattice3(X0),X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k2_lattices(k1_lattice3(X0),X1,X2) = k3_xboole_0(X1,X2)
            & k2_xboole_0(X1,X2) = k1_lattices(k1_lattice3(X0),X1,X2) )
          | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X0))) )
      | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k1_lattices(k1_lattice3(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f34,plain,(
    m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f37,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ r1_lattices(k1_lattice3(sK0),sK1,sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,X1,X2)
      | k1_lattices(X0,X1,X2) != X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_10,negated_conjecture,
    ( r1_lattices(k1_lattice3(sK0),sK1,sK2)
    | r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_102,plain,
    ( r1_tarski(sK1,sK2)
    | r1_lattices(k1_lattice3(sK0),sK1,sK2) ),
    inference(prop_impl,[status(thm)],[c_10])).

cnf(c_103,plain,
    ( r1_lattices(k1_lattice3(sK0),sK1,sK2)
    | r1_tarski(sK1,sK2) ),
    inference(renaming,[status(thm)],[c_102])).

cnf(c_200,plain,
    ( r1_lattices(k1_lattice3(sK0),sK1,sK2)
    | k2_xboole_0(X0,X1) = X1
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_103])).

cnf(c_201,plain,
    ( r1_lattices(k1_lattice3(sK0),sK1,sK2)
    | k2_xboole_0(sK1,sK2) = sK2 ),
    inference(unflattening,[status(thm)],[c_200])).

cnf(c_3,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l2_lattices(X0)
    | k1_lattices(X0,X1,X2) = X2 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_4,plain,
    ( ~ l3_lattices(X0)
    | l2_lattices(X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_5,plain,
    ( l3_lattices(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_182,plain,
    ( l2_lattices(X0)
    | k1_lattice3(X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_5])).

cnf(c_183,plain,
    ( l2_lattices(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_182])).

cnf(c_229,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | k1_lattices(X0,X1,X2) = X2
    | k1_lattice3(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_183])).

cnf(c_230,plain,
    ( ~ r1_lattices(k1_lattice3(X0),X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))
    | v2_struct_0(k1_lattice3(X0))
    | k1_lattices(k1_lattice3(X0),X1,X2) = X2 ),
    inference(unflattening,[status(thm)],[c_229])).

cnf(c_6,plain,
    ( ~ v2_struct_0(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_234,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X0)))
    | ~ r1_lattices(k1_lattice3(X0),X1,X2)
    | k1_lattices(k1_lattice3(X0),X1,X2) = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_230,c_6])).

cnf(c_235,plain,
    ( ~ r1_lattices(k1_lattice3(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X0)))
    | k1_lattices(k1_lattice3(X0),X1,X2) = X2 ),
    inference(renaming,[status(thm)],[c_234])).

cnf(c_296,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k1_lattice3(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X1)))
    | k1_lattices(k1_lattice3(X1),X2,X0) = X0
    | k2_xboole_0(sK1,sK2) = sK2
    | k1_lattice3(X1) != k1_lattice3(sK0)
    | sK2 != X0
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_201,c_235])).

cnf(c_297,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(k1_lattice3(X0)))
    | ~ m1_subset_1(sK1,u1_struct_0(k1_lattice3(X0)))
    | k1_lattices(k1_lattice3(X0),sK1,sK2) = sK2
    | k2_xboole_0(sK1,sK2) = sK2
    | k1_lattice3(X0) != k1_lattice3(sK0) ),
    inference(unflattening,[status(thm)],[c_296])).

cnf(c_398,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(k1_lattice3(X0_46)))
    | ~ m1_subset_1(sK1,u1_struct_0(k1_lattice3(X0_46)))
    | k1_lattice3(X0_46) != k1_lattice3(sK0)
    | k1_lattices(k1_lattice3(X0_46),sK1,sK2) = sK2
    | k2_xboole_0(sK1,sK2) = sK2 ),
    inference(subtyping,[status(esa)],[c_297])).

cnf(c_568,plain,
    ( k1_lattice3(X0_46) != k1_lattice3(sK0)
    | k1_lattices(k1_lattice3(X0_46),sK1,sK2) = sK2
    | k2_xboole_0(sK1,sK2) = sK2
    | m1_subset_1(sK2,u1_struct_0(k1_lattice3(X0_46))) != iProver_top
    | m1_subset_1(sK1,u1_struct_0(k1_lattice3(X0_46))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_398])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0))) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_14,plain,
    ( m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_441,plain,
    ( k1_lattice3(X0_46) != k1_lattice3(sK0)
    | k1_lattices(k1_lattice3(X0_46),sK1,sK2) = sK2
    | k2_xboole_0(sK1,sK2) = sK2
    | m1_subset_1(sK2,u1_struct_0(k1_lattice3(X0_46))) != iProver_top
    | m1_subset_1(sK1,u1_struct_0(k1_lattice3(X0_46))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_398])).

cnf(c_409,plain,
    ( X0_43 = X0_43 ),
    theory(equality)).

cnf(c_663,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_409])).

cnf(c_418,plain,
    ( X0_45 != X1_45
    | u1_struct_0(X0_45) = u1_struct_0(X1_45) ),
    theory(equality)).

cnf(c_680,plain,
    ( X0_45 != k1_lattice3(sK0)
    | u1_struct_0(X0_45) = u1_struct_0(k1_lattice3(sK0)) ),
    inference(instantiation,[status(thm)],[c_418])).

cnf(c_754,plain,
    ( k1_lattice3(X0_46) != k1_lattice3(sK0)
    | u1_struct_0(k1_lattice3(X0_46)) = u1_struct_0(k1_lattice3(sK0)) ),
    inference(instantiation,[status(thm)],[c_680])).

cnf(c_419,plain,
    ( ~ m1_subset_1(X0_43,X0_44)
    | m1_subset_1(X1_43,X1_44)
    | X1_44 != X0_44
    | X1_43 != X0_43 ),
    theory(equality)).

cnf(c_638,plain,
    ( m1_subset_1(X0_43,X0_44)
    | ~ m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0)))
    | X0_44 != u1_struct_0(k1_lattice3(sK0))
    | X0_43 != sK2 ),
    inference(instantiation,[status(thm)],[c_419])).

cnf(c_662,plain,
    ( m1_subset_1(sK2,X0_44)
    | ~ m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0)))
    | X0_44 != u1_struct_0(k1_lattice3(sK0))
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_638])).

cnf(c_810,plain,
    ( m1_subset_1(sK2,u1_struct_0(k1_lattice3(X0_46)))
    | ~ m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0)))
    | u1_struct_0(k1_lattice3(X0_46)) != u1_struct_0(k1_lattice3(sK0))
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_662])).

cnf(c_812,plain,
    ( u1_struct_0(k1_lattice3(X0_46)) != u1_struct_0(k1_lattice3(sK0))
    | sK2 != sK2
    | m1_subset_1(sK2,u1_struct_0(k1_lattice3(X0_46))) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_810])).

cnf(c_413,plain,
    ( X0_43 != X1_43
    | X2_43 != X1_43
    | X2_43 = X0_43 ),
    theory(equality)).

cnf(c_697,plain,
    ( X0_43 != X1_43
    | sK2 != X1_43
    | sK2 = X0_43 ),
    inference(instantiation,[status(thm)],[c_413])).

cnf(c_800,plain,
    ( X0_43 != sK2
    | sK2 = X0_43
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_697])).

cnf(c_840,plain,
    ( k2_xboole_0(sK1,sK2) != sK2
    | sK2 = k2_xboole_0(sK1,sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_800])).

cnf(c_668,plain,
    ( X0_43 != X1_43
    | X0_43 = sK2
    | sK2 != X1_43 ),
    inference(instantiation,[status(thm)],[c_413])).

cnf(c_876,plain,
    ( X0_43 != k2_xboole_0(sK1,sK2)
    | X0_43 = sK2
    | sK2 != k2_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_668])).

cnf(c_922,plain,
    ( k1_lattices(k1_lattice3(X0_46),sK1,sK2) != k2_xboole_0(sK1,sK2)
    | k1_lattices(k1_lattice3(X0_46),sK1,sK2) = sK2
    | sK2 != k2_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_876])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k1_lattice3(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X1)))
    | k1_lattices(k1_lattice3(X1),X2,X0) = k2_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_403,plain,
    ( ~ m1_subset_1(X0_43,u1_struct_0(k1_lattice3(X0_46)))
    | ~ m1_subset_1(X1_43,u1_struct_0(k1_lattice3(X0_46)))
    | k1_lattices(k1_lattice3(X0_46),X1_43,X0_43) = k2_xboole_0(X1_43,X0_43) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_923,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(k1_lattice3(X0_46)))
    | ~ m1_subset_1(sK1,u1_struct_0(k1_lattice3(X0_46)))
    | k1_lattices(k1_lattice3(X0_46),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_403])).

cnf(c_925,plain,
    ( k1_lattices(k1_lattice3(X0_46),sK1,sK2) = k2_xboole_0(sK1,sK2)
    | m1_subset_1(sK2,u1_struct_0(k1_lattice3(X0_46))) != iProver_top
    | m1_subset_1(sK1,u1_struct_0(k1_lattice3(X0_46))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_923])).

cnf(c_1196,plain,
    ( k1_lattice3(X0_46) != k1_lattice3(sK0)
    | k1_lattices(k1_lattice3(X0_46),sK1,sK2) = sK2
    | m1_subset_1(sK1,u1_struct_0(k1_lattice3(X0_46))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_568,c_14,c_441,c_663,c_754,c_812,c_840,c_922,c_925])).

cnf(c_1205,plain,
    ( k1_lattices(k1_lattice3(sK0),sK1,sK2) = sK2
    | m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0))) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1196])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0))) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_401,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0))) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_567,plain,
    ( m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_401])).

cnf(c_402,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0))) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_566,plain,
    ( m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_402])).

cnf(c_565,plain,
    ( k1_lattices(k1_lattice3(X0_46),X0_43,X1_43) = k2_xboole_0(X0_43,X1_43)
    | m1_subset_1(X0_43,u1_struct_0(k1_lattice3(X0_46))) != iProver_top
    | m1_subset_1(X1_43,u1_struct_0(k1_lattice3(X0_46))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_403])).

cnf(c_825,plain,
    ( k1_lattices(k1_lattice3(sK0),X0_43,sK2) = k2_xboole_0(X0_43,sK2)
    | m1_subset_1(X0_43,u1_struct_0(k1_lattice3(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_566,c_565])).

cnf(c_987,plain,
    ( k1_lattices(k1_lattice3(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_567,c_825])).

cnf(c_1206,plain,
    ( k2_xboole_0(sK1,sK2) = sK2
    | m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1205,c_987])).

cnf(c_13,plain,
    ( m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1309,plain,
    ( k2_xboole_0(sK1,sK2) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1206,c_13])).

cnf(c_1,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_9,negated_conjecture,
    ( ~ r1_lattices(k1_lattice3(sK0),sK1,sK2)
    | ~ r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_100,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ r1_lattices(k1_lattice3(sK0),sK1,sK2) ),
    inference(prop_impl,[status(thm)],[c_9])).

cnf(c_101,plain,
    ( ~ r1_lattices(k1_lattice3(sK0),sK1,sK2)
    | ~ r1_tarski(sK1,sK2) ),
    inference(renaming,[status(thm)],[c_100])).

cnf(c_210,plain,
    ( ~ r1_lattices(k1_lattice3(sK0),sK1,sK2)
    | k2_xboole_0(X0,X1) != sK2
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_101])).

cnf(c_211,plain,
    ( ~ r1_lattices(k1_lattice3(sK0),sK1,sK2)
    | k2_xboole_0(sK1,X0) != sK2 ),
    inference(unflattening,[status(thm)],[c_210])).

cnf(c_2,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l2_lattices(X0)
    | k1_lattices(X0,X1,X2) != X2 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_253,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | k1_lattices(X0,X1,X2) != X2
    | k1_lattice3(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_183])).

cnf(c_254,plain,
    ( r1_lattices(k1_lattice3(X0),X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))
    | v2_struct_0(k1_lattice3(X0))
    | k1_lattices(k1_lattice3(X0),X1,X2) != X2 ),
    inference(unflattening,[status(thm)],[c_253])).

cnf(c_258,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X0)))
    | r1_lattices(k1_lattice3(X0),X1,X2)
    | k1_lattices(k1_lattice3(X0),X1,X2) != X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_254,c_6])).

cnf(c_259,plain,
    ( r1_lattices(k1_lattice3(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X0)))
    | k1_lattices(k1_lattice3(X0),X1,X2) != X2 ),
    inference(renaming,[status(thm)],[c_258])).

cnf(c_317,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k1_lattice3(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X1)))
    | k1_lattices(k1_lattice3(X1),X0,X2) != X2
    | k2_xboole_0(sK1,X3) != sK2
    | k1_lattice3(X1) != k1_lattice3(sK0)
    | sK2 != X2
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_211,c_259])).

cnf(c_318,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(k1_lattice3(X0)))
    | ~ m1_subset_1(sK1,u1_struct_0(k1_lattice3(X0)))
    | k1_lattices(k1_lattice3(X0),sK1,sK2) != sK2
    | k2_xboole_0(sK1,X1) != sK2
    | k1_lattice3(X0) != k1_lattice3(sK0) ),
    inference(unflattening,[status(thm)],[c_317])).

cnf(c_397,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(k1_lattice3(X0_46)))
    | ~ m1_subset_1(sK1,u1_struct_0(k1_lattice3(X0_46)))
    | k1_lattice3(X0_46) != k1_lattice3(sK0)
    | k1_lattices(k1_lattice3(X0_46),sK1,sK2) != sK2
    | k2_xboole_0(sK1,X0_43) != sK2 ),
    inference(subtyping,[status(esa)],[c_318])).

cnf(c_405,plain,
    ( k2_xboole_0(sK1,X0_43) != sK2
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_397])).

cnf(c_571,plain,
    ( k2_xboole_0(sK1,X0_43) != sK2
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_405])).

cnf(c_1316,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_1309,c_571])).

cnf(c_406,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(k1_lattice3(X0_46)))
    | ~ m1_subset_1(sK1,u1_struct_0(k1_lattice3(X0_46)))
    | k1_lattice3(X0_46) != k1_lattice3(sK0)
    | k1_lattices(k1_lattice3(X0_46),sK1,sK2) != sK2
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_397])).

cnf(c_570,plain,
    ( k1_lattice3(X0_46) != k1_lattice3(sK0)
    | k1_lattices(k1_lattice3(X0_46),sK1,sK2) != sK2
    | m1_subset_1(sK2,u1_struct_0(k1_lattice3(X0_46))) != iProver_top
    | m1_subset_1(sK1,u1_struct_0(k1_lattice3(X0_46))) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_406])).

cnf(c_442,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0)))
    | k1_lattice3(sK0) != k1_lattice3(sK0)
    | k1_lattices(k1_lattice3(sK0),sK1,sK2) = sK2
    | k2_xboole_0(sK1,sK2) = sK2 ),
    inference(instantiation,[status(thm)],[c_398])).

cnf(c_445,plain,
    ( k1_lattice3(X0_46) != k1_lattice3(sK0)
    | k1_lattices(k1_lattice3(X0_46),sK1,sK2) != sK2
    | m1_subset_1(sK2,u1_struct_0(k1_lattice3(X0_46))) != iProver_top
    | m1_subset_1(sK1,u1_struct_0(k1_lattice3(X0_46))) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_406])).

cnf(c_447,plain,
    ( k1_lattice3(sK0) != k1_lattice3(sK0)
    | k1_lattices(k1_lattice3(sK0),sK1,sK2) != sK2
    | m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0))) != iProver_top
    | m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0))) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(instantiation,[status(thm)],[c_445])).

cnf(c_411,plain,
    ( X0_45 = X0_45 ),
    theory(equality)).

cnf(c_652,plain,
    ( k1_lattice3(sK0) = k1_lattice3(sK0) ),
    inference(instantiation,[status(thm)],[c_411])).

cnf(c_836,plain,
    ( k1_lattices(k1_lattice3(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2)
    | m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_825])).

cnf(c_924,plain,
    ( k1_lattices(k1_lattice3(sK0),sK1,sK2) != k2_xboole_0(sK1,sK2)
    | k1_lattices(k1_lattice3(sK0),sK1,sK2) = sK2
    | sK2 != k2_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_922])).

cnf(c_1141,plain,
    ( sP1_iProver_split != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_570,c_12,c_13,c_11,c_14,c_442,c_447,c_652,c_663,c_836,c_840,c_924])).

cnf(c_407,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_397])).

cnf(c_444,plain,
    ( sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_407])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1316,c_1141,c_444])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.10  % Command    : iproveropt_run.sh %d %s
% 0.10/0.31  % Computer   : n016.cluster.edu
% 0.10/0.31  % Model      : x86_64 x86_64
% 0.10/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.31  % Memory     : 8042.1875MB
% 0.10/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.31  % CPULimit   : 60
% 0.10/0.31  % WCLimit    : 600
% 0.10/0.31  % DateTime   : Tue Dec  1 17:57:04 EST 2020
% 0.10/0.32  % CPUTime    : 
% 0.10/0.32  % Running in FOF mode
% 1.08/0.96  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.08/0.96  
% 1.08/0.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.08/0.96  
% 1.08/0.96  ------  iProver source info
% 1.08/0.96  
% 1.08/0.96  git: date: 2020-06-30 10:37:57 +0100
% 1.08/0.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.08/0.96  git: non_committed_changes: false
% 1.08/0.96  git: last_make_outside_of_git: false
% 1.08/0.96  
% 1.08/0.96  ------ 
% 1.08/0.96  
% 1.08/0.96  ------ Input Options
% 1.08/0.96  
% 1.08/0.96  --out_options                           all
% 1.08/0.96  --tptp_safe_out                         true
% 1.08/0.96  --problem_path                          ""
% 1.08/0.96  --include_path                          ""
% 1.08/0.96  --clausifier                            res/vclausify_rel
% 1.08/0.96  --clausifier_options                    --mode clausify
% 1.08/0.96  --stdin                                 false
% 1.08/0.96  --stats_out                             all
% 1.08/0.96  
% 1.08/0.96  ------ General Options
% 1.08/0.96  
% 1.08/0.96  --fof                                   false
% 1.08/0.96  --time_out_real                         305.
% 1.08/0.96  --time_out_virtual                      -1.
% 1.08/0.96  --symbol_type_check                     false
% 1.08/0.96  --clausify_out                          false
% 1.08/0.96  --sig_cnt_out                           false
% 1.08/0.96  --trig_cnt_out                          false
% 1.08/0.96  --trig_cnt_out_tolerance                1.
% 1.08/0.96  --trig_cnt_out_sk_spl                   false
% 1.08/0.96  --abstr_cl_out                          false
% 1.08/0.96  
% 1.08/0.96  ------ Global Options
% 1.08/0.96  
% 1.08/0.96  --schedule                              default
% 1.08/0.96  --add_important_lit                     false
% 1.08/0.96  --prop_solver_per_cl                    1000
% 1.08/0.96  --min_unsat_core                        false
% 1.08/0.96  --soft_assumptions                      false
% 1.08/0.96  --soft_lemma_size                       3
% 1.08/0.96  --prop_impl_unit_size                   0
% 1.08/0.96  --prop_impl_unit                        []
% 1.08/0.96  --share_sel_clauses                     true
% 1.08/0.96  --reset_solvers                         false
% 1.08/0.96  --bc_imp_inh                            [conj_cone]
% 1.08/0.96  --conj_cone_tolerance                   3.
% 1.08/0.96  --extra_neg_conj                        none
% 1.08/0.96  --large_theory_mode                     true
% 1.08/0.96  --prolific_symb_bound                   200
% 1.08/0.96  --lt_threshold                          2000
% 1.08/0.96  --clause_weak_htbl                      true
% 1.08/0.96  --gc_record_bc_elim                     false
% 1.08/0.96  
% 1.08/0.96  ------ Preprocessing Options
% 1.08/0.96  
% 1.08/0.96  --preprocessing_flag                    true
% 1.08/0.96  --time_out_prep_mult                    0.1
% 1.08/0.96  --splitting_mode                        input
% 1.08/0.96  --splitting_grd                         true
% 1.08/0.96  --splitting_cvd                         false
% 1.08/0.96  --splitting_cvd_svl                     false
% 1.08/0.96  --splitting_nvd                         32
% 1.08/0.96  --sub_typing                            true
% 1.08/0.96  --prep_gs_sim                           true
% 1.08/0.96  --prep_unflatten                        true
% 1.08/0.96  --prep_res_sim                          true
% 1.08/0.96  --prep_upred                            true
% 1.08/0.96  --prep_sem_filter                       exhaustive
% 1.08/0.96  --prep_sem_filter_out                   false
% 1.08/0.96  --pred_elim                             true
% 1.08/0.96  --res_sim_input                         true
% 1.08/0.96  --eq_ax_congr_red                       true
% 1.08/0.96  --pure_diseq_elim                       true
% 1.08/0.96  --brand_transform                       false
% 1.08/0.96  --non_eq_to_eq                          false
% 1.08/0.96  --prep_def_merge                        true
% 1.08/0.96  --prep_def_merge_prop_impl              false
% 1.08/0.96  --prep_def_merge_mbd                    true
% 1.08/0.96  --prep_def_merge_tr_red                 false
% 1.08/0.96  --prep_def_merge_tr_cl                  false
% 1.08/0.96  --smt_preprocessing                     true
% 1.08/0.96  --smt_ac_axioms                         fast
% 1.08/0.96  --preprocessed_out                      false
% 1.08/0.96  --preprocessed_stats                    false
% 1.08/0.96  
% 1.08/0.96  ------ Abstraction refinement Options
% 1.08/0.96  
% 1.08/0.96  --abstr_ref                             []
% 1.08/0.96  --abstr_ref_prep                        false
% 1.08/0.96  --abstr_ref_until_sat                   false
% 1.08/0.96  --abstr_ref_sig_restrict                funpre
% 1.08/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 1.08/0.96  --abstr_ref_under                       []
% 1.08/0.96  
% 1.08/0.96  ------ SAT Options
% 1.08/0.96  
% 1.08/0.96  --sat_mode                              false
% 1.08/0.96  --sat_fm_restart_options                ""
% 1.08/0.96  --sat_gr_def                            false
% 1.08/0.96  --sat_epr_types                         true
% 1.08/0.96  --sat_non_cyclic_types                  false
% 1.08/0.96  --sat_finite_models                     false
% 1.08/0.96  --sat_fm_lemmas                         false
% 1.08/0.96  --sat_fm_prep                           false
% 1.08/0.96  --sat_fm_uc_incr                        true
% 1.08/0.96  --sat_out_model                         small
% 1.08/0.96  --sat_out_clauses                       false
% 1.08/0.96  
% 1.08/0.96  ------ QBF Options
% 1.08/0.96  
% 1.08/0.96  --qbf_mode                              false
% 1.08/0.96  --qbf_elim_univ                         false
% 1.08/0.96  --qbf_dom_inst                          none
% 1.08/0.96  --qbf_dom_pre_inst                      false
% 1.08/0.96  --qbf_sk_in                             false
% 1.08/0.96  --qbf_pred_elim                         true
% 1.08/0.96  --qbf_split                             512
% 1.08/0.96  
% 1.08/0.96  ------ BMC1 Options
% 1.08/0.96  
% 1.08/0.96  --bmc1_incremental                      false
% 1.08/0.96  --bmc1_axioms                           reachable_all
% 1.08/0.96  --bmc1_min_bound                        0
% 1.08/0.96  --bmc1_max_bound                        -1
% 1.08/0.96  --bmc1_max_bound_default                -1
% 1.08/0.96  --bmc1_symbol_reachability              true
% 1.08/0.96  --bmc1_property_lemmas                  false
% 1.08/0.96  --bmc1_k_induction                      false
% 1.08/0.96  --bmc1_non_equiv_states                 false
% 1.08/0.96  --bmc1_deadlock                         false
% 1.08/0.96  --bmc1_ucm                              false
% 1.08/0.96  --bmc1_add_unsat_core                   none
% 1.08/0.96  --bmc1_unsat_core_children              false
% 1.08/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 1.08/0.96  --bmc1_out_stat                         full
% 1.08/0.96  --bmc1_ground_init                      false
% 1.08/0.96  --bmc1_pre_inst_next_state              false
% 1.08/0.96  --bmc1_pre_inst_state                   false
% 1.08/0.96  --bmc1_pre_inst_reach_state             false
% 1.08/0.96  --bmc1_out_unsat_core                   false
% 1.08/0.96  --bmc1_aig_witness_out                  false
% 1.08/0.96  --bmc1_verbose                          false
% 1.08/0.96  --bmc1_dump_clauses_tptp                false
% 1.08/0.96  --bmc1_dump_unsat_core_tptp             false
% 1.08/0.96  --bmc1_dump_file                        -
% 1.08/0.96  --bmc1_ucm_expand_uc_limit              128
% 1.08/0.96  --bmc1_ucm_n_expand_iterations          6
% 1.08/0.96  --bmc1_ucm_extend_mode                  1
% 1.08/0.96  --bmc1_ucm_init_mode                    2
% 1.08/0.96  --bmc1_ucm_cone_mode                    none
% 1.08/0.96  --bmc1_ucm_reduced_relation_type        0
% 1.08/0.96  --bmc1_ucm_relax_model                  4
% 1.08/0.96  --bmc1_ucm_full_tr_after_sat            true
% 1.08/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 1.08/0.96  --bmc1_ucm_layered_model                none
% 1.08/0.96  --bmc1_ucm_max_lemma_size               10
% 1.08/0.96  
% 1.08/0.96  ------ AIG Options
% 1.08/0.96  
% 1.08/0.96  --aig_mode                              false
% 1.08/0.96  
% 1.08/0.96  ------ Instantiation Options
% 1.08/0.96  
% 1.08/0.96  --instantiation_flag                    true
% 1.08/0.96  --inst_sos_flag                         false
% 1.08/0.96  --inst_sos_phase                        true
% 1.08/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.08/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.08/0.96  --inst_lit_sel_side                     num_symb
% 1.08/0.96  --inst_solver_per_active                1400
% 1.08/0.96  --inst_solver_calls_frac                1.
% 1.08/0.96  --inst_passive_queue_type               priority_queues
% 1.08/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.08/0.96  --inst_passive_queues_freq              [25;2]
% 1.08/0.96  --inst_dismatching                      true
% 1.08/0.96  --inst_eager_unprocessed_to_passive     true
% 1.08/0.96  --inst_prop_sim_given                   true
% 1.08/0.96  --inst_prop_sim_new                     false
% 1.08/0.96  --inst_subs_new                         false
% 1.08/0.96  --inst_eq_res_simp                      false
% 1.08/0.96  --inst_subs_given                       false
% 1.08/0.96  --inst_orphan_elimination               true
% 1.08/0.96  --inst_learning_loop_flag               true
% 1.08/0.96  --inst_learning_start                   3000
% 1.08/0.96  --inst_learning_factor                  2
% 1.08/0.96  --inst_start_prop_sim_after_learn       3
% 1.08/0.96  --inst_sel_renew                        solver
% 1.08/0.96  --inst_lit_activity_flag                true
% 1.08/0.96  --inst_restr_to_given                   false
% 1.08/0.96  --inst_activity_threshold               500
% 1.08/0.96  --inst_out_proof                        true
% 1.08/0.96  
% 1.08/0.96  ------ Resolution Options
% 1.08/0.96  
% 1.08/0.96  --resolution_flag                       true
% 1.08/0.96  --res_lit_sel                           adaptive
% 1.08/0.96  --res_lit_sel_side                      none
% 1.08/0.96  --res_ordering                          kbo
% 1.08/0.96  --res_to_prop_solver                    active
% 1.08/0.96  --res_prop_simpl_new                    false
% 1.08/0.96  --res_prop_simpl_given                  true
% 1.08/0.96  --res_passive_queue_type                priority_queues
% 1.08/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.08/0.96  --res_passive_queues_freq               [15;5]
% 1.08/0.96  --res_forward_subs                      full
% 1.08/0.96  --res_backward_subs                     full
% 1.08/0.96  --res_forward_subs_resolution           true
% 1.08/0.96  --res_backward_subs_resolution          true
% 1.08/0.96  --res_orphan_elimination                true
% 1.08/0.96  --res_time_limit                        2.
% 1.08/0.96  --res_out_proof                         true
% 1.08/0.96  
% 1.08/0.96  ------ Superposition Options
% 1.08/0.96  
% 1.08/0.96  --superposition_flag                    true
% 1.08/0.96  --sup_passive_queue_type                priority_queues
% 1.08/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.08/0.96  --sup_passive_queues_freq               [8;1;4]
% 1.08/0.96  --demod_completeness_check              fast
% 1.08/0.96  --demod_use_ground                      true
% 1.08/0.96  --sup_to_prop_solver                    passive
% 1.08/0.96  --sup_prop_simpl_new                    true
% 1.08/0.96  --sup_prop_simpl_given                  true
% 1.08/0.96  --sup_fun_splitting                     false
% 1.08/0.96  --sup_smt_interval                      50000
% 1.08/0.96  
% 1.08/0.96  ------ Superposition Simplification Setup
% 1.08/0.96  
% 1.08/0.96  --sup_indices_passive                   []
% 1.08/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.08/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.08/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.08/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 1.08/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.08/0.96  --sup_full_bw                           [BwDemod]
% 1.08/0.96  --sup_immed_triv                        [TrivRules]
% 1.08/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.08/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.08/0.96  --sup_immed_bw_main                     []
% 1.08/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.08/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 1.08/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.08/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.08/0.96  
% 1.08/0.96  ------ Combination Options
% 1.08/0.96  
% 1.08/0.96  --comb_res_mult                         3
% 1.08/0.96  --comb_sup_mult                         2
% 1.08/0.96  --comb_inst_mult                        10
% 1.08/0.96  
% 1.08/0.96  ------ Debug Options
% 1.08/0.96  
% 1.08/0.96  --dbg_backtrace                         false
% 1.08/0.96  --dbg_dump_prop_clauses                 false
% 1.08/0.96  --dbg_dump_prop_clauses_file            -
% 1.08/0.96  --dbg_out_stat                          false
% 1.08/0.96  ------ Parsing...
% 1.08/0.96  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.08/0.96  
% 1.08/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 1.08/0.96  
% 1.08/0.96  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.08/0.96  
% 1.08/0.96  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.08/0.96  ------ Proving...
% 1.08/0.96  ------ Problem Properties 
% 1.08/0.96  
% 1.08/0.96  
% 1.08/0.96  clauses                                 10
% 1.08/0.96  conjectures                             2
% 1.08/0.96  EPR                                     1
% 1.08/0.96  Horn                                    8
% 1.08/0.96  unary                                   3
% 1.08/0.96  binary                                  3
% 1.08/0.96  lits                                    25
% 1.08/0.96  lits eq                                 11
% 1.08/0.96  fd_pure                                 0
% 1.08/0.96  fd_pseudo                               0
% 1.08/0.96  fd_cond                                 0
% 1.08/0.96  fd_pseudo_cond                          0
% 1.08/0.96  AC symbols                              0
% 1.08/0.96  
% 1.08/0.96  ------ Schedule dynamic 5 is on 
% 1.08/0.96  
% 1.08/0.96  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.08/0.96  
% 1.08/0.96  
% 1.08/0.96  ------ 
% 1.08/0.96  Current options:
% 1.08/0.96  ------ 
% 1.08/0.96  
% 1.08/0.96  ------ Input Options
% 1.08/0.96  
% 1.08/0.96  --out_options                           all
% 1.08/0.96  --tptp_safe_out                         true
% 1.08/0.96  --problem_path                          ""
% 1.08/0.96  --include_path                          ""
% 1.08/0.96  --clausifier                            res/vclausify_rel
% 1.08/0.96  --clausifier_options                    --mode clausify
% 1.08/0.96  --stdin                                 false
% 1.08/0.96  --stats_out                             all
% 1.08/0.96  
% 1.08/0.96  ------ General Options
% 1.08/0.96  
% 1.08/0.96  --fof                                   false
% 1.08/0.96  --time_out_real                         305.
% 1.08/0.96  --time_out_virtual                      -1.
% 1.08/0.96  --symbol_type_check                     false
% 1.08/0.96  --clausify_out                          false
% 1.08/0.96  --sig_cnt_out                           false
% 1.08/0.96  --trig_cnt_out                          false
% 1.08/0.96  --trig_cnt_out_tolerance                1.
% 1.08/0.96  --trig_cnt_out_sk_spl                   false
% 1.08/0.96  --abstr_cl_out                          false
% 1.08/0.96  
% 1.08/0.96  ------ Global Options
% 1.08/0.96  
% 1.08/0.96  --schedule                              default
% 1.08/0.96  --add_important_lit                     false
% 1.08/0.96  --prop_solver_per_cl                    1000
% 1.08/0.96  --min_unsat_core                        false
% 1.08/0.96  --soft_assumptions                      false
% 1.08/0.96  --soft_lemma_size                       3
% 1.08/0.96  --prop_impl_unit_size                   0
% 1.08/0.96  --prop_impl_unit                        []
% 1.08/0.96  --share_sel_clauses                     true
% 1.08/0.96  --reset_solvers                         false
% 1.08/0.96  --bc_imp_inh                            [conj_cone]
% 1.08/0.96  --conj_cone_tolerance                   3.
% 1.08/0.96  --extra_neg_conj                        none
% 1.08/0.96  --large_theory_mode                     true
% 1.08/0.96  --prolific_symb_bound                   200
% 1.08/0.96  --lt_threshold                          2000
% 1.08/0.96  --clause_weak_htbl                      true
% 1.08/0.96  --gc_record_bc_elim                     false
% 1.08/0.96  
% 1.08/0.96  ------ Preprocessing Options
% 1.08/0.96  
% 1.08/0.96  --preprocessing_flag                    true
% 1.08/0.96  --time_out_prep_mult                    0.1
% 1.08/0.96  --splitting_mode                        input
% 1.08/0.96  --splitting_grd                         true
% 1.08/0.96  --splitting_cvd                         false
% 1.08/0.96  --splitting_cvd_svl                     false
% 1.08/0.96  --splitting_nvd                         32
% 1.08/0.96  --sub_typing                            true
% 1.08/0.96  --prep_gs_sim                           true
% 1.08/0.96  --prep_unflatten                        true
% 1.08/0.96  --prep_res_sim                          true
% 1.08/0.96  --prep_upred                            true
% 1.08/0.96  --prep_sem_filter                       exhaustive
% 1.08/0.96  --prep_sem_filter_out                   false
% 1.08/0.96  --pred_elim                             true
% 1.08/0.96  --res_sim_input                         true
% 1.08/0.96  --eq_ax_congr_red                       true
% 1.08/0.96  --pure_diseq_elim                       true
% 1.08/0.96  --brand_transform                       false
% 1.08/0.96  --non_eq_to_eq                          false
% 1.08/0.96  --prep_def_merge                        true
% 1.08/0.96  --prep_def_merge_prop_impl              false
% 1.08/0.96  --prep_def_merge_mbd                    true
% 1.08/0.96  --prep_def_merge_tr_red                 false
% 1.08/0.96  --prep_def_merge_tr_cl                  false
% 1.08/0.96  --smt_preprocessing                     true
% 1.08/0.96  --smt_ac_axioms                         fast
% 1.08/0.96  --preprocessed_out                      false
% 1.08/0.96  --preprocessed_stats                    false
% 1.08/0.96  
% 1.08/0.96  ------ Abstraction refinement Options
% 1.08/0.96  
% 1.08/0.96  --abstr_ref                             []
% 1.08/0.96  --abstr_ref_prep                        false
% 1.08/0.96  --abstr_ref_until_sat                   false
% 1.08/0.96  --abstr_ref_sig_restrict                funpre
% 1.08/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 1.08/0.96  --abstr_ref_under                       []
% 1.08/0.96  
% 1.08/0.96  ------ SAT Options
% 1.08/0.96  
% 1.08/0.96  --sat_mode                              false
% 1.08/0.96  --sat_fm_restart_options                ""
% 1.08/0.96  --sat_gr_def                            false
% 1.08/0.96  --sat_epr_types                         true
% 1.08/0.96  --sat_non_cyclic_types                  false
% 1.08/0.96  --sat_finite_models                     false
% 1.08/0.96  --sat_fm_lemmas                         false
% 1.08/0.96  --sat_fm_prep                           false
% 1.08/0.96  --sat_fm_uc_incr                        true
% 1.08/0.96  --sat_out_model                         small
% 1.08/0.96  --sat_out_clauses                       false
% 1.08/0.96  
% 1.08/0.96  ------ QBF Options
% 1.08/0.96  
% 1.08/0.96  --qbf_mode                              false
% 1.08/0.96  --qbf_elim_univ                         false
% 1.08/0.96  --qbf_dom_inst                          none
% 1.08/0.96  --qbf_dom_pre_inst                      false
% 1.08/0.96  --qbf_sk_in                             false
% 1.08/0.96  --qbf_pred_elim                         true
% 1.08/0.96  --qbf_split                             512
% 1.08/0.96  
% 1.08/0.96  ------ BMC1 Options
% 1.08/0.96  
% 1.08/0.96  --bmc1_incremental                      false
% 1.08/0.96  --bmc1_axioms                           reachable_all
% 1.08/0.96  --bmc1_min_bound                        0
% 1.08/0.96  --bmc1_max_bound                        -1
% 1.08/0.96  --bmc1_max_bound_default                -1
% 1.08/0.96  --bmc1_symbol_reachability              true
% 1.08/0.96  --bmc1_property_lemmas                  false
% 1.08/0.96  --bmc1_k_induction                      false
% 1.08/0.96  --bmc1_non_equiv_states                 false
% 1.08/0.96  --bmc1_deadlock                         false
% 1.08/0.96  --bmc1_ucm                              false
% 1.08/0.96  --bmc1_add_unsat_core                   none
% 1.08/0.96  --bmc1_unsat_core_children              false
% 1.08/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 1.08/0.96  --bmc1_out_stat                         full
% 1.08/0.96  --bmc1_ground_init                      false
% 1.08/0.96  --bmc1_pre_inst_next_state              false
% 1.08/0.96  --bmc1_pre_inst_state                   false
% 1.08/0.96  --bmc1_pre_inst_reach_state             false
% 1.08/0.96  --bmc1_out_unsat_core                   false
% 1.08/0.96  --bmc1_aig_witness_out                  false
% 1.08/0.96  --bmc1_verbose                          false
% 1.08/0.96  --bmc1_dump_clauses_tptp                false
% 1.08/0.96  --bmc1_dump_unsat_core_tptp             false
% 1.08/0.96  --bmc1_dump_file                        -
% 1.08/0.96  --bmc1_ucm_expand_uc_limit              128
% 1.08/0.96  --bmc1_ucm_n_expand_iterations          6
% 1.08/0.96  --bmc1_ucm_extend_mode                  1
% 1.08/0.96  --bmc1_ucm_init_mode                    2
% 1.08/0.96  --bmc1_ucm_cone_mode                    none
% 1.08/0.96  --bmc1_ucm_reduced_relation_type        0
% 1.08/0.96  --bmc1_ucm_relax_model                  4
% 1.08/0.96  --bmc1_ucm_full_tr_after_sat            true
% 1.08/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 1.08/0.96  --bmc1_ucm_layered_model                none
% 1.08/0.96  --bmc1_ucm_max_lemma_size               10
% 1.08/0.96  
% 1.08/0.96  ------ AIG Options
% 1.08/0.96  
% 1.08/0.96  --aig_mode                              false
% 1.08/0.96  
% 1.08/0.96  ------ Instantiation Options
% 1.08/0.96  
% 1.08/0.96  --instantiation_flag                    true
% 1.08/0.96  --inst_sos_flag                         false
% 1.08/0.96  --inst_sos_phase                        true
% 1.08/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.08/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.08/0.96  --inst_lit_sel_side                     none
% 1.08/0.96  --inst_solver_per_active                1400
% 1.08/0.96  --inst_solver_calls_frac                1.
% 1.08/0.96  --inst_passive_queue_type               priority_queues
% 1.08/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.08/0.96  --inst_passive_queues_freq              [25;2]
% 1.08/0.96  --inst_dismatching                      true
% 1.08/0.96  --inst_eager_unprocessed_to_passive     true
% 1.08/0.96  --inst_prop_sim_given                   true
% 1.08/0.96  --inst_prop_sim_new                     false
% 1.08/0.96  --inst_subs_new                         false
% 1.08/0.96  --inst_eq_res_simp                      false
% 1.08/0.96  --inst_subs_given                       false
% 1.08/0.96  --inst_orphan_elimination               true
% 1.08/0.96  --inst_learning_loop_flag               true
% 1.08/0.96  --inst_learning_start                   3000
% 1.08/0.96  --inst_learning_factor                  2
% 1.08/0.96  --inst_start_prop_sim_after_learn       3
% 1.08/0.96  --inst_sel_renew                        solver
% 1.08/0.96  --inst_lit_activity_flag                true
% 1.08/0.96  --inst_restr_to_given                   false
% 1.08/0.96  --inst_activity_threshold               500
% 1.08/0.96  --inst_out_proof                        true
% 1.08/0.96  
% 1.08/0.96  ------ Resolution Options
% 1.08/0.96  
% 1.08/0.96  --resolution_flag                       false
% 1.08/0.96  --res_lit_sel                           adaptive
% 1.08/0.96  --res_lit_sel_side                      none
% 1.08/0.96  --res_ordering                          kbo
% 1.08/0.96  --res_to_prop_solver                    active
% 1.08/0.96  --res_prop_simpl_new                    false
% 1.08/0.96  --res_prop_simpl_given                  true
% 1.08/0.96  --res_passive_queue_type                priority_queues
% 1.08/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.08/0.96  --res_passive_queues_freq               [15;5]
% 1.08/0.96  --res_forward_subs                      full
% 1.08/0.96  --res_backward_subs                     full
% 1.08/0.96  --res_forward_subs_resolution           true
% 1.08/0.96  --res_backward_subs_resolution          true
% 1.08/0.96  --res_orphan_elimination                true
% 1.08/0.96  --res_time_limit                        2.
% 1.08/0.96  --res_out_proof                         true
% 1.08/0.96  
% 1.08/0.96  ------ Superposition Options
% 1.08/0.96  
% 1.08/0.96  --superposition_flag                    true
% 1.08/0.96  --sup_passive_queue_type                priority_queues
% 1.08/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.08/0.96  --sup_passive_queues_freq               [8;1;4]
% 1.08/0.96  --demod_completeness_check              fast
% 1.08/0.96  --demod_use_ground                      true
% 1.08/0.96  --sup_to_prop_solver                    passive
% 1.08/0.96  --sup_prop_simpl_new                    true
% 1.08/0.96  --sup_prop_simpl_given                  true
% 1.08/0.96  --sup_fun_splitting                     false
% 1.08/0.96  --sup_smt_interval                      50000
% 1.08/0.96  
% 1.08/0.96  ------ Superposition Simplification Setup
% 1.08/0.96  
% 1.08/0.96  --sup_indices_passive                   []
% 1.08/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.08/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.08/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.08/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 1.08/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.08/0.96  --sup_full_bw                           [BwDemod]
% 1.08/0.96  --sup_immed_triv                        [TrivRules]
% 1.08/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.08/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.08/0.96  --sup_immed_bw_main                     []
% 1.08/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.08/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 1.08/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.08/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.08/0.96  
% 1.08/0.96  ------ Combination Options
% 1.08/0.96  
% 1.08/0.96  --comb_res_mult                         3
% 1.08/0.96  --comb_sup_mult                         2
% 1.08/0.96  --comb_inst_mult                        10
% 1.08/0.96  
% 1.08/0.96  ------ Debug Options
% 1.08/0.96  
% 1.08/0.96  --dbg_backtrace                         false
% 1.08/0.96  --dbg_dump_prop_clauses                 false
% 1.08/0.96  --dbg_dump_prop_clauses_file            -
% 1.08/0.96  --dbg_out_stat                          false
% 1.08/0.96  
% 1.08/0.96  
% 1.08/0.96  
% 1.08/0.96  
% 1.08/0.96  ------ Proving...
% 1.08/0.96  
% 1.08/0.96  
% 1.08/0.96  % SZS status Theorem for theBenchmark.p
% 1.08/0.96  
% 1.08/0.96  % SZS output start CNFRefutation for theBenchmark.p
% 1.08/0.96  
% 1.08/0.96  fof(f1,axiom,(
% 1.08/0.96    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.08/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.08/0.96  
% 1.08/0.96  fof(f13,plain,(
% 1.08/0.96    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.08/0.96    inference(ennf_transformation,[],[f1])).
% 1.08/0.96  
% 1.08/0.96  fof(f25,plain,(
% 1.08/0.96    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.08/0.96    inference(cnf_transformation,[],[f13])).
% 1.08/0.96  
% 1.08/0.96  fof(f8,conjecture,(
% 1.08/0.96    ! [X0,X1] : (m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k1_lattice3(X0))) => (r1_lattices(k1_lattice3(X0),X1,X2) <=> r1_tarski(X1,X2))))),
% 1.08/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.08/0.96  
% 1.08/0.96  fof(f9,negated_conjecture,(
% 1.08/0.96    ~! [X0,X1] : (m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k1_lattice3(X0))) => (r1_lattices(k1_lattice3(X0),X1,X2) <=> r1_tarski(X1,X2))))),
% 1.08/0.96    inference(negated_conjecture,[],[f8])).
% 1.08/0.96  
% 1.08/0.96  fof(f18,plain,(
% 1.08/0.96    ? [X0,X1] : (? [X2] : ((r1_lattices(k1_lattice3(X0),X1,X2) <~> r1_tarski(X1,X2)) & m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))) & m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))))),
% 1.08/0.96    inference(ennf_transformation,[],[f9])).
% 1.08/0.96  
% 1.08/0.96  fof(f20,plain,(
% 1.08/0.96    ? [X0,X1] : (? [X2] : (((~r1_tarski(X1,X2) | ~r1_lattices(k1_lattice3(X0),X1,X2)) & (r1_tarski(X1,X2) | r1_lattices(k1_lattice3(X0),X1,X2))) & m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))) & m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))))),
% 1.08/0.96    inference(nnf_transformation,[],[f18])).
% 1.08/0.96  
% 1.08/0.96  fof(f21,plain,(
% 1.08/0.96    ? [X0,X1] : (? [X2] : ((~r1_tarski(X1,X2) | ~r1_lattices(k1_lattice3(X0),X1,X2)) & (r1_tarski(X1,X2) | r1_lattices(k1_lattice3(X0),X1,X2)) & m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))) & m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))))),
% 1.08/0.96    inference(flattening,[],[f20])).
% 1.08/0.96  
% 1.08/0.96  fof(f23,plain,(
% 1.08/0.96    ( ! [X0,X1] : (? [X2] : ((~r1_tarski(X1,X2) | ~r1_lattices(k1_lattice3(X0),X1,X2)) & (r1_tarski(X1,X2) | r1_lattices(k1_lattice3(X0),X1,X2)) & m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))) => ((~r1_tarski(X1,sK2) | ~r1_lattices(k1_lattice3(X0),X1,sK2)) & (r1_tarski(X1,sK2) | r1_lattices(k1_lattice3(X0),X1,sK2)) & m1_subset_1(sK2,u1_struct_0(k1_lattice3(X0))))) )),
% 1.08/0.96    introduced(choice_axiom,[])).
% 1.08/0.96  
% 1.08/0.96  fof(f22,plain,(
% 1.08/0.96    ? [X0,X1] : (? [X2] : ((~r1_tarski(X1,X2) | ~r1_lattices(k1_lattice3(X0),X1,X2)) & (r1_tarski(X1,X2) | r1_lattices(k1_lattice3(X0),X1,X2)) & m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))) & m1_subset_1(X1,u1_struct_0(k1_lattice3(X0)))) => (? [X2] : ((~r1_tarski(sK1,X2) | ~r1_lattices(k1_lattice3(sK0),sK1,X2)) & (r1_tarski(sK1,X2) | r1_lattices(k1_lattice3(sK0),sK1,X2)) & m1_subset_1(X2,u1_struct_0(k1_lattice3(sK0)))) & m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0))))),
% 1.08/0.96    introduced(choice_axiom,[])).
% 1.08/0.96  
% 1.08/0.96  fof(f24,plain,(
% 1.08/0.96    ((~r1_tarski(sK1,sK2) | ~r1_lattices(k1_lattice3(sK0),sK1,sK2)) & (r1_tarski(sK1,sK2) | r1_lattices(k1_lattice3(sK0),sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0)))) & m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0)))),
% 1.08/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f23,f22])).
% 1.08/0.96  
% 1.08/0.96  fof(f36,plain,(
% 1.08/0.96    r1_tarski(sK1,sK2) | r1_lattices(k1_lattice3(sK0),sK1,sK2)),
% 1.08/0.96    inference(cnf_transformation,[],[f24])).
% 1.08/0.96  
% 1.08/0.96  fof(f3,axiom,(
% 1.08/0.96    ! [X0] : ((l2_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2))))),
% 1.08/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.08/0.96  
% 1.08/0.96  fof(f14,plain,(
% 1.08/0.96    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l2_lattices(X0) | v2_struct_0(X0)))),
% 1.08/0.96    inference(ennf_transformation,[],[f3])).
% 1.08/0.96  
% 1.08/0.96  fof(f15,plain,(
% 1.08/0.96    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 1.08/0.96    inference(flattening,[],[f14])).
% 1.08/0.96  
% 1.08/0.96  fof(f19,plain,(
% 1.08/0.96    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k1_lattices(X0,X1,X2) != X2) & (k1_lattices(X0,X1,X2) = X2 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 1.08/0.96    inference(nnf_transformation,[],[f15])).
% 1.08/0.96  
% 1.08/0.96  fof(f27,plain,(
% 1.08/0.96    ( ! [X2,X0,X1] : (k1_lattices(X0,X1,X2) = X2 | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0)) )),
% 1.08/0.96    inference(cnf_transformation,[],[f19])).
% 1.08/0.96  
% 1.08/0.96  fof(f4,axiom,(
% 1.08/0.96    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 1.08/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.08/0.96  
% 1.08/0.96  fof(f12,plain,(
% 1.08/0.96    ! [X0] : (l3_lattices(X0) => l2_lattices(X0))),
% 1.08/0.96    inference(pure_predicate_removal,[],[f4])).
% 1.08/0.96  
% 1.08/0.96  fof(f16,plain,(
% 1.08/0.96    ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0))),
% 1.08/0.96    inference(ennf_transformation,[],[f12])).
% 1.08/0.96  
% 1.08/0.96  fof(f29,plain,(
% 1.08/0.96    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 1.08/0.96    inference(cnf_transformation,[],[f16])).
% 1.08/0.96  
% 1.08/0.96  fof(f5,axiom,(
% 1.08/0.96    ! [X0] : (l3_lattices(k1_lattice3(X0)) & v3_lattices(k1_lattice3(X0)))),
% 1.08/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.08/0.96  
% 1.08/0.96  fof(f11,plain,(
% 1.08/0.96    ! [X0] : l3_lattices(k1_lattice3(X0))),
% 1.08/0.96    inference(pure_predicate_removal,[],[f5])).
% 1.08/0.96  
% 1.08/0.96  fof(f30,plain,(
% 1.08/0.96    ( ! [X0] : (l3_lattices(k1_lattice3(X0))) )),
% 1.08/0.96    inference(cnf_transformation,[],[f11])).
% 1.08/0.96  
% 1.08/0.96  fof(f6,axiom,(
% 1.08/0.96    ! [X0] : (v3_lattices(k1_lattice3(X0)) & ~v2_struct_0(k1_lattice3(X0)))),
% 1.08/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.08/0.96  
% 1.08/0.96  fof(f10,plain,(
% 1.08/0.96    ! [X0] : ~v2_struct_0(k1_lattice3(X0))),
% 1.08/0.96    inference(pure_predicate_removal,[],[f6])).
% 1.08/0.96  
% 1.08/0.96  fof(f31,plain,(
% 1.08/0.96    ( ! [X0] : (~v2_struct_0(k1_lattice3(X0))) )),
% 1.08/0.96    inference(cnf_transformation,[],[f10])).
% 1.08/0.96  
% 1.08/0.96  fof(f35,plain,(
% 1.08/0.96    m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0)))),
% 1.08/0.96    inference(cnf_transformation,[],[f24])).
% 1.08/0.96  
% 1.08/0.96  fof(f7,axiom,(
% 1.08/0.96    ! [X0,X1] : (m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k1_lattice3(X0))) => (k2_lattices(k1_lattice3(X0),X1,X2) = k3_xboole_0(X1,X2) & k2_xboole_0(X1,X2) = k1_lattices(k1_lattice3(X0),X1,X2))))),
% 1.08/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.08/0.96  
% 1.08/0.96  fof(f17,plain,(
% 1.08/0.96    ! [X0,X1] : (! [X2] : ((k2_lattices(k1_lattice3(X0),X1,X2) = k3_xboole_0(X1,X2) & k2_xboole_0(X1,X2) = k1_lattices(k1_lattice3(X0),X1,X2)) | ~m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))) | ~m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))))),
% 1.08/0.96    inference(ennf_transformation,[],[f7])).
% 1.08/0.96  
% 1.08/0.96  fof(f32,plain,(
% 1.08/0.96    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k1_lattices(k1_lattice3(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k1_lattice3(X0))) | ~m1_subset_1(X1,u1_struct_0(k1_lattice3(X0)))) )),
% 1.08/0.96    inference(cnf_transformation,[],[f17])).
% 1.08/0.96  
% 1.08/0.96  fof(f34,plain,(
% 1.08/0.96    m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0)))),
% 1.08/0.96    inference(cnf_transformation,[],[f24])).
% 1.08/0.96  
% 1.08/0.96  fof(f2,axiom,(
% 1.08/0.96    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.08/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.08/0.96  
% 1.08/0.96  fof(f26,plain,(
% 1.08/0.96    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.08/0.96    inference(cnf_transformation,[],[f2])).
% 1.08/0.96  
% 1.08/0.96  fof(f37,plain,(
% 1.08/0.96    ~r1_tarski(sK1,sK2) | ~r1_lattices(k1_lattice3(sK0),sK1,sK2)),
% 1.08/0.96    inference(cnf_transformation,[],[f24])).
% 1.08/0.96  
% 1.08/0.96  fof(f28,plain,(
% 1.08/0.96    ( ! [X2,X0,X1] : (r1_lattices(X0,X1,X2) | k1_lattices(X0,X1,X2) != X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0)) )),
% 1.08/0.96    inference(cnf_transformation,[],[f19])).
% 1.08/0.96  
% 1.08/0.96  cnf(c_0,plain,
% 1.08/0.96      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 1.08/0.96      inference(cnf_transformation,[],[f25]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_10,negated_conjecture,
% 1.08/0.96      ( r1_lattices(k1_lattice3(sK0),sK1,sK2) | r1_tarski(sK1,sK2) ),
% 1.08/0.96      inference(cnf_transformation,[],[f36]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_102,plain,
% 1.08/0.96      ( r1_tarski(sK1,sK2) | r1_lattices(k1_lattice3(sK0),sK1,sK2) ),
% 1.08/0.96      inference(prop_impl,[status(thm)],[c_10]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_103,plain,
% 1.08/0.96      ( r1_lattices(k1_lattice3(sK0),sK1,sK2) | r1_tarski(sK1,sK2) ),
% 1.08/0.96      inference(renaming,[status(thm)],[c_102]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_200,plain,
% 1.08/0.96      ( r1_lattices(k1_lattice3(sK0),sK1,sK2)
% 1.08/0.96      | k2_xboole_0(X0,X1) = X1
% 1.08/0.96      | sK2 != X1
% 1.08/0.96      | sK1 != X0 ),
% 1.08/0.96      inference(resolution_lifted,[status(thm)],[c_0,c_103]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_201,plain,
% 1.08/0.96      ( r1_lattices(k1_lattice3(sK0),sK1,sK2)
% 1.08/0.96      | k2_xboole_0(sK1,sK2) = sK2 ),
% 1.08/0.96      inference(unflattening,[status(thm)],[c_200]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_3,plain,
% 1.08/0.96      ( ~ r1_lattices(X0,X1,X2)
% 1.08/0.96      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.08/0.96      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.08/0.96      | v2_struct_0(X0)
% 1.08/0.96      | ~ l2_lattices(X0)
% 1.08/0.96      | k1_lattices(X0,X1,X2) = X2 ),
% 1.08/0.96      inference(cnf_transformation,[],[f27]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_4,plain,
% 1.08/0.96      ( ~ l3_lattices(X0) | l2_lattices(X0) ),
% 1.08/0.96      inference(cnf_transformation,[],[f29]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_5,plain,
% 1.08/0.96      ( l3_lattices(k1_lattice3(X0)) ),
% 1.08/0.96      inference(cnf_transformation,[],[f30]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_182,plain,
% 1.08/0.96      ( l2_lattices(X0) | k1_lattice3(X1) != X0 ),
% 1.08/0.96      inference(resolution_lifted,[status(thm)],[c_4,c_5]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_183,plain,
% 1.08/0.96      ( l2_lattices(k1_lattice3(X0)) ),
% 1.08/0.96      inference(unflattening,[status(thm)],[c_182]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_229,plain,
% 1.08/0.96      ( ~ r1_lattices(X0,X1,X2)
% 1.08/0.96      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.08/0.96      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.08/0.96      | v2_struct_0(X0)
% 1.08/0.96      | k1_lattices(X0,X1,X2) = X2
% 1.08/0.96      | k1_lattice3(X3) != X0 ),
% 1.08/0.96      inference(resolution_lifted,[status(thm)],[c_3,c_183]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_230,plain,
% 1.08/0.96      ( ~ r1_lattices(k1_lattice3(X0),X1,X2)
% 1.08/0.96      | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X0)))
% 1.08/0.96      | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))
% 1.08/0.96      | v2_struct_0(k1_lattice3(X0))
% 1.08/0.96      | k1_lattices(k1_lattice3(X0),X1,X2) = X2 ),
% 1.08/0.96      inference(unflattening,[status(thm)],[c_229]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_6,plain,
% 1.08/0.96      ( ~ v2_struct_0(k1_lattice3(X0)) ),
% 1.08/0.96      inference(cnf_transformation,[],[f31]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_234,plain,
% 1.08/0.96      ( ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))
% 1.08/0.96      | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X0)))
% 1.08/0.96      | ~ r1_lattices(k1_lattice3(X0),X1,X2)
% 1.08/0.96      | k1_lattices(k1_lattice3(X0),X1,X2) = X2 ),
% 1.08/0.96      inference(global_propositional_subsumption,
% 1.08/0.96                [status(thm)],
% 1.08/0.96                [c_230,c_6]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_235,plain,
% 1.08/0.96      ( ~ r1_lattices(k1_lattice3(X0),X1,X2)
% 1.08/0.96      | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))
% 1.08/0.96      | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X0)))
% 1.08/0.96      | k1_lattices(k1_lattice3(X0),X1,X2) = X2 ),
% 1.08/0.96      inference(renaming,[status(thm)],[c_234]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_296,plain,
% 1.08/0.96      ( ~ m1_subset_1(X0,u1_struct_0(k1_lattice3(X1)))
% 1.08/0.96      | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X1)))
% 1.08/0.96      | k1_lattices(k1_lattice3(X1),X2,X0) = X0
% 1.08/0.96      | k2_xboole_0(sK1,sK2) = sK2
% 1.08/0.96      | k1_lattice3(X1) != k1_lattice3(sK0)
% 1.08/0.96      | sK2 != X0
% 1.08/0.96      | sK1 != X2 ),
% 1.08/0.96      inference(resolution_lifted,[status(thm)],[c_201,c_235]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_297,plain,
% 1.08/0.96      ( ~ m1_subset_1(sK2,u1_struct_0(k1_lattice3(X0)))
% 1.08/0.96      | ~ m1_subset_1(sK1,u1_struct_0(k1_lattice3(X0)))
% 1.08/0.96      | k1_lattices(k1_lattice3(X0),sK1,sK2) = sK2
% 1.08/0.96      | k2_xboole_0(sK1,sK2) = sK2
% 1.08/0.96      | k1_lattice3(X0) != k1_lattice3(sK0) ),
% 1.08/0.96      inference(unflattening,[status(thm)],[c_296]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_398,plain,
% 1.08/0.96      ( ~ m1_subset_1(sK2,u1_struct_0(k1_lattice3(X0_46)))
% 1.08/0.96      | ~ m1_subset_1(sK1,u1_struct_0(k1_lattice3(X0_46)))
% 1.08/0.96      | k1_lattice3(X0_46) != k1_lattice3(sK0)
% 1.08/0.96      | k1_lattices(k1_lattice3(X0_46),sK1,sK2) = sK2
% 1.08/0.96      | k2_xboole_0(sK1,sK2) = sK2 ),
% 1.08/0.96      inference(subtyping,[status(esa)],[c_297]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_568,plain,
% 1.08/0.96      ( k1_lattice3(X0_46) != k1_lattice3(sK0)
% 1.08/0.96      | k1_lattices(k1_lattice3(X0_46),sK1,sK2) = sK2
% 1.08/0.96      | k2_xboole_0(sK1,sK2) = sK2
% 1.08/0.96      | m1_subset_1(sK2,u1_struct_0(k1_lattice3(X0_46))) != iProver_top
% 1.08/0.96      | m1_subset_1(sK1,u1_struct_0(k1_lattice3(X0_46))) != iProver_top ),
% 1.08/0.96      inference(predicate_to_equality,[status(thm)],[c_398]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_11,negated_conjecture,
% 1.08/0.96      ( m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0))) ),
% 1.08/0.96      inference(cnf_transformation,[],[f35]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_14,plain,
% 1.08/0.96      ( m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0))) = iProver_top ),
% 1.08/0.96      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_441,plain,
% 1.08/0.96      ( k1_lattice3(X0_46) != k1_lattice3(sK0)
% 1.08/0.96      | k1_lattices(k1_lattice3(X0_46),sK1,sK2) = sK2
% 1.08/0.96      | k2_xboole_0(sK1,sK2) = sK2
% 1.08/0.96      | m1_subset_1(sK2,u1_struct_0(k1_lattice3(X0_46))) != iProver_top
% 1.08/0.96      | m1_subset_1(sK1,u1_struct_0(k1_lattice3(X0_46))) != iProver_top ),
% 1.08/0.96      inference(predicate_to_equality,[status(thm)],[c_398]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_409,plain,( X0_43 = X0_43 ),theory(equality) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_663,plain,
% 1.08/0.96      ( sK2 = sK2 ),
% 1.08/0.96      inference(instantiation,[status(thm)],[c_409]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_418,plain,
% 1.08/0.96      ( X0_45 != X1_45 | u1_struct_0(X0_45) = u1_struct_0(X1_45) ),
% 1.08/0.96      theory(equality) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_680,plain,
% 1.08/0.96      ( X0_45 != k1_lattice3(sK0)
% 1.08/0.96      | u1_struct_0(X0_45) = u1_struct_0(k1_lattice3(sK0)) ),
% 1.08/0.96      inference(instantiation,[status(thm)],[c_418]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_754,plain,
% 1.08/0.96      ( k1_lattice3(X0_46) != k1_lattice3(sK0)
% 1.08/0.96      | u1_struct_0(k1_lattice3(X0_46)) = u1_struct_0(k1_lattice3(sK0)) ),
% 1.08/0.96      inference(instantiation,[status(thm)],[c_680]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_419,plain,
% 1.08/0.96      ( ~ m1_subset_1(X0_43,X0_44)
% 1.08/0.96      | m1_subset_1(X1_43,X1_44)
% 1.08/0.96      | X1_44 != X0_44
% 1.08/0.96      | X1_43 != X0_43 ),
% 1.08/0.96      theory(equality) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_638,plain,
% 1.08/0.96      ( m1_subset_1(X0_43,X0_44)
% 1.08/0.96      | ~ m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0)))
% 1.08/0.96      | X0_44 != u1_struct_0(k1_lattice3(sK0))
% 1.08/0.96      | X0_43 != sK2 ),
% 1.08/0.96      inference(instantiation,[status(thm)],[c_419]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_662,plain,
% 1.08/0.96      ( m1_subset_1(sK2,X0_44)
% 1.08/0.96      | ~ m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0)))
% 1.08/0.96      | X0_44 != u1_struct_0(k1_lattice3(sK0))
% 1.08/0.96      | sK2 != sK2 ),
% 1.08/0.96      inference(instantiation,[status(thm)],[c_638]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_810,plain,
% 1.08/0.96      ( m1_subset_1(sK2,u1_struct_0(k1_lattice3(X0_46)))
% 1.08/0.96      | ~ m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0)))
% 1.08/0.96      | u1_struct_0(k1_lattice3(X0_46)) != u1_struct_0(k1_lattice3(sK0))
% 1.08/0.96      | sK2 != sK2 ),
% 1.08/0.96      inference(instantiation,[status(thm)],[c_662]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_812,plain,
% 1.08/0.96      ( u1_struct_0(k1_lattice3(X0_46)) != u1_struct_0(k1_lattice3(sK0))
% 1.08/0.96      | sK2 != sK2
% 1.08/0.96      | m1_subset_1(sK2,u1_struct_0(k1_lattice3(X0_46))) = iProver_top
% 1.08/0.96      | m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0))) != iProver_top ),
% 1.08/0.96      inference(predicate_to_equality,[status(thm)],[c_810]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_413,plain,
% 1.08/0.96      ( X0_43 != X1_43 | X2_43 != X1_43 | X2_43 = X0_43 ),
% 1.08/0.96      theory(equality) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_697,plain,
% 1.08/0.96      ( X0_43 != X1_43 | sK2 != X1_43 | sK2 = X0_43 ),
% 1.08/0.96      inference(instantiation,[status(thm)],[c_413]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_800,plain,
% 1.08/0.96      ( X0_43 != sK2 | sK2 = X0_43 | sK2 != sK2 ),
% 1.08/0.96      inference(instantiation,[status(thm)],[c_697]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_840,plain,
% 1.08/0.96      ( k2_xboole_0(sK1,sK2) != sK2
% 1.08/0.96      | sK2 = k2_xboole_0(sK1,sK2)
% 1.08/0.96      | sK2 != sK2 ),
% 1.08/0.96      inference(instantiation,[status(thm)],[c_800]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_668,plain,
% 1.08/0.96      ( X0_43 != X1_43 | X0_43 = sK2 | sK2 != X1_43 ),
% 1.08/0.96      inference(instantiation,[status(thm)],[c_413]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_876,plain,
% 1.08/0.96      ( X0_43 != k2_xboole_0(sK1,sK2)
% 1.08/0.96      | X0_43 = sK2
% 1.08/0.96      | sK2 != k2_xboole_0(sK1,sK2) ),
% 1.08/0.96      inference(instantiation,[status(thm)],[c_668]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_922,plain,
% 1.08/0.96      ( k1_lattices(k1_lattice3(X0_46),sK1,sK2) != k2_xboole_0(sK1,sK2)
% 1.08/0.96      | k1_lattices(k1_lattice3(X0_46),sK1,sK2) = sK2
% 1.08/0.96      | sK2 != k2_xboole_0(sK1,sK2) ),
% 1.08/0.96      inference(instantiation,[status(thm)],[c_876]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_8,plain,
% 1.08/0.96      ( ~ m1_subset_1(X0,u1_struct_0(k1_lattice3(X1)))
% 1.08/0.96      | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X1)))
% 1.08/0.96      | k1_lattices(k1_lattice3(X1),X2,X0) = k2_xboole_0(X2,X0) ),
% 1.08/0.96      inference(cnf_transformation,[],[f32]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_403,plain,
% 1.08/0.96      ( ~ m1_subset_1(X0_43,u1_struct_0(k1_lattice3(X0_46)))
% 1.08/0.96      | ~ m1_subset_1(X1_43,u1_struct_0(k1_lattice3(X0_46)))
% 1.08/0.96      | k1_lattices(k1_lattice3(X0_46),X1_43,X0_43) = k2_xboole_0(X1_43,X0_43) ),
% 1.08/0.96      inference(subtyping,[status(esa)],[c_8]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_923,plain,
% 1.08/0.96      ( ~ m1_subset_1(sK2,u1_struct_0(k1_lattice3(X0_46)))
% 1.08/0.96      | ~ m1_subset_1(sK1,u1_struct_0(k1_lattice3(X0_46)))
% 1.08/0.96      | k1_lattices(k1_lattice3(X0_46),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
% 1.08/0.96      inference(instantiation,[status(thm)],[c_403]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_925,plain,
% 1.08/0.96      ( k1_lattices(k1_lattice3(X0_46),sK1,sK2) = k2_xboole_0(sK1,sK2)
% 1.08/0.96      | m1_subset_1(sK2,u1_struct_0(k1_lattice3(X0_46))) != iProver_top
% 1.08/0.96      | m1_subset_1(sK1,u1_struct_0(k1_lattice3(X0_46))) != iProver_top ),
% 1.08/0.96      inference(predicate_to_equality,[status(thm)],[c_923]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_1196,plain,
% 1.08/0.96      ( k1_lattice3(X0_46) != k1_lattice3(sK0)
% 1.08/0.96      | k1_lattices(k1_lattice3(X0_46),sK1,sK2) = sK2
% 1.08/0.96      | m1_subset_1(sK1,u1_struct_0(k1_lattice3(X0_46))) != iProver_top ),
% 1.08/0.96      inference(global_propositional_subsumption,
% 1.08/0.96                [status(thm)],
% 1.08/0.96                [c_568,c_14,c_441,c_663,c_754,c_812,c_840,c_922,c_925]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_1205,plain,
% 1.08/0.96      ( k1_lattices(k1_lattice3(sK0),sK1,sK2) = sK2
% 1.08/0.96      | m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0))) != iProver_top ),
% 1.08/0.96      inference(equality_resolution,[status(thm)],[c_1196]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_12,negated_conjecture,
% 1.08/0.96      ( m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0))) ),
% 1.08/0.96      inference(cnf_transformation,[],[f34]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_401,negated_conjecture,
% 1.08/0.96      ( m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0))) ),
% 1.08/0.96      inference(subtyping,[status(esa)],[c_12]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_567,plain,
% 1.08/0.96      ( m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0))) = iProver_top ),
% 1.08/0.96      inference(predicate_to_equality,[status(thm)],[c_401]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_402,negated_conjecture,
% 1.08/0.96      ( m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0))) ),
% 1.08/0.96      inference(subtyping,[status(esa)],[c_11]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_566,plain,
% 1.08/0.96      ( m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0))) = iProver_top ),
% 1.08/0.96      inference(predicate_to_equality,[status(thm)],[c_402]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_565,plain,
% 1.08/0.96      ( k1_lattices(k1_lattice3(X0_46),X0_43,X1_43) = k2_xboole_0(X0_43,X1_43)
% 1.08/0.96      | m1_subset_1(X0_43,u1_struct_0(k1_lattice3(X0_46))) != iProver_top
% 1.08/0.96      | m1_subset_1(X1_43,u1_struct_0(k1_lattice3(X0_46))) != iProver_top ),
% 1.08/0.96      inference(predicate_to_equality,[status(thm)],[c_403]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_825,plain,
% 1.08/0.96      ( k1_lattices(k1_lattice3(sK0),X0_43,sK2) = k2_xboole_0(X0_43,sK2)
% 1.08/0.96      | m1_subset_1(X0_43,u1_struct_0(k1_lattice3(sK0))) != iProver_top ),
% 1.08/0.96      inference(superposition,[status(thm)],[c_566,c_565]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_987,plain,
% 1.08/0.96      ( k1_lattices(k1_lattice3(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
% 1.08/0.96      inference(superposition,[status(thm)],[c_567,c_825]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_1206,plain,
% 1.08/0.96      ( k2_xboole_0(sK1,sK2) = sK2
% 1.08/0.96      | m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0))) != iProver_top ),
% 1.08/0.96      inference(demodulation,[status(thm)],[c_1205,c_987]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_13,plain,
% 1.08/0.96      ( m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0))) = iProver_top ),
% 1.08/0.96      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_1309,plain,
% 1.08/0.96      ( k2_xboole_0(sK1,sK2) = sK2 ),
% 1.08/0.96      inference(global_propositional_subsumption,
% 1.08/0.96                [status(thm)],
% 1.08/0.96                [c_1206,c_13]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_1,plain,
% 1.08/0.96      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 1.08/0.96      inference(cnf_transformation,[],[f26]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_9,negated_conjecture,
% 1.08/0.96      ( ~ r1_lattices(k1_lattice3(sK0),sK1,sK2) | ~ r1_tarski(sK1,sK2) ),
% 1.08/0.96      inference(cnf_transformation,[],[f37]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_100,plain,
% 1.08/0.96      ( ~ r1_tarski(sK1,sK2) | ~ r1_lattices(k1_lattice3(sK0),sK1,sK2) ),
% 1.08/0.96      inference(prop_impl,[status(thm)],[c_9]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_101,plain,
% 1.08/0.96      ( ~ r1_lattices(k1_lattice3(sK0),sK1,sK2) | ~ r1_tarski(sK1,sK2) ),
% 1.08/0.96      inference(renaming,[status(thm)],[c_100]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_210,plain,
% 1.08/0.96      ( ~ r1_lattices(k1_lattice3(sK0),sK1,sK2)
% 1.08/0.96      | k2_xboole_0(X0,X1) != sK2
% 1.08/0.96      | sK1 != X0 ),
% 1.08/0.96      inference(resolution_lifted,[status(thm)],[c_1,c_101]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_211,plain,
% 1.08/0.96      ( ~ r1_lattices(k1_lattice3(sK0),sK1,sK2)
% 1.08/0.96      | k2_xboole_0(sK1,X0) != sK2 ),
% 1.08/0.96      inference(unflattening,[status(thm)],[c_210]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_2,plain,
% 1.08/0.96      ( r1_lattices(X0,X1,X2)
% 1.08/0.96      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.08/0.96      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.08/0.96      | v2_struct_0(X0)
% 1.08/0.96      | ~ l2_lattices(X0)
% 1.08/0.96      | k1_lattices(X0,X1,X2) != X2 ),
% 1.08/0.96      inference(cnf_transformation,[],[f28]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_253,plain,
% 1.08/0.96      ( r1_lattices(X0,X1,X2)
% 1.08/0.96      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.08/0.96      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.08/0.96      | v2_struct_0(X0)
% 1.08/0.96      | k1_lattices(X0,X1,X2) != X2
% 1.08/0.96      | k1_lattice3(X3) != X0 ),
% 1.08/0.96      inference(resolution_lifted,[status(thm)],[c_2,c_183]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_254,plain,
% 1.08/0.96      ( r1_lattices(k1_lattice3(X0),X1,X2)
% 1.08/0.96      | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X0)))
% 1.08/0.96      | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))
% 1.08/0.96      | v2_struct_0(k1_lattice3(X0))
% 1.08/0.96      | k1_lattices(k1_lattice3(X0),X1,X2) != X2 ),
% 1.08/0.96      inference(unflattening,[status(thm)],[c_253]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_258,plain,
% 1.08/0.96      ( ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))
% 1.08/0.96      | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X0)))
% 1.08/0.96      | r1_lattices(k1_lattice3(X0),X1,X2)
% 1.08/0.96      | k1_lattices(k1_lattice3(X0),X1,X2) != X2 ),
% 1.08/0.96      inference(global_propositional_subsumption,
% 1.08/0.96                [status(thm)],
% 1.08/0.96                [c_254,c_6]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_259,plain,
% 1.08/0.96      ( r1_lattices(k1_lattice3(X0),X1,X2)
% 1.08/0.96      | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))
% 1.08/0.96      | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X0)))
% 1.08/0.96      | k1_lattices(k1_lattice3(X0),X1,X2) != X2 ),
% 1.08/0.96      inference(renaming,[status(thm)],[c_258]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_317,plain,
% 1.08/0.96      ( ~ m1_subset_1(X0,u1_struct_0(k1_lattice3(X1)))
% 1.08/0.96      | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X1)))
% 1.08/0.96      | k1_lattices(k1_lattice3(X1),X0,X2) != X2
% 1.08/0.96      | k2_xboole_0(sK1,X3) != sK2
% 1.08/0.96      | k1_lattice3(X1) != k1_lattice3(sK0)
% 1.08/0.96      | sK2 != X2
% 1.08/0.96      | sK1 != X0 ),
% 1.08/0.96      inference(resolution_lifted,[status(thm)],[c_211,c_259]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_318,plain,
% 1.08/0.96      ( ~ m1_subset_1(sK2,u1_struct_0(k1_lattice3(X0)))
% 1.08/0.96      | ~ m1_subset_1(sK1,u1_struct_0(k1_lattice3(X0)))
% 1.08/0.96      | k1_lattices(k1_lattice3(X0),sK1,sK2) != sK2
% 1.08/0.96      | k2_xboole_0(sK1,X1) != sK2
% 1.08/0.96      | k1_lattice3(X0) != k1_lattice3(sK0) ),
% 1.08/0.96      inference(unflattening,[status(thm)],[c_317]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_397,plain,
% 1.08/0.96      ( ~ m1_subset_1(sK2,u1_struct_0(k1_lattice3(X0_46)))
% 1.08/0.96      | ~ m1_subset_1(sK1,u1_struct_0(k1_lattice3(X0_46)))
% 1.08/0.96      | k1_lattice3(X0_46) != k1_lattice3(sK0)
% 1.08/0.96      | k1_lattices(k1_lattice3(X0_46),sK1,sK2) != sK2
% 1.08/0.96      | k2_xboole_0(sK1,X0_43) != sK2 ),
% 1.08/0.96      inference(subtyping,[status(esa)],[c_318]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_405,plain,
% 1.08/0.96      ( k2_xboole_0(sK1,X0_43) != sK2 | ~ sP0_iProver_split ),
% 1.08/0.96      inference(splitting,
% 1.08/0.96                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 1.08/0.96                [c_397]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_571,plain,
% 1.08/0.96      ( k2_xboole_0(sK1,X0_43) != sK2
% 1.08/0.96      | sP0_iProver_split != iProver_top ),
% 1.08/0.96      inference(predicate_to_equality,[status(thm)],[c_405]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_1316,plain,
% 1.08/0.96      ( sP0_iProver_split != iProver_top ),
% 1.08/0.96      inference(superposition,[status(thm)],[c_1309,c_571]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_406,plain,
% 1.08/0.96      ( ~ m1_subset_1(sK2,u1_struct_0(k1_lattice3(X0_46)))
% 1.08/0.96      | ~ m1_subset_1(sK1,u1_struct_0(k1_lattice3(X0_46)))
% 1.08/0.96      | k1_lattice3(X0_46) != k1_lattice3(sK0)
% 1.08/0.96      | k1_lattices(k1_lattice3(X0_46),sK1,sK2) != sK2
% 1.08/0.96      | ~ sP1_iProver_split ),
% 1.08/0.96      inference(splitting,
% 1.08/0.96                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 1.08/0.96                [c_397]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_570,plain,
% 1.08/0.96      ( k1_lattice3(X0_46) != k1_lattice3(sK0)
% 1.08/0.96      | k1_lattices(k1_lattice3(X0_46),sK1,sK2) != sK2
% 1.08/0.96      | m1_subset_1(sK2,u1_struct_0(k1_lattice3(X0_46))) != iProver_top
% 1.08/0.96      | m1_subset_1(sK1,u1_struct_0(k1_lattice3(X0_46))) != iProver_top
% 1.08/0.96      | sP1_iProver_split != iProver_top ),
% 1.08/0.96      inference(predicate_to_equality,[status(thm)],[c_406]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_442,plain,
% 1.08/0.96      ( ~ m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0)))
% 1.08/0.96      | ~ m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0)))
% 1.08/0.96      | k1_lattice3(sK0) != k1_lattice3(sK0)
% 1.08/0.96      | k1_lattices(k1_lattice3(sK0),sK1,sK2) = sK2
% 1.08/0.96      | k2_xboole_0(sK1,sK2) = sK2 ),
% 1.08/0.96      inference(instantiation,[status(thm)],[c_398]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_445,plain,
% 1.08/0.96      ( k1_lattice3(X0_46) != k1_lattice3(sK0)
% 1.08/0.96      | k1_lattices(k1_lattice3(X0_46),sK1,sK2) != sK2
% 1.08/0.96      | m1_subset_1(sK2,u1_struct_0(k1_lattice3(X0_46))) != iProver_top
% 1.08/0.96      | m1_subset_1(sK1,u1_struct_0(k1_lattice3(X0_46))) != iProver_top
% 1.08/0.96      | sP1_iProver_split != iProver_top ),
% 1.08/0.96      inference(predicate_to_equality,[status(thm)],[c_406]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_447,plain,
% 1.08/0.96      ( k1_lattice3(sK0) != k1_lattice3(sK0)
% 1.08/0.96      | k1_lattices(k1_lattice3(sK0),sK1,sK2) != sK2
% 1.08/0.96      | m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0))) != iProver_top
% 1.08/0.96      | m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0))) != iProver_top
% 1.08/0.96      | sP1_iProver_split != iProver_top ),
% 1.08/0.96      inference(instantiation,[status(thm)],[c_445]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_411,plain,( X0_45 = X0_45 ),theory(equality) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_652,plain,
% 1.08/0.96      ( k1_lattice3(sK0) = k1_lattice3(sK0) ),
% 1.08/0.96      inference(instantiation,[status(thm)],[c_411]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_836,plain,
% 1.08/0.96      ( k1_lattices(k1_lattice3(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2)
% 1.08/0.96      | m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0))) != iProver_top ),
% 1.08/0.96      inference(instantiation,[status(thm)],[c_825]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_924,plain,
% 1.08/0.96      ( k1_lattices(k1_lattice3(sK0),sK1,sK2) != k2_xboole_0(sK1,sK2)
% 1.08/0.96      | k1_lattices(k1_lattice3(sK0),sK1,sK2) = sK2
% 1.08/0.96      | sK2 != k2_xboole_0(sK1,sK2) ),
% 1.08/0.96      inference(instantiation,[status(thm)],[c_922]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_1141,plain,
% 1.08/0.96      ( sP1_iProver_split != iProver_top ),
% 1.08/0.96      inference(global_propositional_subsumption,
% 1.08/0.96                [status(thm)],
% 1.08/0.96                [c_570,c_12,c_13,c_11,c_14,c_442,c_447,c_652,c_663,c_836,
% 1.08/0.96                 c_840,c_924]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_407,plain,
% 1.08/0.96      ( sP1_iProver_split | sP0_iProver_split ),
% 1.08/0.96      inference(splitting,
% 1.08/0.96                [splitting(split),new_symbols(definition,[])],
% 1.08/0.96                [c_397]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(c_444,plain,
% 1.08/0.96      ( sP1_iProver_split = iProver_top
% 1.08/0.96      | sP0_iProver_split = iProver_top ),
% 1.08/0.96      inference(predicate_to_equality,[status(thm)],[c_407]) ).
% 1.08/0.96  
% 1.08/0.96  cnf(contradiction,plain,
% 1.08/0.96      ( $false ),
% 1.08/0.96      inference(minisat,[status(thm)],[c_1316,c_1141,c_444]) ).
% 1.08/0.96  
% 1.08/0.96  
% 1.08/0.96  % SZS output end CNFRefutation for theBenchmark.p
% 1.08/0.96  
% 1.08/0.96  ------                               Statistics
% 1.08/0.96  
% 1.08/0.96  ------ General
% 1.08/0.96  
% 1.08/0.96  abstr_ref_over_cycles:                  0
% 1.08/0.96  abstr_ref_under_cycles:                 0
% 1.08/0.96  gc_basic_clause_elim:                   0
% 1.08/0.96  forced_gc_time:                         0
% 1.08/0.96  parsing_time:                           0.009
% 1.08/0.96  unif_index_cands_time:                  0.
% 1.08/0.96  unif_index_add_time:                    0.
% 1.08/0.96  orderings_time:                         0.
% 1.08/0.96  out_proof_time:                         0.011
% 1.08/0.96  total_time:                             0.076
% 1.08/0.96  num_of_symbols:                         53
% 1.08/0.96  num_of_terms:                           1044
% 1.08/0.96  
% 1.08/0.96  ------ Preprocessing
% 1.08/0.96  
% 1.08/0.96  num_of_splits:                          2
% 1.08/0.96  num_of_split_atoms:                     2
% 1.08/0.96  num_of_reused_defs:                     0
% 1.08/0.96  num_eq_ax_congr_red:                    18
% 1.08/0.96  num_of_sem_filtered_clauses:            5
% 1.08/0.96  num_of_subtypes:                        5
% 1.08/0.96  monotx_restored_types:                  0
% 1.08/0.96  sat_num_of_epr_types:                   0
% 1.08/0.96  sat_num_of_non_cyclic_types:            0
% 1.08/0.96  sat_guarded_non_collapsed_types:        0
% 1.08/0.96  num_pure_diseq_elim:                    0
% 1.08/0.96  simp_replaced_by:                       0
% 1.08/0.96  res_preprocessed:                       62
% 1.08/0.96  prep_upred:                             0
% 1.08/0.96  prep_unflattend:                        12
% 1.08/0.96  smt_new_axioms:                         0
% 1.08/0.96  pred_elim_cands:                        1
% 1.08/0.96  pred_elim:                              5
% 1.08/0.96  pred_elim_cl:                           5
% 1.08/0.96  pred_elim_cycles:                       7
% 1.08/0.96  merged_defs:                            2
% 1.08/0.96  merged_defs_ncl:                        0
% 1.08/0.96  bin_hyper_res:                          2
% 1.08/0.96  prep_cycles:                            4
% 1.08/0.96  pred_elim_time:                         0.003
% 1.08/0.96  splitting_time:                         0.
% 1.08/0.96  sem_filter_time:                        0.
% 1.08/0.96  monotx_time:                            0.
% 1.08/0.96  subtype_inf_time:                       0.
% 1.08/0.96  
% 1.08/0.96  ------ Problem properties
% 1.08/0.96  
% 1.08/0.96  clauses:                                10
% 1.08/0.96  conjectures:                            2
% 1.08/0.96  epr:                                    1
% 1.08/0.96  horn:                                   8
% 1.08/0.96  ground:                                 3
% 1.08/0.96  unary:                                  3
% 1.08/0.96  binary:                                 3
% 1.08/0.96  lits:                                   25
% 1.08/0.96  lits_eq:                                11
% 1.08/0.96  fd_pure:                                0
% 1.08/0.96  fd_pseudo:                              0
% 1.08/0.96  fd_cond:                                0
% 1.08/0.96  fd_pseudo_cond:                         0
% 1.08/0.96  ac_symbols:                             0
% 1.08/0.96  
% 1.08/0.96  ------ Propositional Solver
% 1.08/0.96  
% 1.08/0.96  prop_solver_calls:                      27
% 1.08/0.96  prop_fast_solver_calls:                 385
% 1.08/0.96  smt_solver_calls:                       0
% 1.08/0.96  smt_fast_solver_calls:                  0
% 1.08/0.96  prop_num_of_clauses:                    396
% 1.08/0.96  prop_preprocess_simplified:             1862
% 1.08/0.96  prop_fo_subsumed:                       10
% 1.08/0.96  prop_solver_time:                       0.
% 1.08/0.96  smt_solver_time:                        0.
% 1.08/0.96  smt_fast_solver_time:                   0.
% 1.08/0.96  prop_fast_solver_time:                  0.
% 1.08/0.96  prop_unsat_core_time:                   0.
% 1.08/0.96  
% 1.08/0.96  ------ QBF
% 1.08/0.96  
% 1.08/0.96  qbf_q_res:                              0
% 1.08/0.96  qbf_num_tautologies:                    0
% 1.08/0.96  qbf_prep_cycles:                        0
% 1.08/0.96  
% 1.08/0.96  ------ BMC1
% 1.08/0.96  
% 1.08/0.96  bmc1_current_bound:                     -1
% 1.08/0.96  bmc1_last_solved_bound:                 -1
% 1.08/0.96  bmc1_unsat_core_size:                   -1
% 1.08/0.96  bmc1_unsat_core_parents_size:           -1
% 1.08/0.96  bmc1_merge_next_fun:                    0
% 1.08/0.96  bmc1_unsat_core_clauses_time:           0.
% 1.08/0.96  
% 1.08/0.96  ------ Instantiation
% 1.08/0.96  
% 1.08/0.96  inst_num_of_clauses:                    136
% 1.08/0.96  inst_num_in_passive:                    2
% 1.08/0.96  inst_num_in_active:                     101
% 1.08/0.96  inst_num_in_unprocessed:                33
% 1.08/0.96  inst_num_of_loops:                      120
% 1.08/0.96  inst_num_of_learning_restarts:          0
% 1.08/0.96  inst_num_moves_active_passive:          13
% 1.08/0.96  inst_lit_activity:                      0
% 1.08/0.96  inst_lit_activity_moves:                0
% 1.08/0.96  inst_num_tautologies:                   0
% 1.08/0.96  inst_num_prop_implied:                  0
% 1.08/0.96  inst_num_existing_simplified:           0
% 1.08/0.96  inst_num_eq_res_simplified:             0
% 1.08/0.96  inst_num_child_elim:                    0
% 1.08/0.96  inst_num_of_dismatching_blockings:      22
% 1.08/0.96  inst_num_of_non_proper_insts:           133
% 1.08/0.96  inst_num_of_duplicates:                 0
% 1.08/0.96  inst_inst_num_from_inst_to_res:         0
% 1.08/0.96  inst_dismatching_checking_time:         0.
% 1.08/0.96  
% 1.08/0.96  ------ Resolution
% 1.08/0.96  
% 1.08/0.96  res_num_of_clauses:                     0
% 1.08/0.96  res_num_in_passive:                     0
% 1.08/0.96  res_num_in_active:                      0
% 1.08/0.96  res_num_of_loops:                       66
% 1.08/0.96  res_forward_subset_subsumed:            30
% 1.08/0.96  res_backward_subset_subsumed:           0
% 1.08/0.96  res_forward_subsumed:                   0
% 1.08/0.96  res_backward_subsumed:                  0
% 1.08/0.96  res_forward_subsumption_resolution:     0
% 1.08/0.96  res_backward_subsumption_resolution:    0
% 1.08/0.96  res_clause_to_clause_subsumption:       35
% 1.08/0.96  res_orphan_elimination:                 0
% 1.08/0.96  res_tautology_del:                      31
% 1.08/0.96  res_num_eq_res_simplified:              0
% 1.08/0.96  res_num_sel_changes:                    0
% 1.08/0.96  res_moves_from_active_to_pass:          0
% 1.08/0.96  
% 1.08/0.96  ------ Superposition
% 1.08/0.96  
% 1.08/0.96  sup_time_total:                         0.
% 1.08/0.96  sup_time_generating:                    0.
% 1.08/0.96  sup_time_sim_full:                      0.
% 1.08/0.96  sup_time_sim_immed:                     0.
% 1.08/0.96  
% 1.08/0.96  sup_num_of_clauses:                     23
% 1.08/0.96  sup_num_in_active:                      21
% 1.08/0.96  sup_num_in_passive:                     2
% 1.08/0.96  sup_num_of_loops:                       22
% 1.08/0.96  sup_fw_superposition:                   14
% 1.08/0.96  sup_bw_superposition:                   1
% 1.08/0.96  sup_immediate_simplified:               1
% 1.08/0.96  sup_given_eliminated:                   0
% 1.08/0.96  comparisons_done:                       0
% 1.08/0.96  comparisons_avoided:                    0
% 1.08/0.96  
% 1.08/0.96  ------ Simplifications
% 1.08/0.96  
% 1.08/0.96  
% 1.08/0.96  sim_fw_subset_subsumed:                 0
% 1.08/0.96  sim_bw_subset_subsumed:                 0
% 1.08/0.96  sim_fw_subsumed:                        0
% 1.08/0.96  sim_bw_subsumed:                        0
% 1.08/0.96  sim_fw_subsumption_res:                 0
% 1.08/0.96  sim_bw_subsumption_res:                 0
% 1.08/0.96  sim_tautology_del:                      0
% 1.08/0.96  sim_eq_tautology_del:                   1
% 1.08/0.96  sim_eq_res_simp:                        0
% 1.08/0.96  sim_fw_demodulated:                     1
% 1.08/0.96  sim_bw_demodulated:                     2
% 1.08/0.96  sim_light_normalised:                   0
% 1.08/0.96  sim_joinable_taut:                      0
% 1.08/0.96  sim_joinable_simp:                      0
% 1.08/0.96  sim_ac_normalised:                      0
% 1.08/0.96  sim_smt_subsumption:                    0
% 1.08/0.96  
%------------------------------------------------------------------------------
