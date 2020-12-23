%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:43:07 EST 2020

% Result     : Theorem 7.98s
% Output     : CNFRefutation 7.98s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 132 expanded)
%              Number of clauses        :   51 (  57 expanded)
%              Number of leaves         :   14 (  31 expanded)
%              Depth                    :   13
%              Number of atoms          :  191 ( 335 expanded)
%              Number of equality atoms :   85 ( 109 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))
          & v1_relat_1(X1) )
     => ( ~ r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(X0,sK1)))
        & v1_relat_1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(sK0,X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ~ r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1)))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f18,f17])).

fof(f29,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k6_subset_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f27,f26])).

fof(f30,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k2_xboole_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k2_xboole_0(X0,X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_subset_1(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f25,f26])).

fof(f31,plain,(
    ~ r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k6_subset_1(X1,X0)) ),
    inference(definition_unfolding,[],[f24,f26])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f15])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f35,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f21])).

fof(f22,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f36,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f20])).

cnf(c_10,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_341,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k6_subset_1(X0,X1)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_345,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k6_subset_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_9,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_342,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_344,plain,
    ( k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k2_xboole_0(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_812,plain,
    ( k2_xboole_0(k2_relat_1(sK1),k2_relat_1(X0)) = k2_relat_1(k2_xboole_0(sK1,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_342,c_344])).

cnf(c_966,plain,
    ( k2_xboole_0(k2_relat_1(sK1),k2_relat_1(k6_subset_1(X0,X1))) = k2_relat_1(k2_xboole_0(sK1,k6_subset_1(X0,X1)))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_345,c_812])).

cnf(c_8462,plain,
    ( k2_xboole_0(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,X0))) = k2_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,X0))) ),
    inference(superposition,[status(thm)],[c_341,c_966])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
    | r1_tarski(k6_subset_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_346,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
    | r1_tarski(k6_subset_1(X0,X1),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_8687,plain,
    ( r1_tarski(X0,k2_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,X1)))) != iProver_top
    | r1_tarski(k6_subset_1(X0,k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_8462,c_346])).

cnf(c_8,negated_conjecture,
    ( ~ r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_343,plain,
    ( r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_32762,plain,
    ( r1_tarski(k2_relat_1(sK0),k2_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8687,c_343])).

cnf(c_4,plain,
    ( k2_xboole_0(X0,k6_subset_1(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_32766,plain,
    ( r1_tarski(k2_relat_1(sK0),k2_relat_1(k2_xboole_0(sK1,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_32762,c_4])).

cnf(c_177,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_26167,plain,
    ( k2_relat_1(k2_xboole_0(sK1,sK0)) = k2_relat_1(k2_xboole_0(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_177])).

cnf(c_179,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_485,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(sK0),X2)
    | X2 != X1
    | k2_relat_1(sK0) != X0 ),
    inference(instantiation,[status(thm)],[c_179])).

cnf(c_795,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),X0)
    | r1_tarski(k2_relat_1(sK0),X1)
    | X1 != X0
    | k2_relat_1(sK0) != k2_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_485])).

cnf(c_1184,plain,
    ( r1_tarski(k2_relat_1(sK0),X0)
    | ~ r1_tarski(k2_relat_1(sK0),k2_xboole_0(X1,X2))
    | X0 != k2_xboole_0(X1,X2)
    | k2_relat_1(sK0) != k2_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_795])).

cnf(c_2348,plain,
    ( r1_tarski(k2_relat_1(sK0),X0)
    | ~ r1_tarski(k2_relat_1(sK0),k2_xboole_0(k2_relat_1(sK1),k2_relat_1(sK0)))
    | X0 != k2_xboole_0(k2_relat_1(sK1),k2_relat_1(sK0))
    | k2_relat_1(sK0) != k2_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_1184])).

cnf(c_24281,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_xboole_0(k2_relat_1(sK1),k2_relat_1(sK0)))
    | r1_tarski(k2_relat_1(sK0),k2_relat_1(k2_xboole_0(sK1,sK0)))
    | k2_relat_1(k2_xboole_0(sK1,sK0)) != k2_xboole_0(k2_relat_1(sK1),k2_relat_1(sK0))
    | k2_relat_1(sK0) != k2_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_2348])).

cnf(c_24282,plain,
    ( k2_relat_1(k2_xboole_0(sK1,sK0)) != k2_xboole_0(k2_relat_1(sK1),k2_relat_1(sK0))
    | k2_relat_1(sK0) != k2_relat_1(sK0)
    | r1_tarski(k2_relat_1(sK0),k2_xboole_0(k2_relat_1(sK1),k2_relat_1(sK0))) != iProver_top
    | r1_tarski(k2_relat_1(sK0),k2_relat_1(k2_xboole_0(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24281])).

cnf(c_178,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1345,plain,
    ( X0 != X1
    | k2_relat_1(X2) != X1
    | k2_relat_1(X2) = X0 ),
    inference(instantiation,[status(thm)],[c_178])).

cnf(c_2435,plain,
    ( X0 != k2_relat_1(X1)
    | k2_relat_1(X1) = X0
    | k2_relat_1(X1) != k2_relat_1(X1) ),
    inference(instantiation,[status(thm)],[c_1345])).

cnf(c_6314,plain,
    ( k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) != k2_relat_1(k2_xboole_0(X0,X1))
    | k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1))
    | k2_relat_1(k2_xboole_0(X0,X1)) != k2_relat_1(k2_xboole_0(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_2435])).

cnf(c_15357,plain,
    ( k2_xboole_0(k2_relat_1(X0),k2_relat_1(sK0)) != k2_relat_1(k2_xboole_0(X0,sK0))
    | k2_relat_1(k2_xboole_0(X0,sK0)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(sK0))
    | k2_relat_1(k2_xboole_0(X0,sK0)) != k2_relat_1(k2_xboole_0(X0,sK0)) ),
    inference(instantiation,[status(thm)],[c_6314])).

cnf(c_24279,plain,
    ( k2_xboole_0(k2_relat_1(sK1),k2_relat_1(sK0)) != k2_relat_1(k2_xboole_0(sK1,sK0))
    | k2_relat_1(k2_xboole_0(sK1,sK0)) = k2_xboole_0(k2_relat_1(sK1),k2_relat_1(sK0))
    | k2_relat_1(k2_xboole_0(sK1,sK0)) != k2_relat_1(k2_xboole_0(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_15357])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_736,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),X0)
    | r1_tarski(k2_relat_1(sK0),k2_xboole_0(X1,X0)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1055,plain,
    ( r1_tarski(k2_relat_1(sK0),k2_xboole_0(X0,k2_relat_1(sK0)))
    | ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_736])).

cnf(c_1575,plain,
    ( r1_tarski(k2_relat_1(sK0),k2_xboole_0(k2_relat_1(sK1),k2_relat_1(sK0)))
    | ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_1055])).

cnf(c_1577,plain,
    ( r1_tarski(k2_relat_1(sK0),k2_xboole_0(k2_relat_1(sK1),k2_relat_1(sK0))) = iProver_top
    | r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1575])).

cnf(c_818,plain,
    ( k2_xboole_0(k2_relat_1(sK1),k2_relat_1(sK0)) = k2_relat_1(k2_xboole_0(sK1,sK0))
    | v1_relat_1(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_812])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_635,plain,
    ( r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_636,plain,
    ( r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_635])).

cnf(c_183,plain,
    ( X0 != X1
    | k2_relat_1(X0) = k2_relat_1(X1) ),
    theory(equality)).

cnf(c_188,plain,
    ( k2_relat_1(sK0) = k2_relat_1(sK0)
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_183])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_32,plain,
    ( ~ r1_tarski(sK0,sK0)
    | sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_28,plain,
    ( r1_tarski(sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_11,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_32766,c_26167,c_24282,c_24279,c_1577,c_818,c_636,c_188,c_32,c_28,c_11])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 09:30:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.98/1.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.98/1.48  
% 7.98/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.98/1.48  
% 7.98/1.48  ------  iProver source info
% 7.98/1.48  
% 7.98/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.98/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.98/1.48  git: non_committed_changes: false
% 7.98/1.48  git: last_make_outside_of_git: false
% 7.98/1.48  
% 7.98/1.48  ------ 
% 7.98/1.48  
% 7.98/1.48  ------ Input Options
% 7.98/1.48  
% 7.98/1.48  --out_options                           all
% 7.98/1.48  --tptp_safe_out                         true
% 7.98/1.48  --problem_path                          ""
% 7.98/1.48  --include_path                          ""
% 7.98/1.48  --clausifier                            res/vclausify_rel
% 7.98/1.48  --clausifier_options                    ""
% 7.98/1.48  --stdin                                 false
% 7.98/1.48  --stats_out                             all
% 7.98/1.48  
% 7.98/1.48  ------ General Options
% 7.98/1.48  
% 7.98/1.48  --fof                                   false
% 7.98/1.48  --time_out_real                         305.
% 7.98/1.48  --time_out_virtual                      -1.
% 7.98/1.48  --symbol_type_check                     false
% 7.98/1.48  --clausify_out                          false
% 7.98/1.48  --sig_cnt_out                           false
% 7.98/1.48  --trig_cnt_out                          false
% 7.98/1.48  --trig_cnt_out_tolerance                1.
% 7.98/1.48  --trig_cnt_out_sk_spl                   false
% 7.98/1.48  --abstr_cl_out                          false
% 7.98/1.48  
% 7.98/1.48  ------ Global Options
% 7.98/1.48  
% 7.98/1.48  --schedule                              default
% 7.98/1.48  --add_important_lit                     false
% 7.98/1.48  --prop_solver_per_cl                    1000
% 7.98/1.48  --min_unsat_core                        false
% 7.98/1.48  --soft_assumptions                      false
% 7.98/1.48  --soft_lemma_size                       3
% 7.98/1.48  --prop_impl_unit_size                   0
% 7.98/1.48  --prop_impl_unit                        []
% 7.98/1.48  --share_sel_clauses                     true
% 7.98/1.48  --reset_solvers                         false
% 7.98/1.48  --bc_imp_inh                            [conj_cone]
% 7.98/1.48  --conj_cone_tolerance                   3.
% 7.98/1.48  --extra_neg_conj                        none
% 7.98/1.48  --large_theory_mode                     true
% 7.98/1.48  --prolific_symb_bound                   200
% 7.98/1.48  --lt_threshold                          2000
% 7.98/1.48  --clause_weak_htbl                      true
% 7.98/1.48  --gc_record_bc_elim                     false
% 7.98/1.48  
% 7.98/1.48  ------ Preprocessing Options
% 7.98/1.48  
% 7.98/1.48  --preprocessing_flag                    true
% 7.98/1.48  --time_out_prep_mult                    0.1
% 7.98/1.48  --splitting_mode                        input
% 7.98/1.48  --splitting_grd                         true
% 7.98/1.48  --splitting_cvd                         false
% 7.98/1.48  --splitting_cvd_svl                     false
% 7.98/1.48  --splitting_nvd                         32
% 7.98/1.48  --sub_typing                            true
% 7.98/1.48  --prep_gs_sim                           true
% 7.98/1.48  --prep_unflatten                        true
% 7.98/1.48  --prep_res_sim                          true
% 7.98/1.48  --prep_upred                            true
% 7.98/1.48  --prep_sem_filter                       exhaustive
% 7.98/1.48  --prep_sem_filter_out                   false
% 7.98/1.48  --pred_elim                             true
% 7.98/1.48  --res_sim_input                         true
% 7.98/1.48  --eq_ax_congr_red                       true
% 7.98/1.48  --pure_diseq_elim                       true
% 7.98/1.48  --brand_transform                       false
% 7.98/1.48  --non_eq_to_eq                          false
% 7.98/1.48  --prep_def_merge                        true
% 7.98/1.48  --prep_def_merge_prop_impl              false
% 7.98/1.48  --prep_def_merge_mbd                    true
% 7.98/1.48  --prep_def_merge_tr_red                 false
% 7.98/1.48  --prep_def_merge_tr_cl                  false
% 7.98/1.48  --smt_preprocessing                     true
% 7.98/1.48  --smt_ac_axioms                         fast
% 7.98/1.48  --preprocessed_out                      false
% 7.98/1.48  --preprocessed_stats                    false
% 7.98/1.48  
% 7.98/1.48  ------ Abstraction refinement Options
% 7.98/1.48  
% 7.98/1.48  --abstr_ref                             []
% 7.98/1.48  --abstr_ref_prep                        false
% 7.98/1.48  --abstr_ref_until_sat                   false
% 7.98/1.48  --abstr_ref_sig_restrict                funpre
% 7.98/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.98/1.48  --abstr_ref_under                       []
% 7.98/1.48  
% 7.98/1.48  ------ SAT Options
% 7.98/1.48  
% 7.98/1.48  --sat_mode                              false
% 7.98/1.48  --sat_fm_restart_options                ""
% 7.98/1.48  --sat_gr_def                            false
% 7.98/1.48  --sat_epr_types                         true
% 7.98/1.48  --sat_non_cyclic_types                  false
% 7.98/1.48  --sat_finite_models                     false
% 7.98/1.48  --sat_fm_lemmas                         false
% 7.98/1.48  --sat_fm_prep                           false
% 7.98/1.48  --sat_fm_uc_incr                        true
% 7.98/1.48  --sat_out_model                         small
% 7.98/1.48  --sat_out_clauses                       false
% 7.98/1.48  
% 7.98/1.48  ------ QBF Options
% 7.98/1.48  
% 7.98/1.48  --qbf_mode                              false
% 7.98/1.48  --qbf_elim_univ                         false
% 7.98/1.48  --qbf_dom_inst                          none
% 7.98/1.48  --qbf_dom_pre_inst                      false
% 7.98/1.48  --qbf_sk_in                             false
% 7.98/1.48  --qbf_pred_elim                         true
% 7.98/1.48  --qbf_split                             512
% 7.98/1.48  
% 7.98/1.48  ------ BMC1 Options
% 7.98/1.48  
% 7.98/1.48  --bmc1_incremental                      false
% 7.98/1.48  --bmc1_axioms                           reachable_all
% 7.98/1.48  --bmc1_min_bound                        0
% 7.98/1.48  --bmc1_max_bound                        -1
% 7.98/1.48  --bmc1_max_bound_default                -1
% 7.98/1.48  --bmc1_symbol_reachability              true
% 7.98/1.48  --bmc1_property_lemmas                  false
% 7.98/1.48  --bmc1_k_induction                      false
% 7.98/1.48  --bmc1_non_equiv_states                 false
% 7.98/1.48  --bmc1_deadlock                         false
% 7.98/1.48  --bmc1_ucm                              false
% 7.98/1.48  --bmc1_add_unsat_core                   none
% 7.98/1.48  --bmc1_unsat_core_children              false
% 7.98/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.98/1.48  --bmc1_out_stat                         full
% 7.98/1.48  --bmc1_ground_init                      false
% 7.98/1.48  --bmc1_pre_inst_next_state              false
% 7.98/1.48  --bmc1_pre_inst_state                   false
% 7.98/1.48  --bmc1_pre_inst_reach_state             false
% 7.98/1.48  --bmc1_out_unsat_core                   false
% 7.98/1.48  --bmc1_aig_witness_out                  false
% 7.98/1.48  --bmc1_verbose                          false
% 7.98/1.48  --bmc1_dump_clauses_tptp                false
% 7.98/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.98/1.48  --bmc1_dump_file                        -
% 7.98/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.98/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.98/1.48  --bmc1_ucm_extend_mode                  1
% 7.98/1.48  --bmc1_ucm_init_mode                    2
% 7.98/1.48  --bmc1_ucm_cone_mode                    none
% 7.98/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.98/1.48  --bmc1_ucm_relax_model                  4
% 7.98/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.98/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.98/1.48  --bmc1_ucm_layered_model                none
% 7.98/1.48  --bmc1_ucm_max_lemma_size               10
% 7.98/1.48  
% 7.98/1.48  ------ AIG Options
% 7.98/1.48  
% 7.98/1.48  --aig_mode                              false
% 7.98/1.48  
% 7.98/1.48  ------ Instantiation Options
% 7.98/1.48  
% 7.98/1.48  --instantiation_flag                    true
% 7.98/1.48  --inst_sos_flag                         true
% 7.98/1.48  --inst_sos_phase                        true
% 7.98/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.98/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.98/1.48  --inst_lit_sel_side                     num_symb
% 7.98/1.48  --inst_solver_per_active                1400
% 7.98/1.48  --inst_solver_calls_frac                1.
% 7.98/1.48  --inst_passive_queue_type               priority_queues
% 7.98/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.98/1.48  --inst_passive_queues_freq              [25;2]
% 7.98/1.48  --inst_dismatching                      true
% 7.98/1.48  --inst_eager_unprocessed_to_passive     true
% 7.98/1.48  --inst_prop_sim_given                   true
% 7.98/1.48  --inst_prop_sim_new                     false
% 7.98/1.48  --inst_subs_new                         false
% 7.98/1.48  --inst_eq_res_simp                      false
% 7.98/1.48  --inst_subs_given                       false
% 7.98/1.48  --inst_orphan_elimination               true
% 7.98/1.48  --inst_learning_loop_flag               true
% 7.98/1.48  --inst_learning_start                   3000
% 7.98/1.48  --inst_learning_factor                  2
% 7.98/1.48  --inst_start_prop_sim_after_learn       3
% 7.98/1.48  --inst_sel_renew                        solver
% 7.98/1.48  --inst_lit_activity_flag                true
% 7.98/1.48  --inst_restr_to_given                   false
% 7.98/1.48  --inst_activity_threshold               500
% 7.98/1.48  --inst_out_proof                        true
% 7.98/1.48  
% 7.98/1.48  ------ Resolution Options
% 7.98/1.48  
% 7.98/1.48  --resolution_flag                       true
% 7.98/1.48  --res_lit_sel                           adaptive
% 7.98/1.48  --res_lit_sel_side                      none
% 7.98/1.48  --res_ordering                          kbo
% 7.98/1.48  --res_to_prop_solver                    active
% 7.98/1.48  --res_prop_simpl_new                    false
% 7.98/1.48  --res_prop_simpl_given                  true
% 7.98/1.48  --res_passive_queue_type                priority_queues
% 7.98/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.98/1.48  --res_passive_queues_freq               [15;5]
% 7.98/1.48  --res_forward_subs                      full
% 7.98/1.48  --res_backward_subs                     full
% 7.98/1.48  --res_forward_subs_resolution           true
% 7.98/1.48  --res_backward_subs_resolution          true
% 7.98/1.48  --res_orphan_elimination                true
% 7.98/1.48  --res_time_limit                        2.
% 7.98/1.48  --res_out_proof                         true
% 7.98/1.48  
% 7.98/1.48  ------ Superposition Options
% 7.98/1.48  
% 7.98/1.48  --superposition_flag                    true
% 7.98/1.48  --sup_passive_queue_type                priority_queues
% 7.98/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.98/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.98/1.48  --demod_completeness_check              fast
% 7.98/1.48  --demod_use_ground                      true
% 7.98/1.48  --sup_to_prop_solver                    passive
% 7.98/1.48  --sup_prop_simpl_new                    true
% 7.98/1.48  --sup_prop_simpl_given                  true
% 7.98/1.48  --sup_fun_splitting                     true
% 7.98/1.48  --sup_smt_interval                      50000
% 7.98/1.48  
% 7.98/1.48  ------ Superposition Simplification Setup
% 7.98/1.48  
% 7.98/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.98/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.98/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.98/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.98/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.98/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.98/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.98/1.48  --sup_immed_triv                        [TrivRules]
% 7.98/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.98/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.98/1.48  --sup_immed_bw_main                     []
% 7.98/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.98/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.98/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.98/1.48  --sup_input_bw                          []
% 7.98/1.48  
% 7.98/1.48  ------ Combination Options
% 7.98/1.48  
% 7.98/1.48  --comb_res_mult                         3
% 7.98/1.48  --comb_sup_mult                         2
% 7.98/1.48  --comb_inst_mult                        10
% 7.98/1.48  
% 7.98/1.48  ------ Debug Options
% 7.98/1.48  
% 7.98/1.48  --dbg_backtrace                         false
% 7.98/1.48  --dbg_dump_prop_clauses                 false
% 7.98/1.48  --dbg_dump_prop_clauses_file            -
% 7.98/1.48  --dbg_out_stat                          false
% 7.98/1.48  ------ Parsing...
% 7.98/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.98/1.48  
% 7.98/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.98/1.48  
% 7.98/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.98/1.48  
% 7.98/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.98/1.48  ------ Proving...
% 7.98/1.48  ------ Problem Properties 
% 7.98/1.48  
% 7.98/1.48  
% 7.98/1.48  clauses                                 10
% 7.98/1.48  conjectures                             3
% 7.98/1.48  EPR                                     4
% 7.98/1.48  Horn                                    10
% 7.98/1.48  unary                                   5
% 7.98/1.48  binary                                  3
% 7.98/1.48  lits                                    17
% 7.98/1.48  lits eq                                 3
% 7.98/1.48  fd_pure                                 0
% 7.98/1.48  fd_pseudo                               0
% 7.98/1.48  fd_cond                                 0
% 7.98/1.48  fd_pseudo_cond                          1
% 7.98/1.48  AC symbols                              0
% 7.98/1.48  
% 7.98/1.48  ------ Schedule dynamic 5 is on 
% 7.98/1.48  
% 7.98/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.98/1.48  
% 7.98/1.48  
% 7.98/1.48  ------ 
% 7.98/1.48  Current options:
% 7.98/1.48  ------ 
% 7.98/1.48  
% 7.98/1.48  ------ Input Options
% 7.98/1.48  
% 7.98/1.48  --out_options                           all
% 7.98/1.48  --tptp_safe_out                         true
% 7.98/1.48  --problem_path                          ""
% 7.98/1.48  --include_path                          ""
% 7.98/1.48  --clausifier                            res/vclausify_rel
% 7.98/1.48  --clausifier_options                    ""
% 7.98/1.48  --stdin                                 false
% 7.98/1.48  --stats_out                             all
% 7.98/1.48  
% 7.98/1.48  ------ General Options
% 7.98/1.48  
% 7.98/1.48  --fof                                   false
% 7.98/1.48  --time_out_real                         305.
% 7.98/1.48  --time_out_virtual                      -1.
% 7.98/1.48  --symbol_type_check                     false
% 7.98/1.48  --clausify_out                          false
% 7.98/1.48  --sig_cnt_out                           false
% 7.98/1.48  --trig_cnt_out                          false
% 7.98/1.48  --trig_cnt_out_tolerance                1.
% 7.98/1.48  --trig_cnt_out_sk_spl                   false
% 7.98/1.48  --abstr_cl_out                          false
% 7.98/1.48  
% 7.98/1.48  ------ Global Options
% 7.98/1.48  
% 7.98/1.48  --schedule                              default
% 7.98/1.48  --add_important_lit                     false
% 7.98/1.48  --prop_solver_per_cl                    1000
% 7.98/1.48  --min_unsat_core                        false
% 7.98/1.48  --soft_assumptions                      false
% 7.98/1.48  --soft_lemma_size                       3
% 7.98/1.48  --prop_impl_unit_size                   0
% 7.98/1.48  --prop_impl_unit                        []
% 7.98/1.48  --share_sel_clauses                     true
% 7.98/1.48  --reset_solvers                         false
% 7.98/1.48  --bc_imp_inh                            [conj_cone]
% 7.98/1.48  --conj_cone_tolerance                   3.
% 7.98/1.48  --extra_neg_conj                        none
% 7.98/1.48  --large_theory_mode                     true
% 7.98/1.48  --prolific_symb_bound                   200
% 7.98/1.48  --lt_threshold                          2000
% 7.98/1.48  --clause_weak_htbl                      true
% 7.98/1.48  --gc_record_bc_elim                     false
% 7.98/1.48  
% 7.98/1.48  ------ Preprocessing Options
% 7.98/1.48  
% 7.98/1.48  --preprocessing_flag                    true
% 7.98/1.48  --time_out_prep_mult                    0.1
% 7.98/1.48  --splitting_mode                        input
% 7.98/1.48  --splitting_grd                         true
% 7.98/1.48  --splitting_cvd                         false
% 7.98/1.48  --splitting_cvd_svl                     false
% 7.98/1.48  --splitting_nvd                         32
% 7.98/1.48  --sub_typing                            true
% 7.98/1.48  --prep_gs_sim                           true
% 7.98/1.48  --prep_unflatten                        true
% 7.98/1.48  --prep_res_sim                          true
% 7.98/1.48  --prep_upred                            true
% 7.98/1.48  --prep_sem_filter                       exhaustive
% 7.98/1.48  --prep_sem_filter_out                   false
% 7.98/1.48  --pred_elim                             true
% 7.98/1.48  --res_sim_input                         true
% 7.98/1.48  --eq_ax_congr_red                       true
% 7.98/1.48  --pure_diseq_elim                       true
% 7.98/1.48  --brand_transform                       false
% 7.98/1.48  --non_eq_to_eq                          false
% 7.98/1.48  --prep_def_merge                        true
% 7.98/1.48  --prep_def_merge_prop_impl              false
% 7.98/1.48  --prep_def_merge_mbd                    true
% 7.98/1.48  --prep_def_merge_tr_red                 false
% 7.98/1.48  --prep_def_merge_tr_cl                  false
% 7.98/1.48  --smt_preprocessing                     true
% 7.98/1.48  --smt_ac_axioms                         fast
% 7.98/1.48  --preprocessed_out                      false
% 7.98/1.48  --preprocessed_stats                    false
% 7.98/1.48  
% 7.98/1.48  ------ Abstraction refinement Options
% 7.98/1.48  
% 7.98/1.48  --abstr_ref                             []
% 7.98/1.48  --abstr_ref_prep                        false
% 7.98/1.48  --abstr_ref_until_sat                   false
% 7.98/1.48  --abstr_ref_sig_restrict                funpre
% 7.98/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.98/1.48  --abstr_ref_under                       []
% 7.98/1.48  
% 7.98/1.48  ------ SAT Options
% 7.98/1.48  
% 7.98/1.48  --sat_mode                              false
% 7.98/1.48  --sat_fm_restart_options                ""
% 7.98/1.48  --sat_gr_def                            false
% 7.98/1.48  --sat_epr_types                         true
% 7.98/1.48  --sat_non_cyclic_types                  false
% 7.98/1.48  --sat_finite_models                     false
% 7.98/1.48  --sat_fm_lemmas                         false
% 7.98/1.48  --sat_fm_prep                           false
% 7.98/1.48  --sat_fm_uc_incr                        true
% 7.98/1.48  --sat_out_model                         small
% 7.98/1.48  --sat_out_clauses                       false
% 7.98/1.48  
% 7.98/1.48  ------ QBF Options
% 7.98/1.48  
% 7.98/1.48  --qbf_mode                              false
% 7.98/1.48  --qbf_elim_univ                         false
% 7.98/1.48  --qbf_dom_inst                          none
% 7.98/1.48  --qbf_dom_pre_inst                      false
% 7.98/1.48  --qbf_sk_in                             false
% 7.98/1.48  --qbf_pred_elim                         true
% 7.98/1.48  --qbf_split                             512
% 7.98/1.48  
% 7.98/1.48  ------ BMC1 Options
% 7.98/1.48  
% 7.98/1.48  --bmc1_incremental                      false
% 7.98/1.48  --bmc1_axioms                           reachable_all
% 7.98/1.48  --bmc1_min_bound                        0
% 7.98/1.48  --bmc1_max_bound                        -1
% 7.98/1.48  --bmc1_max_bound_default                -1
% 7.98/1.48  --bmc1_symbol_reachability              true
% 7.98/1.48  --bmc1_property_lemmas                  false
% 7.98/1.48  --bmc1_k_induction                      false
% 7.98/1.48  --bmc1_non_equiv_states                 false
% 7.98/1.48  --bmc1_deadlock                         false
% 7.98/1.48  --bmc1_ucm                              false
% 7.98/1.48  --bmc1_add_unsat_core                   none
% 7.98/1.48  --bmc1_unsat_core_children              false
% 7.98/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.98/1.48  --bmc1_out_stat                         full
% 7.98/1.48  --bmc1_ground_init                      false
% 7.98/1.48  --bmc1_pre_inst_next_state              false
% 7.98/1.48  --bmc1_pre_inst_state                   false
% 7.98/1.48  --bmc1_pre_inst_reach_state             false
% 7.98/1.48  --bmc1_out_unsat_core                   false
% 7.98/1.48  --bmc1_aig_witness_out                  false
% 7.98/1.48  --bmc1_verbose                          false
% 7.98/1.48  --bmc1_dump_clauses_tptp                false
% 7.98/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.98/1.48  --bmc1_dump_file                        -
% 7.98/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.98/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.98/1.48  --bmc1_ucm_extend_mode                  1
% 7.98/1.48  --bmc1_ucm_init_mode                    2
% 7.98/1.48  --bmc1_ucm_cone_mode                    none
% 7.98/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.98/1.48  --bmc1_ucm_relax_model                  4
% 7.98/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.98/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.98/1.48  --bmc1_ucm_layered_model                none
% 7.98/1.48  --bmc1_ucm_max_lemma_size               10
% 7.98/1.48  
% 7.98/1.48  ------ AIG Options
% 7.98/1.48  
% 7.98/1.48  --aig_mode                              false
% 7.98/1.48  
% 7.98/1.48  ------ Instantiation Options
% 7.98/1.48  
% 7.98/1.48  --instantiation_flag                    true
% 7.98/1.48  --inst_sos_flag                         true
% 7.98/1.48  --inst_sos_phase                        true
% 7.98/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.98/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.98/1.48  --inst_lit_sel_side                     none
% 7.98/1.48  --inst_solver_per_active                1400
% 7.98/1.48  --inst_solver_calls_frac                1.
% 7.98/1.48  --inst_passive_queue_type               priority_queues
% 7.98/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.98/1.48  --inst_passive_queues_freq              [25;2]
% 7.98/1.48  --inst_dismatching                      true
% 7.98/1.48  --inst_eager_unprocessed_to_passive     true
% 7.98/1.48  --inst_prop_sim_given                   true
% 7.98/1.48  --inst_prop_sim_new                     false
% 7.98/1.48  --inst_subs_new                         false
% 7.98/1.48  --inst_eq_res_simp                      false
% 7.98/1.48  --inst_subs_given                       false
% 7.98/1.48  --inst_orphan_elimination               true
% 7.98/1.48  --inst_learning_loop_flag               true
% 7.98/1.48  --inst_learning_start                   3000
% 7.98/1.48  --inst_learning_factor                  2
% 7.98/1.48  --inst_start_prop_sim_after_learn       3
% 7.98/1.48  --inst_sel_renew                        solver
% 7.98/1.48  --inst_lit_activity_flag                true
% 7.98/1.48  --inst_restr_to_given                   false
% 7.98/1.48  --inst_activity_threshold               500
% 7.98/1.48  --inst_out_proof                        true
% 7.98/1.48  
% 7.98/1.48  ------ Resolution Options
% 7.98/1.48  
% 7.98/1.48  --resolution_flag                       false
% 7.98/1.48  --res_lit_sel                           adaptive
% 7.98/1.48  --res_lit_sel_side                      none
% 7.98/1.48  --res_ordering                          kbo
% 7.98/1.48  --res_to_prop_solver                    active
% 7.98/1.48  --res_prop_simpl_new                    false
% 7.98/1.48  --res_prop_simpl_given                  true
% 7.98/1.48  --res_passive_queue_type                priority_queues
% 7.98/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.98/1.48  --res_passive_queues_freq               [15;5]
% 7.98/1.48  --res_forward_subs                      full
% 7.98/1.48  --res_backward_subs                     full
% 7.98/1.48  --res_forward_subs_resolution           true
% 7.98/1.48  --res_backward_subs_resolution          true
% 7.98/1.48  --res_orphan_elimination                true
% 7.98/1.48  --res_time_limit                        2.
% 7.98/1.48  --res_out_proof                         true
% 7.98/1.48  
% 7.98/1.48  ------ Superposition Options
% 7.98/1.48  
% 7.98/1.48  --superposition_flag                    true
% 7.98/1.48  --sup_passive_queue_type                priority_queues
% 7.98/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.98/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.98/1.48  --demod_completeness_check              fast
% 7.98/1.48  --demod_use_ground                      true
% 7.98/1.48  --sup_to_prop_solver                    passive
% 7.98/1.48  --sup_prop_simpl_new                    true
% 7.98/1.48  --sup_prop_simpl_given                  true
% 7.98/1.48  --sup_fun_splitting                     true
% 7.98/1.48  --sup_smt_interval                      50000
% 7.98/1.48  
% 7.98/1.48  ------ Superposition Simplification Setup
% 7.98/1.48  
% 7.98/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.98/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.98/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.98/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.98/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.98/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.98/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.98/1.48  --sup_immed_triv                        [TrivRules]
% 7.98/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.98/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.98/1.48  --sup_immed_bw_main                     []
% 7.98/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.98/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.98/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.98/1.48  --sup_input_bw                          []
% 7.98/1.48  
% 7.98/1.48  ------ Combination Options
% 7.98/1.48  
% 7.98/1.48  --comb_res_mult                         3
% 7.98/1.48  --comb_sup_mult                         2
% 7.98/1.48  --comb_inst_mult                        10
% 7.98/1.48  
% 7.98/1.48  ------ Debug Options
% 7.98/1.48  
% 7.98/1.48  --dbg_backtrace                         false
% 7.98/1.48  --dbg_dump_prop_clauses                 false
% 7.98/1.48  --dbg_dump_prop_clauses_file            -
% 7.98/1.48  --dbg_out_stat                          false
% 7.98/1.48  
% 7.98/1.48  
% 7.98/1.48  
% 7.98/1.48  
% 7.98/1.48  ------ Proving...
% 7.98/1.48  
% 7.98/1.48  
% 7.98/1.48  % SZS status Theorem for theBenchmark.p
% 7.98/1.48  
% 7.98/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.98/1.48  
% 7.98/1.48  fof(f8,conjecture,(
% 7.98/1.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))))),
% 7.98/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.98/1.48  
% 7.98/1.48  fof(f9,negated_conjecture,(
% 7.98/1.48    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))))),
% 7.98/1.48    inference(negated_conjecture,[],[f8])).
% 7.98/1.48  
% 7.98/1.48  fof(f14,plain,(
% 7.98/1.48    ? [X0] : (? [X1] : (~r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 7.98/1.48    inference(ennf_transformation,[],[f9])).
% 7.98/1.48  
% 7.98/1.48  fof(f18,plain,(
% 7.98/1.48    ( ! [X0] : (? [X1] : (~r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) & v1_relat_1(X1)) => (~r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(X0,sK1))) & v1_relat_1(sK1))) )),
% 7.98/1.48    introduced(choice_axiom,[])).
% 7.98/1.48  
% 7.98/1.48  fof(f17,plain,(
% 7.98/1.48    ? [X0] : (? [X1] : (~r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(sK0,X1))) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 7.98/1.48    introduced(choice_axiom,[])).
% 7.98/1.48  
% 7.98/1.48  fof(f19,plain,(
% 7.98/1.48    (~r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1))) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 7.98/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f18,f17])).
% 7.98/1.48  
% 7.98/1.48  fof(f29,plain,(
% 7.98/1.48    v1_relat_1(sK0)),
% 7.98/1.48    inference(cnf_transformation,[],[f19])).
% 7.98/1.48  
% 7.98/1.48  fof(f6,axiom,(
% 7.98/1.48    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k4_xboole_0(X0,X1)))),
% 7.98/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.98/1.48  
% 7.98/1.48  fof(f12,plain,(
% 7.98/1.48    ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 7.98/1.48    inference(ennf_transformation,[],[f6])).
% 7.98/1.48  
% 7.98/1.48  fof(f27,plain,(
% 7.98/1.48    ( ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 7.98/1.48    inference(cnf_transformation,[],[f12])).
% 7.98/1.48  
% 7.98/1.48  fof(f5,axiom,(
% 7.98/1.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 7.98/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.98/1.48  
% 7.98/1.48  fof(f26,plain,(
% 7.98/1.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 7.98/1.48    inference(cnf_transformation,[],[f5])).
% 7.98/1.48  
% 7.98/1.48  fof(f34,plain,(
% 7.98/1.48    ( ! [X0,X1] : (v1_relat_1(k6_subset_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 7.98/1.48    inference(definition_unfolding,[],[f27,f26])).
% 7.98/1.48  
% 7.98/1.48  fof(f30,plain,(
% 7.98/1.48    v1_relat_1(sK1)),
% 7.98/1.48    inference(cnf_transformation,[],[f19])).
% 7.98/1.48  
% 7.98/1.48  fof(f7,axiom,(
% 7.98/1.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k2_xboole_0(X0,X1))))),
% 7.98/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.98/1.48  
% 7.98/1.48  fof(f13,plain,(
% 7.98/1.48    ! [X0] : (! [X1] : (k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k2_xboole_0(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.98/1.48    inference(ennf_transformation,[],[f7])).
% 7.98/1.48  
% 7.98/1.48  fof(f28,plain,(
% 7.98/1.48    ( ! [X0,X1] : (k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k2_xboole_0(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.98/1.48    inference(cnf_transformation,[],[f13])).
% 7.98/1.48  
% 7.98/1.48  fof(f4,axiom,(
% 7.98/1.48    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 7.98/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.98/1.48  
% 7.98/1.48  fof(f11,plain,(
% 7.98/1.48    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 7.98/1.48    inference(ennf_transformation,[],[f4])).
% 7.98/1.48  
% 7.98/1.48  fof(f25,plain,(
% 7.98/1.48    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 7.98/1.48    inference(cnf_transformation,[],[f11])).
% 7.98/1.48  
% 7.98/1.48  fof(f33,plain,(
% 7.98/1.48    ( ! [X2,X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 7.98/1.48    inference(definition_unfolding,[],[f25,f26])).
% 7.98/1.48  
% 7.98/1.48  fof(f31,plain,(
% 7.98/1.48    ~r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1)))),
% 7.98/1.48    inference(cnf_transformation,[],[f19])).
% 7.98/1.48  
% 7.98/1.48  fof(f3,axiom,(
% 7.98/1.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 7.98/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.98/1.48  
% 7.98/1.48  fof(f24,plain,(
% 7.98/1.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 7.98/1.48    inference(cnf_transformation,[],[f3])).
% 7.98/1.48  
% 7.98/1.48  fof(f32,plain,(
% 7.98/1.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k6_subset_1(X1,X0))) )),
% 7.98/1.48    inference(definition_unfolding,[],[f24,f26])).
% 7.98/1.48  
% 7.98/1.48  fof(f2,axiom,(
% 7.98/1.48    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 7.98/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.98/1.48  
% 7.98/1.48  fof(f10,plain,(
% 7.98/1.48    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 7.98/1.48    inference(ennf_transformation,[],[f2])).
% 7.98/1.48  
% 7.98/1.48  fof(f23,plain,(
% 7.98/1.48    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 7.98/1.48    inference(cnf_transformation,[],[f10])).
% 7.98/1.48  
% 7.98/1.48  fof(f1,axiom,(
% 7.98/1.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.98/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.98/1.48  
% 7.98/1.48  fof(f15,plain,(
% 7.98/1.48    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.98/1.48    inference(nnf_transformation,[],[f1])).
% 7.98/1.48  
% 7.98/1.48  fof(f16,plain,(
% 7.98/1.48    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.98/1.48    inference(flattening,[],[f15])).
% 7.98/1.48  
% 7.98/1.48  fof(f21,plain,(
% 7.98/1.48    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 7.98/1.48    inference(cnf_transformation,[],[f16])).
% 7.98/1.48  
% 7.98/1.48  fof(f35,plain,(
% 7.98/1.48    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.98/1.48    inference(equality_resolution,[],[f21])).
% 7.98/1.48  
% 7.98/1.48  fof(f22,plain,(
% 7.98/1.48    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.98/1.48    inference(cnf_transformation,[],[f16])).
% 7.98/1.48  
% 7.98/1.48  fof(f20,plain,(
% 7.98/1.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.98/1.48    inference(cnf_transformation,[],[f16])).
% 7.98/1.48  
% 7.98/1.48  fof(f36,plain,(
% 7.98/1.48    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.98/1.48    inference(equality_resolution,[],[f20])).
% 7.98/1.48  
% 7.98/1.48  cnf(c_10,negated_conjecture,
% 7.98/1.48      ( v1_relat_1(sK0) ),
% 7.98/1.48      inference(cnf_transformation,[],[f29]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_341,plain,
% 7.98/1.48      ( v1_relat_1(sK0) = iProver_top ),
% 7.98/1.48      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_6,plain,
% 7.98/1.48      ( ~ v1_relat_1(X0) | v1_relat_1(k6_subset_1(X0,X1)) ),
% 7.98/1.48      inference(cnf_transformation,[],[f34]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_345,plain,
% 7.98/1.48      ( v1_relat_1(X0) != iProver_top
% 7.98/1.48      | v1_relat_1(k6_subset_1(X0,X1)) = iProver_top ),
% 7.98/1.48      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_9,negated_conjecture,
% 7.98/1.48      ( v1_relat_1(sK1) ),
% 7.98/1.48      inference(cnf_transformation,[],[f30]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_342,plain,
% 7.98/1.48      ( v1_relat_1(sK1) = iProver_top ),
% 7.98/1.48      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_7,plain,
% 7.98/1.48      ( ~ v1_relat_1(X0)
% 7.98/1.48      | ~ v1_relat_1(X1)
% 7.98/1.48      | k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k2_xboole_0(X0,X1)) ),
% 7.98/1.48      inference(cnf_transformation,[],[f28]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_344,plain,
% 7.98/1.48      ( k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k2_xboole_0(X0,X1))
% 7.98/1.48      | v1_relat_1(X0) != iProver_top
% 7.98/1.48      | v1_relat_1(X1) != iProver_top ),
% 7.98/1.48      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_812,plain,
% 7.98/1.48      ( k2_xboole_0(k2_relat_1(sK1),k2_relat_1(X0)) = k2_relat_1(k2_xboole_0(sK1,X0))
% 7.98/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.98/1.48      inference(superposition,[status(thm)],[c_342,c_344]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_966,plain,
% 7.98/1.48      ( k2_xboole_0(k2_relat_1(sK1),k2_relat_1(k6_subset_1(X0,X1))) = k2_relat_1(k2_xboole_0(sK1,k6_subset_1(X0,X1)))
% 7.98/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.98/1.48      inference(superposition,[status(thm)],[c_345,c_812]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_8462,plain,
% 7.98/1.48      ( k2_xboole_0(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,X0))) = k2_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,X0))) ),
% 7.98/1.48      inference(superposition,[status(thm)],[c_341,c_966]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_5,plain,
% 7.98/1.48      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
% 7.98/1.48      | r1_tarski(k6_subset_1(X0,X1),X2) ),
% 7.98/1.48      inference(cnf_transformation,[],[f33]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_346,plain,
% 7.98/1.48      ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
% 7.98/1.48      | r1_tarski(k6_subset_1(X0,X1),X2) = iProver_top ),
% 7.98/1.48      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_8687,plain,
% 7.98/1.48      ( r1_tarski(X0,k2_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,X1)))) != iProver_top
% 7.98/1.48      | r1_tarski(k6_subset_1(X0,k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,X1))) = iProver_top ),
% 7.98/1.48      inference(superposition,[status(thm)],[c_8462,c_346]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_8,negated_conjecture,
% 7.98/1.48      ( ~ r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1))) ),
% 7.98/1.48      inference(cnf_transformation,[],[f31]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_343,plain,
% 7.98/1.48      ( r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1))) != iProver_top ),
% 7.98/1.48      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_32762,plain,
% 7.98/1.48      ( r1_tarski(k2_relat_1(sK0),k2_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,sK1)))) != iProver_top ),
% 7.98/1.48      inference(superposition,[status(thm)],[c_8687,c_343]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_4,plain,
% 7.98/1.48      ( k2_xboole_0(X0,k6_subset_1(X1,X0)) = k2_xboole_0(X0,X1) ),
% 7.98/1.48      inference(cnf_transformation,[],[f32]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_32766,plain,
% 7.98/1.48      ( r1_tarski(k2_relat_1(sK0),k2_relat_1(k2_xboole_0(sK1,sK0))) != iProver_top ),
% 7.98/1.48      inference(demodulation,[status(thm)],[c_32762,c_4]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_177,plain,( X0 = X0 ),theory(equality) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_26167,plain,
% 7.98/1.48      ( k2_relat_1(k2_xboole_0(sK1,sK0)) = k2_relat_1(k2_xboole_0(sK1,sK0)) ),
% 7.98/1.48      inference(instantiation,[status(thm)],[c_177]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_179,plain,
% 7.98/1.48      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.98/1.48      theory(equality) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_485,plain,
% 7.98/1.48      ( ~ r1_tarski(X0,X1)
% 7.98/1.48      | r1_tarski(k2_relat_1(sK0),X2)
% 7.98/1.48      | X2 != X1
% 7.98/1.48      | k2_relat_1(sK0) != X0 ),
% 7.98/1.48      inference(instantiation,[status(thm)],[c_179]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_795,plain,
% 7.98/1.48      ( ~ r1_tarski(k2_relat_1(sK0),X0)
% 7.98/1.48      | r1_tarski(k2_relat_1(sK0),X1)
% 7.98/1.48      | X1 != X0
% 7.98/1.48      | k2_relat_1(sK0) != k2_relat_1(sK0) ),
% 7.98/1.48      inference(instantiation,[status(thm)],[c_485]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_1184,plain,
% 7.98/1.48      ( r1_tarski(k2_relat_1(sK0),X0)
% 7.98/1.48      | ~ r1_tarski(k2_relat_1(sK0),k2_xboole_0(X1,X2))
% 7.98/1.48      | X0 != k2_xboole_0(X1,X2)
% 7.98/1.48      | k2_relat_1(sK0) != k2_relat_1(sK0) ),
% 7.98/1.48      inference(instantiation,[status(thm)],[c_795]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_2348,plain,
% 7.98/1.48      ( r1_tarski(k2_relat_1(sK0),X0)
% 7.98/1.48      | ~ r1_tarski(k2_relat_1(sK0),k2_xboole_0(k2_relat_1(sK1),k2_relat_1(sK0)))
% 7.98/1.48      | X0 != k2_xboole_0(k2_relat_1(sK1),k2_relat_1(sK0))
% 7.98/1.48      | k2_relat_1(sK0) != k2_relat_1(sK0) ),
% 7.98/1.48      inference(instantiation,[status(thm)],[c_1184]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_24281,plain,
% 7.98/1.48      ( ~ r1_tarski(k2_relat_1(sK0),k2_xboole_0(k2_relat_1(sK1),k2_relat_1(sK0)))
% 7.98/1.48      | r1_tarski(k2_relat_1(sK0),k2_relat_1(k2_xboole_0(sK1,sK0)))
% 7.98/1.48      | k2_relat_1(k2_xboole_0(sK1,sK0)) != k2_xboole_0(k2_relat_1(sK1),k2_relat_1(sK0))
% 7.98/1.48      | k2_relat_1(sK0) != k2_relat_1(sK0) ),
% 7.98/1.48      inference(instantiation,[status(thm)],[c_2348]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_24282,plain,
% 7.98/1.48      ( k2_relat_1(k2_xboole_0(sK1,sK0)) != k2_xboole_0(k2_relat_1(sK1),k2_relat_1(sK0))
% 7.98/1.48      | k2_relat_1(sK0) != k2_relat_1(sK0)
% 7.98/1.48      | r1_tarski(k2_relat_1(sK0),k2_xboole_0(k2_relat_1(sK1),k2_relat_1(sK0))) != iProver_top
% 7.98/1.48      | r1_tarski(k2_relat_1(sK0),k2_relat_1(k2_xboole_0(sK1,sK0))) = iProver_top ),
% 7.98/1.48      inference(predicate_to_equality,[status(thm)],[c_24281]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_178,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_1345,plain,
% 7.98/1.48      ( X0 != X1 | k2_relat_1(X2) != X1 | k2_relat_1(X2) = X0 ),
% 7.98/1.48      inference(instantiation,[status(thm)],[c_178]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_2435,plain,
% 7.98/1.48      ( X0 != k2_relat_1(X1)
% 7.98/1.48      | k2_relat_1(X1) = X0
% 7.98/1.48      | k2_relat_1(X1) != k2_relat_1(X1) ),
% 7.98/1.48      inference(instantiation,[status(thm)],[c_1345]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_6314,plain,
% 7.98/1.48      ( k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) != k2_relat_1(k2_xboole_0(X0,X1))
% 7.98/1.48      | k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1))
% 7.98/1.48      | k2_relat_1(k2_xboole_0(X0,X1)) != k2_relat_1(k2_xboole_0(X0,X1)) ),
% 7.98/1.48      inference(instantiation,[status(thm)],[c_2435]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_15357,plain,
% 7.98/1.48      ( k2_xboole_0(k2_relat_1(X0),k2_relat_1(sK0)) != k2_relat_1(k2_xboole_0(X0,sK0))
% 7.98/1.48      | k2_relat_1(k2_xboole_0(X0,sK0)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(sK0))
% 7.98/1.48      | k2_relat_1(k2_xboole_0(X0,sK0)) != k2_relat_1(k2_xboole_0(X0,sK0)) ),
% 7.98/1.48      inference(instantiation,[status(thm)],[c_6314]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_24279,plain,
% 7.98/1.48      ( k2_xboole_0(k2_relat_1(sK1),k2_relat_1(sK0)) != k2_relat_1(k2_xboole_0(sK1,sK0))
% 7.98/1.48      | k2_relat_1(k2_xboole_0(sK1,sK0)) = k2_xboole_0(k2_relat_1(sK1),k2_relat_1(sK0))
% 7.98/1.48      | k2_relat_1(k2_xboole_0(sK1,sK0)) != k2_relat_1(k2_xboole_0(sK1,sK0)) ),
% 7.98/1.48      inference(instantiation,[status(thm)],[c_15357]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_3,plain,
% 7.98/1.48      ( ~ r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
% 7.98/1.48      inference(cnf_transformation,[],[f23]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_736,plain,
% 7.98/1.48      ( ~ r1_tarski(k2_relat_1(sK0),X0)
% 7.98/1.48      | r1_tarski(k2_relat_1(sK0),k2_xboole_0(X1,X0)) ),
% 7.98/1.48      inference(instantiation,[status(thm)],[c_3]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_1055,plain,
% 7.98/1.48      ( r1_tarski(k2_relat_1(sK0),k2_xboole_0(X0,k2_relat_1(sK0)))
% 7.98/1.48      | ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) ),
% 7.98/1.48      inference(instantiation,[status(thm)],[c_736]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_1575,plain,
% 7.98/1.48      ( r1_tarski(k2_relat_1(sK0),k2_xboole_0(k2_relat_1(sK1),k2_relat_1(sK0)))
% 7.98/1.48      | ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) ),
% 7.98/1.48      inference(instantiation,[status(thm)],[c_1055]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_1577,plain,
% 7.98/1.48      ( r1_tarski(k2_relat_1(sK0),k2_xboole_0(k2_relat_1(sK1),k2_relat_1(sK0))) = iProver_top
% 7.98/1.48      | r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) != iProver_top ),
% 7.98/1.48      inference(predicate_to_equality,[status(thm)],[c_1575]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_818,plain,
% 7.98/1.48      ( k2_xboole_0(k2_relat_1(sK1),k2_relat_1(sK0)) = k2_relat_1(k2_xboole_0(sK1,sK0))
% 7.98/1.48      | v1_relat_1(sK0) != iProver_top ),
% 7.98/1.48      inference(instantiation,[status(thm)],[c_812]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_1,plain,
% 7.98/1.48      ( r1_tarski(X0,X0) ),
% 7.98/1.48      inference(cnf_transformation,[],[f35]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_635,plain,
% 7.98/1.48      ( r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) ),
% 7.98/1.48      inference(instantiation,[status(thm)],[c_1]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_636,plain,
% 7.98/1.48      ( r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) = iProver_top ),
% 7.98/1.48      inference(predicate_to_equality,[status(thm)],[c_635]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_183,plain,
% 7.98/1.48      ( X0 != X1 | k2_relat_1(X0) = k2_relat_1(X1) ),
% 7.98/1.48      theory(equality) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_188,plain,
% 7.98/1.48      ( k2_relat_1(sK0) = k2_relat_1(sK0) | sK0 != sK0 ),
% 7.98/1.48      inference(instantiation,[status(thm)],[c_183]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_0,plain,
% 7.98/1.48      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.98/1.48      inference(cnf_transformation,[],[f22]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_32,plain,
% 7.98/1.48      ( ~ r1_tarski(sK0,sK0) | sK0 = sK0 ),
% 7.98/1.48      inference(instantiation,[status(thm)],[c_0]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_2,plain,
% 7.98/1.48      ( r1_tarski(X0,X0) ),
% 7.98/1.48      inference(cnf_transformation,[],[f36]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_28,plain,
% 7.98/1.48      ( r1_tarski(sK0,sK0) ),
% 7.98/1.48      inference(instantiation,[status(thm)],[c_2]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_11,plain,
% 7.98/1.48      ( v1_relat_1(sK0) = iProver_top ),
% 7.98/1.48      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(contradiction,plain,
% 7.98/1.48      ( $false ),
% 7.98/1.48      inference(minisat,
% 7.98/1.48                [status(thm)],
% 7.98/1.48                [c_32766,c_26167,c_24282,c_24279,c_1577,c_818,c_636,
% 7.98/1.48                 c_188,c_32,c_28,c_11]) ).
% 7.98/1.48  
% 7.98/1.48  
% 7.98/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.98/1.48  
% 7.98/1.48  ------                               Statistics
% 7.98/1.48  
% 7.98/1.48  ------ General
% 7.98/1.48  
% 7.98/1.48  abstr_ref_over_cycles:                  0
% 7.98/1.48  abstr_ref_under_cycles:                 0
% 7.98/1.48  gc_basic_clause_elim:                   0
% 7.98/1.48  forced_gc_time:                         0
% 7.98/1.48  parsing_time:                           0.007
% 7.98/1.48  unif_index_cands_time:                  0.
% 7.98/1.48  unif_index_add_time:                    0.
% 7.98/1.48  orderings_time:                         0.
% 7.98/1.48  out_proof_time:                         0.008
% 7.98/1.48  total_time:                             0.964
% 7.98/1.48  num_of_symbols:                         38
% 7.98/1.48  num_of_terms:                           33826
% 7.98/1.48  
% 7.98/1.48  ------ Preprocessing
% 7.98/1.48  
% 7.98/1.48  num_of_splits:                          0
% 7.98/1.48  num_of_split_atoms:                     0
% 7.98/1.48  num_of_reused_defs:                     0
% 7.98/1.48  num_eq_ax_congr_red:                    0
% 7.98/1.48  num_of_sem_filtered_clauses:            1
% 7.98/1.48  num_of_subtypes:                        0
% 7.98/1.48  monotx_restored_types:                  0
% 7.98/1.48  sat_num_of_epr_types:                   0
% 7.98/1.48  sat_num_of_non_cyclic_types:            0
% 7.98/1.48  sat_guarded_non_collapsed_types:        0
% 7.98/1.48  num_pure_diseq_elim:                    0
% 7.98/1.48  simp_replaced_by:                       0
% 7.98/1.48  res_preprocessed:                       55
% 7.98/1.48  prep_upred:                             0
% 7.98/1.48  prep_unflattend:                        0
% 7.98/1.48  smt_new_axioms:                         0
% 7.98/1.48  pred_elim_cands:                        2
% 7.98/1.48  pred_elim:                              0
% 7.98/1.48  pred_elim_cl:                           0
% 7.98/1.48  pred_elim_cycles:                       2
% 7.98/1.48  merged_defs:                            0
% 7.98/1.48  merged_defs_ncl:                        0
% 7.98/1.48  bin_hyper_res:                          0
% 7.98/1.48  prep_cycles:                            4
% 7.98/1.48  pred_elim_time:                         0.
% 7.98/1.48  splitting_time:                         0.
% 7.98/1.48  sem_filter_time:                        0.
% 7.98/1.48  monotx_time:                            0.
% 7.98/1.48  subtype_inf_time:                       0.
% 7.98/1.48  
% 7.98/1.48  ------ Problem properties
% 7.98/1.48  
% 7.98/1.48  clauses:                                10
% 7.98/1.48  conjectures:                            3
% 7.98/1.48  epr:                                    4
% 7.98/1.48  horn:                                   10
% 7.98/1.48  ground:                                 3
% 7.98/1.48  unary:                                  5
% 7.98/1.48  binary:                                 3
% 7.98/1.48  lits:                                   17
% 7.98/1.48  lits_eq:                                3
% 7.98/1.48  fd_pure:                                0
% 7.98/1.48  fd_pseudo:                              0
% 7.98/1.48  fd_cond:                                0
% 7.98/1.48  fd_pseudo_cond:                         1
% 7.98/1.48  ac_symbols:                             0
% 7.98/1.48  
% 7.98/1.48  ------ Propositional Solver
% 7.98/1.48  
% 7.98/1.48  prop_solver_calls:                      35
% 7.98/1.48  prop_fast_solver_calls:                 614
% 7.98/1.48  smt_solver_calls:                       0
% 7.98/1.48  smt_fast_solver_calls:                  0
% 7.98/1.48  prop_num_of_clauses:                    13830
% 7.98/1.48  prop_preprocess_simplified:             18660
% 7.98/1.48  prop_fo_subsumed:                       0
% 7.98/1.48  prop_solver_time:                       0.
% 7.98/1.48  smt_solver_time:                        0.
% 7.98/1.48  smt_fast_solver_time:                   0.
% 7.98/1.48  prop_fast_solver_time:                  0.
% 7.98/1.48  prop_unsat_core_time:                   0.001
% 7.98/1.48  
% 7.98/1.48  ------ QBF
% 7.98/1.48  
% 7.98/1.48  qbf_q_res:                              0
% 7.98/1.48  qbf_num_tautologies:                    0
% 7.98/1.48  qbf_prep_cycles:                        0
% 7.98/1.48  
% 7.98/1.48  ------ BMC1
% 7.98/1.48  
% 7.98/1.48  bmc1_current_bound:                     -1
% 7.98/1.48  bmc1_last_solved_bound:                 -1
% 7.98/1.48  bmc1_unsat_core_size:                   -1
% 7.98/1.48  bmc1_unsat_core_parents_size:           -1
% 7.98/1.48  bmc1_merge_next_fun:                    0
% 7.98/1.48  bmc1_unsat_core_clauses_time:           0.
% 7.98/1.48  
% 7.98/1.48  ------ Instantiation
% 7.98/1.48  
% 7.98/1.48  inst_num_of_clauses:                    3242
% 7.98/1.48  inst_num_in_passive:                    206
% 7.98/1.48  inst_num_in_active:                     1535
% 7.98/1.48  inst_num_in_unprocessed:                1503
% 7.98/1.48  inst_num_of_loops:                      1580
% 7.98/1.48  inst_num_of_learning_restarts:          0
% 7.98/1.48  inst_num_moves_active_passive:          40
% 7.98/1.48  inst_lit_activity:                      0
% 7.98/1.48  inst_lit_activity_moves:                0
% 7.98/1.48  inst_num_tautologies:                   0
% 7.98/1.48  inst_num_prop_implied:                  0
% 7.98/1.48  inst_num_existing_simplified:           0
% 7.98/1.48  inst_num_eq_res_simplified:             0
% 7.98/1.48  inst_num_child_elim:                    0
% 7.98/1.48  inst_num_of_dismatching_blockings:      4380
% 7.98/1.48  inst_num_of_non_proper_insts:           6909
% 7.98/1.48  inst_num_of_duplicates:                 0
% 7.98/1.48  inst_inst_num_from_inst_to_res:         0
% 7.98/1.48  inst_dismatching_checking_time:         0.
% 7.98/1.48  
% 7.98/1.48  ------ Resolution
% 7.98/1.48  
% 7.98/1.48  res_num_of_clauses:                     0
% 7.98/1.48  res_num_in_passive:                     0
% 7.98/1.48  res_num_in_active:                      0
% 7.98/1.48  res_num_of_loops:                       59
% 7.98/1.48  res_forward_subset_subsumed:            603
% 7.98/1.48  res_backward_subset_subsumed:           6
% 7.98/1.48  res_forward_subsumed:                   0
% 7.98/1.48  res_backward_subsumed:                  0
% 7.98/1.48  res_forward_subsumption_resolution:     0
% 7.98/1.48  res_backward_subsumption_resolution:    0
% 7.98/1.48  res_clause_to_clause_subsumption:       4805
% 7.98/1.48  res_orphan_elimination:                 0
% 7.98/1.48  res_tautology_del:                      1001
% 7.98/1.48  res_num_eq_res_simplified:              0
% 7.98/1.48  res_num_sel_changes:                    0
% 7.98/1.48  res_moves_from_active_to_pass:          0
% 7.98/1.48  
% 7.98/1.48  ------ Superposition
% 7.98/1.48  
% 7.98/1.48  sup_time_total:                         0.
% 7.98/1.48  sup_time_generating:                    0.
% 7.98/1.48  sup_time_sim_full:                      0.
% 7.98/1.48  sup_time_sim_immed:                     0.
% 7.98/1.48  
% 7.98/1.48  sup_num_of_clauses:                     1401
% 7.98/1.48  sup_num_in_active:                      314
% 7.98/1.48  sup_num_in_passive:                     1087
% 7.98/1.48  sup_num_of_loops:                       314
% 7.98/1.48  sup_fw_superposition:                   1009
% 7.98/1.48  sup_bw_superposition:                   737
% 7.98/1.48  sup_immediate_simplified:               390
% 7.98/1.48  sup_given_eliminated:                   0
% 7.98/1.48  comparisons_done:                       0
% 7.98/1.48  comparisons_avoided:                    0
% 7.98/1.48  
% 7.98/1.48  ------ Simplifications
% 7.98/1.48  
% 7.98/1.48  
% 7.98/1.48  sim_fw_subset_subsumed:                 0
% 7.98/1.48  sim_bw_subset_subsumed:                 0
% 7.98/1.48  sim_fw_subsumed:                        3
% 7.98/1.48  sim_bw_subsumed:                        1
% 7.98/1.48  sim_fw_subsumption_res:                 0
% 7.98/1.48  sim_bw_subsumption_res:                 0
% 7.98/1.48  sim_tautology_del:                      0
% 7.98/1.48  sim_eq_tautology_del:                   5
% 7.98/1.48  sim_eq_res_simp:                        0
% 7.98/1.48  sim_fw_demodulated:                     389
% 7.98/1.48  sim_bw_demodulated:                     0
% 7.98/1.48  sim_light_normalised:                   221
% 7.98/1.48  sim_joinable_taut:                      0
% 7.98/1.48  sim_joinable_simp:                      0
% 7.98/1.48  sim_ac_normalised:                      0
% 7.98/1.48  sim_smt_subsumption:                    0
% 7.98/1.48  
%------------------------------------------------------------------------------
