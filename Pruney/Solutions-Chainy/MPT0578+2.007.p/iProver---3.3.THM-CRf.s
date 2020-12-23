%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:47:53 EST 2020

% Result     : Theorem 39.25s
% Output     : CNFRefutation 39.25s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 314 expanded)
%              Number of clauses        :   51 ( 114 expanded)
%              Number of leaves         :   11 (  78 expanded)
%              Depth                    :   15
%              Number of atoms          :  180 ( 798 expanded)
%              Number of equality atoms :   92 ( 327 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k10_relat_1(X0,k1_relat_1(X1)) != k1_relat_1(k5_relat_1(X0,X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k10_relat_1(X0,k1_relat_1(X1)) != k1_relat_1(k5_relat_1(X0,X1))
          & v1_relat_1(X1) )
     => ( k10_relat_1(X0,k1_relat_1(sK1)) != k1_relat_1(k5_relat_1(X0,sK1))
        & v1_relat_1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k10_relat_1(X0,k1_relat_1(X1)) != k1_relat_1(k5_relat_1(X0,X1))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k10_relat_1(sK0,k1_relat_1(X1)) != k1_relat_1(k5_relat_1(sK0,X1))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( k10_relat_1(sK0,k1_relat_1(sK1)) != k1_relat_1(k5_relat_1(sK0,sK1))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f22,f21])).

fof(f35,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f34,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f13,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f31,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k10_relat_1(X1,k10_relat_1(X2,X0)) = k10_relat_1(k5_relat_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k10_relat_1(X1,k10_relat_1(X2,X0)) = k10_relat_1(k5_relat_1(X1,X2),X0)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X1,k10_relat_1(X2,X0)) = k10_relat_1(k5_relat_1(X1,X2),X0)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f19])).

fof(f26,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f36,plain,(
    k10_relat_1(sK0,k1_relat_1(sK1)) != k1_relat_1(k5_relat_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_11,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_432,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_12,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_431,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_437,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_435,plain,
    ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_887,plain,
    ( k10_relat_1(k5_relat_1(X0,X1),k2_relat_1(k5_relat_1(X0,X1))) = k1_relat_1(k5_relat_1(X0,X1))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_437,c_435])).

cnf(c_2787,plain,
    ( k10_relat_1(k5_relat_1(sK0,X0),k2_relat_1(k5_relat_1(sK0,X0))) = k1_relat_1(k5_relat_1(sK0,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_431,c_887])).

cnf(c_3187,plain,
    ( k10_relat_1(k5_relat_1(sK0,sK1),k2_relat_1(k5_relat_1(sK0,sK1))) = k1_relat_1(k5_relat_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_432,c_2787])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k10_relat_1(k5_relat_1(X0,X1),X2) = k10_relat_1(X0,k10_relat_1(X1,X2)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_433,plain,
    ( k10_relat_1(k5_relat_1(X0,X1),X2) = k10_relat_1(X0,k10_relat_1(X1,X2))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_607,plain,
    ( k10_relat_1(sK0,k10_relat_1(X0,X1)) = k10_relat_1(k5_relat_1(sK0,X0),X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_431,c_433])).

cnf(c_1678,plain,
    ( k10_relat_1(sK0,k10_relat_1(sK1,X0)) = k10_relat_1(k5_relat_1(sK0,sK1),X0) ),
    inference(superposition,[status(thm)],[c_432,c_607])).

cnf(c_3465,plain,
    ( k10_relat_1(sK0,k10_relat_1(sK1,k2_relat_1(k5_relat_1(sK0,sK1)))) = k1_relat_1(k5_relat_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_3187,c_1678])).

cnf(c_701,plain,
    ( k10_relat_1(sK1,k2_relat_1(sK1)) = k1_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_432,c_435])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k2_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_434,plain,
    ( k2_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k2_xboole_0(X1,X2))
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_881,plain,
    ( k2_xboole_0(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1)) = k10_relat_1(sK1,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_432,c_434])).

cnf(c_1212,plain,
    ( k10_relat_1(sK1,k2_xboole_0(X0,k2_relat_1(sK1))) = k2_xboole_0(k10_relat_1(sK1,X0),k1_relat_1(sK1)) ),
    inference(superposition,[status(thm)],[c_701,c_881])).

cnf(c_6,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_436,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4404,plain,
    ( r1_tarski(k2_xboole_0(k10_relat_1(sK1,X0),k1_relat_1(sK1)),k1_relat_1(sK1)) = iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1212,c_436])).

cnf(c_14,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4441,plain,
    ( r1_tarski(k2_xboole_0(k10_relat_1(sK1,X0),k1_relat_1(sK1)),k1_relat_1(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4404,c_14])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_441,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4450,plain,
    ( k2_xboole_0(k10_relat_1(sK1,X0),k1_relat_1(sK1)) = k1_relat_1(sK1)
    | r1_tarski(k1_relat_1(sK1),k2_xboole_0(k10_relat_1(sK1,X0),k1_relat_1(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4441,c_441])).

cnf(c_1040,plain,
    ( r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) = iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_701,c_436])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_439,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k2_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_800,plain,
    ( k2_xboole_0(X0,X1) = X2
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(k2_xboole_0(X0,X1),X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_439,c_441])).

cnf(c_5064,plain,
    ( k2_xboole_0(k10_relat_1(sK1,X0),k1_relat_1(sK1)) = k1_relat_1(sK1)
    | r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4441,c_800])).

cnf(c_6437,plain,
    ( k2_xboole_0(k10_relat_1(sK1,X0),k1_relat_1(sK1)) = k1_relat_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4450,c_14,c_1040,c_5064])).

cnf(c_882,plain,
    ( k2_xboole_0(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1)) = k10_relat_1(sK0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_431,c_434])).

cnf(c_4,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_438,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1481,plain,
    ( r1_tarski(k10_relat_1(sK0,X0),k10_relat_1(sK0,k2_xboole_0(X0,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_882,c_438])).

cnf(c_6452,plain,
    ( r1_tarski(k10_relat_1(sK0,k10_relat_1(sK1,X0)),k10_relat_1(sK0,k1_relat_1(sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_6437,c_1481])).

cnf(c_140264,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,k1_relat_1(sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3465,c_6452])).

cnf(c_1839,plain,
    ( r1_tarski(k10_relat_1(sK0,k10_relat_1(sK1,X0)),k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top
    | v1_relat_1(k5_relat_1(sK0,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1678,c_436])).

cnf(c_13,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_651,plain,
    ( v1_relat_1(k5_relat_1(sK0,sK1))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_652,plain,
    ( v1_relat_1(k5_relat_1(sK0,sK1)) = iProver_top
    | v1_relat_1(sK1) != iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_651])).

cnf(c_4209,plain,
    ( r1_tarski(k10_relat_1(sK0,k10_relat_1(sK1,X0)),k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1839,c_13,c_14,c_652])).

cnf(c_4215,plain,
    ( r1_tarski(k10_relat_1(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_701,c_4209])).

cnf(c_476,plain,
    ( ~ r1_tarski(k10_relat_1(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,k1_relat_1(sK1)))
    | k10_relat_1(sK0,k1_relat_1(sK1)) = k1_relat_1(k5_relat_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_477,plain,
    ( k10_relat_1(sK0,k1_relat_1(sK1)) = k1_relat_1(k5_relat_1(sK0,sK1))
    | r1_tarski(k10_relat_1(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(sK0,sK1))) != iProver_top
    | r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,k1_relat_1(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_476])).

cnf(c_10,negated_conjecture,
    ( k10_relat_1(sK0,k1_relat_1(sK1)) != k1_relat_1(k5_relat_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f36])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_140264,c_4215,c_477,c_10])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:03:03 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 39.25/5.54  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 39.25/5.54  
% 39.25/5.54  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 39.25/5.54  
% 39.25/5.54  ------  iProver source info
% 39.25/5.54  
% 39.25/5.54  git: date: 2020-06-30 10:37:57 +0100
% 39.25/5.54  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 39.25/5.54  git: non_committed_changes: false
% 39.25/5.54  git: last_make_outside_of_git: false
% 39.25/5.54  
% 39.25/5.54  ------ 
% 39.25/5.54  ------ Parsing...
% 39.25/5.54  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 39.25/5.54  
% 39.25/5.54  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 39.25/5.54  
% 39.25/5.54  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 39.25/5.54  
% 39.25/5.54  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.25/5.54  ------ Proving...
% 39.25/5.54  ------ Problem Properties 
% 39.25/5.54  
% 39.25/5.54  
% 39.25/5.54  clauses                                 12
% 39.25/5.54  conjectures                             3
% 39.25/5.54  EPR                                     4
% 39.25/5.54  Horn                                    12
% 39.25/5.54  unary                                   5
% 39.25/5.54  binary                                  4
% 39.25/5.54  lits                                    22
% 39.25/5.54  lits eq                                 5
% 39.25/5.54  fd_pure                                 0
% 39.25/5.54  fd_pseudo                               0
% 39.25/5.54  fd_cond                                 0
% 39.25/5.54  fd_pseudo_cond                          1
% 39.25/5.54  AC symbols                              0
% 39.25/5.54  
% 39.25/5.54  ------ Input Options Time Limit: Unbounded
% 39.25/5.54  
% 39.25/5.54  
% 39.25/5.54  ------ 
% 39.25/5.54  Current options:
% 39.25/5.54  ------ 
% 39.25/5.54  
% 39.25/5.54  
% 39.25/5.54  
% 39.25/5.54  
% 39.25/5.54  ------ Proving...
% 39.25/5.54  
% 39.25/5.54  
% 39.25/5.54  % SZS status Theorem for theBenchmark.p
% 39.25/5.54  
% 39.25/5.54  % SZS output start CNFRefutation for theBenchmark.p
% 39.25/5.54  
% 39.25/5.54  fof(f9,conjecture,(
% 39.25/5.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))))),
% 39.25/5.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.25/5.54  
% 39.25/5.54  fof(f10,negated_conjecture,(
% 39.25/5.54    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))))),
% 39.25/5.54    inference(negated_conjecture,[],[f9])).
% 39.25/5.54  
% 39.25/5.54  fof(f18,plain,(
% 39.25/5.54    ? [X0] : (? [X1] : (k10_relat_1(X0,k1_relat_1(X1)) != k1_relat_1(k5_relat_1(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 39.25/5.54    inference(ennf_transformation,[],[f10])).
% 39.25/5.54  
% 39.25/5.54  fof(f22,plain,(
% 39.25/5.54    ( ! [X0] : (? [X1] : (k10_relat_1(X0,k1_relat_1(X1)) != k1_relat_1(k5_relat_1(X0,X1)) & v1_relat_1(X1)) => (k10_relat_1(X0,k1_relat_1(sK1)) != k1_relat_1(k5_relat_1(X0,sK1)) & v1_relat_1(sK1))) )),
% 39.25/5.54    introduced(choice_axiom,[])).
% 39.25/5.54  
% 39.25/5.54  fof(f21,plain,(
% 39.25/5.54    ? [X0] : (? [X1] : (k10_relat_1(X0,k1_relat_1(X1)) != k1_relat_1(k5_relat_1(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (k10_relat_1(sK0,k1_relat_1(X1)) != k1_relat_1(k5_relat_1(sK0,X1)) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 39.25/5.54    introduced(choice_axiom,[])).
% 39.25/5.54  
% 39.25/5.54  fof(f23,plain,(
% 39.25/5.54    (k10_relat_1(sK0,k1_relat_1(sK1)) != k1_relat_1(k5_relat_1(sK0,sK1)) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 39.25/5.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f22,f21])).
% 39.25/5.54  
% 39.25/5.54  fof(f35,plain,(
% 39.25/5.54    v1_relat_1(sK1)),
% 39.25/5.54    inference(cnf_transformation,[],[f23])).
% 39.25/5.54  
% 39.25/5.54  fof(f34,plain,(
% 39.25/5.54    v1_relat_1(sK0)),
% 39.25/5.54    inference(cnf_transformation,[],[f23])).
% 39.25/5.54  
% 39.25/5.54  fof(f4,axiom,(
% 39.25/5.54    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 39.25/5.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.25/5.54  
% 39.25/5.54  fof(f12,plain,(
% 39.25/5.54    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 39.25/5.54    inference(ennf_transformation,[],[f4])).
% 39.25/5.54  
% 39.25/5.54  fof(f13,plain,(
% 39.25/5.54    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 39.25/5.54    inference(flattening,[],[f12])).
% 39.25/5.54  
% 39.25/5.54  fof(f29,plain,(
% 39.25/5.54    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 39.25/5.54    inference(cnf_transformation,[],[f13])).
% 39.25/5.54  
% 39.25/5.54  fof(f6,axiom,(
% 39.25/5.54    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 39.25/5.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.25/5.54  
% 39.25/5.54  fof(f15,plain,(
% 39.25/5.54    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 39.25/5.54    inference(ennf_transformation,[],[f6])).
% 39.25/5.54  
% 39.25/5.54  fof(f31,plain,(
% 39.25/5.54    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 39.25/5.54    inference(cnf_transformation,[],[f15])).
% 39.25/5.54  
% 39.25/5.54  fof(f8,axiom,(
% 39.25/5.54    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k10_relat_1(X1,k10_relat_1(X2,X0)) = k10_relat_1(k5_relat_1(X1,X2),X0)))),
% 39.25/5.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.25/5.54  
% 39.25/5.54  fof(f17,plain,(
% 39.25/5.54    ! [X0,X1] : (! [X2] : (k10_relat_1(X1,k10_relat_1(X2,X0)) = k10_relat_1(k5_relat_1(X1,X2),X0) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 39.25/5.54    inference(ennf_transformation,[],[f8])).
% 39.25/5.54  
% 39.25/5.54  fof(f33,plain,(
% 39.25/5.54    ( ! [X2,X0,X1] : (k10_relat_1(X1,k10_relat_1(X2,X0)) = k10_relat_1(k5_relat_1(X1,X2),X0) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 39.25/5.54    inference(cnf_transformation,[],[f17])).
% 39.25/5.54  
% 39.25/5.54  fof(f7,axiom,(
% 39.25/5.54    ! [X0,X1,X2] : (v1_relat_1(X2) => k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1)))),
% 39.25/5.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.25/5.54  
% 39.25/5.54  fof(f16,plain,(
% 39.25/5.54    ! [X0,X1,X2] : (k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 39.25/5.54    inference(ennf_transformation,[],[f7])).
% 39.25/5.54  
% 39.25/5.54  fof(f32,plain,(
% 39.25/5.54    ( ! [X2,X0,X1] : (k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 39.25/5.54    inference(cnf_transformation,[],[f16])).
% 39.25/5.54  
% 39.25/5.54  fof(f5,axiom,(
% 39.25/5.54    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 39.25/5.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.25/5.54  
% 39.25/5.54  fof(f14,plain,(
% 39.25/5.54    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 39.25/5.54    inference(ennf_transformation,[],[f5])).
% 39.25/5.54  
% 39.25/5.54  fof(f30,plain,(
% 39.25/5.54    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 39.25/5.54    inference(cnf_transformation,[],[f14])).
% 39.25/5.54  
% 39.25/5.54  fof(f1,axiom,(
% 39.25/5.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 39.25/5.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.25/5.54  
% 39.25/5.54  fof(f19,plain,(
% 39.25/5.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 39.25/5.54    inference(nnf_transformation,[],[f1])).
% 39.25/5.54  
% 39.25/5.54  fof(f20,plain,(
% 39.25/5.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 39.25/5.54    inference(flattening,[],[f19])).
% 39.25/5.54  
% 39.25/5.54  fof(f26,plain,(
% 39.25/5.54    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 39.25/5.54    inference(cnf_transformation,[],[f20])).
% 39.25/5.54  
% 39.25/5.54  fof(f2,axiom,(
% 39.25/5.54    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 39.25/5.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.25/5.54  
% 39.25/5.54  fof(f11,plain,(
% 39.25/5.54    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 39.25/5.54    inference(ennf_transformation,[],[f2])).
% 39.25/5.54  
% 39.25/5.54  fof(f27,plain,(
% 39.25/5.54    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 39.25/5.54    inference(cnf_transformation,[],[f11])).
% 39.25/5.54  
% 39.25/5.54  fof(f3,axiom,(
% 39.25/5.54    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 39.25/5.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.25/5.54  
% 39.25/5.54  fof(f28,plain,(
% 39.25/5.54    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 39.25/5.54    inference(cnf_transformation,[],[f3])).
% 39.25/5.54  
% 39.25/5.54  fof(f36,plain,(
% 39.25/5.54    k10_relat_1(sK0,k1_relat_1(sK1)) != k1_relat_1(k5_relat_1(sK0,sK1))),
% 39.25/5.54    inference(cnf_transformation,[],[f23])).
% 39.25/5.54  
% 39.25/5.54  cnf(c_11,negated_conjecture,
% 39.25/5.54      ( v1_relat_1(sK1) ),
% 39.25/5.54      inference(cnf_transformation,[],[f35]) ).
% 39.25/5.54  
% 39.25/5.54  cnf(c_432,plain,
% 39.25/5.54      ( v1_relat_1(sK1) = iProver_top ),
% 39.25/5.54      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 39.25/5.54  
% 39.25/5.54  cnf(c_12,negated_conjecture,
% 39.25/5.54      ( v1_relat_1(sK0) ),
% 39.25/5.54      inference(cnf_transformation,[],[f34]) ).
% 39.25/5.54  
% 39.25/5.54  cnf(c_431,plain,
% 39.25/5.54      ( v1_relat_1(sK0) = iProver_top ),
% 39.25/5.54      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 39.25/5.54  
% 39.25/5.54  cnf(c_5,plain,
% 39.25/5.54      ( ~ v1_relat_1(X0)
% 39.25/5.54      | ~ v1_relat_1(X1)
% 39.25/5.54      | v1_relat_1(k5_relat_1(X1,X0)) ),
% 39.25/5.54      inference(cnf_transformation,[],[f29]) ).
% 39.25/5.54  
% 39.25/5.54  cnf(c_437,plain,
% 39.25/5.54      ( v1_relat_1(X0) != iProver_top
% 39.25/5.54      | v1_relat_1(X1) != iProver_top
% 39.25/5.54      | v1_relat_1(k5_relat_1(X1,X0)) = iProver_top ),
% 39.25/5.54      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 39.25/5.54  
% 39.25/5.54  cnf(c_7,plain,
% 39.25/5.54      ( ~ v1_relat_1(X0)
% 39.25/5.54      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
% 39.25/5.54      inference(cnf_transformation,[],[f31]) ).
% 39.25/5.54  
% 39.25/5.54  cnf(c_435,plain,
% 39.25/5.54      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
% 39.25/5.54      | v1_relat_1(X0) != iProver_top ),
% 39.25/5.54      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 39.25/5.54  
% 39.25/5.54  cnf(c_887,plain,
% 39.25/5.54      ( k10_relat_1(k5_relat_1(X0,X1),k2_relat_1(k5_relat_1(X0,X1))) = k1_relat_1(k5_relat_1(X0,X1))
% 39.25/5.54      | v1_relat_1(X1) != iProver_top
% 39.25/5.54      | v1_relat_1(X0) != iProver_top ),
% 39.25/5.54      inference(superposition,[status(thm)],[c_437,c_435]) ).
% 39.25/5.54  
% 39.25/5.54  cnf(c_2787,plain,
% 39.25/5.54      ( k10_relat_1(k5_relat_1(sK0,X0),k2_relat_1(k5_relat_1(sK0,X0))) = k1_relat_1(k5_relat_1(sK0,X0))
% 39.25/5.54      | v1_relat_1(X0) != iProver_top ),
% 39.25/5.54      inference(superposition,[status(thm)],[c_431,c_887]) ).
% 39.25/5.54  
% 39.25/5.54  cnf(c_3187,plain,
% 39.25/5.54      ( k10_relat_1(k5_relat_1(sK0,sK1),k2_relat_1(k5_relat_1(sK0,sK1))) = k1_relat_1(k5_relat_1(sK0,sK1)) ),
% 39.25/5.54      inference(superposition,[status(thm)],[c_432,c_2787]) ).
% 39.25/5.54  
% 39.25/5.54  cnf(c_9,plain,
% 39.25/5.54      ( ~ v1_relat_1(X0)
% 39.25/5.54      | ~ v1_relat_1(X1)
% 39.25/5.54      | k10_relat_1(k5_relat_1(X0,X1),X2) = k10_relat_1(X0,k10_relat_1(X1,X2)) ),
% 39.25/5.54      inference(cnf_transformation,[],[f33]) ).
% 39.25/5.54  
% 39.25/5.54  cnf(c_433,plain,
% 39.25/5.54      ( k10_relat_1(k5_relat_1(X0,X1),X2) = k10_relat_1(X0,k10_relat_1(X1,X2))
% 39.25/5.54      | v1_relat_1(X0) != iProver_top
% 39.25/5.54      | v1_relat_1(X1) != iProver_top ),
% 39.25/5.54      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 39.25/5.54  
% 39.25/5.54  cnf(c_607,plain,
% 39.25/5.54      ( k10_relat_1(sK0,k10_relat_1(X0,X1)) = k10_relat_1(k5_relat_1(sK0,X0),X1)
% 39.25/5.54      | v1_relat_1(X0) != iProver_top ),
% 39.25/5.54      inference(superposition,[status(thm)],[c_431,c_433]) ).
% 39.25/5.54  
% 39.25/5.54  cnf(c_1678,plain,
% 39.25/5.54      ( k10_relat_1(sK0,k10_relat_1(sK1,X0)) = k10_relat_1(k5_relat_1(sK0,sK1),X0) ),
% 39.25/5.54      inference(superposition,[status(thm)],[c_432,c_607]) ).
% 39.25/5.54  
% 39.25/5.54  cnf(c_3465,plain,
% 39.25/5.54      ( k10_relat_1(sK0,k10_relat_1(sK1,k2_relat_1(k5_relat_1(sK0,sK1)))) = k1_relat_1(k5_relat_1(sK0,sK1)) ),
% 39.25/5.54      inference(superposition,[status(thm)],[c_3187,c_1678]) ).
% 39.25/5.54  
% 39.25/5.54  cnf(c_701,plain,
% 39.25/5.54      ( k10_relat_1(sK1,k2_relat_1(sK1)) = k1_relat_1(sK1) ),
% 39.25/5.54      inference(superposition,[status(thm)],[c_432,c_435]) ).
% 39.25/5.54  
% 39.25/5.54  cnf(c_8,plain,
% 39.25/5.54      ( ~ v1_relat_1(X0)
% 39.25/5.54      | k2_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k2_xboole_0(X1,X2)) ),
% 39.25/5.54      inference(cnf_transformation,[],[f32]) ).
% 39.25/5.54  
% 39.25/5.54  cnf(c_434,plain,
% 39.25/5.54      ( k2_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k2_xboole_0(X1,X2))
% 39.25/5.54      | v1_relat_1(X0) != iProver_top ),
% 39.25/5.54      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 39.25/5.54  
% 39.25/5.54  cnf(c_881,plain,
% 39.25/5.54      ( k2_xboole_0(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1)) = k10_relat_1(sK1,k2_xboole_0(X0,X1)) ),
% 39.25/5.54      inference(superposition,[status(thm)],[c_432,c_434]) ).
% 39.25/5.54  
% 39.25/5.54  cnf(c_1212,plain,
% 39.25/5.54      ( k10_relat_1(sK1,k2_xboole_0(X0,k2_relat_1(sK1))) = k2_xboole_0(k10_relat_1(sK1,X0),k1_relat_1(sK1)) ),
% 39.25/5.54      inference(superposition,[status(thm)],[c_701,c_881]) ).
% 39.25/5.54  
% 39.25/5.54  cnf(c_6,plain,
% 39.25/5.54      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 39.25/5.54      inference(cnf_transformation,[],[f30]) ).
% 39.25/5.54  
% 39.25/5.54  cnf(c_436,plain,
% 39.25/5.54      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) = iProver_top
% 39.25/5.54      | v1_relat_1(X0) != iProver_top ),
% 39.25/5.54      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 39.25/5.54  
% 39.25/5.54  cnf(c_4404,plain,
% 39.25/5.54      ( r1_tarski(k2_xboole_0(k10_relat_1(sK1,X0),k1_relat_1(sK1)),k1_relat_1(sK1)) = iProver_top
% 39.25/5.54      | v1_relat_1(sK1) != iProver_top ),
% 39.25/5.54      inference(superposition,[status(thm)],[c_1212,c_436]) ).
% 39.25/5.54  
% 39.25/5.54  cnf(c_14,plain,
% 39.25/5.54      ( v1_relat_1(sK1) = iProver_top ),
% 39.25/5.54      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 39.25/5.54  
% 39.25/5.54  cnf(c_4441,plain,
% 39.25/5.54      ( r1_tarski(k2_xboole_0(k10_relat_1(sK1,X0),k1_relat_1(sK1)),k1_relat_1(sK1)) = iProver_top ),
% 39.25/5.54      inference(global_propositional_subsumption,
% 39.25/5.54                [status(thm)],
% 39.25/5.54                [c_4404,c_14]) ).
% 39.25/5.54  
% 39.25/5.54  cnf(c_0,plain,
% 39.25/5.54      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 39.25/5.54      inference(cnf_transformation,[],[f26]) ).
% 39.25/5.54  
% 39.25/5.54  cnf(c_441,plain,
% 39.25/5.54      ( X0 = X1
% 39.25/5.54      | r1_tarski(X0,X1) != iProver_top
% 39.25/5.54      | r1_tarski(X1,X0) != iProver_top ),
% 39.25/5.54      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 39.25/5.54  
% 39.25/5.54  cnf(c_4450,plain,
% 39.25/5.54      ( k2_xboole_0(k10_relat_1(sK1,X0),k1_relat_1(sK1)) = k1_relat_1(sK1)
% 39.25/5.54      | r1_tarski(k1_relat_1(sK1),k2_xboole_0(k10_relat_1(sK1,X0),k1_relat_1(sK1))) != iProver_top ),
% 39.25/5.54      inference(superposition,[status(thm)],[c_4441,c_441]) ).
% 39.25/5.54  
% 39.25/5.54  cnf(c_1040,plain,
% 39.25/5.54      ( r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) = iProver_top
% 39.25/5.54      | v1_relat_1(sK1) != iProver_top ),
% 39.25/5.54      inference(superposition,[status(thm)],[c_701,c_436]) ).
% 39.25/5.54  
% 39.25/5.54  cnf(c_3,plain,
% 39.25/5.54      ( ~ r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
% 39.25/5.54      inference(cnf_transformation,[],[f27]) ).
% 39.25/5.54  
% 39.25/5.54  cnf(c_439,plain,
% 39.25/5.54      ( r1_tarski(X0,X1) != iProver_top
% 39.25/5.54      | r1_tarski(X0,k2_xboole_0(X2,X1)) = iProver_top ),
% 39.25/5.54      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 39.25/5.54  
% 39.25/5.54  cnf(c_800,plain,
% 39.25/5.54      ( k2_xboole_0(X0,X1) = X2
% 39.25/5.54      | r1_tarski(X2,X1) != iProver_top
% 39.25/5.54      | r1_tarski(k2_xboole_0(X0,X1),X2) != iProver_top ),
% 39.25/5.54      inference(superposition,[status(thm)],[c_439,c_441]) ).
% 39.25/5.54  
% 39.25/5.54  cnf(c_5064,plain,
% 39.25/5.54      ( k2_xboole_0(k10_relat_1(sK1,X0),k1_relat_1(sK1)) = k1_relat_1(sK1)
% 39.25/5.54      | r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) != iProver_top ),
% 39.25/5.54      inference(superposition,[status(thm)],[c_4441,c_800]) ).
% 39.25/5.54  
% 39.25/5.54  cnf(c_6437,plain,
% 39.25/5.54      ( k2_xboole_0(k10_relat_1(sK1,X0),k1_relat_1(sK1)) = k1_relat_1(sK1) ),
% 39.25/5.54      inference(global_propositional_subsumption,
% 39.25/5.54                [status(thm)],
% 39.25/5.54                [c_4450,c_14,c_1040,c_5064]) ).
% 39.25/5.54  
% 39.25/5.54  cnf(c_882,plain,
% 39.25/5.54      ( k2_xboole_0(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1)) = k10_relat_1(sK0,k2_xboole_0(X0,X1)) ),
% 39.25/5.54      inference(superposition,[status(thm)],[c_431,c_434]) ).
% 39.25/5.54  
% 39.25/5.54  cnf(c_4,plain,
% 39.25/5.54      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 39.25/5.54      inference(cnf_transformation,[],[f28]) ).
% 39.25/5.54  
% 39.25/5.54  cnf(c_438,plain,
% 39.25/5.54      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 39.25/5.54      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 39.25/5.54  
% 39.25/5.54  cnf(c_1481,plain,
% 39.25/5.54      ( r1_tarski(k10_relat_1(sK0,X0),k10_relat_1(sK0,k2_xboole_0(X0,X1))) = iProver_top ),
% 39.25/5.54      inference(superposition,[status(thm)],[c_882,c_438]) ).
% 39.25/5.54  
% 39.25/5.54  cnf(c_6452,plain,
% 39.25/5.54      ( r1_tarski(k10_relat_1(sK0,k10_relat_1(sK1,X0)),k10_relat_1(sK0,k1_relat_1(sK1))) = iProver_top ),
% 39.25/5.54      inference(superposition,[status(thm)],[c_6437,c_1481]) ).
% 39.25/5.54  
% 39.25/5.54  cnf(c_140264,plain,
% 39.25/5.54      ( r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,k1_relat_1(sK1))) = iProver_top ),
% 39.25/5.54      inference(superposition,[status(thm)],[c_3465,c_6452]) ).
% 39.25/5.54  
% 39.25/5.54  cnf(c_1839,plain,
% 39.25/5.54      ( r1_tarski(k10_relat_1(sK0,k10_relat_1(sK1,X0)),k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top
% 39.25/5.54      | v1_relat_1(k5_relat_1(sK0,sK1)) != iProver_top ),
% 39.25/5.54      inference(superposition,[status(thm)],[c_1678,c_436]) ).
% 39.25/5.54  
% 39.25/5.54  cnf(c_13,plain,
% 39.25/5.54      ( v1_relat_1(sK0) = iProver_top ),
% 39.25/5.54      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 39.25/5.54  
% 39.25/5.54  cnf(c_651,plain,
% 39.25/5.54      ( v1_relat_1(k5_relat_1(sK0,sK1))
% 39.25/5.54      | ~ v1_relat_1(sK1)
% 39.25/5.54      | ~ v1_relat_1(sK0) ),
% 39.25/5.54      inference(instantiation,[status(thm)],[c_5]) ).
% 39.25/5.54  
% 39.25/5.54  cnf(c_652,plain,
% 39.25/5.54      ( v1_relat_1(k5_relat_1(sK0,sK1)) = iProver_top
% 39.25/5.54      | v1_relat_1(sK1) != iProver_top
% 39.25/5.54      | v1_relat_1(sK0) != iProver_top ),
% 39.25/5.54      inference(predicate_to_equality,[status(thm)],[c_651]) ).
% 39.25/5.54  
% 39.25/5.54  cnf(c_4209,plain,
% 39.25/5.54      ( r1_tarski(k10_relat_1(sK0,k10_relat_1(sK1,X0)),k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top ),
% 39.25/5.54      inference(global_propositional_subsumption,
% 39.25/5.54                [status(thm)],
% 39.25/5.54                [c_1839,c_13,c_14,c_652]) ).
% 39.25/5.54  
% 39.25/5.54  cnf(c_4215,plain,
% 39.25/5.54      ( r1_tarski(k10_relat_1(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top ),
% 39.25/5.54      inference(superposition,[status(thm)],[c_701,c_4209]) ).
% 39.25/5.54  
% 39.25/5.54  cnf(c_476,plain,
% 39.25/5.54      ( ~ r1_tarski(k10_relat_1(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(sK0,sK1)))
% 39.25/5.54      | ~ r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,k1_relat_1(sK1)))
% 39.25/5.54      | k10_relat_1(sK0,k1_relat_1(sK1)) = k1_relat_1(k5_relat_1(sK0,sK1)) ),
% 39.25/5.54      inference(instantiation,[status(thm)],[c_0]) ).
% 39.25/5.54  
% 39.25/5.54  cnf(c_477,plain,
% 39.25/5.54      ( k10_relat_1(sK0,k1_relat_1(sK1)) = k1_relat_1(k5_relat_1(sK0,sK1))
% 39.25/5.54      | r1_tarski(k10_relat_1(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(sK0,sK1))) != iProver_top
% 39.25/5.54      | r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,k1_relat_1(sK1))) != iProver_top ),
% 39.25/5.54      inference(predicate_to_equality,[status(thm)],[c_476]) ).
% 39.25/5.54  
% 39.25/5.54  cnf(c_10,negated_conjecture,
% 39.25/5.54      ( k10_relat_1(sK0,k1_relat_1(sK1)) != k1_relat_1(k5_relat_1(sK0,sK1)) ),
% 39.25/5.54      inference(cnf_transformation,[],[f36]) ).
% 39.25/5.54  
% 39.25/5.54  cnf(contradiction,plain,
% 39.25/5.54      ( $false ),
% 39.25/5.54      inference(minisat,[status(thm)],[c_140264,c_4215,c_477,c_10]) ).
% 39.25/5.54  
% 39.25/5.54  
% 39.25/5.54  % SZS output end CNFRefutation for theBenchmark.p
% 39.25/5.54  
% 39.25/5.54  ------                               Statistics
% 39.25/5.54  
% 39.25/5.54  ------ Selected
% 39.25/5.54  
% 39.25/5.54  total_time:                             4.55
% 39.25/5.54  
%------------------------------------------------------------------------------
