%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:43:58 EST 2020

% Result     : Theorem 4.00s
% Output     : CNFRefutation 4.00s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 633 expanded)
%              Number of clauses        :  104 ( 294 expanded)
%              Number of leaves         :   19 ( 141 expanded)
%              Depth                    :   20
%              Number of atoms          :  352 (1331 expanded)
%              Number of equality atoms :  204 ( 594 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ? [X0] : v1_xboole_0(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,
    ( ? [X0] : v1_xboole_0(X0)
   => v1_xboole_0(sK0) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f2,f28])).

fof(f35,plain,(
    v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f40,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f34,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f14,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f27,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f32,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK1,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK1) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK1,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK1) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f32])).

fof(f51,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f46,plain,(
    ! [X0] :
      ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f13,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f41,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f38,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f50,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f44,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f54,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f36])).

fof(f52,plain,
    ( k1_xboole_0 != k5_relat_1(sK1,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1,plain,
    ( v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_503,plain,
    ( v1_xboole_0(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_6,plain,
    ( v1_relat_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_499,plain,
    ( v1_relat_1(X0) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_813,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_503,c_499])).

cnf(c_0,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_504,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_809,plain,
    ( sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_503,c_504])).

cnf(c_1514,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_813,c_809])).

cnf(c_18,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_490,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_14,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_491,plain,
    ( k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,X0))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_734,plain,
    ( k5_relat_1(k4_relat_1(sK1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,sK1))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_490,c_491])).

cnf(c_1517,plain,
    ( k5_relat_1(k4_relat_1(sK1),k4_relat_1(k1_xboole_0)) = k4_relat_1(k5_relat_1(k1_xboole_0,sK1)) ),
    inference(superposition,[status(thm)],[c_1514,c_734])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_494,plain,
    ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1518,plain,
    ( k2_relat_1(k4_relat_1(k1_xboole_0)) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1514,c_494])).

cnf(c_16,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1532,plain,
    ( k2_relat_1(k4_relat_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1518,c_16])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_496,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k2_relat_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1659,plain,
    ( v1_relat_1(k4_relat_1(k1_xboole_0)) != iProver_top
    | v1_xboole_0(k4_relat_1(k1_xboole_0)) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1532,c_496])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k4_relat_1(X0)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_41,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_43,plain,
    ( v1_relat_1(k4_relat_1(k1_xboole_0)) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_41])).

cnf(c_44,plain,
    ( v1_relat_1(X0) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_46,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_44])).

cnf(c_55,plain,
    ( v1_xboole_0(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_686,plain,
    ( ~ v1_xboole_0(sK0)
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_231,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_691,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(sK0)
    | X0 != sK0 ),
    inference(instantiation,[status(thm)],[c_231])).

cnf(c_692,plain,
    ( X0 != sK0
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_691])).

cnf(c_694,plain,
    ( k1_xboole_0 != sK0
    | v1_xboole_0(sK0) != iProver_top
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_692])).

cnf(c_4847,plain,
    ( v1_xboole_0(k4_relat_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1659,c_43,c_46,c_1,c_55,c_686,c_694])).

cnf(c_4853,plain,
    ( k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4847,c_504])).

cnf(c_6855,plain,
    ( k5_relat_1(k4_relat_1(sK1),k1_xboole_0) = k4_relat_1(k5_relat_1(k1_xboole_0,sK1)) ),
    inference(light_normalisation,[status(thm)],[c_1517,c_4853])).

cnf(c_13,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_492,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_502,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1226,plain,
    ( k2_relat_1(k5_relat_1(X0,X1)) = k2_relat_1(X1)
    | r1_tarski(k2_relat_1(X1),k2_relat_1(k5_relat_1(X0,X1))) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_492,c_502])).

cnf(c_6857,plain,
    ( k2_relat_1(k5_relat_1(k4_relat_1(sK1),k1_xboole_0)) = k2_relat_1(k1_xboole_0)
    | r1_tarski(k2_relat_1(k1_xboole_0),k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK1)))) != iProver_top
    | v1_relat_1(k4_relat_1(sK1)) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6855,c_1226])).

cnf(c_15,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_6879,plain,
    ( k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK1))) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK1)))) != iProver_top
    | v1_relat_1(k4_relat_1(sK1)) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6857,c_15,c_6855])).

cnf(c_19,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_620,plain,
    ( v1_relat_1(k4_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_621,plain,
    ( v1_relat_1(k4_relat_1(sK1)) = iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_620])).

cnf(c_7038,plain,
    ( k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK1))) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK1)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6879,c_19,c_46,c_1,c_55,c_621,c_686,c_694])).

cnf(c_5,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_500,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_7044,plain,
    ( k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK1))) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7038,c_500])).

cnf(c_7045,plain,
    ( v1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK1))) != iProver_top
    | v1_xboole_0(k4_relat_1(k5_relat_1(k1_xboole_0,sK1))) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7044,c_496])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_647,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k5_relat_1(X0,sK1))
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_648,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k5_relat_1(X0,sK1)) = iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_647])).

cnf(c_650,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,sK1)) = iProver_top
    | v1_relat_1(sK1) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_648])).

cnf(c_6627,plain,
    ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK1))
    | v1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK1))) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_6628,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,sK1)) != iProver_top
    | v1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6627])).

cnf(c_19325,plain,
    ( v1_xboole_0(k4_relat_1(k5_relat_1(k1_xboole_0,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7045,c_19,c_46,c_1,c_55,c_650,c_686,c_694,c_6628])).

cnf(c_19331,plain,
    ( k4_relat_1(k5_relat_1(k1_xboole_0,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_19325,c_504])).

cnf(c_497,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_861,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_15,c_492])).

cnf(c_1388,plain,
    ( v1_relat_1(X0) != iProver_top
    | r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_861,c_46,c_1,c_55,c_686,c_694])).

cnf(c_1389,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1388])).

cnf(c_1225,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_500,c_502])).

cnf(c_2205,plain,
    ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1389,c_1225])).

cnf(c_9967,plain,
    ( k2_relat_1(k5_relat_1(sK1,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_490,c_2205])).

cnf(c_9999,plain,
    ( v1_relat_1(k5_relat_1(sK1,k1_xboole_0)) != iProver_top
    | v1_xboole_0(k5_relat_1(sK1,k1_xboole_0)) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9967,c_496])).

cnf(c_13713,plain,
    ( v1_xboole_0(k5_relat_1(sK1,k1_xboole_0)) = iProver_top
    | v1_relat_1(k5_relat_1(sK1,k1_xboole_0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9999,c_1,c_55,c_686,c_694])).

cnf(c_13714,plain,
    ( v1_relat_1(k5_relat_1(sK1,k1_xboole_0)) != iProver_top
    | v1_xboole_0(k5_relat_1(sK1,k1_xboole_0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_13713])).

cnf(c_13719,plain,
    ( v1_relat_1(sK1) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top
    | v1_xboole_0(k5_relat_1(sK1,k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_497,c_13714])).

cnf(c_230,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2470,plain,
    ( ~ v1_xboole_0(X0)
    | X1 != X0
    | k1_xboole_0 = X1 ),
    inference(resolution,[status(thm)],[c_230,c_0])).

cnf(c_234,plain,
    ( X0 != X1
    | k4_relat_1(X0) = k4_relat_1(X1) ),
    theory(equality)).

cnf(c_5518,plain,
    ( ~ v1_xboole_0(k4_relat_1(X0))
    | X1 != X0
    | k1_xboole_0 = k4_relat_1(X1) ),
    inference(resolution,[status(thm)],[c_2470,c_234])).

cnf(c_5520,plain,
    ( ~ v1_xboole_0(k4_relat_1(k1_xboole_0))
    | k1_xboole_0 = k4_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5518])).

cnf(c_2371,plain,
    ( k4_relat_1(k5_relat_1(k1_xboole_0,sK1)) != X0
    | k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK1))) = k4_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_234])).

cnf(c_2373,plain,
    ( k4_relat_1(k5_relat_1(k1_xboole_0,sK1)) != k1_xboole_0
    | k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK1))) = k4_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2371])).

cnf(c_1850,plain,
    ( k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK1))) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK1))) ),
    inference(instantiation,[status(thm)],[c_230])).

cnf(c_2370,plain,
    ( k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK1))) != k4_relat_1(X0)
    | k1_xboole_0 != k4_relat_1(X0)
    | k1_xboole_0 = k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK1))) ),
    inference(instantiation,[status(thm)],[c_1850])).

cnf(c_2372,plain,
    ( k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK1))) != k4_relat_1(k1_xboole_0)
    | k1_xboole_0 = k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK1)))
    | k1_xboole_0 != k4_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2370])).

cnf(c_1673,plain,
    ( ~ v1_relat_1(k4_relat_1(k1_xboole_0))
    | v1_xboole_0(k4_relat_1(k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1659])).

cnf(c_683,plain,
    ( k5_relat_1(k1_xboole_0,sK1) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK1) ),
    inference(instantiation,[status(thm)],[c_230])).

cnf(c_1373,plain,
    ( k5_relat_1(k1_xboole_0,sK1) != k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK1)))
    | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK1)
    | k1_xboole_0 != k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK1))) ),
    inference(instantiation,[status(thm)],[c_683])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | k4_relat_1(k4_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1209,plain,
    ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK1))
    | k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK1))) = k5_relat_1(k1_xboole_0,sK1) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_769,plain,
    ( X0 != X1
    | k5_relat_1(k1_xboole_0,sK1) != X1
    | k5_relat_1(k1_xboole_0,sK1) = X0 ),
    inference(instantiation,[status(thm)],[c_230])).

cnf(c_1031,plain,
    ( X0 != k5_relat_1(k1_xboole_0,sK1)
    | k5_relat_1(k1_xboole_0,sK1) = X0
    | k5_relat_1(k1_xboole_0,sK1) != k5_relat_1(k1_xboole_0,sK1) ),
    inference(instantiation,[status(thm)],[c_769])).

cnf(c_1208,plain,
    ( k5_relat_1(k1_xboole_0,sK1) != k5_relat_1(k1_xboole_0,sK1)
    | k5_relat_1(k1_xboole_0,sK1) = k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK1)))
    | k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK1))) != k5_relat_1(k1_xboole_0,sK1) ),
    inference(instantiation,[status(thm)],[c_1031])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_910,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,sK1),k5_relat_1(k1_xboole_0,sK1)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_763,plain,
    ( ~ r1_tarski(X0,k5_relat_1(k1_xboole_0,sK1))
    | ~ r1_tarski(k5_relat_1(k1_xboole_0,sK1),X0)
    | k5_relat_1(k1_xboole_0,sK1) = X0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_909,plain,
    ( ~ r1_tarski(k5_relat_1(k1_xboole_0,sK1),k5_relat_1(k1_xboole_0,sK1))
    | k5_relat_1(k1_xboole_0,sK1) = k5_relat_1(k1_xboole_0,sK1) ),
    inference(instantiation,[status(thm)],[c_763])).

cnf(c_17,negated_conjecture,
    ( k1_xboole_0 != k5_relat_1(sK1,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_874,plain,
    ( ~ v1_xboole_0(k5_relat_1(sK1,k1_xboole_0))
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK1) ),
    inference(resolution,[status(thm)],[c_0,c_17])).

cnf(c_875,plain,
    ( k1_xboole_0 != k5_relat_1(k1_xboole_0,sK1)
    | v1_xboole_0(k5_relat_1(sK1,k1_xboole_0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_874])).

cnf(c_693,plain,
    ( ~ v1_xboole_0(sK0)
    | v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_691])).

cnf(c_649,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,sK1))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_647])).

cnf(c_53,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_48,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_45,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_42,plain,
    ( v1_relat_1(k4_relat_1(k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_19331,c_13719,c_5520,c_2373,c_2372,c_1673,c_1373,c_1209,c_1208,c_910,c_909,c_875,c_694,c_693,c_686,c_649,c_55,c_1,c_53,c_48,c_46,c_45,c_42,c_19,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n001.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 17:48:15 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  % Running in FOF mode
% 4.00/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.00/0.97  
% 4.00/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.00/0.97  
% 4.00/0.97  ------  iProver source info
% 4.00/0.97  
% 4.00/0.97  git: date: 2020-06-30 10:37:57 +0100
% 4.00/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.00/0.97  git: non_committed_changes: false
% 4.00/0.97  git: last_make_outside_of_git: false
% 4.00/0.97  
% 4.00/0.97  ------ 
% 4.00/0.97  
% 4.00/0.97  ------ Input Options
% 4.00/0.97  
% 4.00/0.97  --out_options                           all
% 4.00/0.97  --tptp_safe_out                         true
% 4.00/0.97  --problem_path                          ""
% 4.00/0.97  --include_path                          ""
% 4.00/0.97  --clausifier                            res/vclausify_rel
% 4.00/0.97  --clausifier_options                    --mode clausify
% 4.00/0.97  --stdin                                 false
% 4.00/0.97  --stats_out                             sel
% 4.00/0.97  
% 4.00/0.97  ------ General Options
% 4.00/0.97  
% 4.00/0.97  --fof                                   false
% 4.00/0.97  --time_out_real                         604.99
% 4.00/0.97  --time_out_virtual                      -1.
% 4.00/0.97  --symbol_type_check                     false
% 4.00/0.97  --clausify_out                          false
% 4.00/0.97  --sig_cnt_out                           false
% 4.00/0.97  --trig_cnt_out                          false
% 4.00/0.97  --trig_cnt_out_tolerance                1.
% 4.00/0.97  --trig_cnt_out_sk_spl                   false
% 4.00/0.97  --abstr_cl_out                          false
% 4.00/0.97  
% 4.00/0.97  ------ Global Options
% 4.00/0.97  
% 4.00/0.97  --schedule                              none
% 4.00/0.97  --add_important_lit                     false
% 4.00/0.97  --prop_solver_per_cl                    1000
% 4.00/0.97  --min_unsat_core                        false
% 4.00/0.97  --soft_assumptions                      false
% 4.00/0.97  --soft_lemma_size                       3
% 4.00/0.97  --prop_impl_unit_size                   0
% 4.00/0.97  --prop_impl_unit                        []
% 4.00/0.97  --share_sel_clauses                     true
% 4.00/0.97  --reset_solvers                         false
% 4.00/0.97  --bc_imp_inh                            [conj_cone]
% 4.00/0.97  --conj_cone_tolerance                   3.
% 4.00/0.97  --extra_neg_conj                        none
% 4.00/0.97  --large_theory_mode                     true
% 4.00/0.97  --prolific_symb_bound                   200
% 4.00/0.97  --lt_threshold                          2000
% 4.00/0.97  --clause_weak_htbl                      true
% 4.00/0.97  --gc_record_bc_elim                     false
% 4.00/0.97  
% 4.00/0.97  ------ Preprocessing Options
% 4.00/0.97  
% 4.00/0.97  --preprocessing_flag                    true
% 4.00/0.97  --time_out_prep_mult                    0.1
% 4.00/0.97  --splitting_mode                        input
% 4.00/0.97  --splitting_grd                         true
% 4.00/0.97  --splitting_cvd                         false
% 4.00/0.97  --splitting_cvd_svl                     false
% 4.00/0.97  --splitting_nvd                         32
% 4.00/0.97  --sub_typing                            true
% 4.00/0.97  --prep_gs_sim                           false
% 4.00/0.97  --prep_unflatten                        true
% 4.00/0.97  --prep_res_sim                          true
% 4.00/0.97  --prep_upred                            true
% 4.00/0.97  --prep_sem_filter                       exhaustive
% 4.00/0.97  --prep_sem_filter_out                   false
% 4.00/0.97  --pred_elim                             false
% 4.00/0.97  --res_sim_input                         true
% 4.00/0.97  --eq_ax_congr_red                       true
% 4.00/0.97  --pure_diseq_elim                       true
% 4.00/0.97  --brand_transform                       false
% 4.00/0.97  --non_eq_to_eq                          false
% 4.00/0.97  --prep_def_merge                        true
% 4.00/0.97  --prep_def_merge_prop_impl              false
% 4.00/0.97  --prep_def_merge_mbd                    true
% 4.00/0.97  --prep_def_merge_tr_red                 false
% 4.00/0.97  --prep_def_merge_tr_cl                  false
% 4.00/0.97  --smt_preprocessing                     true
% 4.00/0.97  --smt_ac_axioms                         fast
% 4.00/0.97  --preprocessed_out                      false
% 4.00/0.97  --preprocessed_stats                    false
% 4.00/0.97  
% 4.00/0.97  ------ Abstraction refinement Options
% 4.00/0.97  
% 4.00/0.97  --abstr_ref                             []
% 4.00/0.97  --abstr_ref_prep                        false
% 4.00/0.97  --abstr_ref_until_sat                   false
% 4.00/0.97  --abstr_ref_sig_restrict                funpre
% 4.00/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 4.00/0.97  --abstr_ref_under                       []
% 4.00/0.97  
% 4.00/0.97  ------ SAT Options
% 4.00/0.97  
% 4.00/0.97  --sat_mode                              false
% 4.00/0.97  --sat_fm_restart_options                ""
% 4.00/0.97  --sat_gr_def                            false
% 4.00/0.97  --sat_epr_types                         true
% 4.00/0.97  --sat_non_cyclic_types                  false
% 4.00/0.97  --sat_finite_models                     false
% 4.00/0.97  --sat_fm_lemmas                         false
% 4.00/0.97  --sat_fm_prep                           false
% 4.00/0.97  --sat_fm_uc_incr                        true
% 4.00/0.97  --sat_out_model                         small
% 4.00/0.97  --sat_out_clauses                       false
% 4.00/0.97  
% 4.00/0.97  ------ QBF Options
% 4.00/0.97  
% 4.00/0.97  --qbf_mode                              false
% 4.00/0.97  --qbf_elim_univ                         false
% 4.00/0.97  --qbf_dom_inst                          none
% 4.00/0.97  --qbf_dom_pre_inst                      false
% 4.00/0.97  --qbf_sk_in                             false
% 4.00/0.97  --qbf_pred_elim                         true
% 4.00/0.97  --qbf_split                             512
% 4.00/0.97  
% 4.00/0.97  ------ BMC1 Options
% 4.00/0.97  
% 4.00/0.97  --bmc1_incremental                      false
% 4.00/0.97  --bmc1_axioms                           reachable_all
% 4.00/0.97  --bmc1_min_bound                        0
% 4.00/0.97  --bmc1_max_bound                        -1
% 4.00/0.97  --bmc1_max_bound_default                -1
% 4.00/0.97  --bmc1_symbol_reachability              true
% 4.00/0.97  --bmc1_property_lemmas                  false
% 4.00/0.97  --bmc1_k_induction                      false
% 4.00/0.97  --bmc1_non_equiv_states                 false
% 4.00/0.97  --bmc1_deadlock                         false
% 4.00/0.97  --bmc1_ucm                              false
% 4.00/0.97  --bmc1_add_unsat_core                   none
% 4.00/0.97  --bmc1_unsat_core_children              false
% 4.00/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 4.00/0.97  --bmc1_out_stat                         full
% 4.00/0.97  --bmc1_ground_init                      false
% 4.00/0.97  --bmc1_pre_inst_next_state              false
% 4.00/0.97  --bmc1_pre_inst_state                   false
% 4.00/0.97  --bmc1_pre_inst_reach_state             false
% 4.00/0.97  --bmc1_out_unsat_core                   false
% 4.00/0.97  --bmc1_aig_witness_out                  false
% 4.00/0.97  --bmc1_verbose                          false
% 4.00/0.97  --bmc1_dump_clauses_tptp                false
% 4.00/0.97  --bmc1_dump_unsat_core_tptp             false
% 4.00/0.97  --bmc1_dump_file                        -
% 4.00/0.97  --bmc1_ucm_expand_uc_limit              128
% 4.00/0.97  --bmc1_ucm_n_expand_iterations          6
% 4.00/0.97  --bmc1_ucm_extend_mode                  1
% 4.00/0.97  --bmc1_ucm_init_mode                    2
% 4.00/0.97  --bmc1_ucm_cone_mode                    none
% 4.00/0.97  --bmc1_ucm_reduced_relation_type        0
% 4.00/0.97  --bmc1_ucm_relax_model                  4
% 4.00/0.97  --bmc1_ucm_full_tr_after_sat            true
% 4.00/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 4.00/0.97  --bmc1_ucm_layered_model                none
% 4.00/0.97  --bmc1_ucm_max_lemma_size               10
% 4.00/0.97  
% 4.00/0.97  ------ AIG Options
% 4.00/0.97  
% 4.00/0.97  --aig_mode                              false
% 4.00/0.97  
% 4.00/0.97  ------ Instantiation Options
% 4.00/0.97  
% 4.00/0.97  --instantiation_flag                    true
% 4.00/0.97  --inst_sos_flag                         false
% 4.00/0.97  --inst_sos_phase                        true
% 4.00/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.00/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.00/0.97  --inst_lit_sel_side                     num_symb
% 4.00/0.97  --inst_solver_per_active                1400
% 4.00/0.97  --inst_solver_calls_frac                1.
% 4.00/0.97  --inst_passive_queue_type               priority_queues
% 4.00/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.00/0.97  --inst_passive_queues_freq              [25;2]
% 4.00/0.97  --inst_dismatching                      true
% 4.00/0.97  --inst_eager_unprocessed_to_passive     true
% 4.00/0.97  --inst_prop_sim_given                   true
% 4.00/0.97  --inst_prop_sim_new                     false
% 4.00/0.97  --inst_subs_new                         false
% 4.00/0.97  --inst_eq_res_simp                      false
% 4.00/0.97  --inst_subs_given                       false
% 4.00/0.97  --inst_orphan_elimination               true
% 4.00/0.97  --inst_learning_loop_flag               true
% 4.00/0.97  --inst_learning_start                   3000
% 4.00/0.97  --inst_learning_factor                  2
% 4.00/0.97  --inst_start_prop_sim_after_learn       3
% 4.00/0.97  --inst_sel_renew                        solver
% 4.00/0.97  --inst_lit_activity_flag                true
% 4.00/0.97  --inst_restr_to_given                   false
% 4.00/0.97  --inst_activity_threshold               500
% 4.00/0.97  --inst_out_proof                        true
% 4.00/0.97  
% 4.00/0.97  ------ Resolution Options
% 4.00/0.97  
% 4.00/0.97  --resolution_flag                       true
% 4.00/0.97  --res_lit_sel                           adaptive
% 4.00/0.97  --res_lit_sel_side                      none
% 4.00/0.97  --res_ordering                          kbo
% 4.00/0.97  --res_to_prop_solver                    active
% 4.00/0.97  --res_prop_simpl_new                    false
% 4.00/0.97  --res_prop_simpl_given                  true
% 4.00/0.97  --res_passive_queue_type                priority_queues
% 4.00/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.00/0.97  --res_passive_queues_freq               [15;5]
% 4.00/0.97  --res_forward_subs                      full
% 4.00/0.97  --res_backward_subs                     full
% 4.00/0.97  --res_forward_subs_resolution           true
% 4.00/0.97  --res_backward_subs_resolution          true
% 4.00/0.97  --res_orphan_elimination                true
% 4.00/0.97  --res_time_limit                        2.
% 4.00/0.97  --res_out_proof                         true
% 4.00/0.97  
% 4.00/0.97  ------ Superposition Options
% 4.00/0.97  
% 4.00/0.97  --superposition_flag                    true
% 4.00/0.97  --sup_passive_queue_type                priority_queues
% 4.00/0.97  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.00/0.97  --sup_passive_queues_freq               [1;4]
% 4.00/0.97  --demod_completeness_check              fast
% 4.00/0.97  --demod_use_ground                      true
% 4.00/0.97  --sup_to_prop_solver                    passive
% 4.00/0.97  --sup_prop_simpl_new                    true
% 4.00/0.97  --sup_prop_simpl_given                  true
% 4.00/0.97  --sup_fun_splitting                     false
% 4.00/0.97  --sup_smt_interval                      50000
% 4.00/0.97  
% 4.00/0.97  ------ Superposition Simplification Setup
% 4.00/0.97  
% 4.00/0.97  --sup_indices_passive                   []
% 4.00/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.00/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.00/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.00/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 4.00/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.00/0.97  --sup_full_bw                           [BwDemod]
% 4.00/0.97  --sup_immed_triv                        [TrivRules]
% 4.00/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.00/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.00/0.97  --sup_immed_bw_main                     []
% 4.00/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.00/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 4.00/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.00/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.00/0.97  
% 4.00/0.97  ------ Combination Options
% 4.00/0.97  
% 4.00/0.97  --comb_res_mult                         3
% 4.00/0.97  --comb_sup_mult                         2
% 4.00/0.97  --comb_inst_mult                        10
% 4.00/0.97  
% 4.00/0.97  ------ Debug Options
% 4.00/0.97  
% 4.00/0.97  --dbg_backtrace                         false
% 4.00/0.97  --dbg_dump_prop_clauses                 false
% 4.00/0.97  --dbg_dump_prop_clauses_file            -
% 4.00/0.97  --dbg_out_stat                          false
% 4.00/0.97  ------ Parsing...
% 4.00/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.00/0.97  
% 4.00/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 4.00/0.97  
% 4.00/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.00/0.97  
% 4.00/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.00/0.97  ------ Proving...
% 4.00/0.97  ------ Problem Properties 
% 4.00/0.97  
% 4.00/0.97  
% 4.00/0.97  clauses                                 18
% 4.00/0.97  conjectures                             2
% 4.00/0.97  EPR                                     7
% 4.00/0.97  Horn                                    18
% 4.00/0.97  unary                                   6
% 4.00/0.97  binary                                  7
% 4.00/0.97  lits                                    35
% 4.00/0.97  lits eq                                 10
% 4.00/0.97  fd_pure                                 0
% 4.00/0.97  fd_pseudo                               0
% 4.00/0.97  fd_cond                                 1
% 4.00/0.97  fd_pseudo_cond                          1
% 4.00/0.97  AC symbols                              0
% 4.00/0.97  
% 4.00/0.97  ------ Input Options Time Limit: Unbounded
% 4.00/0.97  
% 4.00/0.97  
% 4.00/0.97  ------ 
% 4.00/0.97  Current options:
% 4.00/0.97  ------ 
% 4.00/0.97  
% 4.00/0.97  ------ Input Options
% 4.00/0.97  
% 4.00/0.97  --out_options                           all
% 4.00/0.97  --tptp_safe_out                         true
% 4.00/0.97  --problem_path                          ""
% 4.00/0.97  --include_path                          ""
% 4.00/0.97  --clausifier                            res/vclausify_rel
% 4.00/0.97  --clausifier_options                    --mode clausify
% 4.00/0.97  --stdin                                 false
% 4.00/0.97  --stats_out                             sel
% 4.00/0.97  
% 4.00/0.97  ------ General Options
% 4.00/0.97  
% 4.00/0.97  --fof                                   false
% 4.00/0.97  --time_out_real                         604.99
% 4.00/0.97  --time_out_virtual                      -1.
% 4.00/0.97  --symbol_type_check                     false
% 4.00/0.97  --clausify_out                          false
% 4.00/0.97  --sig_cnt_out                           false
% 4.00/0.97  --trig_cnt_out                          false
% 4.00/0.97  --trig_cnt_out_tolerance                1.
% 4.00/0.97  --trig_cnt_out_sk_spl                   false
% 4.00/0.97  --abstr_cl_out                          false
% 4.00/0.97  
% 4.00/0.97  ------ Global Options
% 4.00/0.97  
% 4.00/0.97  --schedule                              none
% 4.00/0.97  --add_important_lit                     false
% 4.00/0.97  --prop_solver_per_cl                    1000
% 4.00/0.97  --min_unsat_core                        false
% 4.00/0.97  --soft_assumptions                      false
% 4.00/0.97  --soft_lemma_size                       3
% 4.00/0.97  --prop_impl_unit_size                   0
% 4.00/0.97  --prop_impl_unit                        []
% 4.00/0.97  --share_sel_clauses                     true
% 4.00/0.97  --reset_solvers                         false
% 4.00/0.97  --bc_imp_inh                            [conj_cone]
% 4.00/0.97  --conj_cone_tolerance                   3.
% 4.00/0.97  --extra_neg_conj                        none
% 4.00/0.97  --large_theory_mode                     true
% 4.00/0.97  --prolific_symb_bound                   200
% 4.00/0.97  --lt_threshold                          2000
% 4.00/0.97  --clause_weak_htbl                      true
% 4.00/0.97  --gc_record_bc_elim                     false
% 4.00/0.97  
% 4.00/0.97  ------ Preprocessing Options
% 4.00/0.97  
% 4.00/0.97  --preprocessing_flag                    true
% 4.00/0.97  --time_out_prep_mult                    0.1
% 4.00/0.97  --splitting_mode                        input
% 4.00/0.97  --splitting_grd                         true
% 4.00/0.97  --splitting_cvd                         false
% 4.00/0.97  --splitting_cvd_svl                     false
% 4.00/0.97  --splitting_nvd                         32
% 4.00/0.97  --sub_typing                            true
% 4.00/0.97  --prep_gs_sim                           false
% 4.00/0.97  --prep_unflatten                        true
% 4.00/0.97  --prep_res_sim                          true
% 4.00/0.97  --prep_upred                            true
% 4.00/0.97  --prep_sem_filter                       exhaustive
% 4.00/0.97  --prep_sem_filter_out                   false
% 4.00/0.97  --pred_elim                             false
% 4.00/0.97  --res_sim_input                         true
% 4.00/0.97  --eq_ax_congr_red                       true
% 4.00/0.97  --pure_diseq_elim                       true
% 4.00/0.97  --brand_transform                       false
% 4.00/0.97  --non_eq_to_eq                          false
% 4.00/0.97  --prep_def_merge                        true
% 4.00/0.97  --prep_def_merge_prop_impl              false
% 4.00/0.97  --prep_def_merge_mbd                    true
% 4.00/0.97  --prep_def_merge_tr_red                 false
% 4.00/0.97  --prep_def_merge_tr_cl                  false
% 4.00/0.97  --smt_preprocessing                     true
% 4.00/0.97  --smt_ac_axioms                         fast
% 4.00/0.97  --preprocessed_out                      false
% 4.00/0.97  --preprocessed_stats                    false
% 4.00/0.97  
% 4.00/0.97  ------ Abstraction refinement Options
% 4.00/0.97  
% 4.00/0.97  --abstr_ref                             []
% 4.00/0.97  --abstr_ref_prep                        false
% 4.00/0.97  --abstr_ref_until_sat                   false
% 4.00/0.97  --abstr_ref_sig_restrict                funpre
% 4.00/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 4.00/0.97  --abstr_ref_under                       []
% 4.00/0.97  
% 4.00/0.97  ------ SAT Options
% 4.00/0.97  
% 4.00/0.97  --sat_mode                              false
% 4.00/0.97  --sat_fm_restart_options                ""
% 4.00/0.97  --sat_gr_def                            false
% 4.00/0.97  --sat_epr_types                         true
% 4.00/0.97  --sat_non_cyclic_types                  false
% 4.00/0.97  --sat_finite_models                     false
% 4.00/0.97  --sat_fm_lemmas                         false
% 4.00/0.97  --sat_fm_prep                           false
% 4.00/0.97  --sat_fm_uc_incr                        true
% 4.00/0.97  --sat_out_model                         small
% 4.00/0.97  --sat_out_clauses                       false
% 4.00/0.97  
% 4.00/0.97  ------ QBF Options
% 4.00/0.97  
% 4.00/0.97  --qbf_mode                              false
% 4.00/0.97  --qbf_elim_univ                         false
% 4.00/0.97  --qbf_dom_inst                          none
% 4.00/0.97  --qbf_dom_pre_inst                      false
% 4.00/0.97  --qbf_sk_in                             false
% 4.00/0.97  --qbf_pred_elim                         true
% 4.00/0.97  --qbf_split                             512
% 4.00/0.97  
% 4.00/0.97  ------ BMC1 Options
% 4.00/0.97  
% 4.00/0.97  --bmc1_incremental                      false
% 4.00/0.97  --bmc1_axioms                           reachable_all
% 4.00/0.97  --bmc1_min_bound                        0
% 4.00/0.97  --bmc1_max_bound                        -1
% 4.00/0.97  --bmc1_max_bound_default                -1
% 4.00/0.97  --bmc1_symbol_reachability              true
% 4.00/0.97  --bmc1_property_lemmas                  false
% 4.00/0.97  --bmc1_k_induction                      false
% 4.00/0.97  --bmc1_non_equiv_states                 false
% 4.00/0.97  --bmc1_deadlock                         false
% 4.00/0.97  --bmc1_ucm                              false
% 4.00/0.97  --bmc1_add_unsat_core                   none
% 4.00/0.97  --bmc1_unsat_core_children              false
% 4.00/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 4.00/0.97  --bmc1_out_stat                         full
% 4.00/0.97  --bmc1_ground_init                      false
% 4.00/0.97  --bmc1_pre_inst_next_state              false
% 4.00/0.97  --bmc1_pre_inst_state                   false
% 4.00/0.97  --bmc1_pre_inst_reach_state             false
% 4.00/0.97  --bmc1_out_unsat_core                   false
% 4.00/0.97  --bmc1_aig_witness_out                  false
% 4.00/0.97  --bmc1_verbose                          false
% 4.00/0.97  --bmc1_dump_clauses_tptp                false
% 4.00/0.97  --bmc1_dump_unsat_core_tptp             false
% 4.00/0.97  --bmc1_dump_file                        -
% 4.00/0.97  --bmc1_ucm_expand_uc_limit              128
% 4.00/0.97  --bmc1_ucm_n_expand_iterations          6
% 4.00/0.97  --bmc1_ucm_extend_mode                  1
% 4.00/0.97  --bmc1_ucm_init_mode                    2
% 4.00/0.97  --bmc1_ucm_cone_mode                    none
% 4.00/0.97  --bmc1_ucm_reduced_relation_type        0
% 4.00/0.97  --bmc1_ucm_relax_model                  4
% 4.00/0.97  --bmc1_ucm_full_tr_after_sat            true
% 4.00/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 4.00/0.97  --bmc1_ucm_layered_model                none
% 4.00/0.97  --bmc1_ucm_max_lemma_size               10
% 4.00/0.97  
% 4.00/0.97  ------ AIG Options
% 4.00/0.97  
% 4.00/0.97  --aig_mode                              false
% 4.00/0.97  
% 4.00/0.97  ------ Instantiation Options
% 4.00/0.97  
% 4.00/0.97  --instantiation_flag                    true
% 4.00/0.97  --inst_sos_flag                         false
% 4.00/0.97  --inst_sos_phase                        true
% 4.00/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.00/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.00/0.97  --inst_lit_sel_side                     num_symb
% 4.00/0.97  --inst_solver_per_active                1400
% 4.00/0.97  --inst_solver_calls_frac                1.
% 4.00/0.97  --inst_passive_queue_type               priority_queues
% 4.00/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.00/0.97  --inst_passive_queues_freq              [25;2]
% 4.00/0.97  --inst_dismatching                      true
% 4.00/0.97  --inst_eager_unprocessed_to_passive     true
% 4.00/0.97  --inst_prop_sim_given                   true
% 4.00/0.97  --inst_prop_sim_new                     false
% 4.00/0.97  --inst_subs_new                         false
% 4.00/0.97  --inst_eq_res_simp                      false
% 4.00/0.97  --inst_subs_given                       false
% 4.00/0.97  --inst_orphan_elimination               true
% 4.00/0.97  --inst_learning_loop_flag               true
% 4.00/0.97  --inst_learning_start                   3000
% 4.00/0.97  --inst_learning_factor                  2
% 4.00/0.97  --inst_start_prop_sim_after_learn       3
% 4.00/0.97  --inst_sel_renew                        solver
% 4.00/0.97  --inst_lit_activity_flag                true
% 4.00/0.97  --inst_restr_to_given                   false
% 4.00/0.97  --inst_activity_threshold               500
% 4.00/0.97  --inst_out_proof                        true
% 4.00/0.97  
% 4.00/0.97  ------ Resolution Options
% 4.00/0.97  
% 4.00/0.97  --resolution_flag                       true
% 4.00/0.97  --res_lit_sel                           adaptive
% 4.00/0.97  --res_lit_sel_side                      none
% 4.00/0.97  --res_ordering                          kbo
% 4.00/0.97  --res_to_prop_solver                    active
% 4.00/0.97  --res_prop_simpl_new                    false
% 4.00/0.97  --res_prop_simpl_given                  true
% 4.00/0.97  --res_passive_queue_type                priority_queues
% 4.00/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.00/0.97  --res_passive_queues_freq               [15;5]
% 4.00/0.97  --res_forward_subs                      full
% 4.00/0.97  --res_backward_subs                     full
% 4.00/0.97  --res_forward_subs_resolution           true
% 4.00/0.97  --res_backward_subs_resolution          true
% 4.00/0.97  --res_orphan_elimination                true
% 4.00/0.97  --res_time_limit                        2.
% 4.00/0.97  --res_out_proof                         true
% 4.00/0.97  
% 4.00/0.97  ------ Superposition Options
% 4.00/0.97  
% 4.00/0.97  --superposition_flag                    true
% 4.00/0.97  --sup_passive_queue_type                priority_queues
% 4.00/0.97  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.00/0.97  --sup_passive_queues_freq               [1;4]
% 4.00/0.97  --demod_completeness_check              fast
% 4.00/0.97  --demod_use_ground                      true
% 4.00/0.97  --sup_to_prop_solver                    passive
% 4.00/0.97  --sup_prop_simpl_new                    true
% 4.00/0.97  --sup_prop_simpl_given                  true
% 4.00/0.97  --sup_fun_splitting                     false
% 4.00/0.97  --sup_smt_interval                      50000
% 4.00/0.97  
% 4.00/0.97  ------ Superposition Simplification Setup
% 4.00/0.97  
% 4.00/0.97  --sup_indices_passive                   []
% 4.00/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.00/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.00/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.00/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 4.00/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.00/0.97  --sup_full_bw                           [BwDemod]
% 4.00/0.97  --sup_immed_triv                        [TrivRules]
% 4.00/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.00/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.00/0.97  --sup_immed_bw_main                     []
% 4.00/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.00/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 4.00/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.00/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.00/0.97  
% 4.00/0.97  ------ Combination Options
% 4.00/0.97  
% 4.00/0.97  --comb_res_mult                         3
% 4.00/0.97  --comb_sup_mult                         2
% 4.00/0.97  --comb_inst_mult                        10
% 4.00/0.97  
% 4.00/0.97  ------ Debug Options
% 4.00/0.97  
% 4.00/0.97  --dbg_backtrace                         false
% 4.00/0.97  --dbg_dump_prop_clauses                 false
% 4.00/0.97  --dbg_dump_prop_clauses_file            -
% 4.00/0.97  --dbg_out_stat                          false
% 4.00/0.97  
% 4.00/0.97  
% 4.00/0.97  
% 4.00/0.97  
% 4.00/0.97  ------ Proving...
% 4.00/0.97  
% 4.00/0.97  
% 4.00/0.97  % SZS status Theorem for theBenchmark.p
% 4.00/0.97  
% 4.00/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 4.00/0.97  
% 4.00/0.97  fof(f2,axiom,(
% 4.00/0.97    ? [X0] : v1_xboole_0(X0)),
% 4.00/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.97  
% 4.00/0.97  fof(f28,plain,(
% 4.00/0.97    ? [X0] : v1_xboole_0(X0) => v1_xboole_0(sK0)),
% 4.00/0.97    introduced(choice_axiom,[])).
% 4.00/0.97  
% 4.00/0.97  fof(f29,plain,(
% 4.00/0.97    v1_xboole_0(sK0)),
% 4.00/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f2,f28])).
% 4.00/0.97  
% 4.00/0.97  fof(f35,plain,(
% 4.00/0.97    v1_xboole_0(sK0)),
% 4.00/0.97    inference(cnf_transformation,[],[f29])).
% 4.00/0.97  
% 4.00/0.97  fof(f5,axiom,(
% 4.00/0.97    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 4.00/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.97  
% 4.00/0.97  fof(f17,plain,(
% 4.00/0.97    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 4.00/0.97    inference(ennf_transformation,[],[f5])).
% 4.00/0.97  
% 4.00/0.97  fof(f40,plain,(
% 4.00/0.97    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 4.00/0.97    inference(cnf_transformation,[],[f17])).
% 4.00/0.97  
% 4.00/0.97  fof(f1,axiom,(
% 4.00/0.97    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 4.00/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.97  
% 4.00/0.97  fof(f16,plain,(
% 4.00/0.97    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 4.00/0.97    inference(ennf_transformation,[],[f1])).
% 4.00/0.97  
% 4.00/0.97  fof(f34,plain,(
% 4.00/0.97    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 4.00/0.97    inference(cnf_transformation,[],[f16])).
% 4.00/0.97  
% 4.00/0.97  fof(f14,conjecture,(
% 4.00/0.97    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 4.00/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.97  
% 4.00/0.97  fof(f15,negated_conjecture,(
% 4.00/0.97    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 4.00/0.97    inference(negated_conjecture,[],[f14])).
% 4.00/0.97  
% 4.00/0.97  fof(f27,plain,(
% 4.00/0.97    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 4.00/0.97    inference(ennf_transformation,[],[f15])).
% 4.00/0.97  
% 4.00/0.97  fof(f32,plain,(
% 4.00/0.97    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK1,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK1)) & v1_relat_1(sK1))),
% 4.00/0.97    introduced(choice_axiom,[])).
% 4.00/0.97  
% 4.00/0.97  fof(f33,plain,(
% 4.00/0.97    (k1_xboole_0 != k5_relat_1(sK1,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK1)) & v1_relat_1(sK1)),
% 4.00/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f32])).
% 4.00/0.97  
% 4.00/0.97  fof(f51,plain,(
% 4.00/0.97    v1_relat_1(sK1)),
% 4.00/0.97    inference(cnf_transformation,[],[f33])).
% 4.00/0.97  
% 4.00/0.97  fof(f12,axiom,(
% 4.00/0.97    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 4.00/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.97  
% 4.00/0.97  fof(f26,plain,(
% 4.00/0.97    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 4.00/0.97    inference(ennf_transformation,[],[f12])).
% 4.00/0.97  
% 4.00/0.97  fof(f48,plain,(
% 4.00/0.97    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 4.00/0.97    inference(cnf_transformation,[],[f26])).
% 4.00/0.97  
% 4.00/0.97  fof(f10,axiom,(
% 4.00/0.97    ! [X0] : (v1_relat_1(X0) => (k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 4.00/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.97  
% 4.00/0.97  fof(f24,plain,(
% 4.00/0.97    ! [X0] : ((k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 4.00/0.97    inference(ennf_transformation,[],[f10])).
% 4.00/0.97  
% 4.00/0.97  fof(f46,plain,(
% 4.00/0.97    ( ! [X0] : (k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 4.00/0.97    inference(cnf_transformation,[],[f24])).
% 4.00/0.97  
% 4.00/0.97  fof(f13,axiom,(
% 4.00/0.97    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 4.00/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.97  
% 4.00/0.97  fof(f49,plain,(
% 4.00/0.97    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 4.00/0.97    inference(cnf_transformation,[],[f13])).
% 4.00/0.97  
% 4.00/0.97  fof(f8,axiom,(
% 4.00/0.97    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k2_relat_1(X0)))),
% 4.00/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.97  
% 4.00/0.97  fof(f21,plain,(
% 4.00/0.97    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 4.00/0.97    inference(ennf_transformation,[],[f8])).
% 4.00/0.97  
% 4.00/0.97  fof(f22,plain,(
% 4.00/0.97    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 4.00/0.97    inference(flattening,[],[f21])).
% 4.00/0.97  
% 4.00/0.97  fof(f43,plain,(
% 4.00/0.97    ( ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 4.00/0.97    inference(cnf_transformation,[],[f22])).
% 4.00/0.97  
% 4.00/0.97  fof(f6,axiom,(
% 4.00/0.97    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 4.00/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.97  
% 4.00/0.97  fof(f18,plain,(
% 4.00/0.97    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 4.00/0.97    inference(ennf_transformation,[],[f6])).
% 4.00/0.97  
% 4.00/0.97  fof(f41,plain,(
% 4.00/0.97    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 4.00/0.97    inference(cnf_transformation,[],[f18])).
% 4.00/0.97  
% 4.00/0.97  fof(f11,axiom,(
% 4.00/0.97    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 4.00/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.97  
% 4.00/0.97  fof(f25,plain,(
% 4.00/0.97    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 4.00/0.97    inference(ennf_transformation,[],[f11])).
% 4.00/0.97  
% 4.00/0.97  fof(f47,plain,(
% 4.00/0.97    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 4.00/0.97    inference(cnf_transformation,[],[f25])).
% 4.00/0.97  
% 4.00/0.97  fof(f3,axiom,(
% 4.00/0.97    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 4.00/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.97  
% 4.00/0.97  fof(f30,plain,(
% 4.00/0.97    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.00/0.97    inference(nnf_transformation,[],[f3])).
% 4.00/0.97  
% 4.00/0.97  fof(f31,plain,(
% 4.00/0.97    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.00/0.97    inference(flattening,[],[f30])).
% 4.00/0.97  
% 4.00/0.97  fof(f38,plain,(
% 4.00/0.97    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 4.00/0.97    inference(cnf_transformation,[],[f31])).
% 4.00/0.97  
% 4.00/0.97  fof(f50,plain,(
% 4.00/0.97    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 4.00/0.97    inference(cnf_transformation,[],[f13])).
% 4.00/0.97  
% 4.00/0.97  fof(f4,axiom,(
% 4.00/0.97    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 4.00/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.97  
% 4.00/0.97  fof(f39,plain,(
% 4.00/0.97    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 4.00/0.97    inference(cnf_transformation,[],[f4])).
% 4.00/0.97  
% 4.00/0.97  fof(f7,axiom,(
% 4.00/0.97    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 4.00/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.97  
% 4.00/0.97  fof(f19,plain,(
% 4.00/0.97    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 4.00/0.97    inference(ennf_transformation,[],[f7])).
% 4.00/0.97  
% 4.00/0.97  fof(f20,plain,(
% 4.00/0.97    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 4.00/0.97    inference(flattening,[],[f19])).
% 4.00/0.97  
% 4.00/0.97  fof(f42,plain,(
% 4.00/0.97    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 4.00/0.97    inference(cnf_transformation,[],[f20])).
% 4.00/0.97  
% 4.00/0.97  fof(f9,axiom,(
% 4.00/0.97    ! [X0] : (v1_relat_1(X0) => k4_relat_1(k4_relat_1(X0)) = X0)),
% 4.00/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.97  
% 4.00/0.97  fof(f23,plain,(
% 4.00/0.97    ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 4.00/0.97    inference(ennf_transformation,[],[f9])).
% 4.00/0.97  
% 4.00/0.97  fof(f44,plain,(
% 4.00/0.97    ( ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 4.00/0.97    inference(cnf_transformation,[],[f23])).
% 4.00/0.97  
% 4.00/0.97  fof(f36,plain,(
% 4.00/0.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 4.00/0.97    inference(cnf_transformation,[],[f31])).
% 4.00/0.97  
% 4.00/0.97  fof(f54,plain,(
% 4.00/0.97    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 4.00/0.97    inference(equality_resolution,[],[f36])).
% 4.00/0.97  
% 4.00/0.97  fof(f52,plain,(
% 4.00/0.97    k1_xboole_0 != k5_relat_1(sK1,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK1)),
% 4.00/0.97    inference(cnf_transformation,[],[f33])).
% 4.00/0.97  
% 4.00/0.97  cnf(c_1,plain,
% 4.00/0.97      ( v1_xboole_0(sK0) ),
% 4.00/0.97      inference(cnf_transformation,[],[f35]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_503,plain,
% 4.00/0.97      ( v1_xboole_0(sK0) = iProver_top ),
% 4.00/0.97      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_6,plain,
% 4.00/0.97      ( v1_relat_1(X0) | ~ v1_xboole_0(X0) ),
% 4.00/0.97      inference(cnf_transformation,[],[f40]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_499,plain,
% 4.00/0.97      ( v1_relat_1(X0) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 4.00/0.97      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_813,plain,
% 4.00/0.97      ( v1_relat_1(sK0) = iProver_top ),
% 4.00/0.97      inference(superposition,[status(thm)],[c_503,c_499]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_0,plain,
% 4.00/0.97      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 4.00/0.97      inference(cnf_transformation,[],[f34]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_504,plain,
% 4.00/0.97      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 4.00/0.97      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_809,plain,
% 4.00/0.97      ( sK0 = k1_xboole_0 ),
% 4.00/0.97      inference(superposition,[status(thm)],[c_503,c_504]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_1514,plain,
% 4.00/0.97      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 4.00/0.97      inference(light_normalisation,[status(thm)],[c_813,c_809]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_18,negated_conjecture,
% 4.00/0.97      ( v1_relat_1(sK1) ),
% 4.00/0.97      inference(cnf_transformation,[],[f51]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_490,plain,
% 4.00/0.97      ( v1_relat_1(sK1) = iProver_top ),
% 4.00/0.97      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_14,plain,
% 4.00/0.97      ( ~ v1_relat_1(X0)
% 4.00/0.97      | ~ v1_relat_1(X1)
% 4.00/0.97      | k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1)) ),
% 4.00/0.97      inference(cnf_transformation,[],[f48]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_491,plain,
% 4.00/0.97      ( k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,X0))
% 4.00/0.97      | v1_relat_1(X1) != iProver_top
% 4.00/0.97      | v1_relat_1(X0) != iProver_top ),
% 4.00/0.97      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_734,plain,
% 4.00/0.97      ( k5_relat_1(k4_relat_1(sK1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,sK1))
% 4.00/0.97      | v1_relat_1(X0) != iProver_top ),
% 4.00/0.97      inference(superposition,[status(thm)],[c_490,c_491]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_1517,plain,
% 4.00/0.97      ( k5_relat_1(k4_relat_1(sK1),k4_relat_1(k1_xboole_0)) = k4_relat_1(k5_relat_1(k1_xboole_0,sK1)) ),
% 4.00/0.97      inference(superposition,[status(thm)],[c_1514,c_734]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_11,plain,
% 4.00/0.97      ( ~ v1_relat_1(X0) | k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) ),
% 4.00/0.97      inference(cnf_transformation,[],[f46]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_494,plain,
% 4.00/0.97      ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
% 4.00/0.97      | v1_relat_1(X0) != iProver_top ),
% 4.00/0.97      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_1518,plain,
% 4.00/0.97      ( k2_relat_1(k4_relat_1(k1_xboole_0)) = k1_relat_1(k1_xboole_0) ),
% 4.00/0.97      inference(superposition,[status(thm)],[c_1514,c_494]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_16,plain,
% 4.00/0.97      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 4.00/0.97      inference(cnf_transformation,[],[f49]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_1532,plain,
% 4.00/0.97      ( k2_relat_1(k4_relat_1(k1_xboole_0)) = k1_xboole_0 ),
% 4.00/0.97      inference(light_normalisation,[status(thm)],[c_1518,c_16]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_9,plain,
% 4.00/0.97      ( ~ v1_relat_1(X0)
% 4.00/0.97      | v1_xboole_0(X0)
% 4.00/0.97      | ~ v1_xboole_0(k2_relat_1(X0)) ),
% 4.00/0.97      inference(cnf_transformation,[],[f43]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_496,plain,
% 4.00/0.97      ( v1_relat_1(X0) != iProver_top
% 4.00/0.97      | v1_xboole_0(X0) = iProver_top
% 4.00/0.97      | v1_xboole_0(k2_relat_1(X0)) != iProver_top ),
% 4.00/0.97      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_1659,plain,
% 4.00/0.97      ( v1_relat_1(k4_relat_1(k1_xboole_0)) != iProver_top
% 4.00/0.97      | v1_xboole_0(k4_relat_1(k1_xboole_0)) = iProver_top
% 4.00/0.97      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 4.00/0.97      inference(superposition,[status(thm)],[c_1532,c_496]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_7,plain,
% 4.00/0.97      ( ~ v1_relat_1(X0) | v1_relat_1(k4_relat_1(X0)) ),
% 4.00/0.97      inference(cnf_transformation,[],[f41]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_41,plain,
% 4.00/0.97      ( v1_relat_1(X0) != iProver_top
% 4.00/0.97      | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
% 4.00/0.97      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_43,plain,
% 4.00/0.97      ( v1_relat_1(k4_relat_1(k1_xboole_0)) = iProver_top
% 4.00/0.97      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 4.00/0.97      inference(instantiation,[status(thm)],[c_41]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_44,plain,
% 4.00/0.97      ( v1_relat_1(X0) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 4.00/0.97      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_46,plain,
% 4.00/0.97      ( v1_relat_1(k1_xboole_0) = iProver_top
% 4.00/0.97      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 4.00/0.97      inference(instantiation,[status(thm)],[c_44]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_55,plain,
% 4.00/0.97      ( v1_xboole_0(sK0) = iProver_top ),
% 4.00/0.97      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_686,plain,
% 4.00/0.97      ( ~ v1_xboole_0(sK0) | k1_xboole_0 = sK0 ),
% 4.00/0.97      inference(instantiation,[status(thm)],[c_0]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_231,plain,
% 4.00/0.97      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 4.00/0.97      theory(equality) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_691,plain,
% 4.00/0.97      ( v1_xboole_0(X0) | ~ v1_xboole_0(sK0) | X0 != sK0 ),
% 4.00/0.97      inference(instantiation,[status(thm)],[c_231]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_692,plain,
% 4.00/0.97      ( X0 != sK0
% 4.00/0.97      | v1_xboole_0(X0) = iProver_top
% 4.00/0.97      | v1_xboole_0(sK0) != iProver_top ),
% 4.00/0.97      inference(predicate_to_equality,[status(thm)],[c_691]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_694,plain,
% 4.00/0.97      ( k1_xboole_0 != sK0
% 4.00/0.97      | v1_xboole_0(sK0) != iProver_top
% 4.00/0.97      | v1_xboole_0(k1_xboole_0) = iProver_top ),
% 4.00/0.97      inference(instantiation,[status(thm)],[c_692]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_4847,plain,
% 4.00/0.97      ( v1_xboole_0(k4_relat_1(k1_xboole_0)) = iProver_top ),
% 4.00/0.97      inference(global_propositional_subsumption,
% 4.00/0.97                [status(thm)],
% 4.00/0.97                [c_1659,c_43,c_46,c_1,c_55,c_686,c_694]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_4853,plain,
% 4.00/0.97      ( k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 4.00/0.97      inference(superposition,[status(thm)],[c_4847,c_504]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_6855,plain,
% 4.00/0.97      ( k5_relat_1(k4_relat_1(sK1),k1_xboole_0) = k4_relat_1(k5_relat_1(k1_xboole_0,sK1)) ),
% 4.00/0.97      inference(light_normalisation,[status(thm)],[c_1517,c_4853]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_13,plain,
% 4.00/0.97      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
% 4.00/0.97      | ~ v1_relat_1(X0)
% 4.00/0.97      | ~ v1_relat_1(X1) ),
% 4.00/0.97      inference(cnf_transformation,[],[f47]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_492,plain,
% 4.00/0.97      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
% 4.00/0.97      | v1_relat_1(X0) != iProver_top
% 4.00/0.97      | v1_relat_1(X1) != iProver_top ),
% 4.00/0.97      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_2,plain,
% 4.00/0.97      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 4.00/0.97      inference(cnf_transformation,[],[f38]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_502,plain,
% 4.00/0.97      ( X0 = X1
% 4.00/0.97      | r1_tarski(X0,X1) != iProver_top
% 4.00/0.97      | r1_tarski(X1,X0) != iProver_top ),
% 4.00/0.97      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_1226,plain,
% 4.00/0.97      ( k2_relat_1(k5_relat_1(X0,X1)) = k2_relat_1(X1)
% 4.00/0.97      | r1_tarski(k2_relat_1(X1),k2_relat_1(k5_relat_1(X0,X1))) != iProver_top
% 4.00/0.97      | v1_relat_1(X0) != iProver_top
% 4.00/0.97      | v1_relat_1(X1) != iProver_top ),
% 4.00/0.97      inference(superposition,[status(thm)],[c_492,c_502]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_6857,plain,
% 4.00/0.97      ( k2_relat_1(k5_relat_1(k4_relat_1(sK1),k1_xboole_0)) = k2_relat_1(k1_xboole_0)
% 4.00/0.97      | r1_tarski(k2_relat_1(k1_xboole_0),k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK1)))) != iProver_top
% 4.00/0.97      | v1_relat_1(k4_relat_1(sK1)) != iProver_top
% 4.00/0.97      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 4.00/0.97      inference(superposition,[status(thm)],[c_6855,c_1226]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_15,plain,
% 4.00/0.97      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 4.00/0.97      inference(cnf_transformation,[],[f50]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_6879,plain,
% 4.00/0.97      ( k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK1))) = k1_xboole_0
% 4.00/0.97      | r1_tarski(k1_xboole_0,k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK1)))) != iProver_top
% 4.00/0.97      | v1_relat_1(k4_relat_1(sK1)) != iProver_top
% 4.00/0.97      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 4.00/0.97      inference(light_normalisation,[status(thm)],[c_6857,c_15,c_6855]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_19,plain,
% 4.00/0.97      ( v1_relat_1(sK1) = iProver_top ),
% 4.00/0.97      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_620,plain,
% 4.00/0.97      ( v1_relat_1(k4_relat_1(sK1)) | ~ v1_relat_1(sK1) ),
% 4.00/0.97      inference(instantiation,[status(thm)],[c_7]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_621,plain,
% 4.00/0.97      ( v1_relat_1(k4_relat_1(sK1)) = iProver_top
% 4.00/0.97      | v1_relat_1(sK1) != iProver_top ),
% 4.00/0.97      inference(predicate_to_equality,[status(thm)],[c_620]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_7038,plain,
% 4.00/0.97      ( k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK1))) = k1_xboole_0
% 4.00/0.97      | r1_tarski(k1_xboole_0,k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK1)))) != iProver_top ),
% 4.00/0.97      inference(global_propositional_subsumption,
% 4.00/0.97                [status(thm)],
% 4.00/0.97                [c_6879,c_19,c_46,c_1,c_55,c_621,c_686,c_694]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_5,plain,
% 4.00/0.97      ( r1_tarski(k1_xboole_0,X0) ),
% 4.00/0.97      inference(cnf_transformation,[],[f39]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_500,plain,
% 4.00/0.97      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 4.00/0.97      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_7044,plain,
% 4.00/0.97      ( k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK1))) = k1_xboole_0 ),
% 4.00/0.97      inference(forward_subsumption_resolution,
% 4.00/0.97                [status(thm)],
% 4.00/0.97                [c_7038,c_500]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_7045,plain,
% 4.00/0.97      ( v1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK1))) != iProver_top
% 4.00/0.97      | v1_xboole_0(k4_relat_1(k5_relat_1(k1_xboole_0,sK1))) = iProver_top
% 4.00/0.97      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 4.00/0.97      inference(superposition,[status(thm)],[c_7044,c_496]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_8,plain,
% 4.00/0.97      ( ~ v1_relat_1(X0)
% 4.00/0.97      | ~ v1_relat_1(X1)
% 4.00/0.97      | v1_relat_1(k5_relat_1(X0,X1)) ),
% 4.00/0.97      inference(cnf_transformation,[],[f42]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_647,plain,
% 4.00/0.97      ( ~ v1_relat_1(X0)
% 4.00/0.97      | v1_relat_1(k5_relat_1(X0,sK1))
% 4.00/0.97      | ~ v1_relat_1(sK1) ),
% 4.00/0.97      inference(instantiation,[status(thm)],[c_8]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_648,plain,
% 4.00/0.97      ( v1_relat_1(X0) != iProver_top
% 4.00/0.97      | v1_relat_1(k5_relat_1(X0,sK1)) = iProver_top
% 4.00/0.97      | v1_relat_1(sK1) != iProver_top ),
% 4.00/0.97      inference(predicate_to_equality,[status(thm)],[c_647]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_650,plain,
% 4.00/0.97      ( v1_relat_1(k5_relat_1(k1_xboole_0,sK1)) = iProver_top
% 4.00/0.97      | v1_relat_1(sK1) != iProver_top
% 4.00/0.97      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 4.00/0.97      inference(instantiation,[status(thm)],[c_648]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_6627,plain,
% 4.00/0.97      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK1))
% 4.00/0.97      | v1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK1))) ),
% 4.00/0.97      inference(instantiation,[status(thm)],[c_7]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_6628,plain,
% 4.00/0.97      ( v1_relat_1(k5_relat_1(k1_xboole_0,sK1)) != iProver_top
% 4.00/0.97      | v1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK1))) = iProver_top ),
% 4.00/0.97      inference(predicate_to_equality,[status(thm)],[c_6627]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_19325,plain,
% 4.00/0.97      ( v1_xboole_0(k4_relat_1(k5_relat_1(k1_xboole_0,sK1))) = iProver_top ),
% 4.00/0.97      inference(global_propositional_subsumption,
% 4.00/0.97                [status(thm)],
% 4.00/0.97                [c_7045,c_19,c_46,c_1,c_55,c_650,c_686,c_694,c_6628]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_19331,plain,
% 4.00/0.97      ( k4_relat_1(k5_relat_1(k1_xboole_0,sK1)) = k1_xboole_0 ),
% 4.00/0.97      inference(superposition,[status(thm)],[c_19325,c_504]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_497,plain,
% 4.00/0.97      ( v1_relat_1(X0) != iProver_top
% 4.00/0.97      | v1_relat_1(X1) != iProver_top
% 4.00/0.97      | v1_relat_1(k5_relat_1(X0,X1)) = iProver_top ),
% 4.00/0.97      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_861,plain,
% 4.00/0.97      ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) = iProver_top
% 4.00/0.97      | v1_relat_1(X0) != iProver_top
% 4.00/0.97      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 4.00/0.97      inference(superposition,[status(thm)],[c_15,c_492]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_1388,plain,
% 4.00/0.97      ( v1_relat_1(X0) != iProver_top
% 4.00/0.97      | r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) = iProver_top ),
% 4.00/0.97      inference(global_propositional_subsumption,
% 4.00/0.97                [status(thm)],
% 4.00/0.97                [c_861,c_46,c_1,c_55,c_686,c_694]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_1389,plain,
% 4.00/0.97      ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) = iProver_top
% 4.00/0.97      | v1_relat_1(X0) != iProver_top ),
% 4.00/0.97      inference(renaming,[status(thm)],[c_1388]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_1225,plain,
% 4.00/0.97      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 4.00/0.97      inference(superposition,[status(thm)],[c_500,c_502]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_2205,plain,
% 4.00/0.97      ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
% 4.00/0.97      | v1_relat_1(X0) != iProver_top ),
% 4.00/0.97      inference(superposition,[status(thm)],[c_1389,c_1225]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_9967,plain,
% 4.00/0.97      ( k2_relat_1(k5_relat_1(sK1,k1_xboole_0)) = k1_xboole_0 ),
% 4.00/0.97      inference(superposition,[status(thm)],[c_490,c_2205]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_9999,plain,
% 4.00/0.97      ( v1_relat_1(k5_relat_1(sK1,k1_xboole_0)) != iProver_top
% 4.00/0.97      | v1_xboole_0(k5_relat_1(sK1,k1_xboole_0)) = iProver_top
% 4.00/0.97      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 4.00/0.97      inference(superposition,[status(thm)],[c_9967,c_496]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_13713,plain,
% 4.00/0.97      ( v1_xboole_0(k5_relat_1(sK1,k1_xboole_0)) = iProver_top
% 4.00/0.97      | v1_relat_1(k5_relat_1(sK1,k1_xboole_0)) != iProver_top ),
% 4.00/0.97      inference(global_propositional_subsumption,
% 4.00/0.97                [status(thm)],
% 4.00/0.97                [c_9999,c_1,c_55,c_686,c_694]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_13714,plain,
% 4.00/0.97      ( v1_relat_1(k5_relat_1(sK1,k1_xboole_0)) != iProver_top
% 4.00/0.97      | v1_xboole_0(k5_relat_1(sK1,k1_xboole_0)) = iProver_top ),
% 4.00/0.97      inference(renaming,[status(thm)],[c_13713]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_13719,plain,
% 4.00/0.97      ( v1_relat_1(sK1) != iProver_top
% 4.00/0.97      | v1_relat_1(k1_xboole_0) != iProver_top
% 4.00/0.97      | v1_xboole_0(k5_relat_1(sK1,k1_xboole_0)) = iProver_top ),
% 4.00/0.97      inference(superposition,[status(thm)],[c_497,c_13714]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_230,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_2470,plain,
% 4.00/0.97      ( ~ v1_xboole_0(X0) | X1 != X0 | k1_xboole_0 = X1 ),
% 4.00/0.97      inference(resolution,[status(thm)],[c_230,c_0]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_234,plain,
% 4.00/0.97      ( X0 != X1 | k4_relat_1(X0) = k4_relat_1(X1) ),
% 4.00/0.97      theory(equality) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_5518,plain,
% 4.00/0.97      ( ~ v1_xboole_0(k4_relat_1(X0))
% 4.00/0.97      | X1 != X0
% 4.00/0.97      | k1_xboole_0 = k4_relat_1(X1) ),
% 4.00/0.97      inference(resolution,[status(thm)],[c_2470,c_234]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_5520,plain,
% 4.00/0.97      ( ~ v1_xboole_0(k4_relat_1(k1_xboole_0))
% 4.00/0.97      | k1_xboole_0 = k4_relat_1(k1_xboole_0)
% 4.00/0.97      | k1_xboole_0 != k1_xboole_0 ),
% 4.00/0.97      inference(instantiation,[status(thm)],[c_5518]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_2371,plain,
% 4.00/0.97      ( k4_relat_1(k5_relat_1(k1_xboole_0,sK1)) != X0
% 4.00/0.97      | k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK1))) = k4_relat_1(X0) ),
% 4.00/0.97      inference(instantiation,[status(thm)],[c_234]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_2373,plain,
% 4.00/0.97      ( k4_relat_1(k5_relat_1(k1_xboole_0,sK1)) != k1_xboole_0
% 4.00/0.97      | k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK1))) = k4_relat_1(k1_xboole_0) ),
% 4.00/0.97      inference(instantiation,[status(thm)],[c_2371]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_1850,plain,
% 4.00/0.97      ( k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK1))) != X0
% 4.00/0.97      | k1_xboole_0 != X0
% 4.00/0.97      | k1_xboole_0 = k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK1))) ),
% 4.00/0.97      inference(instantiation,[status(thm)],[c_230]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_2370,plain,
% 4.00/0.97      ( k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK1))) != k4_relat_1(X0)
% 4.00/0.97      | k1_xboole_0 != k4_relat_1(X0)
% 4.00/0.97      | k1_xboole_0 = k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK1))) ),
% 4.00/0.97      inference(instantiation,[status(thm)],[c_1850]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_2372,plain,
% 4.00/0.97      ( k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK1))) != k4_relat_1(k1_xboole_0)
% 4.00/0.97      | k1_xboole_0 = k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK1)))
% 4.00/0.97      | k1_xboole_0 != k4_relat_1(k1_xboole_0) ),
% 4.00/0.97      inference(instantiation,[status(thm)],[c_2370]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_1673,plain,
% 4.00/0.97      ( ~ v1_relat_1(k4_relat_1(k1_xboole_0))
% 4.00/0.97      | v1_xboole_0(k4_relat_1(k1_xboole_0))
% 4.00/0.97      | ~ v1_xboole_0(k1_xboole_0) ),
% 4.00/0.97      inference(predicate_to_equality_rev,[status(thm)],[c_1659]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_683,plain,
% 4.00/0.97      ( k5_relat_1(k1_xboole_0,sK1) != X0
% 4.00/0.97      | k1_xboole_0 != X0
% 4.00/0.97      | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK1) ),
% 4.00/0.97      inference(instantiation,[status(thm)],[c_230]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_1373,plain,
% 4.00/0.97      ( k5_relat_1(k1_xboole_0,sK1) != k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK1)))
% 4.00/0.97      | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK1)
% 4.00/0.97      | k1_xboole_0 != k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK1))) ),
% 4.00/0.97      inference(instantiation,[status(thm)],[c_683]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_10,plain,
% 4.00/0.97      ( ~ v1_relat_1(X0) | k4_relat_1(k4_relat_1(X0)) = X0 ),
% 4.00/0.97      inference(cnf_transformation,[],[f44]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_1209,plain,
% 4.00/0.97      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK1))
% 4.00/0.97      | k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK1))) = k5_relat_1(k1_xboole_0,sK1) ),
% 4.00/0.97      inference(instantiation,[status(thm)],[c_10]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_769,plain,
% 4.00/0.97      ( X0 != X1
% 4.00/0.97      | k5_relat_1(k1_xboole_0,sK1) != X1
% 4.00/0.97      | k5_relat_1(k1_xboole_0,sK1) = X0 ),
% 4.00/0.97      inference(instantiation,[status(thm)],[c_230]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_1031,plain,
% 4.00/0.97      ( X0 != k5_relat_1(k1_xboole_0,sK1)
% 4.00/0.97      | k5_relat_1(k1_xboole_0,sK1) = X0
% 4.00/0.97      | k5_relat_1(k1_xboole_0,sK1) != k5_relat_1(k1_xboole_0,sK1) ),
% 4.00/0.97      inference(instantiation,[status(thm)],[c_769]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_1208,plain,
% 4.00/0.97      ( k5_relat_1(k1_xboole_0,sK1) != k5_relat_1(k1_xboole_0,sK1)
% 4.00/0.97      | k5_relat_1(k1_xboole_0,sK1) = k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK1)))
% 4.00/0.97      | k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK1))) != k5_relat_1(k1_xboole_0,sK1) ),
% 4.00/0.97      inference(instantiation,[status(thm)],[c_1031]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_4,plain,
% 4.00/0.97      ( r1_tarski(X0,X0) ),
% 4.00/0.97      inference(cnf_transformation,[],[f54]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_910,plain,
% 4.00/0.97      ( r1_tarski(k5_relat_1(k1_xboole_0,sK1),k5_relat_1(k1_xboole_0,sK1)) ),
% 4.00/0.97      inference(instantiation,[status(thm)],[c_4]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_763,plain,
% 4.00/0.97      ( ~ r1_tarski(X0,k5_relat_1(k1_xboole_0,sK1))
% 4.00/0.97      | ~ r1_tarski(k5_relat_1(k1_xboole_0,sK1),X0)
% 4.00/0.97      | k5_relat_1(k1_xboole_0,sK1) = X0 ),
% 4.00/0.97      inference(instantiation,[status(thm)],[c_2]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_909,plain,
% 4.00/0.97      ( ~ r1_tarski(k5_relat_1(k1_xboole_0,sK1),k5_relat_1(k1_xboole_0,sK1))
% 4.00/0.97      | k5_relat_1(k1_xboole_0,sK1) = k5_relat_1(k1_xboole_0,sK1) ),
% 4.00/0.97      inference(instantiation,[status(thm)],[c_763]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_17,negated_conjecture,
% 4.00/0.97      ( k1_xboole_0 != k5_relat_1(sK1,k1_xboole_0)
% 4.00/0.97      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK1) ),
% 4.00/0.97      inference(cnf_transformation,[],[f52]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_874,plain,
% 4.00/0.97      ( ~ v1_xboole_0(k5_relat_1(sK1,k1_xboole_0))
% 4.00/0.97      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK1) ),
% 4.00/0.97      inference(resolution,[status(thm)],[c_0,c_17]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_875,plain,
% 4.00/0.97      ( k1_xboole_0 != k5_relat_1(k1_xboole_0,sK1)
% 4.00/0.97      | v1_xboole_0(k5_relat_1(sK1,k1_xboole_0)) != iProver_top ),
% 4.00/0.97      inference(predicate_to_equality,[status(thm)],[c_874]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_693,plain,
% 4.00/0.97      ( ~ v1_xboole_0(sK0)
% 4.00/0.97      | v1_xboole_0(k1_xboole_0)
% 4.00/0.97      | k1_xboole_0 != sK0 ),
% 4.00/0.97      inference(instantiation,[status(thm)],[c_691]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_649,plain,
% 4.00/0.97      ( v1_relat_1(k5_relat_1(k1_xboole_0,sK1))
% 4.00/0.97      | ~ v1_relat_1(sK1)
% 4.00/0.97      | ~ v1_relat_1(k1_xboole_0) ),
% 4.00/0.97      inference(instantiation,[status(thm)],[c_647]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_53,plain,
% 4.00/0.97      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 4.00/0.97      | k1_xboole_0 = k1_xboole_0 ),
% 4.00/0.97      inference(instantiation,[status(thm)],[c_2]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_48,plain,
% 4.00/0.97      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 4.00/0.97      inference(instantiation,[status(thm)],[c_5]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_45,plain,
% 4.00/0.97      ( v1_relat_1(k1_xboole_0) | ~ v1_xboole_0(k1_xboole_0) ),
% 4.00/0.97      inference(instantiation,[status(thm)],[c_6]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(c_42,plain,
% 4.00/0.97      ( v1_relat_1(k4_relat_1(k1_xboole_0)) | ~ v1_relat_1(k1_xboole_0) ),
% 4.00/0.97      inference(instantiation,[status(thm)],[c_7]) ).
% 4.00/0.97  
% 4.00/0.97  cnf(contradiction,plain,
% 4.00/0.97      ( $false ),
% 4.00/0.97      inference(minisat,
% 4.00/0.97                [status(thm)],
% 4.00/0.97                [c_19331,c_13719,c_5520,c_2373,c_2372,c_1673,c_1373,
% 4.00/0.97                 c_1209,c_1208,c_910,c_909,c_875,c_694,c_693,c_686,c_649,
% 4.00/0.97                 c_55,c_1,c_53,c_48,c_46,c_45,c_42,c_19,c_18]) ).
% 4.00/0.97  
% 4.00/0.97  
% 4.00/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 4.00/0.97  
% 4.00/0.97  ------                               Statistics
% 4.00/0.97  
% 4.00/0.97  ------ Selected
% 4.00/0.97  
% 4.00/0.97  total_time:                             0.488
% 4.00/0.97  
%------------------------------------------------------------------------------
