%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:43:57 EST 2020

% Result     : Theorem 23.84s
% Output     : CNFRefutation 23.84s
% Verified   : 
% Statistics : Number of formulae       :  208 ( 568 expanded)
%              Number of clauses        :  163 ( 319 expanded)
%              Number of leaves         :   19 ( 105 expanded)
%              Depth                    :   18
%              Number of atoms          :  516 (1362 expanded)
%              Number of equality atoms :  328 ( 670 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f36,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f37,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f12,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f34,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f31,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f40,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f48,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f32])).

fof(f13,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f25,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f28,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f28])).

fof(f45,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f46,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_202,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2819,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,k5_relat_1(X3,X4))
    | X2 != X0
    | k5_relat_1(X3,X4) != X1 ),
    inference(instantiation,[status(thm)],[c_202])).

cnf(c_5840,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(X2,X3))
    | k5_relat_1(X2,X3) != X1
    | k5_relat_1(k1_xboole_0,sK0) != X0 ),
    inference(instantiation,[status(thm)],[c_2819])).

cnf(c_10534,plain,
    ( ~ r1_tarski(k5_relat_1(X0,k4_relat_1(k4_relat_1(sK0))),X1)
    | r1_tarski(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(X2,X3))
    | k5_relat_1(X2,X3) != X1
    | k5_relat_1(k1_xboole_0,sK0) != k5_relat_1(X0,k4_relat_1(k4_relat_1(sK0))) ),
    inference(instantiation,[status(thm)],[c_5840])).

cnf(c_114399,plain,
    ( ~ r1_tarski(k5_relat_1(k4_relat_1(X0),k4_relat_1(k4_relat_1(sK0))),k5_relat_1(X1,X2))
    | r1_tarski(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(X3,X4))
    | k5_relat_1(X3,X4) != k5_relat_1(X1,X2)
    | k5_relat_1(k1_xboole_0,sK0) != k5_relat_1(k4_relat_1(X0),k4_relat_1(k4_relat_1(sK0))) ),
    inference(instantiation,[status(thm)],[c_10534])).

cnf(c_114403,plain,
    ( ~ r1_tarski(k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(k4_relat_1(sK0))),k5_relat_1(k1_xboole_0,k1_xboole_0))
    | r1_tarski(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,k1_xboole_0))
    | k5_relat_1(k1_xboole_0,sK0) != k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(k4_relat_1(sK0)))
    | k5_relat_1(k1_xboole_0,k1_xboole_0) != k5_relat_1(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_114399])).

cnf(c_200,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_100771,plain,
    ( X0 != X1
    | X0 = k5_relat_1(k4_relat_1(sK0),X2)
    | k5_relat_1(k4_relat_1(sK0),X2) != X1 ),
    inference(instantiation,[status(thm)],[c_200])).

cnf(c_100772,plain,
    ( k5_relat_1(k4_relat_1(sK0),k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k5_relat_1(k4_relat_1(sK0),k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_100771])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_435,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_442,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_6,plain,
    ( v1_relat_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_437,plain,
    ( v1_relat_1(X0) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_811,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_442,c_437])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k4_relat_1(X0)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_436,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_13,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_11,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_432,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_936,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_432])).

cnf(c_36,plain,
    ( v1_relat_1(X0) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_38,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_36])).

cnf(c_50,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1353,plain,
    ( v1_relat_1(X0) != iProver_top
    | r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_936,c_38,c_50])).

cnf(c_1354,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1353])).

cnf(c_5,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_438,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_440,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1187,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_438,c_440])).

cnf(c_1562,plain,
    ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1354,c_1187])).

cnf(c_5327,plain,
    ( k2_relat_1(k5_relat_1(k4_relat_1(X0),k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_436,c_1562])).

cnf(c_5552,plain,
    ( k2_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_811,c_5327])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_434,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k2_relat_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_88860,plain,
    ( v1_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0)) != iProver_top
    | v1_xboole_0(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0)) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5552,c_434])).

cnf(c_89505,plain,
    ( v1_xboole_0(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0)) = iProver_top
    | v1_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_88860,c_50])).

cnf(c_89506,plain,
    ( v1_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0)) != iProver_top
    | v1_xboole_0(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_89505])).

cnf(c_89511,plain,
    ( v1_relat_1(k4_relat_1(k1_xboole_0)) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top
    | v1_xboole_0(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_435,c_89506])).

cnf(c_33,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_35,plain,
    ( v1_relat_1(k4_relat_1(k1_xboole_0)) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_89514,plain,
    ( v1_xboole_0(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_89511,c_35,c_38,c_50])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_441,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_89520,plain,
    ( k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_89514,c_441])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_431,plain,
    ( k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,X0))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1366,plain,
    ( k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,k1_xboole_0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_811,c_431])).

cnf(c_2164,plain,
    ( k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(k4_relat_1(X0))) = k4_relat_1(k5_relat_1(k4_relat_1(X0),k1_xboole_0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_436,c_1366])).

cnf(c_3953,plain,
    ( k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(k4_relat_1(k1_xboole_0))) = k4_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_811,c_2164])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | k4_relat_1(k4_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_433,plain,
    ( k4_relat_1(k4_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1365,plain,
    ( k4_relat_1(k4_relat_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_811,c_433])).

cnf(c_3961,plain,
    ( k4_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0)) = k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_3953,c_1365])).

cnf(c_90147,plain,
    ( k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_89520,c_3961])).

cnf(c_879,plain,
    ( X0 != X1
    | k5_relat_1(X2,X3) != X1
    | k5_relat_1(X2,X3) = X0 ),
    inference(instantiation,[status(thm)],[c_200])).

cnf(c_3764,plain,
    ( k5_relat_1(X0,X1) != X2
    | k5_relat_1(X0,X1) = k4_relat_1(k5_relat_1(X3,X4))
    | k4_relat_1(k5_relat_1(X3,X4)) != X2 ),
    inference(instantiation,[status(thm)],[c_879])).

cnf(c_8984,plain,
    ( k5_relat_1(X0,X1) != k4_relat_1(X2)
    | k5_relat_1(X0,X1) = k4_relat_1(k5_relat_1(X3,X4))
    | k4_relat_1(k5_relat_1(X3,X4)) != k4_relat_1(X2) ),
    inference(instantiation,[status(thm)],[c_3764])).

cnf(c_21352,plain,
    ( k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) != k4_relat_1(X2)
    | k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X3,X4))
    | k4_relat_1(k5_relat_1(X3,X4)) != k4_relat_1(X2) ),
    inference(instantiation,[status(thm)],[c_8984])).

cnf(c_81722,plain,
    ( k5_relat_1(k4_relat_1(X0),k4_relat_1(k4_relat_1(sK0))) != k4_relat_1(X1)
    | k5_relat_1(k4_relat_1(X0),k4_relat_1(k4_relat_1(sK0))) = k4_relat_1(k5_relat_1(X2,X3))
    | k4_relat_1(k5_relat_1(X2,X3)) != k4_relat_1(X1) ),
    inference(instantiation,[status(thm)],[c_21352])).

cnf(c_81725,plain,
    ( k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(k4_relat_1(sK0))) = k4_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0))
    | k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(k4_relat_1(sK0))) != k4_relat_1(k1_xboole_0)
    | k4_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0)) != k4_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_81722])).

cnf(c_205,plain,
    ( X0 != X1
    | X2 != X3
    | k5_relat_1(X0,X2) = k5_relat_1(X1,X3) ),
    theory(equality)).

cnf(c_777,plain,
    ( X0 != sK0
    | X1 != k1_xboole_0
    | k5_relat_1(X1,X0) = k5_relat_1(k1_xboole_0,sK0) ),
    inference(instantiation,[status(thm)],[c_205])).

cnf(c_1438,plain,
    ( X0 != k1_xboole_0
    | k5_relat_1(X0,k4_relat_1(k4_relat_1(sK0))) = k5_relat_1(k1_xboole_0,sK0)
    | k4_relat_1(k4_relat_1(sK0)) != sK0 ),
    inference(instantiation,[status(thm)],[c_777])).

cnf(c_46727,plain,
    ( k5_relat_1(k4_relat_1(X0),k4_relat_1(k4_relat_1(sK0))) = k5_relat_1(k1_xboole_0,sK0)
    | k4_relat_1(X0) != k1_xboole_0
    | k4_relat_1(k4_relat_1(sK0)) != sK0 ),
    inference(instantiation,[status(thm)],[c_1438])).

cnf(c_46728,plain,
    ( k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(k4_relat_1(sK0))) = k5_relat_1(k1_xboole_0,sK0)
    | k4_relat_1(k4_relat_1(sK0)) != sK0
    | k4_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_46727])).

cnf(c_7659,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k4_relat_1(k5_relat_1(X2,X3)),k5_relat_1(X4,X5))
    | k5_relat_1(X4,X5) != X1
    | k4_relat_1(k5_relat_1(X2,X3)) != X0 ),
    inference(instantiation,[status(thm)],[c_2819])).

cnf(c_16140,plain,
    ( ~ r1_tarski(k4_relat_1(X0),X1)
    | r1_tarski(k4_relat_1(k5_relat_1(X2,X3)),k5_relat_1(X4,X5))
    | k5_relat_1(X4,X5) != X1
    | k4_relat_1(k5_relat_1(X2,X3)) != k4_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_7659])).

cnf(c_36856,plain,
    ( ~ r1_tarski(k4_relat_1(X0),k4_relat_1(X0))
    | r1_tarski(k4_relat_1(k5_relat_1(X1,X2)),k5_relat_1(X3,X4))
    | k5_relat_1(X3,X4) != k4_relat_1(X0)
    | k4_relat_1(k5_relat_1(X1,X2)) != k4_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_16140])).

cnf(c_36862,plain,
    ( r1_tarski(k4_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0)),k5_relat_1(k1_xboole_0,k1_xboole_0))
    | ~ r1_tarski(k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0))
    | k5_relat_1(k1_xboole_0,k1_xboole_0) != k4_relat_1(k1_xboole_0)
    | k4_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0)) != k4_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_36856])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_22530,plain,
    ( r1_tarski(k4_relat_1(X0),k4_relat_1(X0)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_22536,plain,
    ( r1_tarski(k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_22530])).

cnf(c_5951,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k5_relat_1(X2,k4_relat_1(k4_relat_1(sK0))),k5_relat_1(X3,X4))
    | k5_relat_1(X3,X4) != X1
    | k5_relat_1(X2,k4_relat_1(k4_relat_1(sK0))) != X0 ),
    inference(instantiation,[status(thm)],[c_2819])).

cnf(c_21522,plain,
    ( ~ r1_tarski(k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)),X2)
    | r1_tarski(k5_relat_1(k4_relat_1(X3),k4_relat_1(k4_relat_1(sK0))),k5_relat_1(X4,X5))
    | k5_relat_1(X4,X5) != X2
    | k5_relat_1(k4_relat_1(X3),k4_relat_1(k4_relat_1(sK0))) != k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) ),
    inference(instantiation,[status(thm)],[c_5951])).

cnf(c_21527,plain,
    ( r1_tarski(k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(k4_relat_1(sK0))),k5_relat_1(k1_xboole_0,k1_xboole_0))
    | ~ r1_tarski(k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0)),k1_xboole_0)
    | k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(k4_relat_1(sK0))) != k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0))
    | k5_relat_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_21522])).

cnf(c_1295,plain,
    ( X0 != k5_relat_1(X1,X2)
    | k5_relat_1(X1,X2) = X0
    | k5_relat_1(X1,X2) != k5_relat_1(X1,X2) ),
    inference(instantiation,[status(thm)],[c_879])).

cnf(c_4252,plain,
    ( X0 != k5_relat_1(X1,k4_relat_1(k4_relat_1(sK0)))
    | k5_relat_1(X1,k4_relat_1(k4_relat_1(sK0))) = X0
    | k5_relat_1(X1,k4_relat_1(k4_relat_1(sK0))) != k5_relat_1(X1,k4_relat_1(k4_relat_1(sK0))) ),
    inference(instantiation,[status(thm)],[c_1295])).

cnf(c_21511,plain,
    ( k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) != k5_relat_1(k4_relat_1(X2),k4_relat_1(k4_relat_1(sK0)))
    | k5_relat_1(k4_relat_1(X2),k4_relat_1(k4_relat_1(sK0))) = k5_relat_1(k4_relat_1(X0),k4_relat_1(X1))
    | k5_relat_1(k4_relat_1(X2),k4_relat_1(k4_relat_1(sK0))) != k5_relat_1(k4_relat_1(X2),k4_relat_1(k4_relat_1(sK0))) ),
    inference(instantiation,[status(thm)],[c_4252])).

cnf(c_21515,plain,
    ( k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(k4_relat_1(sK0))) != k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(k4_relat_1(sK0)))
    | k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(k4_relat_1(sK0))) = k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0))
    | k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0)) != k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(k4_relat_1(sK0))) ),
    inference(instantiation,[status(thm)],[c_21511])).

cnf(c_1293,plain,
    ( X0 != k4_relat_1(k5_relat_1(X1,X2))
    | k5_relat_1(k4_relat_1(X2),k4_relat_1(X1)) = X0
    | k5_relat_1(k4_relat_1(X2),k4_relat_1(X1)) != k4_relat_1(k5_relat_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_879])).

cnf(c_3763,plain,
    ( k5_relat_1(X0,X1) != k4_relat_1(k5_relat_1(X2,X3))
    | k5_relat_1(k4_relat_1(X3),k4_relat_1(X2)) = k5_relat_1(X0,X1)
    | k5_relat_1(k4_relat_1(X3),k4_relat_1(X2)) != k4_relat_1(k5_relat_1(X2,X3)) ),
    inference(instantiation,[status(thm)],[c_1293])).

cnf(c_10385,plain,
    ( k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) = k5_relat_1(k4_relat_1(X2),k4_relat_1(X3))
    | k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) != k4_relat_1(k5_relat_1(X1,X0))
    | k5_relat_1(k4_relat_1(X2),k4_relat_1(X3)) != k4_relat_1(k5_relat_1(X1,X0)) ),
    inference(instantiation,[status(thm)],[c_3763])).

cnf(c_21508,plain,
    ( k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) = k5_relat_1(k4_relat_1(X2),k4_relat_1(k4_relat_1(sK0)))
    | k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) != k4_relat_1(k5_relat_1(X1,X0))
    | k5_relat_1(k4_relat_1(X2),k4_relat_1(k4_relat_1(sK0))) != k4_relat_1(k5_relat_1(X1,X0)) ),
    inference(instantiation,[status(thm)],[c_10385])).

cnf(c_21514,plain,
    ( k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(k4_relat_1(sK0))) != k4_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0))
    | k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0)) = k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(k4_relat_1(sK0)))
    | k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0)) != k4_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_21508])).

cnf(c_21341,plain,
    ( k5_relat_1(X0,X1) != X2
    | k5_relat_1(X0,X1) = k4_relat_1(X3)
    | k4_relat_1(X3) != X2 ),
    inference(instantiation,[status(thm)],[c_879])).

cnf(c_21342,plain,
    ( k5_relat_1(k1_xboole_0,k1_xboole_0) = k4_relat_1(k1_xboole_0)
    | k5_relat_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k4_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_21341])).

cnf(c_599,plain,
    ( X0 != X1
    | k5_relat_1(k1_xboole_0,sK0) != X1
    | k5_relat_1(k1_xboole_0,sK0) = X0 ),
    inference(instantiation,[status(thm)],[c_200])).

cnf(c_701,plain,
    ( X0 != k5_relat_1(k1_xboole_0,sK0)
    | k5_relat_1(k1_xboole_0,sK0) = X0
    | k5_relat_1(k1_xboole_0,sK0) != k5_relat_1(k1_xboole_0,sK0) ),
    inference(instantiation,[status(thm)],[c_599])).

cnf(c_776,plain,
    ( k5_relat_1(X0,X1) != k5_relat_1(k1_xboole_0,sK0)
    | k5_relat_1(k1_xboole_0,sK0) = k5_relat_1(X0,X1)
    | k5_relat_1(k1_xboole_0,sK0) != k5_relat_1(k1_xboole_0,sK0) ),
    inference(instantiation,[status(thm)],[c_701])).

cnf(c_3072,plain,
    ( k5_relat_1(X0,k4_relat_1(k4_relat_1(sK0))) != k5_relat_1(k1_xboole_0,sK0)
    | k5_relat_1(k1_xboole_0,sK0) = k5_relat_1(X0,k4_relat_1(k4_relat_1(sK0)))
    | k5_relat_1(k1_xboole_0,sK0) != k5_relat_1(k1_xboole_0,sK0) ),
    inference(instantiation,[status(thm)],[c_776])).

cnf(c_19302,plain,
    ( k5_relat_1(k4_relat_1(X0),k4_relat_1(k4_relat_1(sK0))) != k5_relat_1(k1_xboole_0,sK0)
    | k5_relat_1(k1_xboole_0,sK0) = k5_relat_1(k4_relat_1(X0),k4_relat_1(k4_relat_1(sK0)))
    | k5_relat_1(k1_xboole_0,sK0) != k5_relat_1(k1_xboole_0,sK0) ),
    inference(instantiation,[status(thm)],[c_3072])).

cnf(c_19305,plain,
    ( k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(k4_relat_1(sK0))) != k5_relat_1(k1_xboole_0,sK0)
    | k5_relat_1(k1_xboole_0,sK0) = k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(k4_relat_1(sK0)))
    | k5_relat_1(k1_xboole_0,sK0) != k5_relat_1(k1_xboole_0,sK0) ),
    inference(instantiation,[status(thm)],[c_19302])).

cnf(c_16,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_430,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_5551,plain,
    ( k2_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_430,c_5327])).

cnf(c_5740,plain,
    ( v1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) != iProver_top
    | v1_xboole_0(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5551,c_434])).

cnf(c_18361,plain,
    ( v1_xboole_0(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) = iProver_top
    | v1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5740,c_50])).

cnf(c_18362,plain,
    ( v1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) != iProver_top
    | v1_xboole_0(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_18361])).

cnf(c_18367,plain,
    ( v1_relat_1(k4_relat_1(sK0)) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top
    | v1_xboole_0(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_435,c_18362])).

cnf(c_17,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_8513,plain,
    ( v1_relat_1(k4_relat_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_8514,plain,
    ( v1_relat_1(k4_relat_1(sK0)) = iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8513])).

cnf(c_18370,plain,
    ( v1_xboole_0(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_18367,c_17,c_38,c_50,c_8514])).

cnf(c_18376,plain,
    ( k5_relat_1(k4_relat_1(sK0),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_18370,c_441])).

cnf(c_204,plain,
    ( X0 != X1
    | k4_relat_1(X0) = k4_relat_1(X1) ),
    theory(equality)).

cnf(c_3760,plain,
    ( X0 != k5_relat_1(X1,X2)
    | k4_relat_1(X0) = k4_relat_1(k5_relat_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_204])).

cnf(c_15380,plain,
    ( X0 != k5_relat_1(k4_relat_1(sK0),X1)
    | k4_relat_1(X0) = k4_relat_1(k5_relat_1(k4_relat_1(sK0),X1)) ),
    inference(instantiation,[status(thm)],[c_3760])).

cnf(c_15381,plain,
    ( k4_relat_1(k1_xboole_0) = k4_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))
    | k1_xboole_0 != k5_relat_1(k4_relat_1(sK0),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_15380])).

cnf(c_2702,plain,
    ( r1_tarski(k1_xboole_0,k5_relat_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_10542,plain,
    ( r1_tarski(k1_xboole_0,k5_relat_1(X0,sK0)) ),
    inference(instantiation,[status(thm)],[c_2702])).

cnf(c_10544,plain,
    ( r1_tarski(k1_xboole_0,k5_relat_1(k1_xboole_0,sK0)) ),
    inference(instantiation,[status(thm)],[c_10542])).

cnf(c_3759,plain,
    ( k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(X2)
    | k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) != k4_relat_1(k5_relat_1(X1,X0))
    | k4_relat_1(X2) != k4_relat_1(k5_relat_1(X1,X0)) ),
    inference(instantiation,[status(thm)],[c_1293])).

cnf(c_10354,plain,
    ( k5_relat_1(k4_relat_1(X0),k4_relat_1(k4_relat_1(sK0))) = k4_relat_1(X1)
    | k5_relat_1(k4_relat_1(X0),k4_relat_1(k4_relat_1(sK0))) != k4_relat_1(k5_relat_1(k4_relat_1(sK0),X0))
    | k4_relat_1(X1) != k4_relat_1(k5_relat_1(k4_relat_1(sK0),X0)) ),
    inference(instantiation,[status(thm)],[c_3759])).

cnf(c_10356,plain,
    ( k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(k4_relat_1(sK0))) != k4_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))
    | k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(k4_relat_1(sK0))) = k4_relat_1(k1_xboole_0)
    | k4_relat_1(k1_xboole_0) != k4_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_10354])).

cnf(c_3755,plain,
    ( k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) = k5_relat_1(k4_relat_1(X0),k4_relat_1(X1))
    | k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) != k4_relat_1(k5_relat_1(X1,X0)) ),
    inference(instantiation,[status(thm)],[c_1293])).

cnf(c_10297,plain,
    ( k5_relat_1(k4_relat_1(X0),k4_relat_1(k4_relat_1(sK0))) = k5_relat_1(k4_relat_1(X0),k4_relat_1(k4_relat_1(sK0)))
    | k5_relat_1(k4_relat_1(X0),k4_relat_1(k4_relat_1(sK0))) != k4_relat_1(k5_relat_1(k4_relat_1(sK0),X0)) ),
    inference(instantiation,[status(thm)],[c_3755])).

cnf(c_10300,plain,
    ( k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(k4_relat_1(sK0))) = k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(k4_relat_1(sK0)))
    | k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(k4_relat_1(sK0))) != k4_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_10297])).

cnf(c_5329,plain,
    ( k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_430,c_1562])).

cnf(c_5501,plain,
    ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) != iProver_top
    | v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5329,c_434])).

cnf(c_10226,plain,
    ( v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) = iProver_top
    | v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5501,c_50])).

cnf(c_10227,plain,
    ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) != iProver_top
    | v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_10226])).

cnf(c_10232,plain,
    ( v1_relat_1(sK0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top
    | v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_435,c_10227])).

cnf(c_866,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k5_relat_1(X2,X3),k1_xboole_0)
    | k5_relat_1(X2,X3) != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_202])).

cnf(c_1337,plain,
    ( r1_tarski(k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)),k1_xboole_0)
    | ~ r1_tarski(k4_relat_1(k5_relat_1(X1,X0)),X2)
    | k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) != k4_relat_1(k5_relat_1(X1,X0))
    | k1_xboole_0 != X2 ),
    inference(instantiation,[status(thm)],[c_866])).

cnf(c_7658,plain,
    ( r1_tarski(k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)),k1_xboole_0)
    | ~ r1_tarski(k4_relat_1(k5_relat_1(X1,X0)),k5_relat_1(X2,X3))
    | k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) != k4_relat_1(k5_relat_1(X1,X0))
    | k1_xboole_0 != k5_relat_1(X2,X3) ),
    inference(instantiation,[status(thm)],[c_1337])).

cnf(c_7661,plain,
    ( r1_tarski(k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0)),k1_xboole_0)
    | ~ r1_tarski(k4_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0)),k5_relat_1(k1_xboole_0,k1_xboole_0))
    | k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0)) != k4_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0))
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_7658])).

cnf(c_588,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k5_relat_1(k1_xboole_0,sK0),k1_xboole_0)
    | k5_relat_1(k1_xboole_0,sK0) != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_202])).

cnf(c_657,plain,
    ( ~ r1_tarski(k5_relat_1(k1_xboole_0,sK0),X0)
    | r1_tarski(k5_relat_1(k1_xboole_0,sK0),k1_xboole_0)
    | k5_relat_1(k1_xboole_0,sK0) != k5_relat_1(k1_xboole_0,sK0)
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_588])).

cnf(c_5843,plain,
    ( ~ r1_tarski(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(X0,X1))
    | r1_tarski(k5_relat_1(k1_xboole_0,sK0),k1_xboole_0)
    | k5_relat_1(k1_xboole_0,sK0) != k5_relat_1(k1_xboole_0,sK0)
    | k1_xboole_0 != k5_relat_1(X0,X1) ),
    inference(instantiation,[status(thm)],[c_657])).

cnf(c_5854,plain,
    ( ~ r1_tarski(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,k1_xboole_0))
    | r1_tarski(k5_relat_1(k1_xboole_0,sK0),k1_xboole_0)
    | k5_relat_1(k1_xboole_0,sK0) != k5_relat_1(k1_xboole_0,sK0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_5843])).

cnf(c_4243,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(k4_relat_1(sK0))
    | k5_relat_1(k4_relat_1(X0),k4_relat_1(k4_relat_1(sK0))) = k4_relat_1(k5_relat_1(k4_relat_1(sK0),X0)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_4246,plain,
    ( ~ v1_relat_1(k4_relat_1(sK0))
    | ~ v1_relat_1(k1_xboole_0)
    | k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(k4_relat_1(sK0))) = k4_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_4243])).

cnf(c_3625,plain,
    ( k5_relat_1(X0,X1) != X2
    | k4_relat_1(k5_relat_1(X0,X1)) = k4_relat_1(X2) ),
    inference(instantiation,[status(thm)],[c_204])).

cnf(c_3627,plain,
    ( k5_relat_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k4_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0)) = k4_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3625])).

cnf(c_1568,plain,
    ( k2_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1562])).

cnf(c_1297,plain,
    ( k5_relat_1(k1_xboole_0,k1_xboole_0) != k5_relat_1(k1_xboole_0,k1_xboole_0)
    | k5_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1295])).

cnf(c_201,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1265,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_relat_1(k5_relat_1(X1,X2)))
    | k2_relat_1(k5_relat_1(X1,X2)) != X0 ),
    inference(instantiation,[status(thm)],[c_201])).

cnf(c_1267,plain,
    ( v1_xboole_0(k2_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_xboole_0(k1_xboole_0)
    | k2_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1265])).

cnf(c_913,plain,
    ( ~ v1_relat_1(sK0)
    | k4_relat_1(k4_relat_1(sK0)) = sK0 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_788,plain,
    ( ~ v1_relat_1(k5_relat_1(X0,X1))
    | v1_xboole_0(k5_relat_1(X0,X1))
    | ~ v1_xboole_0(k2_relat_1(k5_relat_1(X0,X1))) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_790,plain,
    ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0))
    | v1_xboole_0(k5_relat_1(k1_xboole_0,k1_xboole_0))
    | ~ v1_xboole_0(k2_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_788])).

cnf(c_670,plain,
    ( ~ v1_xboole_0(k5_relat_1(X0,X1))
    | k1_xboole_0 = k5_relat_1(X0,X1) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_672,plain,
    ( ~ v1_xboole_0(k5_relat_1(k1_xboole_0,k1_xboole_0))
    | k1_xboole_0 = k5_relat_1(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_670])).

cnf(c_648,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_593,plain,
    ( ~ r1_tarski(X0,k5_relat_1(k1_xboole_0,sK0))
    | ~ r1_tarski(k5_relat_1(k1_xboole_0,sK0),X0)
    | k5_relat_1(k1_xboole_0,sK0) = X0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_647,plain,
    ( ~ r1_tarski(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0))
    | k5_relat_1(k1_xboole_0,sK0) = k5_relat_1(k1_xboole_0,sK0) ),
    inference(instantiation,[status(thm)],[c_593])).

cnf(c_15,negated_conjecture,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_626,plain,
    ( ~ v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(resolution,[status(thm)],[c_1,c_15])).

cnf(c_627,plain,
    ( k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)
    | v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_626])).

cnf(c_595,plain,
    ( ~ r1_tarski(k5_relat_1(k1_xboole_0,sK0),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k5_relat_1(k1_xboole_0,sK0))
    | k5_relat_1(k1_xboole_0,sK0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_593])).

cnf(c_578,plain,
    ( k5_relat_1(k1_xboole_0,sK0) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
    inference(instantiation,[status(thm)],[c_200])).

cnf(c_579,plain,
    ( k5_relat_1(k1_xboole_0,sK0) != k1_xboole_0
    | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_578])).

cnf(c_212,plain,
    ( k5_relat_1(k1_xboole_0,k1_xboole_0) = k5_relat_1(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_205])).

cnf(c_45,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_40,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_37,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_31,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_19,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0)) = k4_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_114403,c_100772,c_90147,c_81725,c_46728,c_36862,c_22536,c_21527,c_21515,c_21514,c_21342,c_19305,c_18376,c_15381,c_10544,c_10356,c_10300,c_10232,c_8513,c_7661,c_5854,c_4246,c_3627,c_1568,c_1297,c_1267,c_913,c_790,c_672,c_648,c_647,c_627,c_595,c_579,c_212,c_50,c_0,c_45,c_40,c_38,c_37,c_31,c_19,c_17,c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:35:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 23.84/3.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.84/3.49  
% 23.84/3.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.84/3.49  
% 23.84/3.49  ------  iProver source info
% 23.84/3.49  
% 23.84/3.49  git: date: 2020-06-30 10:37:57 +0100
% 23.84/3.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.84/3.49  git: non_committed_changes: false
% 23.84/3.49  git: last_make_outside_of_git: false
% 23.84/3.49  
% 23.84/3.49  ------ 
% 23.84/3.49  
% 23.84/3.49  ------ Input Options
% 23.84/3.49  
% 23.84/3.49  --out_options                           all
% 23.84/3.49  --tptp_safe_out                         true
% 23.84/3.49  --problem_path                          ""
% 23.84/3.49  --include_path                          ""
% 23.84/3.49  --clausifier                            res/vclausify_rel
% 23.84/3.49  --clausifier_options                    --mode clausify
% 23.84/3.49  --stdin                                 false
% 23.84/3.49  --stats_out                             sel
% 23.84/3.49  
% 23.84/3.49  ------ General Options
% 23.84/3.49  
% 23.84/3.49  --fof                                   false
% 23.84/3.49  --time_out_real                         604.99
% 23.84/3.49  --time_out_virtual                      -1.
% 23.84/3.49  --symbol_type_check                     false
% 23.84/3.49  --clausify_out                          false
% 23.84/3.49  --sig_cnt_out                           false
% 23.84/3.49  --trig_cnt_out                          false
% 23.84/3.49  --trig_cnt_out_tolerance                1.
% 23.84/3.49  --trig_cnt_out_sk_spl                   false
% 23.84/3.49  --abstr_cl_out                          false
% 23.84/3.49  
% 23.84/3.49  ------ Global Options
% 23.84/3.49  
% 23.84/3.49  --schedule                              none
% 23.84/3.49  --add_important_lit                     false
% 23.84/3.49  --prop_solver_per_cl                    1000
% 23.84/3.49  --min_unsat_core                        false
% 23.84/3.49  --soft_assumptions                      false
% 23.84/3.49  --soft_lemma_size                       3
% 23.84/3.49  --prop_impl_unit_size                   0
% 23.84/3.49  --prop_impl_unit                        []
% 23.84/3.49  --share_sel_clauses                     true
% 23.84/3.49  --reset_solvers                         false
% 23.84/3.49  --bc_imp_inh                            [conj_cone]
% 23.84/3.49  --conj_cone_tolerance                   3.
% 23.84/3.49  --extra_neg_conj                        none
% 23.84/3.49  --large_theory_mode                     true
% 23.84/3.49  --prolific_symb_bound                   200
% 23.84/3.49  --lt_threshold                          2000
% 23.84/3.49  --clause_weak_htbl                      true
% 23.84/3.49  --gc_record_bc_elim                     false
% 23.84/3.49  
% 23.84/3.49  ------ Preprocessing Options
% 23.84/3.49  
% 23.84/3.49  --preprocessing_flag                    true
% 23.84/3.49  --time_out_prep_mult                    0.1
% 23.84/3.49  --splitting_mode                        input
% 23.84/3.49  --splitting_grd                         true
% 23.84/3.49  --splitting_cvd                         false
% 23.84/3.49  --splitting_cvd_svl                     false
% 23.84/3.49  --splitting_nvd                         32
% 23.84/3.49  --sub_typing                            true
% 23.84/3.49  --prep_gs_sim                           false
% 23.84/3.49  --prep_unflatten                        true
% 23.84/3.49  --prep_res_sim                          true
% 23.84/3.49  --prep_upred                            true
% 23.84/3.49  --prep_sem_filter                       exhaustive
% 23.84/3.49  --prep_sem_filter_out                   false
% 23.84/3.49  --pred_elim                             false
% 23.84/3.49  --res_sim_input                         true
% 23.84/3.49  --eq_ax_congr_red                       true
% 23.84/3.49  --pure_diseq_elim                       true
% 23.84/3.49  --brand_transform                       false
% 23.84/3.49  --non_eq_to_eq                          false
% 23.84/3.49  --prep_def_merge                        true
% 23.84/3.49  --prep_def_merge_prop_impl              false
% 23.84/3.49  --prep_def_merge_mbd                    true
% 23.84/3.49  --prep_def_merge_tr_red                 false
% 23.84/3.49  --prep_def_merge_tr_cl                  false
% 23.84/3.49  --smt_preprocessing                     true
% 23.84/3.49  --smt_ac_axioms                         fast
% 23.84/3.49  --preprocessed_out                      false
% 23.84/3.49  --preprocessed_stats                    false
% 23.84/3.49  
% 23.84/3.49  ------ Abstraction refinement Options
% 23.84/3.49  
% 23.84/3.49  --abstr_ref                             []
% 23.84/3.49  --abstr_ref_prep                        false
% 23.84/3.49  --abstr_ref_until_sat                   false
% 23.84/3.49  --abstr_ref_sig_restrict                funpre
% 23.84/3.49  --abstr_ref_af_restrict_to_split_sk     false
% 23.84/3.49  --abstr_ref_under                       []
% 23.84/3.49  
% 23.84/3.49  ------ SAT Options
% 23.84/3.49  
% 23.84/3.49  --sat_mode                              false
% 23.84/3.49  --sat_fm_restart_options                ""
% 23.84/3.49  --sat_gr_def                            false
% 23.84/3.49  --sat_epr_types                         true
% 23.84/3.49  --sat_non_cyclic_types                  false
% 23.84/3.49  --sat_finite_models                     false
% 23.84/3.49  --sat_fm_lemmas                         false
% 23.84/3.49  --sat_fm_prep                           false
% 23.84/3.49  --sat_fm_uc_incr                        true
% 23.84/3.49  --sat_out_model                         small
% 23.84/3.49  --sat_out_clauses                       false
% 23.84/3.49  
% 23.84/3.49  ------ QBF Options
% 23.84/3.49  
% 23.84/3.49  --qbf_mode                              false
% 23.84/3.49  --qbf_elim_univ                         false
% 23.84/3.49  --qbf_dom_inst                          none
% 23.84/3.49  --qbf_dom_pre_inst                      false
% 23.84/3.49  --qbf_sk_in                             false
% 23.84/3.49  --qbf_pred_elim                         true
% 23.84/3.49  --qbf_split                             512
% 23.84/3.49  
% 23.84/3.49  ------ BMC1 Options
% 23.84/3.49  
% 23.84/3.49  --bmc1_incremental                      false
% 23.84/3.49  --bmc1_axioms                           reachable_all
% 23.84/3.49  --bmc1_min_bound                        0
% 23.84/3.49  --bmc1_max_bound                        -1
% 23.84/3.49  --bmc1_max_bound_default                -1
% 23.84/3.49  --bmc1_symbol_reachability              true
% 23.84/3.49  --bmc1_property_lemmas                  false
% 23.84/3.49  --bmc1_k_induction                      false
% 23.84/3.49  --bmc1_non_equiv_states                 false
% 23.84/3.49  --bmc1_deadlock                         false
% 23.84/3.49  --bmc1_ucm                              false
% 23.84/3.49  --bmc1_add_unsat_core                   none
% 23.84/3.49  --bmc1_unsat_core_children              false
% 23.84/3.49  --bmc1_unsat_core_extrapolate_axioms    false
% 23.84/3.49  --bmc1_out_stat                         full
% 23.84/3.49  --bmc1_ground_init                      false
% 23.84/3.49  --bmc1_pre_inst_next_state              false
% 23.84/3.49  --bmc1_pre_inst_state                   false
% 23.84/3.49  --bmc1_pre_inst_reach_state             false
% 23.84/3.49  --bmc1_out_unsat_core                   false
% 23.84/3.49  --bmc1_aig_witness_out                  false
% 23.84/3.49  --bmc1_verbose                          false
% 23.84/3.49  --bmc1_dump_clauses_tptp                false
% 23.84/3.49  --bmc1_dump_unsat_core_tptp             false
% 23.84/3.49  --bmc1_dump_file                        -
% 23.84/3.49  --bmc1_ucm_expand_uc_limit              128
% 23.84/3.49  --bmc1_ucm_n_expand_iterations          6
% 23.84/3.49  --bmc1_ucm_extend_mode                  1
% 23.84/3.49  --bmc1_ucm_init_mode                    2
% 23.84/3.49  --bmc1_ucm_cone_mode                    none
% 23.84/3.49  --bmc1_ucm_reduced_relation_type        0
% 23.84/3.49  --bmc1_ucm_relax_model                  4
% 23.84/3.49  --bmc1_ucm_full_tr_after_sat            true
% 23.84/3.49  --bmc1_ucm_expand_neg_assumptions       false
% 23.84/3.49  --bmc1_ucm_layered_model                none
% 23.84/3.49  --bmc1_ucm_max_lemma_size               10
% 23.84/3.49  
% 23.84/3.49  ------ AIG Options
% 23.84/3.49  
% 23.84/3.49  --aig_mode                              false
% 23.84/3.49  
% 23.84/3.49  ------ Instantiation Options
% 23.84/3.49  
% 23.84/3.49  --instantiation_flag                    true
% 23.84/3.49  --inst_sos_flag                         false
% 23.84/3.49  --inst_sos_phase                        true
% 23.84/3.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.84/3.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.84/3.49  --inst_lit_sel_side                     num_symb
% 23.84/3.49  --inst_solver_per_active                1400
% 23.84/3.49  --inst_solver_calls_frac                1.
% 23.84/3.49  --inst_passive_queue_type               priority_queues
% 23.84/3.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.84/3.49  --inst_passive_queues_freq              [25;2]
% 23.84/3.49  --inst_dismatching                      true
% 23.84/3.49  --inst_eager_unprocessed_to_passive     true
% 23.84/3.49  --inst_prop_sim_given                   true
% 23.84/3.49  --inst_prop_sim_new                     false
% 23.84/3.49  --inst_subs_new                         false
% 23.84/3.49  --inst_eq_res_simp                      false
% 23.84/3.49  --inst_subs_given                       false
% 23.84/3.49  --inst_orphan_elimination               true
% 23.84/3.49  --inst_learning_loop_flag               true
% 23.84/3.49  --inst_learning_start                   3000
% 23.84/3.49  --inst_learning_factor                  2
% 23.84/3.49  --inst_start_prop_sim_after_learn       3
% 23.84/3.49  --inst_sel_renew                        solver
% 23.84/3.49  --inst_lit_activity_flag                true
% 23.84/3.49  --inst_restr_to_given                   false
% 23.84/3.49  --inst_activity_threshold               500
% 23.84/3.49  --inst_out_proof                        true
% 23.84/3.49  
% 23.84/3.49  ------ Resolution Options
% 23.84/3.49  
% 23.84/3.49  --resolution_flag                       true
% 23.84/3.49  --res_lit_sel                           adaptive
% 23.84/3.49  --res_lit_sel_side                      none
% 23.84/3.49  --res_ordering                          kbo
% 23.84/3.49  --res_to_prop_solver                    active
% 23.84/3.49  --res_prop_simpl_new                    false
% 23.84/3.49  --res_prop_simpl_given                  true
% 23.84/3.49  --res_passive_queue_type                priority_queues
% 23.84/3.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.84/3.49  --res_passive_queues_freq               [15;5]
% 23.84/3.49  --res_forward_subs                      full
% 23.84/3.49  --res_backward_subs                     full
% 23.84/3.49  --res_forward_subs_resolution           true
% 23.84/3.49  --res_backward_subs_resolution          true
% 23.84/3.49  --res_orphan_elimination                true
% 23.84/3.49  --res_time_limit                        2.
% 23.84/3.49  --res_out_proof                         true
% 23.84/3.49  
% 23.84/3.49  ------ Superposition Options
% 23.84/3.49  
% 23.84/3.49  --superposition_flag                    true
% 23.84/3.49  --sup_passive_queue_type                priority_queues
% 23.84/3.49  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.84/3.49  --sup_passive_queues_freq               [1;4]
% 23.84/3.49  --demod_completeness_check              fast
% 23.84/3.49  --demod_use_ground                      true
% 23.84/3.49  --sup_to_prop_solver                    passive
% 23.84/3.49  --sup_prop_simpl_new                    true
% 23.84/3.49  --sup_prop_simpl_given                  true
% 23.84/3.49  --sup_fun_splitting                     false
% 23.84/3.49  --sup_smt_interval                      50000
% 23.84/3.49  
% 23.84/3.49  ------ Superposition Simplification Setup
% 23.84/3.49  
% 23.84/3.49  --sup_indices_passive                   []
% 23.84/3.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.84/3.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.84/3.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.84/3.49  --sup_full_triv                         [TrivRules;PropSubs]
% 23.84/3.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.84/3.49  --sup_full_bw                           [BwDemod]
% 23.84/3.49  --sup_immed_triv                        [TrivRules]
% 23.84/3.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.84/3.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.84/3.49  --sup_immed_bw_main                     []
% 23.84/3.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.84/3.49  --sup_input_triv                        [Unflattening;TrivRules]
% 23.84/3.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.84/3.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.84/3.49  
% 23.84/3.49  ------ Combination Options
% 23.84/3.49  
% 23.84/3.49  --comb_res_mult                         3
% 23.84/3.49  --comb_sup_mult                         2
% 23.84/3.49  --comb_inst_mult                        10
% 23.84/3.49  
% 23.84/3.49  ------ Debug Options
% 23.84/3.49  
% 23.84/3.49  --dbg_backtrace                         false
% 23.84/3.49  --dbg_dump_prop_clauses                 false
% 23.84/3.49  --dbg_dump_prop_clauses_file            -
% 23.84/3.49  --dbg_out_stat                          false
% 23.84/3.49  ------ Parsing...
% 23.84/3.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.84/3.49  
% 23.84/3.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 23.84/3.49  
% 23.84/3.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.84/3.49  
% 23.84/3.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.84/3.49  ------ Proving...
% 23.84/3.49  ------ Problem Properties 
% 23.84/3.49  
% 23.84/3.49  
% 23.84/3.49  clauses                                 16
% 23.84/3.49  conjectures                             2
% 23.84/3.49  EPR                                     7
% 23.84/3.49  Horn                                    16
% 23.84/3.49  unary                                   6
% 23.84/3.49  binary                                  5
% 23.84/3.49  lits                                    31
% 23.84/3.49  lits eq                                 8
% 23.84/3.49  fd_pure                                 0
% 23.84/3.49  fd_pseudo                               0
% 23.84/3.49  fd_cond                                 1
% 23.84/3.49  fd_pseudo_cond                          1
% 23.84/3.49  AC symbols                              0
% 23.84/3.49  
% 23.84/3.49  ------ Input Options Time Limit: Unbounded
% 23.84/3.49  
% 23.84/3.49  
% 23.84/3.49  ------ 
% 23.84/3.49  Current options:
% 23.84/3.49  ------ 
% 23.84/3.49  
% 23.84/3.49  ------ Input Options
% 23.84/3.49  
% 23.84/3.49  --out_options                           all
% 23.84/3.49  --tptp_safe_out                         true
% 23.84/3.49  --problem_path                          ""
% 23.84/3.49  --include_path                          ""
% 23.84/3.49  --clausifier                            res/vclausify_rel
% 23.84/3.49  --clausifier_options                    --mode clausify
% 23.84/3.49  --stdin                                 false
% 23.84/3.49  --stats_out                             sel
% 23.84/3.49  
% 23.84/3.49  ------ General Options
% 23.84/3.49  
% 23.84/3.49  --fof                                   false
% 23.84/3.49  --time_out_real                         604.99
% 23.84/3.49  --time_out_virtual                      -1.
% 23.84/3.49  --symbol_type_check                     false
% 23.84/3.49  --clausify_out                          false
% 23.84/3.49  --sig_cnt_out                           false
% 23.84/3.49  --trig_cnt_out                          false
% 23.84/3.49  --trig_cnt_out_tolerance                1.
% 23.84/3.49  --trig_cnt_out_sk_spl                   false
% 23.84/3.49  --abstr_cl_out                          false
% 23.84/3.49  
% 23.84/3.49  ------ Global Options
% 23.84/3.49  
% 23.84/3.49  --schedule                              none
% 23.84/3.49  --add_important_lit                     false
% 23.84/3.49  --prop_solver_per_cl                    1000
% 23.84/3.49  --min_unsat_core                        false
% 23.84/3.49  --soft_assumptions                      false
% 23.84/3.49  --soft_lemma_size                       3
% 23.84/3.49  --prop_impl_unit_size                   0
% 23.84/3.49  --prop_impl_unit                        []
% 23.84/3.49  --share_sel_clauses                     true
% 23.84/3.49  --reset_solvers                         false
% 23.84/3.49  --bc_imp_inh                            [conj_cone]
% 23.84/3.49  --conj_cone_tolerance                   3.
% 23.84/3.49  --extra_neg_conj                        none
% 23.84/3.49  --large_theory_mode                     true
% 23.84/3.49  --prolific_symb_bound                   200
% 23.84/3.49  --lt_threshold                          2000
% 23.84/3.49  --clause_weak_htbl                      true
% 23.84/3.49  --gc_record_bc_elim                     false
% 23.84/3.49  
% 23.84/3.49  ------ Preprocessing Options
% 23.84/3.49  
% 23.84/3.49  --preprocessing_flag                    true
% 23.84/3.49  --time_out_prep_mult                    0.1
% 23.84/3.49  --splitting_mode                        input
% 23.84/3.49  --splitting_grd                         true
% 23.84/3.49  --splitting_cvd                         false
% 23.84/3.49  --splitting_cvd_svl                     false
% 23.84/3.49  --splitting_nvd                         32
% 23.84/3.49  --sub_typing                            true
% 23.84/3.49  --prep_gs_sim                           false
% 23.84/3.49  --prep_unflatten                        true
% 23.84/3.49  --prep_res_sim                          true
% 23.84/3.49  --prep_upred                            true
% 23.84/3.49  --prep_sem_filter                       exhaustive
% 23.84/3.49  --prep_sem_filter_out                   false
% 23.84/3.49  --pred_elim                             false
% 23.84/3.49  --res_sim_input                         true
% 23.84/3.49  --eq_ax_congr_red                       true
% 23.84/3.49  --pure_diseq_elim                       true
% 23.84/3.49  --brand_transform                       false
% 23.84/3.49  --non_eq_to_eq                          false
% 23.84/3.49  --prep_def_merge                        true
% 23.84/3.49  --prep_def_merge_prop_impl              false
% 23.84/3.49  --prep_def_merge_mbd                    true
% 23.84/3.49  --prep_def_merge_tr_red                 false
% 23.84/3.49  --prep_def_merge_tr_cl                  false
% 23.84/3.49  --smt_preprocessing                     true
% 23.84/3.49  --smt_ac_axioms                         fast
% 23.84/3.49  --preprocessed_out                      false
% 23.84/3.49  --preprocessed_stats                    false
% 23.84/3.49  
% 23.84/3.49  ------ Abstraction refinement Options
% 23.84/3.49  
% 23.84/3.49  --abstr_ref                             []
% 23.84/3.49  --abstr_ref_prep                        false
% 23.84/3.49  --abstr_ref_until_sat                   false
% 23.84/3.49  --abstr_ref_sig_restrict                funpre
% 23.84/3.49  --abstr_ref_af_restrict_to_split_sk     false
% 23.84/3.49  --abstr_ref_under                       []
% 23.84/3.49  
% 23.84/3.49  ------ SAT Options
% 23.84/3.49  
% 23.84/3.49  --sat_mode                              false
% 23.84/3.49  --sat_fm_restart_options                ""
% 23.84/3.49  --sat_gr_def                            false
% 23.84/3.49  --sat_epr_types                         true
% 23.84/3.49  --sat_non_cyclic_types                  false
% 23.84/3.49  --sat_finite_models                     false
% 23.84/3.49  --sat_fm_lemmas                         false
% 23.84/3.49  --sat_fm_prep                           false
% 23.84/3.49  --sat_fm_uc_incr                        true
% 23.84/3.49  --sat_out_model                         small
% 23.84/3.49  --sat_out_clauses                       false
% 23.84/3.49  
% 23.84/3.49  ------ QBF Options
% 23.84/3.49  
% 23.84/3.49  --qbf_mode                              false
% 23.84/3.49  --qbf_elim_univ                         false
% 23.84/3.49  --qbf_dom_inst                          none
% 23.84/3.49  --qbf_dom_pre_inst                      false
% 23.84/3.49  --qbf_sk_in                             false
% 23.84/3.49  --qbf_pred_elim                         true
% 23.84/3.49  --qbf_split                             512
% 23.84/3.49  
% 23.84/3.49  ------ BMC1 Options
% 23.84/3.49  
% 23.84/3.49  --bmc1_incremental                      false
% 23.84/3.49  --bmc1_axioms                           reachable_all
% 23.84/3.49  --bmc1_min_bound                        0
% 23.84/3.49  --bmc1_max_bound                        -1
% 23.84/3.49  --bmc1_max_bound_default                -1
% 23.84/3.49  --bmc1_symbol_reachability              true
% 23.84/3.49  --bmc1_property_lemmas                  false
% 23.84/3.49  --bmc1_k_induction                      false
% 23.84/3.49  --bmc1_non_equiv_states                 false
% 23.84/3.49  --bmc1_deadlock                         false
% 23.84/3.49  --bmc1_ucm                              false
% 23.84/3.49  --bmc1_add_unsat_core                   none
% 23.84/3.49  --bmc1_unsat_core_children              false
% 23.84/3.49  --bmc1_unsat_core_extrapolate_axioms    false
% 23.84/3.49  --bmc1_out_stat                         full
% 23.84/3.49  --bmc1_ground_init                      false
% 23.84/3.49  --bmc1_pre_inst_next_state              false
% 23.84/3.49  --bmc1_pre_inst_state                   false
% 23.84/3.49  --bmc1_pre_inst_reach_state             false
% 23.84/3.49  --bmc1_out_unsat_core                   false
% 23.84/3.49  --bmc1_aig_witness_out                  false
% 23.84/3.49  --bmc1_verbose                          false
% 23.84/3.49  --bmc1_dump_clauses_tptp                false
% 23.84/3.49  --bmc1_dump_unsat_core_tptp             false
% 23.84/3.49  --bmc1_dump_file                        -
% 23.84/3.49  --bmc1_ucm_expand_uc_limit              128
% 23.84/3.49  --bmc1_ucm_n_expand_iterations          6
% 23.84/3.49  --bmc1_ucm_extend_mode                  1
% 23.84/3.49  --bmc1_ucm_init_mode                    2
% 23.84/3.49  --bmc1_ucm_cone_mode                    none
% 23.84/3.49  --bmc1_ucm_reduced_relation_type        0
% 23.84/3.49  --bmc1_ucm_relax_model                  4
% 23.84/3.49  --bmc1_ucm_full_tr_after_sat            true
% 23.84/3.49  --bmc1_ucm_expand_neg_assumptions       false
% 23.84/3.49  --bmc1_ucm_layered_model                none
% 23.84/3.49  --bmc1_ucm_max_lemma_size               10
% 23.84/3.49  
% 23.84/3.49  ------ AIG Options
% 23.84/3.49  
% 23.84/3.49  --aig_mode                              false
% 23.84/3.49  
% 23.84/3.49  ------ Instantiation Options
% 23.84/3.49  
% 23.84/3.49  --instantiation_flag                    true
% 23.84/3.49  --inst_sos_flag                         false
% 23.84/3.49  --inst_sos_phase                        true
% 23.84/3.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.84/3.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.84/3.49  --inst_lit_sel_side                     num_symb
% 23.84/3.49  --inst_solver_per_active                1400
% 23.84/3.49  --inst_solver_calls_frac                1.
% 23.84/3.49  --inst_passive_queue_type               priority_queues
% 23.84/3.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.84/3.49  --inst_passive_queues_freq              [25;2]
% 23.84/3.49  --inst_dismatching                      true
% 23.84/3.49  --inst_eager_unprocessed_to_passive     true
% 23.84/3.49  --inst_prop_sim_given                   true
% 23.84/3.49  --inst_prop_sim_new                     false
% 23.84/3.49  --inst_subs_new                         false
% 23.84/3.49  --inst_eq_res_simp                      false
% 23.84/3.49  --inst_subs_given                       false
% 23.84/3.49  --inst_orphan_elimination               true
% 23.84/3.49  --inst_learning_loop_flag               true
% 23.84/3.49  --inst_learning_start                   3000
% 23.84/3.49  --inst_learning_factor                  2
% 23.84/3.49  --inst_start_prop_sim_after_learn       3
% 23.84/3.49  --inst_sel_renew                        solver
% 23.84/3.49  --inst_lit_activity_flag                true
% 23.84/3.49  --inst_restr_to_given                   false
% 23.84/3.49  --inst_activity_threshold               500
% 23.84/3.49  --inst_out_proof                        true
% 23.84/3.49  
% 23.84/3.49  ------ Resolution Options
% 23.84/3.49  
% 23.84/3.49  --resolution_flag                       true
% 23.84/3.49  --res_lit_sel                           adaptive
% 23.84/3.49  --res_lit_sel_side                      none
% 23.84/3.49  --res_ordering                          kbo
% 23.84/3.49  --res_to_prop_solver                    active
% 23.84/3.49  --res_prop_simpl_new                    false
% 23.84/3.49  --res_prop_simpl_given                  true
% 23.84/3.49  --res_passive_queue_type                priority_queues
% 23.84/3.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.84/3.49  --res_passive_queues_freq               [15;5]
% 23.84/3.49  --res_forward_subs                      full
% 23.84/3.49  --res_backward_subs                     full
% 23.84/3.49  --res_forward_subs_resolution           true
% 23.84/3.49  --res_backward_subs_resolution          true
% 23.84/3.49  --res_orphan_elimination                true
% 23.84/3.49  --res_time_limit                        2.
% 23.84/3.49  --res_out_proof                         true
% 23.84/3.49  
% 23.84/3.49  ------ Superposition Options
% 23.84/3.49  
% 23.84/3.49  --superposition_flag                    true
% 23.84/3.49  --sup_passive_queue_type                priority_queues
% 23.84/3.49  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.84/3.49  --sup_passive_queues_freq               [1;4]
% 23.84/3.49  --demod_completeness_check              fast
% 23.84/3.49  --demod_use_ground                      true
% 23.84/3.49  --sup_to_prop_solver                    passive
% 23.84/3.49  --sup_prop_simpl_new                    true
% 23.84/3.49  --sup_prop_simpl_given                  true
% 23.84/3.49  --sup_fun_splitting                     false
% 23.84/3.49  --sup_smt_interval                      50000
% 23.84/3.49  
% 23.84/3.49  ------ Superposition Simplification Setup
% 23.84/3.49  
% 23.84/3.49  --sup_indices_passive                   []
% 23.84/3.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.84/3.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.84/3.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.84/3.49  --sup_full_triv                         [TrivRules;PropSubs]
% 23.84/3.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.84/3.49  --sup_full_bw                           [BwDemod]
% 23.84/3.49  --sup_immed_triv                        [TrivRules]
% 23.84/3.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.84/3.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.84/3.49  --sup_immed_bw_main                     []
% 23.84/3.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.84/3.49  --sup_input_triv                        [Unflattening;TrivRules]
% 23.84/3.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.84/3.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.84/3.49  
% 23.84/3.49  ------ Combination Options
% 23.84/3.49  
% 23.84/3.49  --comb_res_mult                         3
% 23.84/3.49  --comb_sup_mult                         2
% 23.84/3.49  --comb_inst_mult                        10
% 23.84/3.49  
% 23.84/3.49  ------ Debug Options
% 23.84/3.49  
% 23.84/3.49  --dbg_backtrace                         false
% 23.84/3.49  --dbg_dump_prop_clauses                 false
% 23.84/3.49  --dbg_dump_prop_clauses_file            -
% 23.84/3.49  --dbg_out_stat                          false
% 23.84/3.49  
% 23.84/3.49  
% 23.84/3.49  
% 23.84/3.49  
% 23.84/3.49  ------ Proving...
% 23.84/3.49  
% 23.84/3.49  
% 23.84/3.49  % SZS status Theorem for theBenchmark.p
% 23.84/3.49  
% 23.84/3.49  % SZS output start CNFRefutation for theBenchmark.p
% 23.84/3.49  
% 23.84/3.49  fof(f7,axiom,(
% 23.84/3.49    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 23.84/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.84/3.49  
% 23.84/3.49  fof(f18,plain,(
% 23.84/3.49    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 23.84/3.49    inference(ennf_transformation,[],[f7])).
% 23.84/3.49  
% 23.84/3.49  fof(f19,plain,(
% 23.84/3.49    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 23.84/3.49    inference(flattening,[],[f18])).
% 23.84/3.49  
% 23.84/3.49  fof(f38,plain,(
% 23.84/3.49    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 23.84/3.49    inference(cnf_transformation,[],[f19])).
% 23.84/3.49  
% 23.84/3.49  fof(f1,axiom,(
% 23.84/3.49    v1_xboole_0(k1_xboole_0)),
% 23.84/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.84/3.49  
% 23.84/3.49  fof(f30,plain,(
% 23.84/3.49    v1_xboole_0(k1_xboole_0)),
% 23.84/3.49    inference(cnf_transformation,[],[f1])).
% 23.84/3.49  
% 23.84/3.49  fof(f5,axiom,(
% 23.84/3.49    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 23.84/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.84/3.49  
% 23.84/3.49  fof(f16,plain,(
% 23.84/3.49    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 23.84/3.49    inference(ennf_transformation,[],[f5])).
% 23.84/3.49  
% 23.84/3.49  fof(f36,plain,(
% 23.84/3.49    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 23.84/3.49    inference(cnf_transformation,[],[f16])).
% 23.84/3.49  
% 23.84/3.49  fof(f6,axiom,(
% 23.84/3.49    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 23.84/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.84/3.49  
% 23.84/3.49  fof(f17,plain,(
% 23.84/3.49    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 23.84/3.49    inference(ennf_transformation,[],[f6])).
% 23.84/3.49  
% 23.84/3.49  fof(f37,plain,(
% 23.84/3.49    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 23.84/3.49    inference(cnf_transformation,[],[f17])).
% 23.84/3.49  
% 23.84/3.49  fof(f12,axiom,(
% 23.84/3.49    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 23.84/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.84/3.49  
% 23.84/3.49  fof(f44,plain,(
% 23.84/3.49    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 23.84/3.49    inference(cnf_transformation,[],[f12])).
% 23.84/3.49  
% 23.84/3.49  fof(f10,axiom,(
% 23.84/3.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 23.84/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.84/3.49  
% 23.84/3.49  fof(f23,plain,(
% 23.84/3.49    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 23.84/3.49    inference(ennf_transformation,[],[f10])).
% 23.84/3.49  
% 23.84/3.49  fof(f41,plain,(
% 23.84/3.49    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 23.84/3.49    inference(cnf_transformation,[],[f23])).
% 23.84/3.49  
% 23.84/3.49  fof(f4,axiom,(
% 23.84/3.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 23.84/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.84/3.49  
% 23.84/3.49  fof(f35,plain,(
% 23.84/3.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 23.84/3.49    inference(cnf_transformation,[],[f4])).
% 23.84/3.49  
% 23.84/3.49  fof(f3,axiom,(
% 23.84/3.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 23.84/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.84/3.49  
% 23.84/3.49  fof(f26,plain,(
% 23.84/3.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 23.84/3.49    inference(nnf_transformation,[],[f3])).
% 23.84/3.49  
% 23.84/3.49  fof(f27,plain,(
% 23.84/3.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 23.84/3.49    inference(flattening,[],[f26])).
% 23.84/3.49  
% 23.84/3.49  fof(f34,plain,(
% 23.84/3.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 23.84/3.49    inference(cnf_transformation,[],[f27])).
% 23.84/3.49  
% 23.84/3.49  fof(f8,axiom,(
% 23.84/3.49    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k2_relat_1(X0)))),
% 23.84/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.84/3.49  
% 23.84/3.49  fof(f20,plain,(
% 23.84/3.49    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 23.84/3.49    inference(ennf_transformation,[],[f8])).
% 23.84/3.49  
% 23.84/3.49  fof(f21,plain,(
% 23.84/3.49    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 23.84/3.49    inference(flattening,[],[f20])).
% 23.84/3.49  
% 23.84/3.49  fof(f39,plain,(
% 23.84/3.49    ( ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 23.84/3.49    inference(cnf_transformation,[],[f21])).
% 23.84/3.49  
% 23.84/3.49  fof(f2,axiom,(
% 23.84/3.49    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 23.84/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.84/3.49  
% 23.84/3.49  fof(f15,plain,(
% 23.84/3.49    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 23.84/3.49    inference(ennf_transformation,[],[f2])).
% 23.84/3.49  
% 23.84/3.49  fof(f31,plain,(
% 23.84/3.49    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 23.84/3.49    inference(cnf_transformation,[],[f15])).
% 23.84/3.49  
% 23.84/3.49  fof(f11,axiom,(
% 23.84/3.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 23.84/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.84/3.49  
% 23.84/3.49  fof(f24,plain,(
% 23.84/3.49    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 23.84/3.49    inference(ennf_transformation,[],[f11])).
% 23.84/3.49  
% 23.84/3.49  fof(f42,plain,(
% 23.84/3.49    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 23.84/3.49    inference(cnf_transformation,[],[f24])).
% 23.84/3.49  
% 23.84/3.49  fof(f9,axiom,(
% 23.84/3.49    ! [X0] : (v1_relat_1(X0) => k4_relat_1(k4_relat_1(X0)) = X0)),
% 23.84/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.84/3.49  
% 23.84/3.49  fof(f22,plain,(
% 23.84/3.49    ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 23.84/3.49    inference(ennf_transformation,[],[f9])).
% 23.84/3.49  
% 23.84/3.49  fof(f40,plain,(
% 23.84/3.49    ( ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 23.84/3.49    inference(cnf_transformation,[],[f22])).
% 23.84/3.49  
% 23.84/3.49  fof(f32,plain,(
% 23.84/3.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 23.84/3.49    inference(cnf_transformation,[],[f27])).
% 23.84/3.49  
% 23.84/3.49  fof(f48,plain,(
% 23.84/3.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 23.84/3.49    inference(equality_resolution,[],[f32])).
% 23.84/3.49  
% 23.84/3.49  fof(f13,conjecture,(
% 23.84/3.49    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 23.84/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.84/3.49  
% 23.84/3.49  fof(f14,negated_conjecture,(
% 23.84/3.49    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 23.84/3.49    inference(negated_conjecture,[],[f13])).
% 23.84/3.49  
% 23.84/3.49  fof(f25,plain,(
% 23.84/3.49    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 23.84/3.49    inference(ennf_transformation,[],[f14])).
% 23.84/3.49  
% 23.84/3.49  fof(f28,plain,(
% 23.84/3.49    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 23.84/3.49    introduced(choice_axiom,[])).
% 23.84/3.49  
% 23.84/3.49  fof(f29,plain,(
% 23.84/3.49    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 23.84/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f28])).
% 23.84/3.49  
% 23.84/3.49  fof(f45,plain,(
% 23.84/3.49    v1_relat_1(sK0)),
% 23.84/3.49    inference(cnf_transformation,[],[f29])).
% 23.84/3.49  
% 23.84/3.49  fof(f46,plain,(
% 23.84/3.49    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 23.84/3.49    inference(cnf_transformation,[],[f29])).
% 23.84/3.49  
% 23.84/3.49  cnf(c_202,plain,
% 23.84/3.49      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 23.84/3.49      theory(equality) ).
% 23.84/3.49  
% 23.84/3.49  cnf(c_2819,plain,
% 23.84/3.49      ( ~ r1_tarski(X0,X1)
% 23.84/3.49      | r1_tarski(X2,k5_relat_1(X3,X4))
% 23.84/3.49      | X2 != X0
% 23.84/3.49      | k5_relat_1(X3,X4) != X1 ),
% 23.84/3.49      inference(instantiation,[status(thm)],[c_202]) ).
% 23.84/3.49  
% 23.84/3.49  cnf(c_5840,plain,
% 23.84/3.49      ( ~ r1_tarski(X0,X1)
% 23.84/3.49      | r1_tarski(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(X2,X3))
% 23.84/3.49      | k5_relat_1(X2,X3) != X1
% 23.84/3.49      | k5_relat_1(k1_xboole_0,sK0) != X0 ),
% 23.84/3.49      inference(instantiation,[status(thm)],[c_2819]) ).
% 23.84/3.49  
% 23.84/3.49  cnf(c_10534,plain,
% 23.84/3.49      ( ~ r1_tarski(k5_relat_1(X0,k4_relat_1(k4_relat_1(sK0))),X1)
% 23.84/3.49      | r1_tarski(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(X2,X3))
% 23.84/3.49      | k5_relat_1(X2,X3) != X1
% 23.84/3.49      | k5_relat_1(k1_xboole_0,sK0) != k5_relat_1(X0,k4_relat_1(k4_relat_1(sK0))) ),
% 23.84/3.49      inference(instantiation,[status(thm)],[c_5840]) ).
% 23.84/3.49  
% 23.84/3.49  cnf(c_114399,plain,
% 23.84/3.49      ( ~ r1_tarski(k5_relat_1(k4_relat_1(X0),k4_relat_1(k4_relat_1(sK0))),k5_relat_1(X1,X2))
% 23.84/3.49      | r1_tarski(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(X3,X4))
% 23.84/3.49      | k5_relat_1(X3,X4) != k5_relat_1(X1,X2)
% 23.84/3.49      | k5_relat_1(k1_xboole_0,sK0) != k5_relat_1(k4_relat_1(X0),k4_relat_1(k4_relat_1(sK0))) ),
% 23.84/3.49      inference(instantiation,[status(thm)],[c_10534]) ).
% 23.84/3.49  
% 23.84/3.49  cnf(c_114403,plain,
% 23.84/3.49      ( ~ r1_tarski(k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(k4_relat_1(sK0))),k5_relat_1(k1_xboole_0,k1_xboole_0))
% 23.84/3.49      | r1_tarski(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,k1_xboole_0))
% 23.84/3.49      | k5_relat_1(k1_xboole_0,sK0) != k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(k4_relat_1(sK0)))
% 23.84/3.49      | k5_relat_1(k1_xboole_0,k1_xboole_0) != k5_relat_1(k1_xboole_0,k1_xboole_0) ),
% 23.84/3.49      inference(instantiation,[status(thm)],[c_114399]) ).
% 23.84/3.49  
% 23.84/3.49  cnf(c_200,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 23.84/3.49  
% 23.84/3.49  cnf(c_100771,plain,
% 23.84/3.49      ( X0 != X1
% 23.84/3.49      | X0 = k5_relat_1(k4_relat_1(sK0),X2)
% 23.84/3.49      | k5_relat_1(k4_relat_1(sK0),X2) != X1 ),
% 23.84/3.49      inference(instantiation,[status(thm)],[c_200]) ).
% 23.84/3.49  
% 23.84/3.49  cnf(c_100772,plain,
% 23.84/3.49      ( k5_relat_1(k4_relat_1(sK0),k1_xboole_0) != k1_xboole_0
% 23.84/3.49      | k1_xboole_0 = k5_relat_1(k4_relat_1(sK0),k1_xboole_0)
% 23.84/3.49      | k1_xboole_0 != k1_xboole_0 ),
% 23.84/3.49      inference(instantiation,[status(thm)],[c_100771]) ).
% 23.84/3.49  
% 23.84/3.49  cnf(c_8,plain,
% 23.84/3.49      ( ~ v1_relat_1(X0)
% 23.84/3.49      | ~ v1_relat_1(X1)
% 23.84/3.49      | v1_relat_1(k5_relat_1(X0,X1)) ),
% 23.84/3.49      inference(cnf_transformation,[],[f38]) ).
% 23.84/3.49  
% 23.84/3.49  cnf(c_435,plain,
% 23.84/3.49      ( v1_relat_1(X0) != iProver_top
% 23.84/3.49      | v1_relat_1(X1) != iProver_top
% 23.84/3.49      | v1_relat_1(k5_relat_1(X0,X1)) = iProver_top ),
% 23.84/3.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 23.84/3.49  
% 23.84/3.49  cnf(c_0,plain,
% 23.84/3.49      ( v1_xboole_0(k1_xboole_0) ),
% 23.84/3.49      inference(cnf_transformation,[],[f30]) ).
% 23.84/3.49  
% 23.84/3.49  cnf(c_442,plain,
% 23.84/3.49      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 23.84/3.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 23.84/3.49  
% 23.84/3.49  cnf(c_6,plain,
% 23.84/3.49      ( v1_relat_1(X0) | ~ v1_xboole_0(X0) ),
% 23.84/3.49      inference(cnf_transformation,[],[f36]) ).
% 23.84/3.49  
% 23.84/3.49  cnf(c_437,plain,
% 23.84/3.49      ( v1_relat_1(X0) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 23.84/3.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 23.84/3.49  
% 23.84/3.49  cnf(c_811,plain,
% 23.84/3.49      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 23.84/3.49      inference(superposition,[status(thm)],[c_442,c_437]) ).
% 23.84/3.49  
% 23.84/3.49  cnf(c_7,plain,
% 23.84/3.49      ( ~ v1_relat_1(X0) | v1_relat_1(k4_relat_1(X0)) ),
% 23.84/3.49      inference(cnf_transformation,[],[f37]) ).
% 23.84/3.49  
% 23.84/3.49  cnf(c_436,plain,
% 23.84/3.49      ( v1_relat_1(X0) != iProver_top
% 23.84/3.49      | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
% 23.84/3.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 23.84/3.49  
% 23.84/3.49  cnf(c_13,plain,
% 23.84/3.49      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 23.84/3.49      inference(cnf_transformation,[],[f44]) ).
% 23.84/3.49  
% 23.84/3.49  cnf(c_11,plain,
% 23.84/3.49      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
% 23.84/3.49      | ~ v1_relat_1(X0)
% 23.84/3.49      | ~ v1_relat_1(X1) ),
% 23.84/3.49      inference(cnf_transformation,[],[f41]) ).
% 23.84/3.49  
% 23.84/3.49  cnf(c_432,plain,
% 23.84/3.49      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
% 23.84/3.49      | v1_relat_1(X0) != iProver_top
% 23.84/3.49      | v1_relat_1(X1) != iProver_top ),
% 23.84/3.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 23.84/3.49  
% 23.84/3.49  cnf(c_936,plain,
% 23.84/3.49      ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) = iProver_top
% 23.84/3.49      | v1_relat_1(X0) != iProver_top
% 23.84/3.49      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 23.84/3.49      inference(superposition,[status(thm)],[c_13,c_432]) ).
% 23.84/3.49  
% 23.84/3.49  cnf(c_36,plain,
% 23.84/3.49      ( v1_relat_1(X0) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 23.84/3.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 23.84/3.49  
% 23.84/3.49  cnf(c_38,plain,
% 23.84/3.49      ( v1_relat_1(k1_xboole_0) = iProver_top
% 23.84/3.49      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 23.84/3.49      inference(instantiation,[status(thm)],[c_36]) ).
% 23.84/3.49  
% 23.84/3.49  cnf(c_50,plain,
% 23.84/3.49      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 23.84/3.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 23.84/3.49  
% 23.84/3.49  cnf(c_1353,plain,
% 23.84/3.49      ( v1_relat_1(X0) != iProver_top
% 23.84/3.49      | r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) = iProver_top ),
% 23.84/3.49      inference(global_propositional_subsumption,
% 23.84/3.49                [status(thm)],
% 23.84/3.49                [c_936,c_38,c_50]) ).
% 23.84/3.49  
% 23.84/3.49  cnf(c_1354,plain,
% 23.84/3.49      ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) = iProver_top
% 23.84/3.49      | v1_relat_1(X0) != iProver_top ),
% 23.84/3.49      inference(renaming,[status(thm)],[c_1353]) ).
% 23.84/3.49  
% 23.84/3.49  cnf(c_5,plain,
% 23.84/3.49      ( r1_tarski(k1_xboole_0,X0) ),
% 23.84/3.49      inference(cnf_transformation,[],[f35]) ).
% 23.84/3.49  
% 23.84/3.49  cnf(c_438,plain,
% 23.84/3.49      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 23.84/3.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 23.84/3.49  
% 23.84/3.49  cnf(c_2,plain,
% 23.84/3.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 23.84/3.49      inference(cnf_transformation,[],[f34]) ).
% 23.84/3.49  
% 23.84/3.49  cnf(c_440,plain,
% 23.84/3.49      ( X0 = X1
% 23.84/3.49      | r1_tarski(X0,X1) != iProver_top
% 23.84/3.49      | r1_tarski(X1,X0) != iProver_top ),
% 23.84/3.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 23.84/3.49  
% 23.84/3.49  cnf(c_1187,plain,
% 23.84/3.49      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 23.84/3.49      inference(superposition,[status(thm)],[c_438,c_440]) ).
% 23.84/3.49  
% 23.84/3.49  cnf(c_1562,plain,
% 23.84/3.49      ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
% 23.84/3.49      | v1_relat_1(X0) != iProver_top ),
% 23.84/3.49      inference(superposition,[status(thm)],[c_1354,c_1187]) ).
% 23.84/3.49  
% 23.84/3.49  cnf(c_5327,plain,
% 23.84/3.49      ( k2_relat_1(k5_relat_1(k4_relat_1(X0),k1_xboole_0)) = k1_xboole_0
% 23.84/3.49      | v1_relat_1(X0) != iProver_top ),
% 23.84/3.49      inference(superposition,[status(thm)],[c_436,c_1562]) ).
% 23.84/3.49  
% 23.84/3.49  cnf(c_5552,plain,
% 23.84/3.49      ( k2_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0)) = k1_xboole_0 ),
% 23.84/3.49      inference(superposition,[status(thm)],[c_811,c_5327]) ).
% 23.84/3.49  
% 23.84/3.49  cnf(c_9,plain,
% 23.84/3.49      ( ~ v1_relat_1(X0)
% 23.84/3.49      | v1_xboole_0(X0)
% 23.84/3.49      | ~ v1_xboole_0(k2_relat_1(X0)) ),
% 23.84/3.49      inference(cnf_transformation,[],[f39]) ).
% 23.84/3.49  
% 23.84/3.49  cnf(c_434,plain,
% 23.84/3.49      ( v1_relat_1(X0) != iProver_top
% 23.84/3.49      | v1_xboole_0(X0) = iProver_top
% 23.84/3.49      | v1_xboole_0(k2_relat_1(X0)) != iProver_top ),
% 23.84/3.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 23.84/3.49  
% 23.84/3.49  cnf(c_88860,plain,
% 23.84/3.49      ( v1_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0)) != iProver_top
% 23.84/3.49      | v1_xboole_0(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0)) = iProver_top
% 23.84/3.49      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 23.84/3.49      inference(superposition,[status(thm)],[c_5552,c_434]) ).
% 23.84/3.49  
% 23.84/3.49  cnf(c_89505,plain,
% 23.84/3.49      ( v1_xboole_0(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0)) = iProver_top
% 23.84/3.49      | v1_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0)) != iProver_top ),
% 23.84/3.49      inference(global_propositional_subsumption,
% 23.84/3.49                [status(thm)],
% 23.84/3.49                [c_88860,c_50]) ).
% 23.84/3.49  
% 23.84/3.49  cnf(c_89506,plain,
% 23.84/3.49      ( v1_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0)) != iProver_top
% 23.84/3.49      | v1_xboole_0(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0)) = iProver_top ),
% 23.84/3.49      inference(renaming,[status(thm)],[c_89505]) ).
% 23.84/3.49  
% 23.84/3.49  cnf(c_89511,plain,
% 23.84/3.49      ( v1_relat_1(k4_relat_1(k1_xboole_0)) != iProver_top
% 23.84/3.49      | v1_relat_1(k1_xboole_0) != iProver_top
% 23.84/3.49      | v1_xboole_0(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0)) = iProver_top ),
% 23.84/3.49      inference(superposition,[status(thm)],[c_435,c_89506]) ).
% 23.84/3.49  
% 23.84/3.49  cnf(c_33,plain,
% 23.84/3.49      ( v1_relat_1(X0) != iProver_top
% 23.84/3.49      | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
% 23.84/3.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 23.84/3.49  
% 23.84/3.49  cnf(c_35,plain,
% 23.84/3.49      ( v1_relat_1(k4_relat_1(k1_xboole_0)) = iProver_top
% 23.84/3.49      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 23.84/3.49      inference(instantiation,[status(thm)],[c_33]) ).
% 23.84/3.49  
% 23.84/3.49  cnf(c_89514,plain,
% 23.84/3.49      ( v1_xboole_0(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0)) = iProver_top ),
% 23.84/3.49      inference(global_propositional_subsumption,
% 23.84/3.49                [status(thm)],
% 23.84/3.49                [c_89511,c_35,c_38,c_50]) ).
% 23.84/3.49  
% 23.84/3.49  cnf(c_1,plain,
% 23.84/3.49      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 23.84/3.49      inference(cnf_transformation,[],[f31]) ).
% 23.84/3.49  
% 23.84/3.49  cnf(c_441,plain,
% 23.84/3.49      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 23.84/3.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 23.84/3.49  
% 23.84/3.49  cnf(c_89520,plain,
% 23.84/3.49      ( k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
% 23.84/3.49      inference(superposition,[status(thm)],[c_89514,c_441]) ).
% 23.84/3.49  
% 23.84/3.49  cnf(c_12,plain,
% 23.84/3.49      ( ~ v1_relat_1(X0)
% 23.84/3.49      | ~ v1_relat_1(X1)
% 23.84/3.49      | k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1)) ),
% 23.84/3.49      inference(cnf_transformation,[],[f42]) ).
% 23.84/3.49  
% 23.84/3.49  cnf(c_431,plain,
% 23.84/3.49      ( k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,X0))
% 23.84/3.49      | v1_relat_1(X1) != iProver_top
% 23.84/3.49      | v1_relat_1(X0) != iProver_top ),
% 23.84/3.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 23.84/3.49  
% 23.84/3.49  cnf(c_1366,plain,
% 23.84/3.49      ( k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,k1_xboole_0))
% 23.84/3.49      | v1_relat_1(X0) != iProver_top ),
% 23.84/3.49      inference(superposition,[status(thm)],[c_811,c_431]) ).
% 23.84/3.49  
% 23.84/3.49  cnf(c_2164,plain,
% 23.84/3.49      ( k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(k4_relat_1(X0))) = k4_relat_1(k5_relat_1(k4_relat_1(X0),k1_xboole_0))
% 23.84/3.49      | v1_relat_1(X0) != iProver_top ),
% 23.84/3.49      inference(superposition,[status(thm)],[c_436,c_1366]) ).
% 23.84/3.49  
% 23.84/3.49  cnf(c_3953,plain,
% 23.84/3.49      ( k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(k4_relat_1(k1_xboole_0))) = k4_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0)) ),
% 23.84/3.49      inference(superposition,[status(thm)],[c_811,c_2164]) ).
% 23.84/3.49  
% 23.84/3.49  cnf(c_10,plain,
% 23.84/3.49      ( ~ v1_relat_1(X0) | k4_relat_1(k4_relat_1(X0)) = X0 ),
% 23.84/3.49      inference(cnf_transformation,[],[f40]) ).
% 23.84/3.49  
% 23.84/3.49  cnf(c_433,plain,
% 23.84/3.49      ( k4_relat_1(k4_relat_1(X0)) = X0 | v1_relat_1(X0) != iProver_top ),
% 23.84/3.50      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_1365,plain,
% 23.84/3.50      ( k4_relat_1(k4_relat_1(k1_xboole_0)) = k1_xboole_0 ),
% 23.84/3.50      inference(superposition,[status(thm)],[c_811,c_433]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_3961,plain,
% 23.84/3.50      ( k4_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0)) = k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0) ),
% 23.84/3.50      inference(light_normalisation,[status(thm)],[c_3953,c_1365]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_90147,plain,
% 23.84/3.50      ( k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 23.84/3.50      inference(demodulation,[status(thm)],[c_89520,c_3961]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_879,plain,
% 23.84/3.50      ( X0 != X1 | k5_relat_1(X2,X3) != X1 | k5_relat_1(X2,X3) = X0 ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_200]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_3764,plain,
% 23.84/3.50      ( k5_relat_1(X0,X1) != X2
% 23.84/3.50      | k5_relat_1(X0,X1) = k4_relat_1(k5_relat_1(X3,X4))
% 23.84/3.50      | k4_relat_1(k5_relat_1(X3,X4)) != X2 ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_879]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_8984,plain,
% 23.84/3.50      ( k5_relat_1(X0,X1) != k4_relat_1(X2)
% 23.84/3.50      | k5_relat_1(X0,X1) = k4_relat_1(k5_relat_1(X3,X4))
% 23.84/3.50      | k4_relat_1(k5_relat_1(X3,X4)) != k4_relat_1(X2) ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_3764]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_21352,plain,
% 23.84/3.50      ( k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) != k4_relat_1(X2)
% 23.84/3.50      | k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X3,X4))
% 23.84/3.50      | k4_relat_1(k5_relat_1(X3,X4)) != k4_relat_1(X2) ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_8984]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_81722,plain,
% 23.84/3.50      ( k5_relat_1(k4_relat_1(X0),k4_relat_1(k4_relat_1(sK0))) != k4_relat_1(X1)
% 23.84/3.50      | k5_relat_1(k4_relat_1(X0),k4_relat_1(k4_relat_1(sK0))) = k4_relat_1(k5_relat_1(X2,X3))
% 23.84/3.50      | k4_relat_1(k5_relat_1(X2,X3)) != k4_relat_1(X1) ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_21352]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_81725,plain,
% 23.84/3.50      ( k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(k4_relat_1(sK0))) = k4_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0))
% 23.84/3.50      | k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(k4_relat_1(sK0))) != k4_relat_1(k1_xboole_0)
% 23.84/3.50      | k4_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0)) != k4_relat_1(k1_xboole_0) ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_81722]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_205,plain,
% 23.84/3.50      ( X0 != X1 | X2 != X3 | k5_relat_1(X0,X2) = k5_relat_1(X1,X3) ),
% 23.84/3.50      theory(equality) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_777,plain,
% 23.84/3.50      ( X0 != sK0
% 23.84/3.50      | X1 != k1_xboole_0
% 23.84/3.50      | k5_relat_1(X1,X0) = k5_relat_1(k1_xboole_0,sK0) ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_205]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_1438,plain,
% 23.84/3.50      ( X0 != k1_xboole_0
% 23.84/3.50      | k5_relat_1(X0,k4_relat_1(k4_relat_1(sK0))) = k5_relat_1(k1_xboole_0,sK0)
% 23.84/3.50      | k4_relat_1(k4_relat_1(sK0)) != sK0 ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_777]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_46727,plain,
% 23.84/3.50      ( k5_relat_1(k4_relat_1(X0),k4_relat_1(k4_relat_1(sK0))) = k5_relat_1(k1_xboole_0,sK0)
% 23.84/3.50      | k4_relat_1(X0) != k1_xboole_0
% 23.84/3.50      | k4_relat_1(k4_relat_1(sK0)) != sK0 ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_1438]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_46728,plain,
% 23.84/3.50      ( k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(k4_relat_1(sK0))) = k5_relat_1(k1_xboole_0,sK0)
% 23.84/3.50      | k4_relat_1(k4_relat_1(sK0)) != sK0
% 23.84/3.50      | k4_relat_1(k1_xboole_0) != k1_xboole_0 ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_46727]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_7659,plain,
% 23.84/3.50      ( ~ r1_tarski(X0,X1)
% 23.84/3.50      | r1_tarski(k4_relat_1(k5_relat_1(X2,X3)),k5_relat_1(X4,X5))
% 23.84/3.50      | k5_relat_1(X4,X5) != X1
% 23.84/3.50      | k4_relat_1(k5_relat_1(X2,X3)) != X0 ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_2819]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_16140,plain,
% 23.84/3.50      ( ~ r1_tarski(k4_relat_1(X0),X1)
% 23.84/3.50      | r1_tarski(k4_relat_1(k5_relat_1(X2,X3)),k5_relat_1(X4,X5))
% 23.84/3.50      | k5_relat_1(X4,X5) != X1
% 23.84/3.50      | k4_relat_1(k5_relat_1(X2,X3)) != k4_relat_1(X0) ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_7659]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_36856,plain,
% 23.84/3.50      ( ~ r1_tarski(k4_relat_1(X0),k4_relat_1(X0))
% 23.84/3.50      | r1_tarski(k4_relat_1(k5_relat_1(X1,X2)),k5_relat_1(X3,X4))
% 23.84/3.50      | k5_relat_1(X3,X4) != k4_relat_1(X0)
% 23.84/3.50      | k4_relat_1(k5_relat_1(X1,X2)) != k4_relat_1(X0) ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_16140]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_36862,plain,
% 23.84/3.50      ( r1_tarski(k4_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0)),k5_relat_1(k1_xboole_0,k1_xboole_0))
% 23.84/3.50      | ~ r1_tarski(k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0))
% 23.84/3.50      | k5_relat_1(k1_xboole_0,k1_xboole_0) != k4_relat_1(k1_xboole_0)
% 23.84/3.50      | k4_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0)) != k4_relat_1(k1_xboole_0) ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_36856]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_4,plain,
% 23.84/3.50      ( r1_tarski(X0,X0) ),
% 23.84/3.50      inference(cnf_transformation,[],[f48]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_22530,plain,
% 23.84/3.50      ( r1_tarski(k4_relat_1(X0),k4_relat_1(X0)) ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_4]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_22536,plain,
% 23.84/3.50      ( r1_tarski(k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0)) ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_22530]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_5951,plain,
% 23.84/3.50      ( ~ r1_tarski(X0,X1)
% 23.84/3.50      | r1_tarski(k5_relat_1(X2,k4_relat_1(k4_relat_1(sK0))),k5_relat_1(X3,X4))
% 23.84/3.50      | k5_relat_1(X3,X4) != X1
% 23.84/3.50      | k5_relat_1(X2,k4_relat_1(k4_relat_1(sK0))) != X0 ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_2819]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_21522,plain,
% 23.84/3.50      ( ~ r1_tarski(k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)),X2)
% 23.84/3.50      | r1_tarski(k5_relat_1(k4_relat_1(X3),k4_relat_1(k4_relat_1(sK0))),k5_relat_1(X4,X5))
% 23.84/3.50      | k5_relat_1(X4,X5) != X2
% 23.84/3.50      | k5_relat_1(k4_relat_1(X3),k4_relat_1(k4_relat_1(sK0))) != k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_5951]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_21527,plain,
% 23.84/3.50      ( r1_tarski(k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(k4_relat_1(sK0))),k5_relat_1(k1_xboole_0,k1_xboole_0))
% 23.84/3.50      | ~ r1_tarski(k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0)),k1_xboole_0)
% 23.84/3.50      | k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(k4_relat_1(sK0))) != k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0))
% 23.84/3.50      | k5_relat_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_21522]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_1295,plain,
% 23.84/3.50      ( X0 != k5_relat_1(X1,X2)
% 23.84/3.50      | k5_relat_1(X1,X2) = X0
% 23.84/3.50      | k5_relat_1(X1,X2) != k5_relat_1(X1,X2) ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_879]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_4252,plain,
% 23.84/3.50      ( X0 != k5_relat_1(X1,k4_relat_1(k4_relat_1(sK0)))
% 23.84/3.50      | k5_relat_1(X1,k4_relat_1(k4_relat_1(sK0))) = X0
% 23.84/3.50      | k5_relat_1(X1,k4_relat_1(k4_relat_1(sK0))) != k5_relat_1(X1,k4_relat_1(k4_relat_1(sK0))) ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_1295]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_21511,plain,
% 23.84/3.50      ( k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) != k5_relat_1(k4_relat_1(X2),k4_relat_1(k4_relat_1(sK0)))
% 23.84/3.50      | k5_relat_1(k4_relat_1(X2),k4_relat_1(k4_relat_1(sK0))) = k5_relat_1(k4_relat_1(X0),k4_relat_1(X1))
% 23.84/3.50      | k5_relat_1(k4_relat_1(X2),k4_relat_1(k4_relat_1(sK0))) != k5_relat_1(k4_relat_1(X2),k4_relat_1(k4_relat_1(sK0))) ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_4252]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_21515,plain,
% 23.84/3.50      ( k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(k4_relat_1(sK0))) != k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(k4_relat_1(sK0)))
% 23.84/3.50      | k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(k4_relat_1(sK0))) = k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0))
% 23.84/3.50      | k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0)) != k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(k4_relat_1(sK0))) ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_21511]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_1293,plain,
% 23.84/3.50      ( X0 != k4_relat_1(k5_relat_1(X1,X2))
% 23.84/3.50      | k5_relat_1(k4_relat_1(X2),k4_relat_1(X1)) = X0
% 23.84/3.50      | k5_relat_1(k4_relat_1(X2),k4_relat_1(X1)) != k4_relat_1(k5_relat_1(X1,X2)) ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_879]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_3763,plain,
% 23.84/3.50      ( k5_relat_1(X0,X1) != k4_relat_1(k5_relat_1(X2,X3))
% 23.84/3.50      | k5_relat_1(k4_relat_1(X3),k4_relat_1(X2)) = k5_relat_1(X0,X1)
% 23.84/3.50      | k5_relat_1(k4_relat_1(X3),k4_relat_1(X2)) != k4_relat_1(k5_relat_1(X2,X3)) ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_1293]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_10385,plain,
% 23.84/3.50      ( k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) = k5_relat_1(k4_relat_1(X2),k4_relat_1(X3))
% 23.84/3.50      | k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) != k4_relat_1(k5_relat_1(X1,X0))
% 23.84/3.50      | k5_relat_1(k4_relat_1(X2),k4_relat_1(X3)) != k4_relat_1(k5_relat_1(X1,X0)) ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_3763]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_21508,plain,
% 23.84/3.50      ( k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) = k5_relat_1(k4_relat_1(X2),k4_relat_1(k4_relat_1(sK0)))
% 23.84/3.50      | k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) != k4_relat_1(k5_relat_1(X1,X0))
% 23.84/3.50      | k5_relat_1(k4_relat_1(X2),k4_relat_1(k4_relat_1(sK0))) != k4_relat_1(k5_relat_1(X1,X0)) ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_10385]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_21514,plain,
% 23.84/3.50      ( k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(k4_relat_1(sK0))) != k4_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0))
% 23.84/3.50      | k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0)) = k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(k4_relat_1(sK0)))
% 23.84/3.50      | k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0)) != k4_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0)) ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_21508]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_21341,plain,
% 23.84/3.50      ( k5_relat_1(X0,X1) != X2
% 23.84/3.50      | k5_relat_1(X0,X1) = k4_relat_1(X3)
% 23.84/3.50      | k4_relat_1(X3) != X2 ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_879]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_21342,plain,
% 23.84/3.50      ( k5_relat_1(k1_xboole_0,k1_xboole_0) = k4_relat_1(k1_xboole_0)
% 23.84/3.50      | k5_relat_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 23.84/3.50      | k4_relat_1(k1_xboole_0) != k1_xboole_0 ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_21341]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_599,plain,
% 23.84/3.50      ( X0 != X1
% 23.84/3.50      | k5_relat_1(k1_xboole_0,sK0) != X1
% 23.84/3.50      | k5_relat_1(k1_xboole_0,sK0) = X0 ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_200]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_701,plain,
% 23.84/3.50      ( X0 != k5_relat_1(k1_xboole_0,sK0)
% 23.84/3.50      | k5_relat_1(k1_xboole_0,sK0) = X0
% 23.84/3.50      | k5_relat_1(k1_xboole_0,sK0) != k5_relat_1(k1_xboole_0,sK0) ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_599]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_776,plain,
% 23.84/3.50      ( k5_relat_1(X0,X1) != k5_relat_1(k1_xboole_0,sK0)
% 23.84/3.50      | k5_relat_1(k1_xboole_0,sK0) = k5_relat_1(X0,X1)
% 23.84/3.50      | k5_relat_1(k1_xboole_0,sK0) != k5_relat_1(k1_xboole_0,sK0) ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_701]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_3072,plain,
% 23.84/3.50      ( k5_relat_1(X0,k4_relat_1(k4_relat_1(sK0))) != k5_relat_1(k1_xboole_0,sK0)
% 23.84/3.50      | k5_relat_1(k1_xboole_0,sK0) = k5_relat_1(X0,k4_relat_1(k4_relat_1(sK0)))
% 23.84/3.50      | k5_relat_1(k1_xboole_0,sK0) != k5_relat_1(k1_xboole_0,sK0) ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_776]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_19302,plain,
% 23.84/3.50      ( k5_relat_1(k4_relat_1(X0),k4_relat_1(k4_relat_1(sK0))) != k5_relat_1(k1_xboole_0,sK0)
% 23.84/3.50      | k5_relat_1(k1_xboole_0,sK0) = k5_relat_1(k4_relat_1(X0),k4_relat_1(k4_relat_1(sK0)))
% 23.84/3.50      | k5_relat_1(k1_xboole_0,sK0) != k5_relat_1(k1_xboole_0,sK0) ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_3072]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_19305,plain,
% 23.84/3.50      ( k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(k4_relat_1(sK0))) != k5_relat_1(k1_xboole_0,sK0)
% 23.84/3.50      | k5_relat_1(k1_xboole_0,sK0) = k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(k4_relat_1(sK0)))
% 23.84/3.50      | k5_relat_1(k1_xboole_0,sK0) != k5_relat_1(k1_xboole_0,sK0) ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_19302]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_16,negated_conjecture,
% 23.84/3.50      ( v1_relat_1(sK0) ),
% 23.84/3.50      inference(cnf_transformation,[],[f45]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_430,plain,
% 23.84/3.50      ( v1_relat_1(sK0) = iProver_top ),
% 23.84/3.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_5551,plain,
% 23.84/3.50      ( k2_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) = k1_xboole_0 ),
% 23.84/3.50      inference(superposition,[status(thm)],[c_430,c_5327]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_5740,plain,
% 23.84/3.50      ( v1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) != iProver_top
% 23.84/3.50      | v1_xboole_0(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) = iProver_top
% 23.84/3.50      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 23.84/3.50      inference(superposition,[status(thm)],[c_5551,c_434]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_18361,plain,
% 23.84/3.50      ( v1_xboole_0(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) = iProver_top
% 23.84/3.50      | v1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) != iProver_top ),
% 23.84/3.50      inference(global_propositional_subsumption,
% 23.84/3.50                [status(thm)],
% 23.84/3.50                [c_5740,c_50]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_18362,plain,
% 23.84/3.50      ( v1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) != iProver_top
% 23.84/3.50      | v1_xboole_0(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) = iProver_top ),
% 23.84/3.50      inference(renaming,[status(thm)],[c_18361]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_18367,plain,
% 23.84/3.50      ( v1_relat_1(k4_relat_1(sK0)) != iProver_top
% 23.84/3.50      | v1_relat_1(k1_xboole_0) != iProver_top
% 23.84/3.50      | v1_xboole_0(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) = iProver_top ),
% 23.84/3.50      inference(superposition,[status(thm)],[c_435,c_18362]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_17,plain,
% 23.84/3.50      ( v1_relat_1(sK0) = iProver_top ),
% 23.84/3.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_8513,plain,
% 23.84/3.50      ( v1_relat_1(k4_relat_1(sK0)) | ~ v1_relat_1(sK0) ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_7]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_8514,plain,
% 23.84/3.50      ( v1_relat_1(k4_relat_1(sK0)) = iProver_top
% 23.84/3.50      | v1_relat_1(sK0) != iProver_top ),
% 23.84/3.50      inference(predicate_to_equality,[status(thm)],[c_8513]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_18370,plain,
% 23.84/3.50      ( v1_xboole_0(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) = iProver_top ),
% 23.84/3.50      inference(global_propositional_subsumption,
% 23.84/3.50                [status(thm)],
% 23.84/3.50                [c_18367,c_17,c_38,c_50,c_8514]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_18376,plain,
% 23.84/3.50      ( k5_relat_1(k4_relat_1(sK0),k1_xboole_0) = k1_xboole_0 ),
% 23.84/3.50      inference(superposition,[status(thm)],[c_18370,c_441]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_204,plain,
% 23.84/3.50      ( X0 != X1 | k4_relat_1(X0) = k4_relat_1(X1) ),
% 23.84/3.50      theory(equality) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_3760,plain,
% 23.84/3.50      ( X0 != k5_relat_1(X1,X2)
% 23.84/3.50      | k4_relat_1(X0) = k4_relat_1(k5_relat_1(X1,X2)) ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_204]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_15380,plain,
% 23.84/3.50      ( X0 != k5_relat_1(k4_relat_1(sK0),X1)
% 23.84/3.50      | k4_relat_1(X0) = k4_relat_1(k5_relat_1(k4_relat_1(sK0),X1)) ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_3760]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_15381,plain,
% 23.84/3.50      ( k4_relat_1(k1_xboole_0) = k4_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))
% 23.84/3.50      | k1_xboole_0 != k5_relat_1(k4_relat_1(sK0),k1_xboole_0) ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_15380]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_2702,plain,
% 23.84/3.50      ( r1_tarski(k1_xboole_0,k5_relat_1(X0,X1)) ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_5]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_10542,plain,
% 23.84/3.50      ( r1_tarski(k1_xboole_0,k5_relat_1(X0,sK0)) ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_2702]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_10544,plain,
% 23.84/3.50      ( r1_tarski(k1_xboole_0,k5_relat_1(k1_xboole_0,sK0)) ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_10542]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_3759,plain,
% 23.84/3.50      ( k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(X2)
% 23.84/3.50      | k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) != k4_relat_1(k5_relat_1(X1,X0))
% 23.84/3.50      | k4_relat_1(X2) != k4_relat_1(k5_relat_1(X1,X0)) ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_1293]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_10354,plain,
% 23.84/3.50      ( k5_relat_1(k4_relat_1(X0),k4_relat_1(k4_relat_1(sK0))) = k4_relat_1(X1)
% 23.84/3.50      | k5_relat_1(k4_relat_1(X0),k4_relat_1(k4_relat_1(sK0))) != k4_relat_1(k5_relat_1(k4_relat_1(sK0),X0))
% 23.84/3.50      | k4_relat_1(X1) != k4_relat_1(k5_relat_1(k4_relat_1(sK0),X0)) ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_3759]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_10356,plain,
% 23.84/3.50      ( k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(k4_relat_1(sK0))) != k4_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))
% 23.84/3.50      | k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(k4_relat_1(sK0))) = k4_relat_1(k1_xboole_0)
% 23.84/3.50      | k4_relat_1(k1_xboole_0) != k4_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_10354]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_3755,plain,
% 23.84/3.50      ( k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) = k5_relat_1(k4_relat_1(X0),k4_relat_1(X1))
% 23.84/3.50      | k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) != k4_relat_1(k5_relat_1(X1,X0)) ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_1293]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_10297,plain,
% 23.84/3.50      ( k5_relat_1(k4_relat_1(X0),k4_relat_1(k4_relat_1(sK0))) = k5_relat_1(k4_relat_1(X0),k4_relat_1(k4_relat_1(sK0)))
% 23.84/3.50      | k5_relat_1(k4_relat_1(X0),k4_relat_1(k4_relat_1(sK0))) != k4_relat_1(k5_relat_1(k4_relat_1(sK0),X0)) ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_3755]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_10300,plain,
% 23.84/3.50      ( k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(k4_relat_1(sK0))) = k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(k4_relat_1(sK0)))
% 23.84/3.50      | k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(k4_relat_1(sK0))) != k4_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_10297]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_5329,plain,
% 23.84/3.50      ( k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_xboole_0 ),
% 23.84/3.50      inference(superposition,[status(thm)],[c_430,c_1562]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_5501,plain,
% 23.84/3.50      ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) != iProver_top
% 23.84/3.50      | v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) = iProver_top
% 23.84/3.50      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 23.84/3.50      inference(superposition,[status(thm)],[c_5329,c_434]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_10226,plain,
% 23.84/3.50      ( v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) = iProver_top
% 23.84/3.50      | v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) != iProver_top ),
% 23.84/3.50      inference(global_propositional_subsumption,
% 23.84/3.50                [status(thm)],
% 23.84/3.50                [c_5501,c_50]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_10227,plain,
% 23.84/3.50      ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) != iProver_top
% 23.84/3.50      | v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) = iProver_top ),
% 23.84/3.50      inference(renaming,[status(thm)],[c_10226]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_10232,plain,
% 23.84/3.50      ( v1_relat_1(sK0) != iProver_top
% 23.84/3.50      | v1_relat_1(k1_xboole_0) != iProver_top
% 23.84/3.50      | v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) = iProver_top ),
% 23.84/3.50      inference(superposition,[status(thm)],[c_435,c_10227]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_866,plain,
% 23.84/3.50      ( ~ r1_tarski(X0,X1)
% 23.84/3.50      | r1_tarski(k5_relat_1(X2,X3),k1_xboole_0)
% 23.84/3.50      | k5_relat_1(X2,X3) != X0
% 23.84/3.50      | k1_xboole_0 != X1 ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_202]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_1337,plain,
% 23.84/3.50      ( r1_tarski(k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)),k1_xboole_0)
% 23.84/3.50      | ~ r1_tarski(k4_relat_1(k5_relat_1(X1,X0)),X2)
% 23.84/3.50      | k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) != k4_relat_1(k5_relat_1(X1,X0))
% 23.84/3.50      | k1_xboole_0 != X2 ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_866]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_7658,plain,
% 23.84/3.50      ( r1_tarski(k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)),k1_xboole_0)
% 23.84/3.50      | ~ r1_tarski(k4_relat_1(k5_relat_1(X1,X0)),k5_relat_1(X2,X3))
% 23.84/3.50      | k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) != k4_relat_1(k5_relat_1(X1,X0))
% 23.84/3.50      | k1_xboole_0 != k5_relat_1(X2,X3) ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_1337]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_7661,plain,
% 23.84/3.50      ( r1_tarski(k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0)),k1_xboole_0)
% 23.84/3.50      | ~ r1_tarski(k4_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0)),k5_relat_1(k1_xboole_0,k1_xboole_0))
% 23.84/3.50      | k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0)) != k4_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0))
% 23.84/3.50      | k1_xboole_0 != k5_relat_1(k1_xboole_0,k1_xboole_0) ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_7658]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_588,plain,
% 23.84/3.50      ( ~ r1_tarski(X0,X1)
% 23.84/3.50      | r1_tarski(k5_relat_1(k1_xboole_0,sK0),k1_xboole_0)
% 23.84/3.50      | k5_relat_1(k1_xboole_0,sK0) != X0
% 23.84/3.50      | k1_xboole_0 != X1 ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_202]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_657,plain,
% 23.84/3.50      ( ~ r1_tarski(k5_relat_1(k1_xboole_0,sK0),X0)
% 23.84/3.50      | r1_tarski(k5_relat_1(k1_xboole_0,sK0),k1_xboole_0)
% 23.84/3.50      | k5_relat_1(k1_xboole_0,sK0) != k5_relat_1(k1_xboole_0,sK0)
% 23.84/3.50      | k1_xboole_0 != X0 ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_588]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_5843,plain,
% 23.84/3.50      ( ~ r1_tarski(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(X0,X1))
% 23.84/3.50      | r1_tarski(k5_relat_1(k1_xboole_0,sK0),k1_xboole_0)
% 23.84/3.50      | k5_relat_1(k1_xboole_0,sK0) != k5_relat_1(k1_xboole_0,sK0)
% 23.84/3.50      | k1_xboole_0 != k5_relat_1(X0,X1) ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_657]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_5854,plain,
% 23.84/3.50      ( ~ r1_tarski(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,k1_xboole_0))
% 23.84/3.50      | r1_tarski(k5_relat_1(k1_xboole_0,sK0),k1_xboole_0)
% 23.84/3.50      | k5_relat_1(k1_xboole_0,sK0) != k5_relat_1(k1_xboole_0,sK0)
% 23.84/3.50      | k1_xboole_0 != k5_relat_1(k1_xboole_0,k1_xboole_0) ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_5843]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_4243,plain,
% 23.84/3.50      ( ~ v1_relat_1(X0)
% 23.84/3.50      | ~ v1_relat_1(k4_relat_1(sK0))
% 23.84/3.50      | k5_relat_1(k4_relat_1(X0),k4_relat_1(k4_relat_1(sK0))) = k4_relat_1(k5_relat_1(k4_relat_1(sK0),X0)) ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_12]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_4246,plain,
% 23.84/3.50      ( ~ v1_relat_1(k4_relat_1(sK0))
% 23.84/3.50      | ~ v1_relat_1(k1_xboole_0)
% 23.84/3.50      | k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(k4_relat_1(sK0))) = k4_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_4243]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_3625,plain,
% 23.84/3.50      ( k5_relat_1(X0,X1) != X2
% 23.84/3.50      | k4_relat_1(k5_relat_1(X0,X1)) = k4_relat_1(X2) ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_204]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_3627,plain,
% 23.84/3.50      ( k5_relat_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 23.84/3.50      | k4_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0)) = k4_relat_1(k1_xboole_0) ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_3625]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_1568,plain,
% 23.84/3.50      ( k2_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0)) = k1_xboole_0
% 23.84/3.50      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_1562]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_1297,plain,
% 23.84/3.50      ( k5_relat_1(k1_xboole_0,k1_xboole_0) != k5_relat_1(k1_xboole_0,k1_xboole_0)
% 23.84/3.50      | k5_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0
% 23.84/3.50      | k1_xboole_0 != k5_relat_1(k1_xboole_0,k1_xboole_0) ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_1295]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_201,plain,
% 23.84/3.50      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 23.84/3.50      theory(equality) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_1265,plain,
% 23.84/3.50      ( ~ v1_xboole_0(X0)
% 23.84/3.50      | v1_xboole_0(k2_relat_1(k5_relat_1(X1,X2)))
% 23.84/3.50      | k2_relat_1(k5_relat_1(X1,X2)) != X0 ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_201]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_1267,plain,
% 23.84/3.50      ( v1_xboole_0(k2_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0)))
% 23.84/3.50      | ~ v1_xboole_0(k1_xboole_0)
% 23.84/3.50      | k2_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0)) != k1_xboole_0 ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_1265]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_913,plain,
% 23.84/3.50      ( ~ v1_relat_1(sK0) | k4_relat_1(k4_relat_1(sK0)) = sK0 ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_10]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_788,plain,
% 23.84/3.50      ( ~ v1_relat_1(k5_relat_1(X0,X1))
% 23.84/3.50      | v1_xboole_0(k5_relat_1(X0,X1))
% 23.84/3.50      | ~ v1_xboole_0(k2_relat_1(k5_relat_1(X0,X1))) ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_9]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_790,plain,
% 23.84/3.50      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0))
% 23.84/3.50      | v1_xboole_0(k5_relat_1(k1_xboole_0,k1_xboole_0))
% 23.84/3.50      | ~ v1_xboole_0(k2_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0))) ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_788]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_670,plain,
% 23.84/3.50      ( ~ v1_xboole_0(k5_relat_1(X0,X1))
% 23.84/3.50      | k1_xboole_0 = k5_relat_1(X0,X1) ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_1]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_672,plain,
% 23.84/3.50      ( ~ v1_xboole_0(k5_relat_1(k1_xboole_0,k1_xboole_0))
% 23.84/3.50      | k1_xboole_0 = k5_relat_1(k1_xboole_0,k1_xboole_0) ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_670]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_648,plain,
% 23.84/3.50      ( r1_tarski(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0)) ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_4]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_593,plain,
% 23.84/3.50      ( ~ r1_tarski(X0,k5_relat_1(k1_xboole_0,sK0))
% 23.84/3.50      | ~ r1_tarski(k5_relat_1(k1_xboole_0,sK0),X0)
% 23.84/3.50      | k5_relat_1(k1_xboole_0,sK0) = X0 ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_2]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_647,plain,
% 23.84/3.50      ( ~ r1_tarski(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0))
% 23.84/3.50      | k5_relat_1(k1_xboole_0,sK0) = k5_relat_1(k1_xboole_0,sK0) ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_593]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_15,negated_conjecture,
% 23.84/3.50      ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
% 23.84/3.50      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
% 23.84/3.50      inference(cnf_transformation,[],[f46]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_626,plain,
% 23.84/3.50      ( ~ v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))
% 23.84/3.50      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
% 23.84/3.50      inference(resolution,[status(thm)],[c_1,c_15]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_627,plain,
% 23.84/3.50      ( k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)
% 23.84/3.50      | v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) != iProver_top ),
% 23.84/3.50      inference(predicate_to_equality,[status(thm)],[c_626]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_595,plain,
% 23.84/3.50      ( ~ r1_tarski(k5_relat_1(k1_xboole_0,sK0),k1_xboole_0)
% 23.84/3.50      | ~ r1_tarski(k1_xboole_0,k5_relat_1(k1_xboole_0,sK0))
% 23.84/3.50      | k5_relat_1(k1_xboole_0,sK0) = k1_xboole_0 ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_593]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_578,plain,
% 23.84/3.50      ( k5_relat_1(k1_xboole_0,sK0) != X0
% 23.84/3.50      | k1_xboole_0 != X0
% 23.84/3.50      | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_200]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_579,plain,
% 23.84/3.50      ( k5_relat_1(k1_xboole_0,sK0) != k1_xboole_0
% 23.84/3.50      | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)
% 23.84/3.50      | k1_xboole_0 != k1_xboole_0 ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_578]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_212,plain,
% 23.84/3.50      ( k5_relat_1(k1_xboole_0,k1_xboole_0) = k5_relat_1(k1_xboole_0,k1_xboole_0)
% 23.84/3.50      | k1_xboole_0 != k1_xboole_0 ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_205]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_45,plain,
% 23.84/3.50      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 23.84/3.50      | k1_xboole_0 = k1_xboole_0 ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_2]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_40,plain,
% 23.84/3.50      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_5]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_37,plain,
% 23.84/3.50      ( v1_relat_1(k1_xboole_0) | ~ v1_xboole_0(k1_xboole_0) ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_6]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_31,plain,
% 23.84/3.50      ( v1_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0))
% 23.84/3.50      | ~ v1_relat_1(k1_xboole_0) ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_8]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_19,plain,
% 23.84/3.50      ( ~ v1_relat_1(k1_xboole_0)
% 23.84/3.50      | k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0)) = k4_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0)) ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_12]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(contradiction,plain,
% 23.84/3.50      ( $false ),
% 23.84/3.50      inference(minisat,
% 23.84/3.50                [status(thm)],
% 23.84/3.50                [c_114403,c_100772,c_90147,c_81725,c_46728,c_36862,
% 23.84/3.50                 c_22536,c_21527,c_21515,c_21514,c_21342,c_19305,c_18376,
% 23.84/3.50                 c_15381,c_10544,c_10356,c_10300,c_10232,c_8513,c_7661,
% 23.84/3.50                 c_5854,c_4246,c_3627,c_1568,c_1297,c_1267,c_913,c_790,
% 23.84/3.50                 c_672,c_648,c_647,c_627,c_595,c_579,c_212,c_50,c_0,c_45,
% 23.84/3.50                 c_40,c_38,c_37,c_31,c_19,c_17,c_16]) ).
% 23.84/3.50  
% 23.84/3.50  
% 23.84/3.50  % SZS output end CNFRefutation for theBenchmark.p
% 23.84/3.50  
% 23.84/3.50  ------                               Statistics
% 23.84/3.50  
% 23.84/3.50  ------ Selected
% 23.84/3.50  
% 23.84/3.50  total_time:                             2.861
% 23.84/3.50  
%------------------------------------------------------------------------------
