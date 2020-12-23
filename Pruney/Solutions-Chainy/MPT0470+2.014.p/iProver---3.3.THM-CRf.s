%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:43:57 EST 2020

% Result     : Theorem 27.81s
% Output     : CNFRefutation 27.81s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 610 expanded)
%              Number of clauses        :   95 ( 306 expanded)
%              Number of leaves         :   18 ( 114 expanded)
%              Depth                    :   20
%              Number of atoms          :  307 (1298 expanded)
%              Number of equality atoms :  187 ( 580 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f12,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
     => ~ v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f13,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

cnf(c_1066,plain,
    ( k5_relat_1(k4_relat_1(k4_relat_1(X0)),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,k4_relat_1(X0)))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_436,c_431])).

cnf(c_1945,plain,
    ( k5_relat_1(k4_relat_1(k4_relat_1(k1_xboole_0)),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,k4_relat_1(k1_xboole_0)))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_811,c_1066])).

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

cnf(c_1948,plain,
    ( k4_relat_1(k5_relat_1(X0,k4_relat_1(k1_xboole_0))) = k5_relat_1(k1_xboole_0,k4_relat_1(X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1945,c_1365])).

cnf(c_8313,plain,
    ( k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(k1_xboole_0))) = k5_relat_1(k1_xboole_0,k4_relat_1(k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_811,c_1948])).

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

cnf(c_14,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_11,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_432,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_936,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_14,c_432])).

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
    | r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_936,c_38,c_50])).

cnf(c_1354,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0) = iProver_top
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
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1354,c_1187])).

cnf(c_5327,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(X0))) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_436,c_1562])).

cnf(c_5552,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(k1_xboole_0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_811,c_5327])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_434,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k1_relat_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_82327,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(k1_xboole_0))) != iProver_top
    | v1_xboole_0(k5_relat_1(k1_xboole_0,k4_relat_1(k1_xboole_0))) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5552,c_434])).

cnf(c_82372,plain,
    ( v1_xboole_0(k5_relat_1(k1_xboole_0,k4_relat_1(k1_xboole_0))) = iProver_top
    | v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(k1_xboole_0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_82327,c_50])).

cnf(c_82373,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(k1_xboole_0))) != iProver_top
    | v1_xboole_0(k5_relat_1(k1_xboole_0,k4_relat_1(k1_xboole_0))) = iProver_top ),
    inference(renaming,[status(thm)],[c_82372])).

cnf(c_82378,plain,
    ( v1_relat_1(k4_relat_1(k1_xboole_0)) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top
    | v1_xboole_0(k5_relat_1(k1_xboole_0,k4_relat_1(k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_435,c_82373])).

cnf(c_33,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_35,plain,
    ( v1_relat_1(k4_relat_1(k1_xboole_0)) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_82919,plain,
    ( v1_xboole_0(k5_relat_1(k1_xboole_0,k4_relat_1(k1_xboole_0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_82378,c_35,c_38,c_50])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_441,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_82925,plain,
    ( k5_relat_1(k1_xboole_0,k4_relat_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_82919,c_441])).

cnf(c_132029,plain,
    ( k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_8313,c_82925])).

cnf(c_16,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_430,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1366,plain,
    ( k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,k1_xboole_0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_811,c_431])).

cnf(c_2166,plain,
    ( k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(sK0)) = k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_430,c_1366])).

cnf(c_132071,plain,
    ( k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) = k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(demodulation,[status(thm)],[c_132029,c_2166])).

cnf(c_5551,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_430,c_5327])).

cnf(c_5741,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) != iProver_top
    | v1_xboole_0(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5551,c_434])).

cnf(c_17,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_8312,plain,
    ( k4_relat_1(k5_relat_1(sK0,k4_relat_1(k1_xboole_0))) = k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) ),
    inference(superposition,[status(thm)],[c_430,c_1948])).

cnf(c_8506,plain,
    ( v1_relat_1(k5_relat_1(sK0,k4_relat_1(k1_xboole_0))) != iProver_top
    | v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_8312,c_436])).

cnf(c_8759,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) = iProver_top
    | v1_relat_1(k4_relat_1(k1_xboole_0)) != iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_435,c_8506])).

cnf(c_16643,plain,
    ( v1_xboole_0(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5741,c_17,c_35,c_38,c_50,c_8759])).

cnf(c_16649,plain,
    ( k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_16643,c_441])).

cnf(c_132079,plain,
    ( k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_132071,c_16649])).

cnf(c_204,plain,
    ( X0 != X1
    | k4_relat_1(X0) = k4_relat_1(X1) ),
    theory(equality)).

cnf(c_126974,plain,
    ( k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) != X0
    | k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = k4_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_204])).

cnf(c_126976,plain,
    ( k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) != k1_xboole_0
    | k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = k4_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_126974])).

cnf(c_200,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_126224,plain,
    ( k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_200])).

cnf(c_126973,plain,
    ( k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) != k4_relat_1(X0)
    | k1_xboole_0 != k4_relat_1(X0)
    | k1_xboole_0 = k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_126224])).

cnf(c_126975,plain,
    ( k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) != k4_relat_1(k1_xboole_0)
    | k1_xboole_0 = k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | k1_xboole_0 != k4_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_126973])).

cnf(c_125105,plain,
    ( k5_relat_1(sK0,k1_xboole_0) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_200])).

cnf(c_125997,plain,
    ( k5_relat_1(sK0,k1_xboole_0) != k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_125105])).

cnf(c_879,plain,
    ( X0 != X1
    | k5_relat_1(X2,X3) != X1
    | k5_relat_1(X2,X3) = X0 ),
    inference(instantiation,[status(thm)],[c_200])).

cnf(c_1295,plain,
    ( X0 != k5_relat_1(X1,X2)
    | k5_relat_1(X1,X2) = X0
    | k5_relat_1(X1,X2) != k5_relat_1(X1,X2) ),
    inference(instantiation,[status(thm)],[c_879])).

cnf(c_10768,plain,
    ( X0 != k5_relat_1(sK0,k1_xboole_0)
    | k5_relat_1(sK0,k1_xboole_0) = X0
    | k5_relat_1(sK0,k1_xboole_0) != k5_relat_1(sK0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1295])).

cnf(c_67608,plain,
    ( k5_relat_1(sK0,k1_xboole_0) != k5_relat_1(sK0,k1_xboole_0)
    | k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) != k5_relat_1(sK0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_10768])).

cnf(c_199,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1296,plain,
    ( k5_relat_1(X0,X1) = k5_relat_1(X0,X1) ),
    inference(instantiation,[status(thm)],[c_199])).

cnf(c_26476,plain,
    ( k5_relat_1(sK0,k1_xboole_0) = k5_relat_1(sK0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1296])).

cnf(c_5329,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_430,c_1562])).

cnf(c_4088,plain,
    ( k4_relat_1(X0) != X1
    | k1_xboole_0 != X1
    | k1_xboole_0 = k4_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_200])).

cnf(c_4089,plain,
    ( k4_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k4_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4088])).

cnf(c_1209,plain,
    ( k4_relat_1(k4_relat_1(k5_relat_1(X0,X1))) = k5_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_435,c_433])).

cnf(c_2870,plain,
    ( k4_relat_1(k4_relat_1(k5_relat_1(sK0,X0))) = k5_relat_1(sK0,X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_430,c_1209])).

cnf(c_2908,plain,
    ( k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = k5_relat_1(sK0,k1_xboole_0)
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2870])).

cnf(c_998,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_201,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_637,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)))
    | k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) != X0 ),
    inference(instantiation,[status(thm)],[c_201])).

cnf(c_639,plain,
    ( v1_xboole_0(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)))
    | ~ v1_xboole_0(k1_xboole_0)
    | k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_637])).

cnf(c_580,plain,
    ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))
    | ~ v1_xboole_0(k1_relat_1(k5_relat_1(k1_xboole_0,sK0))) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_546,plain,
    ( ~ v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))
    | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
    inference(instantiation,[status(thm)],[c_1])).

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

cnf(c_15,negated_conjecture,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f46])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_132079,c_132029,c_126976,c_126975,c_125997,c_67608,c_26476,c_5329,c_4089,c_2908,c_998,c_639,c_580,c_546,c_50,c_0,c_45,c_40,c_38,c_37,c_15,c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:20:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 27.81/3.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.81/3.99  
% 27.81/3.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.81/3.99  
% 27.81/3.99  ------  iProver source info
% 27.81/3.99  
% 27.81/3.99  git: date: 2020-06-30 10:37:57 +0100
% 27.81/3.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.81/3.99  git: non_committed_changes: false
% 27.81/3.99  git: last_make_outside_of_git: false
% 27.81/3.99  
% 27.81/3.99  ------ 
% 27.81/3.99  
% 27.81/3.99  ------ Input Options
% 27.81/3.99  
% 27.81/3.99  --out_options                           all
% 27.81/3.99  --tptp_safe_out                         true
% 27.81/3.99  --problem_path                          ""
% 27.81/3.99  --include_path                          ""
% 27.81/3.99  --clausifier                            res/vclausify_rel
% 27.81/3.99  --clausifier_options                    --mode clausify
% 27.81/3.99  --stdin                                 false
% 27.81/3.99  --stats_out                             sel
% 27.81/3.99  
% 27.81/3.99  ------ General Options
% 27.81/3.99  
% 27.81/3.99  --fof                                   false
% 27.81/3.99  --time_out_real                         604.99
% 27.81/3.99  --time_out_virtual                      -1.
% 27.81/3.99  --symbol_type_check                     false
% 27.81/3.99  --clausify_out                          false
% 27.81/3.99  --sig_cnt_out                           false
% 27.81/3.99  --trig_cnt_out                          false
% 27.81/3.99  --trig_cnt_out_tolerance                1.
% 27.81/3.99  --trig_cnt_out_sk_spl                   false
% 27.81/3.99  --abstr_cl_out                          false
% 27.81/3.99  
% 27.81/3.99  ------ Global Options
% 27.81/3.99  
% 27.81/3.99  --schedule                              none
% 27.81/3.99  --add_important_lit                     false
% 27.81/3.99  --prop_solver_per_cl                    1000
% 27.81/3.99  --min_unsat_core                        false
% 27.81/3.99  --soft_assumptions                      false
% 27.81/3.99  --soft_lemma_size                       3
% 27.81/3.99  --prop_impl_unit_size                   0
% 27.81/3.99  --prop_impl_unit                        []
% 27.81/3.99  --share_sel_clauses                     true
% 27.81/3.99  --reset_solvers                         false
% 27.81/3.99  --bc_imp_inh                            [conj_cone]
% 27.81/3.99  --conj_cone_tolerance                   3.
% 27.81/3.99  --extra_neg_conj                        none
% 27.81/3.99  --large_theory_mode                     true
% 27.81/3.99  --prolific_symb_bound                   200
% 27.81/3.99  --lt_threshold                          2000
% 27.81/3.99  --clause_weak_htbl                      true
% 27.81/3.99  --gc_record_bc_elim                     false
% 27.81/3.99  
% 27.81/3.99  ------ Preprocessing Options
% 27.81/3.99  
% 27.81/3.99  --preprocessing_flag                    true
% 27.81/3.99  --time_out_prep_mult                    0.1
% 27.81/3.99  --splitting_mode                        input
% 27.81/3.99  --splitting_grd                         true
% 27.81/3.99  --splitting_cvd                         false
% 27.81/3.99  --splitting_cvd_svl                     false
% 27.81/3.99  --splitting_nvd                         32
% 27.81/3.99  --sub_typing                            true
% 27.81/3.99  --prep_gs_sim                           false
% 27.81/3.99  --prep_unflatten                        true
% 27.81/3.99  --prep_res_sim                          true
% 27.81/3.99  --prep_upred                            true
% 27.81/3.99  --prep_sem_filter                       exhaustive
% 27.81/3.99  --prep_sem_filter_out                   false
% 27.81/3.99  --pred_elim                             false
% 27.81/3.99  --res_sim_input                         true
% 27.81/3.99  --eq_ax_congr_red                       true
% 27.81/3.99  --pure_diseq_elim                       true
% 27.81/3.99  --brand_transform                       false
% 27.81/3.99  --non_eq_to_eq                          false
% 27.81/3.99  --prep_def_merge                        true
% 27.81/3.99  --prep_def_merge_prop_impl              false
% 27.81/3.99  --prep_def_merge_mbd                    true
% 27.81/3.99  --prep_def_merge_tr_red                 false
% 27.81/3.99  --prep_def_merge_tr_cl                  false
% 27.81/3.99  --smt_preprocessing                     true
% 27.81/3.99  --smt_ac_axioms                         fast
% 27.81/3.99  --preprocessed_out                      false
% 27.81/3.99  --preprocessed_stats                    false
% 27.81/3.99  
% 27.81/3.99  ------ Abstraction refinement Options
% 27.81/3.99  
% 27.81/3.99  --abstr_ref                             []
% 27.81/3.99  --abstr_ref_prep                        false
% 27.81/3.99  --abstr_ref_until_sat                   false
% 27.81/3.99  --abstr_ref_sig_restrict                funpre
% 27.81/3.99  --abstr_ref_af_restrict_to_split_sk     false
% 27.81/3.99  --abstr_ref_under                       []
% 27.81/3.99  
% 27.81/3.99  ------ SAT Options
% 27.81/3.99  
% 27.81/3.99  --sat_mode                              false
% 27.81/3.99  --sat_fm_restart_options                ""
% 27.81/3.99  --sat_gr_def                            false
% 27.81/3.99  --sat_epr_types                         true
% 27.81/3.99  --sat_non_cyclic_types                  false
% 27.81/3.99  --sat_finite_models                     false
% 27.81/3.99  --sat_fm_lemmas                         false
% 27.81/3.99  --sat_fm_prep                           false
% 27.81/3.99  --sat_fm_uc_incr                        true
% 27.81/3.99  --sat_out_model                         small
% 27.81/3.99  --sat_out_clauses                       false
% 27.81/3.99  
% 27.81/3.99  ------ QBF Options
% 27.81/3.99  
% 27.81/3.99  --qbf_mode                              false
% 27.81/3.99  --qbf_elim_univ                         false
% 27.81/3.99  --qbf_dom_inst                          none
% 27.81/3.99  --qbf_dom_pre_inst                      false
% 27.81/3.99  --qbf_sk_in                             false
% 27.81/3.99  --qbf_pred_elim                         true
% 27.81/3.99  --qbf_split                             512
% 27.81/3.99  
% 27.81/3.99  ------ BMC1 Options
% 27.81/3.99  
% 27.81/3.99  --bmc1_incremental                      false
% 27.81/3.99  --bmc1_axioms                           reachable_all
% 27.81/3.99  --bmc1_min_bound                        0
% 27.81/3.99  --bmc1_max_bound                        -1
% 27.81/3.99  --bmc1_max_bound_default                -1
% 27.81/3.99  --bmc1_symbol_reachability              true
% 27.81/3.99  --bmc1_property_lemmas                  false
% 27.81/3.99  --bmc1_k_induction                      false
% 27.81/3.99  --bmc1_non_equiv_states                 false
% 27.81/3.99  --bmc1_deadlock                         false
% 27.81/3.99  --bmc1_ucm                              false
% 27.81/3.99  --bmc1_add_unsat_core                   none
% 27.81/3.99  --bmc1_unsat_core_children              false
% 27.81/3.99  --bmc1_unsat_core_extrapolate_axioms    false
% 27.81/3.99  --bmc1_out_stat                         full
% 27.81/3.99  --bmc1_ground_init                      false
% 27.81/3.99  --bmc1_pre_inst_next_state              false
% 27.81/3.99  --bmc1_pre_inst_state                   false
% 27.81/3.99  --bmc1_pre_inst_reach_state             false
% 27.81/3.99  --bmc1_out_unsat_core                   false
% 27.81/3.99  --bmc1_aig_witness_out                  false
% 27.81/3.99  --bmc1_verbose                          false
% 27.81/3.99  --bmc1_dump_clauses_tptp                false
% 27.81/3.99  --bmc1_dump_unsat_core_tptp             false
% 27.81/3.99  --bmc1_dump_file                        -
% 27.81/3.99  --bmc1_ucm_expand_uc_limit              128
% 27.81/3.99  --bmc1_ucm_n_expand_iterations          6
% 27.81/3.99  --bmc1_ucm_extend_mode                  1
% 27.81/3.99  --bmc1_ucm_init_mode                    2
% 27.81/3.99  --bmc1_ucm_cone_mode                    none
% 27.81/3.99  --bmc1_ucm_reduced_relation_type        0
% 27.81/3.99  --bmc1_ucm_relax_model                  4
% 27.81/3.99  --bmc1_ucm_full_tr_after_sat            true
% 27.81/3.99  --bmc1_ucm_expand_neg_assumptions       false
% 27.81/3.99  --bmc1_ucm_layered_model                none
% 27.81/3.99  --bmc1_ucm_max_lemma_size               10
% 27.81/3.99  
% 27.81/3.99  ------ AIG Options
% 27.81/3.99  
% 27.81/3.99  --aig_mode                              false
% 27.81/3.99  
% 27.81/3.99  ------ Instantiation Options
% 27.81/3.99  
% 27.81/3.99  --instantiation_flag                    true
% 27.81/3.99  --inst_sos_flag                         false
% 27.81/3.99  --inst_sos_phase                        true
% 27.81/3.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.81/3.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.81/3.99  --inst_lit_sel_side                     num_symb
% 27.81/3.99  --inst_solver_per_active                1400
% 27.81/3.99  --inst_solver_calls_frac                1.
% 27.81/3.99  --inst_passive_queue_type               priority_queues
% 27.81/3.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.81/3.99  --inst_passive_queues_freq              [25;2]
% 27.81/3.99  --inst_dismatching                      true
% 27.81/3.99  --inst_eager_unprocessed_to_passive     true
% 27.81/3.99  --inst_prop_sim_given                   true
% 27.81/3.99  --inst_prop_sim_new                     false
% 27.81/3.99  --inst_subs_new                         false
% 27.81/3.99  --inst_eq_res_simp                      false
% 27.81/3.99  --inst_subs_given                       false
% 27.81/3.99  --inst_orphan_elimination               true
% 27.81/3.99  --inst_learning_loop_flag               true
% 27.81/3.99  --inst_learning_start                   3000
% 27.81/3.99  --inst_learning_factor                  2
% 27.81/3.99  --inst_start_prop_sim_after_learn       3
% 27.81/3.99  --inst_sel_renew                        solver
% 27.81/3.99  --inst_lit_activity_flag                true
% 27.81/3.99  --inst_restr_to_given                   false
% 27.81/3.99  --inst_activity_threshold               500
% 27.81/3.99  --inst_out_proof                        true
% 27.81/3.99  
% 27.81/3.99  ------ Resolution Options
% 27.81/3.99  
% 27.81/3.99  --resolution_flag                       true
% 27.81/3.99  --res_lit_sel                           adaptive
% 27.81/3.99  --res_lit_sel_side                      none
% 27.81/3.99  --res_ordering                          kbo
% 27.81/3.99  --res_to_prop_solver                    active
% 27.81/3.99  --res_prop_simpl_new                    false
% 27.81/3.99  --res_prop_simpl_given                  true
% 27.81/3.99  --res_passive_queue_type                priority_queues
% 27.81/3.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.81/3.99  --res_passive_queues_freq               [15;5]
% 27.81/3.99  --res_forward_subs                      full
% 27.81/3.99  --res_backward_subs                     full
% 27.81/3.99  --res_forward_subs_resolution           true
% 27.81/3.99  --res_backward_subs_resolution          true
% 27.81/3.99  --res_orphan_elimination                true
% 27.81/3.99  --res_time_limit                        2.
% 27.81/3.99  --res_out_proof                         true
% 27.81/3.99  
% 27.81/3.99  ------ Superposition Options
% 27.81/3.99  
% 27.81/3.99  --superposition_flag                    true
% 27.81/3.99  --sup_passive_queue_type                priority_queues
% 27.81/3.99  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.81/3.99  --sup_passive_queues_freq               [1;4]
% 27.81/3.99  --demod_completeness_check              fast
% 27.81/3.99  --demod_use_ground                      true
% 27.81/3.99  --sup_to_prop_solver                    passive
% 27.81/3.99  --sup_prop_simpl_new                    true
% 27.81/3.99  --sup_prop_simpl_given                  true
% 27.81/3.99  --sup_fun_splitting                     false
% 27.81/3.99  --sup_smt_interval                      50000
% 27.81/3.99  
% 27.81/3.99  ------ Superposition Simplification Setup
% 27.81/3.99  
% 27.81/3.99  --sup_indices_passive                   []
% 27.81/3.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.81/3.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.81/3.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.81/3.99  --sup_full_triv                         [TrivRules;PropSubs]
% 27.81/3.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.81/3.99  --sup_full_bw                           [BwDemod]
% 27.81/3.99  --sup_immed_triv                        [TrivRules]
% 27.81/3.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.81/3.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.81/3.99  --sup_immed_bw_main                     []
% 27.81/3.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.81/3.99  --sup_input_triv                        [Unflattening;TrivRules]
% 27.81/3.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.81/3.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.81/3.99  
% 27.81/3.99  ------ Combination Options
% 27.81/3.99  
% 27.81/3.99  --comb_res_mult                         3
% 27.81/3.99  --comb_sup_mult                         2
% 27.81/3.99  --comb_inst_mult                        10
% 27.81/3.99  
% 27.81/3.99  ------ Debug Options
% 27.81/3.99  
% 27.81/3.99  --dbg_backtrace                         false
% 27.81/3.99  --dbg_dump_prop_clauses                 false
% 27.81/3.99  --dbg_dump_prop_clauses_file            -
% 27.81/3.99  --dbg_out_stat                          false
% 27.81/3.99  ------ Parsing...
% 27.81/3.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.81/3.99  
% 27.81/3.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 27.81/3.99  
% 27.81/3.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.81/3.99  
% 27.81/3.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.81/3.99  ------ Proving...
% 27.81/3.99  ------ Problem Properties 
% 27.81/3.99  
% 27.81/3.99  
% 27.81/3.99  clauses                                 16
% 27.81/3.99  conjectures                             2
% 27.81/3.99  EPR                                     7
% 27.81/3.99  Horn                                    16
% 27.81/3.99  unary                                   6
% 27.81/3.99  binary                                  5
% 27.81/3.99  lits                                    31
% 27.81/3.99  lits eq                                 8
% 27.81/3.99  fd_pure                                 0
% 27.81/3.99  fd_pseudo                               0
% 27.81/3.99  fd_cond                                 1
% 27.81/3.99  fd_pseudo_cond                          1
% 27.81/3.99  AC symbols                              0
% 27.81/3.99  
% 27.81/3.99  ------ Input Options Time Limit: Unbounded
% 27.81/3.99  
% 27.81/3.99  
% 27.81/3.99  ------ 
% 27.81/3.99  Current options:
% 27.81/3.99  ------ 
% 27.81/3.99  
% 27.81/3.99  ------ Input Options
% 27.81/3.99  
% 27.81/3.99  --out_options                           all
% 27.81/3.99  --tptp_safe_out                         true
% 27.81/3.99  --problem_path                          ""
% 27.81/3.99  --include_path                          ""
% 27.81/3.99  --clausifier                            res/vclausify_rel
% 27.81/3.99  --clausifier_options                    --mode clausify
% 27.81/3.99  --stdin                                 false
% 27.81/3.99  --stats_out                             sel
% 27.81/3.99  
% 27.81/3.99  ------ General Options
% 27.81/3.99  
% 27.81/3.99  --fof                                   false
% 27.81/3.99  --time_out_real                         604.99
% 27.81/3.99  --time_out_virtual                      -1.
% 27.81/3.99  --symbol_type_check                     false
% 27.81/3.99  --clausify_out                          false
% 27.81/3.99  --sig_cnt_out                           false
% 27.81/3.99  --trig_cnt_out                          false
% 27.81/3.99  --trig_cnt_out_tolerance                1.
% 27.81/3.99  --trig_cnt_out_sk_spl                   false
% 27.81/3.99  --abstr_cl_out                          false
% 27.81/3.99  
% 27.81/3.99  ------ Global Options
% 27.81/3.99  
% 27.81/3.99  --schedule                              none
% 27.81/3.99  --add_important_lit                     false
% 27.81/3.99  --prop_solver_per_cl                    1000
% 27.81/3.99  --min_unsat_core                        false
% 27.81/3.99  --soft_assumptions                      false
% 27.81/3.99  --soft_lemma_size                       3
% 27.81/3.99  --prop_impl_unit_size                   0
% 27.81/3.99  --prop_impl_unit                        []
% 27.81/3.99  --share_sel_clauses                     true
% 27.81/3.99  --reset_solvers                         false
% 27.81/3.99  --bc_imp_inh                            [conj_cone]
% 27.81/3.99  --conj_cone_tolerance                   3.
% 27.81/3.99  --extra_neg_conj                        none
% 27.81/3.99  --large_theory_mode                     true
% 27.81/3.99  --prolific_symb_bound                   200
% 27.81/3.99  --lt_threshold                          2000
% 27.81/3.99  --clause_weak_htbl                      true
% 27.81/3.99  --gc_record_bc_elim                     false
% 27.81/3.99  
% 27.81/3.99  ------ Preprocessing Options
% 27.81/3.99  
% 27.81/3.99  --preprocessing_flag                    true
% 27.81/3.99  --time_out_prep_mult                    0.1
% 27.81/3.99  --splitting_mode                        input
% 27.81/3.99  --splitting_grd                         true
% 27.81/3.99  --splitting_cvd                         false
% 27.81/3.99  --splitting_cvd_svl                     false
% 27.81/3.99  --splitting_nvd                         32
% 27.81/3.99  --sub_typing                            true
% 27.81/3.99  --prep_gs_sim                           false
% 27.81/3.99  --prep_unflatten                        true
% 27.81/3.99  --prep_res_sim                          true
% 27.81/3.99  --prep_upred                            true
% 27.81/3.99  --prep_sem_filter                       exhaustive
% 27.81/3.99  --prep_sem_filter_out                   false
% 27.81/3.99  --pred_elim                             false
% 27.81/3.99  --res_sim_input                         true
% 27.81/3.99  --eq_ax_congr_red                       true
% 27.81/3.99  --pure_diseq_elim                       true
% 27.81/3.99  --brand_transform                       false
% 27.81/3.99  --non_eq_to_eq                          false
% 27.81/3.99  --prep_def_merge                        true
% 27.81/3.99  --prep_def_merge_prop_impl              false
% 27.81/3.99  --prep_def_merge_mbd                    true
% 27.81/3.99  --prep_def_merge_tr_red                 false
% 27.81/3.99  --prep_def_merge_tr_cl                  false
% 27.81/3.99  --smt_preprocessing                     true
% 27.81/3.99  --smt_ac_axioms                         fast
% 27.81/3.99  --preprocessed_out                      false
% 27.81/3.99  --preprocessed_stats                    false
% 27.81/3.99  
% 27.81/3.99  ------ Abstraction refinement Options
% 27.81/3.99  
% 27.81/3.99  --abstr_ref                             []
% 27.81/3.99  --abstr_ref_prep                        false
% 27.81/3.99  --abstr_ref_until_sat                   false
% 27.81/3.99  --abstr_ref_sig_restrict                funpre
% 27.81/3.99  --abstr_ref_af_restrict_to_split_sk     false
% 27.81/3.99  --abstr_ref_under                       []
% 27.81/3.99  
% 27.81/3.99  ------ SAT Options
% 27.81/3.99  
% 27.81/3.99  --sat_mode                              false
% 27.81/3.99  --sat_fm_restart_options                ""
% 27.81/3.99  --sat_gr_def                            false
% 27.81/3.99  --sat_epr_types                         true
% 27.81/3.99  --sat_non_cyclic_types                  false
% 27.81/3.99  --sat_finite_models                     false
% 27.81/3.99  --sat_fm_lemmas                         false
% 27.81/3.99  --sat_fm_prep                           false
% 27.81/3.99  --sat_fm_uc_incr                        true
% 27.81/3.99  --sat_out_model                         small
% 27.81/3.99  --sat_out_clauses                       false
% 27.81/3.99  
% 27.81/3.99  ------ QBF Options
% 27.81/3.99  
% 27.81/3.99  --qbf_mode                              false
% 27.81/3.99  --qbf_elim_univ                         false
% 27.81/3.99  --qbf_dom_inst                          none
% 27.81/3.99  --qbf_dom_pre_inst                      false
% 27.81/3.99  --qbf_sk_in                             false
% 27.81/3.99  --qbf_pred_elim                         true
% 27.81/3.99  --qbf_split                             512
% 27.81/3.99  
% 27.81/3.99  ------ BMC1 Options
% 27.81/3.99  
% 27.81/3.99  --bmc1_incremental                      false
% 27.81/3.99  --bmc1_axioms                           reachable_all
% 27.81/3.99  --bmc1_min_bound                        0
% 27.81/3.99  --bmc1_max_bound                        -1
% 27.81/3.99  --bmc1_max_bound_default                -1
% 27.81/3.99  --bmc1_symbol_reachability              true
% 27.81/3.99  --bmc1_property_lemmas                  false
% 27.81/3.99  --bmc1_k_induction                      false
% 27.81/3.99  --bmc1_non_equiv_states                 false
% 27.81/3.99  --bmc1_deadlock                         false
% 27.81/3.99  --bmc1_ucm                              false
% 27.81/3.99  --bmc1_add_unsat_core                   none
% 27.81/3.99  --bmc1_unsat_core_children              false
% 27.81/3.99  --bmc1_unsat_core_extrapolate_axioms    false
% 27.81/3.99  --bmc1_out_stat                         full
% 27.81/3.99  --bmc1_ground_init                      false
% 27.81/3.99  --bmc1_pre_inst_next_state              false
% 27.81/3.99  --bmc1_pre_inst_state                   false
% 27.81/3.99  --bmc1_pre_inst_reach_state             false
% 27.81/3.99  --bmc1_out_unsat_core                   false
% 27.81/3.99  --bmc1_aig_witness_out                  false
% 27.81/3.99  --bmc1_verbose                          false
% 27.81/3.99  --bmc1_dump_clauses_tptp                false
% 27.81/3.99  --bmc1_dump_unsat_core_tptp             false
% 27.81/3.99  --bmc1_dump_file                        -
% 27.81/3.99  --bmc1_ucm_expand_uc_limit              128
% 27.81/3.99  --bmc1_ucm_n_expand_iterations          6
% 27.81/3.99  --bmc1_ucm_extend_mode                  1
% 27.81/3.99  --bmc1_ucm_init_mode                    2
% 27.81/3.99  --bmc1_ucm_cone_mode                    none
% 27.81/3.99  --bmc1_ucm_reduced_relation_type        0
% 27.81/3.99  --bmc1_ucm_relax_model                  4
% 27.81/3.99  --bmc1_ucm_full_tr_after_sat            true
% 27.81/3.99  --bmc1_ucm_expand_neg_assumptions       false
% 27.81/3.99  --bmc1_ucm_layered_model                none
% 27.81/3.99  --bmc1_ucm_max_lemma_size               10
% 27.81/3.99  
% 27.81/3.99  ------ AIG Options
% 27.81/3.99  
% 27.81/3.99  --aig_mode                              false
% 27.81/3.99  
% 27.81/3.99  ------ Instantiation Options
% 27.81/3.99  
% 27.81/3.99  --instantiation_flag                    true
% 27.81/3.99  --inst_sos_flag                         false
% 27.81/3.99  --inst_sos_phase                        true
% 27.81/3.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.81/3.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.81/3.99  --inst_lit_sel_side                     num_symb
% 27.81/3.99  --inst_solver_per_active                1400
% 27.81/3.99  --inst_solver_calls_frac                1.
% 27.81/3.99  --inst_passive_queue_type               priority_queues
% 27.81/3.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.81/3.99  --inst_passive_queues_freq              [25;2]
% 27.81/3.99  --inst_dismatching                      true
% 27.81/3.99  --inst_eager_unprocessed_to_passive     true
% 27.81/3.99  --inst_prop_sim_given                   true
% 27.81/3.99  --inst_prop_sim_new                     false
% 27.81/3.99  --inst_subs_new                         false
% 27.81/3.99  --inst_eq_res_simp                      false
% 27.81/3.99  --inst_subs_given                       false
% 27.81/3.99  --inst_orphan_elimination               true
% 27.81/3.99  --inst_learning_loop_flag               true
% 27.81/3.99  --inst_learning_start                   3000
% 27.81/3.99  --inst_learning_factor                  2
% 27.81/3.99  --inst_start_prop_sim_after_learn       3
% 27.81/3.99  --inst_sel_renew                        solver
% 27.81/3.99  --inst_lit_activity_flag                true
% 27.81/3.99  --inst_restr_to_given                   false
% 27.81/3.99  --inst_activity_threshold               500
% 27.81/3.99  --inst_out_proof                        true
% 27.81/3.99  
% 27.81/3.99  ------ Resolution Options
% 27.81/3.99  
% 27.81/3.99  --resolution_flag                       true
% 27.81/3.99  --res_lit_sel                           adaptive
% 27.81/3.99  --res_lit_sel_side                      none
% 27.81/3.99  --res_ordering                          kbo
% 27.81/3.99  --res_to_prop_solver                    active
% 27.81/3.99  --res_prop_simpl_new                    false
% 27.81/3.99  --res_prop_simpl_given                  true
% 27.81/3.99  --res_passive_queue_type                priority_queues
% 27.81/3.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.81/3.99  --res_passive_queues_freq               [15;5]
% 27.81/3.99  --res_forward_subs                      full
% 27.81/3.99  --res_backward_subs                     full
% 27.81/3.99  --res_forward_subs_resolution           true
% 27.81/3.99  --res_backward_subs_resolution          true
% 27.81/3.99  --res_orphan_elimination                true
% 27.81/3.99  --res_time_limit                        2.
% 27.81/3.99  --res_out_proof                         true
% 27.81/3.99  
% 27.81/3.99  ------ Superposition Options
% 27.81/3.99  
% 27.81/3.99  --superposition_flag                    true
% 27.81/3.99  --sup_passive_queue_type                priority_queues
% 27.81/3.99  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.81/3.99  --sup_passive_queues_freq               [1;4]
% 27.81/3.99  --demod_completeness_check              fast
% 27.81/3.99  --demod_use_ground                      true
% 27.81/3.99  --sup_to_prop_solver                    passive
% 27.81/3.99  --sup_prop_simpl_new                    true
% 27.81/3.99  --sup_prop_simpl_given                  true
% 27.81/3.99  --sup_fun_splitting                     false
% 27.81/3.99  --sup_smt_interval                      50000
% 27.81/3.99  
% 27.81/3.99  ------ Superposition Simplification Setup
% 27.81/3.99  
% 27.81/3.99  --sup_indices_passive                   []
% 27.81/3.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.81/3.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.81/3.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.81/3.99  --sup_full_triv                         [TrivRules;PropSubs]
% 27.81/3.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.81/3.99  --sup_full_bw                           [BwDemod]
% 27.81/3.99  --sup_immed_triv                        [TrivRules]
% 27.81/3.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.81/3.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.81/3.99  --sup_immed_bw_main                     []
% 27.81/3.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.81/3.99  --sup_input_triv                        [Unflattening;TrivRules]
% 27.81/3.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.81/3.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.81/3.99  
% 27.81/3.99  ------ Combination Options
% 27.81/3.99  
% 27.81/3.99  --comb_res_mult                         3
% 27.81/3.99  --comb_sup_mult                         2
% 27.81/3.99  --comb_inst_mult                        10
% 27.81/3.99  
% 27.81/3.99  ------ Debug Options
% 27.81/3.99  
% 27.81/3.99  --dbg_backtrace                         false
% 27.81/3.99  --dbg_dump_prop_clauses                 false
% 27.81/3.99  --dbg_dump_prop_clauses_file            -
% 27.81/3.99  --dbg_out_stat                          false
% 27.81/3.99  
% 27.81/3.99  
% 27.81/3.99  
% 27.81/3.99  
% 27.81/3.99  ------ Proving...
% 27.81/3.99  
% 27.81/3.99  
% 27.81/3.99  % SZS status Theorem for theBenchmark.p
% 27.81/3.99  
% 27.81/3.99  % SZS output start CNFRefutation for theBenchmark.p
% 27.81/3.99  
% 27.81/3.99  fof(f1,axiom,(
% 27.81/3.99    v1_xboole_0(k1_xboole_0)),
% 27.81/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.81/3.99  
% 27.81/3.99  fof(f30,plain,(
% 27.81/3.99    v1_xboole_0(k1_xboole_0)),
% 27.81/3.99    inference(cnf_transformation,[],[f1])).
% 27.81/3.99  
% 27.81/3.99  fof(f5,axiom,(
% 27.81/3.99    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 27.81/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.81/3.99  
% 27.81/3.99  fof(f16,plain,(
% 27.81/3.99    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 27.81/3.99    inference(ennf_transformation,[],[f5])).
% 27.81/3.99  
% 27.81/3.99  fof(f36,plain,(
% 27.81/3.99    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 27.81/3.99    inference(cnf_transformation,[],[f16])).
% 27.81/3.99  
% 27.81/3.99  fof(f6,axiom,(
% 27.81/3.99    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 27.81/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.81/3.99  
% 27.81/3.99  fof(f17,plain,(
% 27.81/3.99    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 27.81/3.99    inference(ennf_transformation,[],[f6])).
% 27.81/3.99  
% 27.81/3.99  fof(f37,plain,(
% 27.81/3.99    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 27.81/3.99    inference(cnf_transformation,[],[f17])).
% 27.81/3.99  
% 27.81/3.99  fof(f11,axiom,(
% 27.81/3.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 27.81/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.81/3.99  
% 27.81/3.99  fof(f24,plain,(
% 27.81/3.99    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 27.81/3.99    inference(ennf_transformation,[],[f11])).
% 27.81/3.99  
% 27.81/3.99  fof(f42,plain,(
% 27.81/3.99    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 27.81/3.99    inference(cnf_transformation,[],[f24])).
% 27.81/3.99  
% 27.81/3.99  fof(f9,axiom,(
% 27.81/3.99    ! [X0] : (v1_relat_1(X0) => k4_relat_1(k4_relat_1(X0)) = X0)),
% 27.81/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.81/3.99  
% 27.81/3.99  fof(f22,plain,(
% 27.81/3.99    ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 27.81/3.99    inference(ennf_transformation,[],[f9])).
% 27.81/3.99  
% 27.81/3.99  fof(f40,plain,(
% 27.81/3.99    ( ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 27.81/3.99    inference(cnf_transformation,[],[f22])).
% 27.81/3.99  
% 27.81/3.99  fof(f7,axiom,(
% 27.81/3.99    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 27.81/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.81/3.99  
% 27.81/3.99  fof(f18,plain,(
% 27.81/3.99    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 27.81/3.99    inference(ennf_transformation,[],[f7])).
% 27.81/3.99  
% 27.81/3.99  fof(f19,plain,(
% 27.81/3.99    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 27.81/3.99    inference(flattening,[],[f18])).
% 27.81/3.99  
% 27.81/3.99  fof(f38,plain,(
% 27.81/3.99    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 27.81/3.99    inference(cnf_transformation,[],[f19])).
% 27.81/3.99  
% 27.81/3.99  fof(f12,axiom,(
% 27.81/3.99    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 27.81/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.81/3.99  
% 27.81/3.99  fof(f43,plain,(
% 27.81/3.99    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 27.81/3.99    inference(cnf_transformation,[],[f12])).
% 27.81/3.99  
% 27.81/3.99  fof(f10,axiom,(
% 27.81/3.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 27.81/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.81/3.99  
% 27.81/3.99  fof(f23,plain,(
% 27.81/3.99    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 27.81/3.99    inference(ennf_transformation,[],[f10])).
% 27.81/3.99  
% 27.81/3.99  fof(f41,plain,(
% 27.81/3.99    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 27.81/3.99    inference(cnf_transformation,[],[f23])).
% 27.81/3.99  
% 27.81/3.99  fof(f4,axiom,(
% 27.81/3.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 27.81/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.81/3.99  
% 27.81/3.99  fof(f35,plain,(
% 27.81/3.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 27.81/3.99    inference(cnf_transformation,[],[f4])).
% 27.81/3.99  
% 27.81/3.99  fof(f3,axiom,(
% 27.81/3.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 27.81/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.81/3.99  
% 27.81/3.99  fof(f26,plain,(
% 27.81/3.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 27.81/3.99    inference(nnf_transformation,[],[f3])).
% 27.81/3.99  
% 27.81/3.99  fof(f27,plain,(
% 27.81/3.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 27.81/3.99    inference(flattening,[],[f26])).
% 27.81/3.99  
% 27.81/3.99  fof(f34,plain,(
% 27.81/3.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 27.81/3.99    inference(cnf_transformation,[],[f27])).
% 27.81/3.99  
% 27.81/3.99  fof(f8,axiom,(
% 27.81/3.99    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k1_relat_1(X0)))),
% 27.81/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.81/3.99  
% 27.81/3.99  fof(f20,plain,(
% 27.81/3.99    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 27.81/3.99    inference(ennf_transformation,[],[f8])).
% 27.81/3.99  
% 27.81/3.99  fof(f21,plain,(
% 27.81/3.99    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 27.81/3.99    inference(flattening,[],[f20])).
% 27.81/3.99  
% 27.81/3.99  fof(f39,plain,(
% 27.81/3.99    ( ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 27.81/3.99    inference(cnf_transformation,[],[f21])).
% 27.81/3.99  
% 27.81/3.99  fof(f2,axiom,(
% 27.81/3.99    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 27.81/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.81/3.99  
% 27.81/3.99  fof(f15,plain,(
% 27.81/3.99    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 27.81/3.99    inference(ennf_transformation,[],[f2])).
% 27.81/3.99  
% 27.81/3.99  fof(f31,plain,(
% 27.81/3.99    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 27.81/3.99    inference(cnf_transformation,[],[f15])).
% 27.81/3.99  
% 27.81/3.99  fof(f13,conjecture,(
% 27.81/3.99    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 27.81/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.81/3.99  
% 27.81/3.99  fof(f14,negated_conjecture,(
% 27.81/3.99    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 27.81/3.99    inference(negated_conjecture,[],[f13])).
% 27.81/3.99  
% 27.81/3.99  fof(f25,plain,(
% 27.81/3.99    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 27.81/3.99    inference(ennf_transformation,[],[f14])).
% 27.81/3.99  
% 27.81/3.99  fof(f28,plain,(
% 27.81/3.99    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 27.81/3.99    introduced(choice_axiom,[])).
% 27.81/3.99  
% 27.81/3.99  fof(f29,plain,(
% 27.81/3.99    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 27.81/3.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f28])).
% 27.81/3.99  
% 27.81/3.99  fof(f45,plain,(
% 27.81/3.99    v1_relat_1(sK0)),
% 27.81/3.99    inference(cnf_transformation,[],[f29])).
% 27.81/3.99  
% 27.81/3.99  fof(f46,plain,(
% 27.81/3.99    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 27.81/3.99    inference(cnf_transformation,[],[f29])).
% 27.81/3.99  
% 27.81/3.99  cnf(c_0,plain,
% 27.81/3.99      ( v1_xboole_0(k1_xboole_0) ),
% 27.81/3.99      inference(cnf_transformation,[],[f30]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_442,plain,
% 27.81/3.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 27.81/3.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_6,plain,
% 27.81/3.99      ( v1_relat_1(X0) | ~ v1_xboole_0(X0) ),
% 27.81/3.99      inference(cnf_transformation,[],[f36]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_437,plain,
% 27.81/3.99      ( v1_relat_1(X0) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 27.81/3.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_811,plain,
% 27.81/3.99      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 27.81/3.99      inference(superposition,[status(thm)],[c_442,c_437]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_7,plain,
% 27.81/3.99      ( ~ v1_relat_1(X0) | v1_relat_1(k4_relat_1(X0)) ),
% 27.81/3.99      inference(cnf_transformation,[],[f37]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_436,plain,
% 27.81/3.99      ( v1_relat_1(X0) != iProver_top
% 27.81/3.99      | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
% 27.81/3.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_12,plain,
% 27.81/3.99      ( ~ v1_relat_1(X0)
% 27.81/3.99      | ~ v1_relat_1(X1)
% 27.81/3.99      | k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1)) ),
% 27.81/3.99      inference(cnf_transformation,[],[f42]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_431,plain,
% 27.81/3.99      ( k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,X0))
% 27.81/3.99      | v1_relat_1(X1) != iProver_top
% 27.81/3.99      | v1_relat_1(X0) != iProver_top ),
% 27.81/3.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_1066,plain,
% 27.81/3.99      ( k5_relat_1(k4_relat_1(k4_relat_1(X0)),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,k4_relat_1(X0)))
% 27.81/3.99      | v1_relat_1(X0) != iProver_top
% 27.81/3.99      | v1_relat_1(X1) != iProver_top ),
% 27.81/3.99      inference(superposition,[status(thm)],[c_436,c_431]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_1945,plain,
% 27.81/3.99      ( k5_relat_1(k4_relat_1(k4_relat_1(k1_xboole_0)),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,k4_relat_1(k1_xboole_0)))
% 27.81/3.99      | v1_relat_1(X0) != iProver_top ),
% 27.81/3.99      inference(superposition,[status(thm)],[c_811,c_1066]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_10,plain,
% 27.81/3.99      ( ~ v1_relat_1(X0) | k4_relat_1(k4_relat_1(X0)) = X0 ),
% 27.81/3.99      inference(cnf_transformation,[],[f40]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_433,plain,
% 27.81/3.99      ( k4_relat_1(k4_relat_1(X0)) = X0 | v1_relat_1(X0) != iProver_top ),
% 27.81/3.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_1365,plain,
% 27.81/3.99      ( k4_relat_1(k4_relat_1(k1_xboole_0)) = k1_xboole_0 ),
% 27.81/3.99      inference(superposition,[status(thm)],[c_811,c_433]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_1948,plain,
% 27.81/3.99      ( k4_relat_1(k5_relat_1(X0,k4_relat_1(k1_xboole_0))) = k5_relat_1(k1_xboole_0,k4_relat_1(X0))
% 27.81/3.99      | v1_relat_1(X0) != iProver_top ),
% 27.81/3.99      inference(light_normalisation,[status(thm)],[c_1945,c_1365]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_8313,plain,
% 27.81/3.99      ( k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(k1_xboole_0))) = k5_relat_1(k1_xboole_0,k4_relat_1(k1_xboole_0)) ),
% 27.81/3.99      inference(superposition,[status(thm)],[c_811,c_1948]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_8,plain,
% 27.81/3.99      ( ~ v1_relat_1(X0)
% 27.81/3.99      | ~ v1_relat_1(X1)
% 27.81/3.99      | v1_relat_1(k5_relat_1(X0,X1)) ),
% 27.81/3.99      inference(cnf_transformation,[],[f38]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_435,plain,
% 27.81/3.99      ( v1_relat_1(X0) != iProver_top
% 27.81/3.99      | v1_relat_1(X1) != iProver_top
% 27.81/3.99      | v1_relat_1(k5_relat_1(X0,X1)) = iProver_top ),
% 27.81/3.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_14,plain,
% 27.81/3.99      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 27.81/3.99      inference(cnf_transformation,[],[f43]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_11,plain,
% 27.81/3.99      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
% 27.81/3.99      | ~ v1_relat_1(X0)
% 27.81/3.99      | ~ v1_relat_1(X1) ),
% 27.81/3.99      inference(cnf_transformation,[],[f41]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_432,plain,
% 27.81/3.99      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) = iProver_top
% 27.81/3.99      | v1_relat_1(X0) != iProver_top
% 27.81/3.99      | v1_relat_1(X1) != iProver_top ),
% 27.81/3.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_936,plain,
% 27.81/3.99      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0) = iProver_top
% 27.81/3.99      | v1_relat_1(X0) != iProver_top
% 27.81/3.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 27.81/3.99      inference(superposition,[status(thm)],[c_14,c_432]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_36,plain,
% 27.81/3.99      ( v1_relat_1(X0) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 27.81/3.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_38,plain,
% 27.81/3.99      ( v1_relat_1(k1_xboole_0) = iProver_top
% 27.81/3.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 27.81/3.99      inference(instantiation,[status(thm)],[c_36]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_50,plain,
% 27.81/3.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 27.81/3.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_1353,plain,
% 27.81/3.99      ( v1_relat_1(X0) != iProver_top
% 27.81/3.99      | r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0) = iProver_top ),
% 27.81/3.99      inference(global_propositional_subsumption,
% 27.81/3.99                [status(thm)],
% 27.81/3.99                [c_936,c_38,c_50]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_1354,plain,
% 27.81/3.99      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0) = iProver_top
% 27.81/3.99      | v1_relat_1(X0) != iProver_top ),
% 27.81/3.99      inference(renaming,[status(thm)],[c_1353]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_5,plain,
% 27.81/3.99      ( r1_tarski(k1_xboole_0,X0) ),
% 27.81/3.99      inference(cnf_transformation,[],[f35]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_438,plain,
% 27.81/3.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 27.81/3.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_2,plain,
% 27.81/3.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 27.81/3.99      inference(cnf_transformation,[],[f34]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_440,plain,
% 27.81/3.99      ( X0 = X1
% 27.81/3.99      | r1_tarski(X0,X1) != iProver_top
% 27.81/3.99      | r1_tarski(X1,X0) != iProver_top ),
% 27.81/3.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_1187,plain,
% 27.81/3.99      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 27.81/3.99      inference(superposition,[status(thm)],[c_438,c_440]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_1562,plain,
% 27.81/3.99      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
% 27.81/3.99      | v1_relat_1(X0) != iProver_top ),
% 27.81/3.99      inference(superposition,[status(thm)],[c_1354,c_1187]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_5327,plain,
% 27.81/3.99      ( k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(X0))) = k1_xboole_0
% 27.81/3.99      | v1_relat_1(X0) != iProver_top ),
% 27.81/3.99      inference(superposition,[status(thm)],[c_436,c_1562]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_5552,plain,
% 27.81/3.99      ( k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(k1_xboole_0))) = k1_xboole_0 ),
% 27.81/3.99      inference(superposition,[status(thm)],[c_811,c_5327]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_9,plain,
% 27.81/3.99      ( ~ v1_relat_1(X0)
% 27.81/3.99      | v1_xboole_0(X0)
% 27.81/3.99      | ~ v1_xboole_0(k1_relat_1(X0)) ),
% 27.81/3.99      inference(cnf_transformation,[],[f39]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_434,plain,
% 27.81/3.99      ( v1_relat_1(X0) != iProver_top
% 27.81/3.99      | v1_xboole_0(X0) = iProver_top
% 27.81/3.99      | v1_xboole_0(k1_relat_1(X0)) != iProver_top ),
% 27.81/3.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_82327,plain,
% 27.81/3.99      ( v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(k1_xboole_0))) != iProver_top
% 27.81/3.99      | v1_xboole_0(k5_relat_1(k1_xboole_0,k4_relat_1(k1_xboole_0))) = iProver_top
% 27.81/3.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 27.81/3.99      inference(superposition,[status(thm)],[c_5552,c_434]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_82372,plain,
% 27.81/3.99      ( v1_xboole_0(k5_relat_1(k1_xboole_0,k4_relat_1(k1_xboole_0))) = iProver_top
% 27.81/3.99      | v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(k1_xboole_0))) != iProver_top ),
% 27.81/3.99      inference(global_propositional_subsumption,
% 27.81/3.99                [status(thm)],
% 27.81/3.99                [c_82327,c_50]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_82373,plain,
% 27.81/3.99      ( v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(k1_xboole_0))) != iProver_top
% 27.81/3.99      | v1_xboole_0(k5_relat_1(k1_xboole_0,k4_relat_1(k1_xboole_0))) = iProver_top ),
% 27.81/3.99      inference(renaming,[status(thm)],[c_82372]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_82378,plain,
% 27.81/3.99      ( v1_relat_1(k4_relat_1(k1_xboole_0)) != iProver_top
% 27.81/3.99      | v1_relat_1(k1_xboole_0) != iProver_top
% 27.81/3.99      | v1_xboole_0(k5_relat_1(k1_xboole_0,k4_relat_1(k1_xboole_0))) = iProver_top ),
% 27.81/3.99      inference(superposition,[status(thm)],[c_435,c_82373]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_33,plain,
% 27.81/3.99      ( v1_relat_1(X0) != iProver_top
% 27.81/3.99      | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
% 27.81/3.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_35,plain,
% 27.81/3.99      ( v1_relat_1(k4_relat_1(k1_xboole_0)) = iProver_top
% 27.81/3.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 27.81/3.99      inference(instantiation,[status(thm)],[c_33]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_82919,plain,
% 27.81/3.99      ( v1_xboole_0(k5_relat_1(k1_xboole_0,k4_relat_1(k1_xboole_0))) = iProver_top ),
% 27.81/3.99      inference(global_propositional_subsumption,
% 27.81/3.99                [status(thm)],
% 27.81/3.99                [c_82378,c_35,c_38,c_50]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_1,plain,
% 27.81/3.99      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 27.81/3.99      inference(cnf_transformation,[],[f31]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_441,plain,
% 27.81/3.99      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 27.81/3.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_82925,plain,
% 27.81/3.99      ( k5_relat_1(k1_xboole_0,k4_relat_1(k1_xboole_0)) = k1_xboole_0 ),
% 27.81/3.99      inference(superposition,[status(thm)],[c_82919,c_441]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_132029,plain,
% 27.81/3.99      ( k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 27.81/3.99      inference(light_normalisation,[status(thm)],[c_8313,c_82925]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_16,negated_conjecture,
% 27.81/3.99      ( v1_relat_1(sK0) ),
% 27.81/3.99      inference(cnf_transformation,[],[f45]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_430,plain,
% 27.81/3.99      ( v1_relat_1(sK0) = iProver_top ),
% 27.81/3.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_1366,plain,
% 27.81/3.99      ( k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,k1_xboole_0))
% 27.81/3.99      | v1_relat_1(X0) != iProver_top ),
% 27.81/3.99      inference(superposition,[status(thm)],[c_811,c_431]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_2166,plain,
% 27.81/3.99      ( k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(sK0)) = k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
% 27.81/3.99      inference(superposition,[status(thm)],[c_430,c_1366]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_132071,plain,
% 27.81/3.99      ( k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) = k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
% 27.81/3.99      inference(demodulation,[status(thm)],[c_132029,c_2166]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_5551,plain,
% 27.81/3.99      ( k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) = k1_xboole_0 ),
% 27.81/3.99      inference(superposition,[status(thm)],[c_430,c_5327]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_5741,plain,
% 27.81/3.99      ( v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) != iProver_top
% 27.81/3.99      | v1_xboole_0(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) = iProver_top
% 27.81/3.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 27.81/3.99      inference(superposition,[status(thm)],[c_5551,c_434]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_17,plain,
% 27.81/3.99      ( v1_relat_1(sK0) = iProver_top ),
% 27.81/3.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_8312,plain,
% 27.81/3.99      ( k4_relat_1(k5_relat_1(sK0,k4_relat_1(k1_xboole_0))) = k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) ),
% 27.81/3.99      inference(superposition,[status(thm)],[c_430,c_1948]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_8506,plain,
% 27.81/3.99      ( v1_relat_1(k5_relat_1(sK0,k4_relat_1(k1_xboole_0))) != iProver_top
% 27.81/3.99      | v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) = iProver_top ),
% 27.81/3.99      inference(superposition,[status(thm)],[c_8312,c_436]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_8759,plain,
% 27.81/3.99      ( v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) = iProver_top
% 27.81/3.99      | v1_relat_1(k4_relat_1(k1_xboole_0)) != iProver_top
% 27.81/3.99      | v1_relat_1(sK0) != iProver_top ),
% 27.81/3.99      inference(superposition,[status(thm)],[c_435,c_8506]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_16643,plain,
% 27.81/3.99      ( v1_xboole_0(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) = iProver_top ),
% 27.81/3.99      inference(global_propositional_subsumption,
% 27.81/3.99                [status(thm)],
% 27.81/3.99                [c_5741,c_17,c_35,c_38,c_50,c_8759]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_16649,plain,
% 27.81/3.99      ( k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) = k1_xboole_0 ),
% 27.81/3.99      inference(superposition,[status(thm)],[c_16643,c_441]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_132079,plain,
% 27.81/3.99      ( k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_xboole_0 ),
% 27.81/3.99      inference(light_normalisation,[status(thm)],[c_132071,c_16649]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_204,plain,
% 27.81/3.99      ( X0 != X1 | k4_relat_1(X0) = k4_relat_1(X1) ),
% 27.81/3.99      theory(equality) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_126974,plain,
% 27.81/3.99      ( k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) != X0
% 27.81/3.99      | k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = k4_relat_1(X0) ),
% 27.81/3.99      inference(instantiation,[status(thm)],[c_204]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_126976,plain,
% 27.81/3.99      ( k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) != k1_xboole_0
% 27.81/3.99      | k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = k4_relat_1(k1_xboole_0) ),
% 27.81/3.99      inference(instantiation,[status(thm)],[c_126974]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_200,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_126224,plain,
% 27.81/3.99      ( k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) != X0
% 27.81/3.99      | k1_xboole_0 != X0
% 27.81/3.99      | k1_xboole_0 = k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
% 27.81/3.99      inference(instantiation,[status(thm)],[c_200]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_126973,plain,
% 27.81/3.99      ( k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) != k4_relat_1(X0)
% 27.81/3.99      | k1_xboole_0 != k4_relat_1(X0)
% 27.81/3.99      | k1_xboole_0 = k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
% 27.81/3.99      inference(instantiation,[status(thm)],[c_126224]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_126975,plain,
% 27.81/3.99      ( k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) != k4_relat_1(k1_xboole_0)
% 27.81/3.99      | k1_xboole_0 = k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))
% 27.81/3.99      | k1_xboole_0 != k4_relat_1(k1_xboole_0) ),
% 27.81/3.99      inference(instantiation,[status(thm)],[c_126973]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_125105,plain,
% 27.81/3.99      ( k5_relat_1(sK0,k1_xboole_0) != X0
% 27.81/3.99      | k1_xboole_0 != X0
% 27.81/3.99      | k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
% 27.81/3.99      inference(instantiation,[status(thm)],[c_200]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_125997,plain,
% 27.81/3.99      ( k5_relat_1(sK0,k1_xboole_0) != k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))
% 27.81/3.99      | k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)
% 27.81/3.99      | k1_xboole_0 != k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
% 27.81/3.99      inference(instantiation,[status(thm)],[c_125105]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_879,plain,
% 27.81/3.99      ( X0 != X1 | k5_relat_1(X2,X3) != X1 | k5_relat_1(X2,X3) = X0 ),
% 27.81/3.99      inference(instantiation,[status(thm)],[c_200]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_1295,plain,
% 27.81/3.99      ( X0 != k5_relat_1(X1,X2)
% 27.81/3.99      | k5_relat_1(X1,X2) = X0
% 27.81/3.99      | k5_relat_1(X1,X2) != k5_relat_1(X1,X2) ),
% 27.81/3.99      inference(instantiation,[status(thm)],[c_879]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_10768,plain,
% 27.81/3.99      ( X0 != k5_relat_1(sK0,k1_xboole_0)
% 27.81/3.99      | k5_relat_1(sK0,k1_xboole_0) = X0
% 27.81/3.99      | k5_relat_1(sK0,k1_xboole_0) != k5_relat_1(sK0,k1_xboole_0) ),
% 27.81/3.99      inference(instantiation,[status(thm)],[c_1295]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_67608,plain,
% 27.81/3.99      ( k5_relat_1(sK0,k1_xboole_0) != k5_relat_1(sK0,k1_xboole_0)
% 27.81/3.99      | k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))
% 27.81/3.99      | k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) != k5_relat_1(sK0,k1_xboole_0) ),
% 27.81/3.99      inference(instantiation,[status(thm)],[c_10768]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_199,plain,( X0 = X0 ),theory(equality) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_1296,plain,
% 27.81/3.99      ( k5_relat_1(X0,X1) = k5_relat_1(X0,X1) ),
% 27.81/3.99      inference(instantiation,[status(thm)],[c_199]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_26476,plain,
% 27.81/3.99      ( k5_relat_1(sK0,k1_xboole_0) = k5_relat_1(sK0,k1_xboole_0) ),
% 27.81/3.99      inference(instantiation,[status(thm)],[c_1296]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_5329,plain,
% 27.81/3.99      ( k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k1_xboole_0 ),
% 27.81/3.99      inference(superposition,[status(thm)],[c_430,c_1562]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_4088,plain,
% 27.81/3.99      ( k4_relat_1(X0) != X1
% 27.81/3.99      | k1_xboole_0 != X1
% 27.81/3.99      | k1_xboole_0 = k4_relat_1(X0) ),
% 27.81/3.99      inference(instantiation,[status(thm)],[c_200]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_4089,plain,
% 27.81/3.99      ( k4_relat_1(k1_xboole_0) != k1_xboole_0
% 27.81/3.99      | k1_xboole_0 = k4_relat_1(k1_xboole_0)
% 27.81/3.99      | k1_xboole_0 != k1_xboole_0 ),
% 27.81/3.99      inference(instantiation,[status(thm)],[c_4088]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_1209,plain,
% 27.81/3.99      ( k4_relat_1(k4_relat_1(k5_relat_1(X0,X1))) = k5_relat_1(X0,X1)
% 27.81/3.99      | v1_relat_1(X0) != iProver_top
% 27.81/3.99      | v1_relat_1(X1) != iProver_top ),
% 27.81/3.99      inference(superposition,[status(thm)],[c_435,c_433]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_2870,plain,
% 27.81/3.99      ( k4_relat_1(k4_relat_1(k5_relat_1(sK0,X0))) = k5_relat_1(sK0,X0)
% 27.81/3.99      | v1_relat_1(X0) != iProver_top ),
% 27.81/3.99      inference(superposition,[status(thm)],[c_430,c_1209]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_2908,plain,
% 27.81/3.99      ( k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = k5_relat_1(sK0,k1_xboole_0)
% 27.81/3.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 27.81/3.99      inference(instantiation,[status(thm)],[c_2870]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_998,plain,
% 27.81/3.99      ( v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
% 27.81/3.99      | ~ v1_relat_1(sK0)
% 27.81/3.99      | ~ v1_relat_1(k1_xboole_0) ),
% 27.81/3.99      inference(instantiation,[status(thm)],[c_8]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_201,plain,
% 27.81/3.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 27.81/3.99      theory(equality) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_637,plain,
% 27.81/3.99      ( ~ v1_xboole_0(X0)
% 27.81/3.99      | v1_xboole_0(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)))
% 27.81/3.99      | k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) != X0 ),
% 27.81/3.99      inference(instantiation,[status(thm)],[c_201]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_639,plain,
% 27.81/3.99      ( v1_xboole_0(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)))
% 27.81/3.99      | ~ v1_xboole_0(k1_xboole_0)
% 27.81/3.99      | k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) != k1_xboole_0 ),
% 27.81/3.99      inference(instantiation,[status(thm)],[c_637]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_580,plain,
% 27.81/3.99      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
% 27.81/3.99      | v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))
% 27.81/3.99      | ~ v1_xboole_0(k1_relat_1(k5_relat_1(k1_xboole_0,sK0))) ),
% 27.81/3.99      inference(instantiation,[status(thm)],[c_9]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_546,plain,
% 27.81/3.99      ( ~ v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))
% 27.81/3.99      | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
% 27.81/3.99      inference(instantiation,[status(thm)],[c_1]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_45,plain,
% 27.81/3.99      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 27.81/3.99      | k1_xboole_0 = k1_xboole_0 ),
% 27.81/3.99      inference(instantiation,[status(thm)],[c_2]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_40,plain,
% 27.81/3.99      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 27.81/3.99      inference(instantiation,[status(thm)],[c_5]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_37,plain,
% 27.81/3.99      ( v1_relat_1(k1_xboole_0) | ~ v1_xboole_0(k1_xboole_0) ),
% 27.81/3.99      inference(instantiation,[status(thm)],[c_6]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(c_15,negated_conjecture,
% 27.81/3.99      ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
% 27.81/3.99      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
% 27.81/3.99      inference(cnf_transformation,[],[f46]) ).
% 27.81/3.99  
% 27.81/3.99  cnf(contradiction,plain,
% 27.81/3.99      ( $false ),
% 27.81/3.99      inference(minisat,
% 27.81/3.99                [status(thm)],
% 27.81/3.99                [c_132079,c_132029,c_126976,c_126975,c_125997,c_67608,
% 27.81/3.99                 c_26476,c_5329,c_4089,c_2908,c_998,c_639,c_580,c_546,
% 27.81/3.99                 c_50,c_0,c_45,c_40,c_38,c_37,c_15,c_16]) ).
% 27.81/3.99  
% 27.81/3.99  
% 27.81/3.99  % SZS output end CNFRefutation for theBenchmark.p
% 27.81/3.99  
% 27.81/3.99  ------                               Statistics
% 27.81/3.99  
% 27.81/3.99  ------ Selected
% 27.81/3.99  
% 27.81/3.99  total_time:                             3.388
% 27.81/3.99  
%------------------------------------------------------------------------------
