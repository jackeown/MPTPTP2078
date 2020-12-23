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
% DateTime   : Thu Dec  3 11:52:12 EST 2020

% Result     : Theorem 3.76s
% Output     : CNFRefutation 3.76s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 233 expanded)
%              Number of clauses        :   56 (  76 expanded)
%              Number of leaves         :   10 (  44 expanded)
%              Depth                    :   18
%              Number of atoms          :  252 ( 929 expanded)
%              Number of equality atoms :  101 ( 147 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_tarski(X0,k1_relat_1(X2))
          & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( v2_funct_1(X2)
            & r1_tarski(X0,k1_relat_1(X2))
            & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f23,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & v2_funct_1(X2)
        & r1_tarski(X0,k1_relat_1(X2))
        & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(sK0,sK1)
      & v2_funct_1(sK2)
      & r1_tarski(sK0,k1_relat_1(sK2))
      & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ~ r1_tarski(sK0,sK1)
    & v2_funct_1(sK2)
    & r1_tarski(sK0,k1_relat_1(sK2))
    & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f23])).

fof(f36,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f37,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f40,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f38,plain,(
    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f39,plain,(
    r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f20])).

fof(f27,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f28,f30])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f45,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f25])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f29,f30])).

fof(f41,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_15,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_640,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k3_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_648,plain,
    ( k3_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k3_xboole_0(X1,X2))
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1535,plain,
    ( k3_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) = k9_relat_1(sK2,k3_xboole_0(X0,X1))
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_640,c_648])).

cnf(c_14,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_17,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_11,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_20,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3137,plain,
    ( k3_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) = k9_relat_1(sK2,k3_xboole_0(X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1535,c_17,c_20])).

cnf(c_13,negated_conjecture,
    ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_642,plain,
    ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_649,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1046,plain,
    ( k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) = k9_relat_1(sK2,sK0) ),
    inference(superposition,[status(thm)],[c_642,c_649])).

cnf(c_3148,plain,
    ( k9_relat_1(sK2,k3_xboole_0(sK0,sK1)) = k9_relat_1(sK2,sK0) ),
    inference(superposition,[status(thm)],[c_3137,c_1046])).

cnf(c_9,plain,
    ( r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_646,plain,
    ( r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_5091,plain,
    ( r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k3_xboole_0(sK0,sK1)) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3148,c_646])).

cnf(c_12,negated_conjecture,
    ( r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_643,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_8,plain,
    ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_647,plain,
    ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) = iProver_top
    | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_654,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1369,plain,
    ( k10_relat_1(X0,k9_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k10_relat_1(X0,k9_relat_1(X0,X1))) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_646,c_654])).

cnf(c_2984,plain,
    ( k10_relat_1(X0,k9_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_647,c_1369])).

cnf(c_3769,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,sK0)) = sK0
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_643,c_2984])).

cnf(c_801,plain,
    ( r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0)))
    | ~ r1_tarski(sK0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1304,plain,
    ( r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),sK0)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1273,plain,
    ( ~ r1_tarski(X0,sK0)
    | ~ r1_tarski(sK0,X0)
    | X0 = sK0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1612,plain,
    ( ~ r1_tarski(k10_relat_1(X0,k9_relat_1(X0,sK0)),sK0)
    | ~ r1_tarski(sK0,k10_relat_1(X0,k9_relat_1(X0,sK0)))
    | k10_relat_1(X0,k9_relat_1(X0,sK0)) = sK0 ),
    inference(instantiation,[status(thm)],[c_1273])).

cnf(c_1615,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),sK0)
    | ~ r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0)))
    | k10_relat_1(sK2,k9_relat_1(sK2,sK0)) = sK0 ),
    inference(instantiation,[status(thm)],[c_1612])).

cnf(c_4052,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,sK0)) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3769,c_15,c_14,c_12,c_11,c_801,c_1304,c_1615])).

cnf(c_5123,plain,
    ( r1_tarski(sK0,k3_xboole_0(sK0,sK1)) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5091,c_4052])).

cnf(c_16,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_5687,plain,
    ( r1_tarski(sK0,k3_xboole_0(sK0,sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5123,c_16,c_17,c_20])).

cnf(c_5,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_650,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1368,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,k3_xboole_0(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_650,c_654])).

cnf(c_5695,plain,
    ( k3_xboole_0(sK0,sK1) = sK0 ),
    inference(superposition,[status(thm)],[c_5687,c_1368])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_651,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_5713,plain,
    ( k5_xboole_0(sK0,sK0) != k1_xboole_0
    | r1_tarski(sK0,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_5695,c_651])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_653,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_652,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1220,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_653,c_652])).

cnf(c_1043,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_653,c_649])).

cnf(c_1680,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1220,c_1043])).

cnf(c_5717,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK0,sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5713,c_1680])).

cnf(c_5718,plain,
    ( r1_tarski(sK0,sK1) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_5717])).

cnf(c_10,negated_conjecture,
    ( ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_21,plain,
    ( r1_tarski(sK0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5718,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : iproveropt_run.sh %d %s
% 0.15/0.36  % Computer   : n006.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 11:17:52 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  % Running in FOF mode
% 3.76/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.76/1.01  
% 3.76/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.76/1.01  
% 3.76/1.01  ------  iProver source info
% 3.76/1.01  
% 3.76/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.76/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.76/1.01  git: non_committed_changes: false
% 3.76/1.01  git: last_make_outside_of_git: false
% 3.76/1.01  
% 3.76/1.01  ------ 
% 3.76/1.01  
% 3.76/1.01  ------ Input Options
% 3.76/1.01  
% 3.76/1.01  --out_options                           all
% 3.76/1.01  --tptp_safe_out                         true
% 3.76/1.01  --problem_path                          ""
% 3.76/1.01  --include_path                          ""
% 3.76/1.01  --clausifier                            res/vclausify_rel
% 3.76/1.01  --clausifier_options                    --mode clausify
% 3.76/1.01  --stdin                                 false
% 3.76/1.01  --stats_out                             sel
% 3.76/1.01  
% 3.76/1.01  ------ General Options
% 3.76/1.01  
% 3.76/1.01  --fof                                   false
% 3.76/1.01  --time_out_real                         604.99
% 3.76/1.01  --time_out_virtual                      -1.
% 3.76/1.01  --symbol_type_check                     false
% 3.76/1.01  --clausify_out                          false
% 3.76/1.01  --sig_cnt_out                           false
% 3.76/1.01  --trig_cnt_out                          false
% 3.76/1.01  --trig_cnt_out_tolerance                1.
% 3.76/1.01  --trig_cnt_out_sk_spl                   false
% 3.76/1.01  --abstr_cl_out                          false
% 3.76/1.01  
% 3.76/1.01  ------ Global Options
% 3.76/1.01  
% 3.76/1.01  --schedule                              none
% 3.76/1.01  --add_important_lit                     false
% 3.76/1.01  --prop_solver_per_cl                    1000
% 3.76/1.01  --min_unsat_core                        false
% 3.76/1.01  --soft_assumptions                      false
% 3.76/1.01  --soft_lemma_size                       3
% 3.76/1.01  --prop_impl_unit_size                   0
% 3.76/1.01  --prop_impl_unit                        []
% 3.76/1.01  --share_sel_clauses                     true
% 3.76/1.01  --reset_solvers                         false
% 3.76/1.01  --bc_imp_inh                            [conj_cone]
% 3.76/1.01  --conj_cone_tolerance                   3.
% 3.76/1.01  --extra_neg_conj                        none
% 3.76/1.01  --large_theory_mode                     true
% 3.76/1.01  --prolific_symb_bound                   200
% 3.76/1.01  --lt_threshold                          2000
% 3.76/1.01  --clause_weak_htbl                      true
% 3.76/1.01  --gc_record_bc_elim                     false
% 3.76/1.01  
% 3.76/1.01  ------ Preprocessing Options
% 3.76/1.01  
% 3.76/1.01  --preprocessing_flag                    true
% 3.76/1.01  --time_out_prep_mult                    0.1
% 3.76/1.01  --splitting_mode                        input
% 3.76/1.01  --splitting_grd                         true
% 3.76/1.01  --splitting_cvd                         false
% 3.76/1.01  --splitting_cvd_svl                     false
% 3.76/1.01  --splitting_nvd                         32
% 3.76/1.01  --sub_typing                            true
% 3.76/1.01  --prep_gs_sim                           false
% 3.76/1.01  --prep_unflatten                        true
% 3.76/1.01  --prep_res_sim                          true
% 3.76/1.01  --prep_upred                            true
% 3.76/1.01  --prep_sem_filter                       exhaustive
% 3.76/1.01  --prep_sem_filter_out                   false
% 3.76/1.01  --pred_elim                             false
% 3.76/1.01  --res_sim_input                         true
% 3.76/1.01  --eq_ax_congr_red                       true
% 3.76/1.01  --pure_diseq_elim                       true
% 3.76/1.01  --brand_transform                       false
% 3.76/1.01  --non_eq_to_eq                          false
% 3.76/1.01  --prep_def_merge                        true
% 3.76/1.01  --prep_def_merge_prop_impl              false
% 3.76/1.01  --prep_def_merge_mbd                    true
% 3.76/1.01  --prep_def_merge_tr_red                 false
% 3.76/1.01  --prep_def_merge_tr_cl                  false
% 3.76/1.01  --smt_preprocessing                     true
% 3.76/1.01  --smt_ac_axioms                         fast
% 3.76/1.01  --preprocessed_out                      false
% 3.76/1.01  --preprocessed_stats                    false
% 3.76/1.01  
% 3.76/1.01  ------ Abstraction refinement Options
% 3.76/1.01  
% 3.76/1.01  --abstr_ref                             []
% 3.76/1.01  --abstr_ref_prep                        false
% 3.76/1.01  --abstr_ref_until_sat                   false
% 3.76/1.01  --abstr_ref_sig_restrict                funpre
% 3.76/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.76/1.01  --abstr_ref_under                       []
% 3.76/1.01  
% 3.76/1.01  ------ SAT Options
% 3.76/1.01  
% 3.76/1.01  --sat_mode                              false
% 3.76/1.01  --sat_fm_restart_options                ""
% 3.76/1.01  --sat_gr_def                            false
% 3.76/1.01  --sat_epr_types                         true
% 3.76/1.01  --sat_non_cyclic_types                  false
% 3.76/1.01  --sat_finite_models                     false
% 3.76/1.01  --sat_fm_lemmas                         false
% 3.76/1.01  --sat_fm_prep                           false
% 3.76/1.01  --sat_fm_uc_incr                        true
% 3.76/1.01  --sat_out_model                         small
% 3.76/1.01  --sat_out_clauses                       false
% 3.76/1.01  
% 3.76/1.01  ------ QBF Options
% 3.76/1.01  
% 3.76/1.01  --qbf_mode                              false
% 3.76/1.01  --qbf_elim_univ                         false
% 3.76/1.01  --qbf_dom_inst                          none
% 3.76/1.01  --qbf_dom_pre_inst                      false
% 3.76/1.01  --qbf_sk_in                             false
% 3.76/1.01  --qbf_pred_elim                         true
% 3.76/1.01  --qbf_split                             512
% 3.76/1.01  
% 3.76/1.01  ------ BMC1 Options
% 3.76/1.01  
% 3.76/1.01  --bmc1_incremental                      false
% 3.76/1.01  --bmc1_axioms                           reachable_all
% 3.76/1.01  --bmc1_min_bound                        0
% 3.76/1.01  --bmc1_max_bound                        -1
% 3.76/1.01  --bmc1_max_bound_default                -1
% 3.76/1.01  --bmc1_symbol_reachability              true
% 3.76/1.01  --bmc1_property_lemmas                  false
% 3.76/1.01  --bmc1_k_induction                      false
% 3.76/1.01  --bmc1_non_equiv_states                 false
% 3.76/1.01  --bmc1_deadlock                         false
% 3.76/1.01  --bmc1_ucm                              false
% 3.76/1.01  --bmc1_add_unsat_core                   none
% 3.76/1.01  --bmc1_unsat_core_children              false
% 3.76/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.76/1.01  --bmc1_out_stat                         full
% 3.76/1.01  --bmc1_ground_init                      false
% 3.76/1.01  --bmc1_pre_inst_next_state              false
% 3.76/1.01  --bmc1_pre_inst_state                   false
% 3.76/1.01  --bmc1_pre_inst_reach_state             false
% 3.76/1.01  --bmc1_out_unsat_core                   false
% 3.76/1.01  --bmc1_aig_witness_out                  false
% 3.76/1.01  --bmc1_verbose                          false
% 3.76/1.01  --bmc1_dump_clauses_tptp                false
% 3.76/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.76/1.01  --bmc1_dump_file                        -
% 3.76/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.76/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.76/1.01  --bmc1_ucm_extend_mode                  1
% 3.76/1.01  --bmc1_ucm_init_mode                    2
% 3.76/1.01  --bmc1_ucm_cone_mode                    none
% 3.76/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.76/1.01  --bmc1_ucm_relax_model                  4
% 3.76/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.76/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.76/1.01  --bmc1_ucm_layered_model                none
% 3.76/1.01  --bmc1_ucm_max_lemma_size               10
% 3.76/1.01  
% 3.76/1.01  ------ AIG Options
% 3.76/1.01  
% 3.76/1.01  --aig_mode                              false
% 3.76/1.01  
% 3.76/1.01  ------ Instantiation Options
% 3.76/1.01  
% 3.76/1.01  --instantiation_flag                    true
% 3.76/1.01  --inst_sos_flag                         false
% 3.76/1.01  --inst_sos_phase                        true
% 3.76/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.76/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.76/1.01  --inst_lit_sel_side                     num_symb
% 3.76/1.01  --inst_solver_per_active                1400
% 3.76/1.01  --inst_solver_calls_frac                1.
% 3.76/1.01  --inst_passive_queue_type               priority_queues
% 3.76/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.76/1.01  --inst_passive_queues_freq              [25;2]
% 3.76/1.01  --inst_dismatching                      true
% 3.76/1.01  --inst_eager_unprocessed_to_passive     true
% 3.76/1.01  --inst_prop_sim_given                   true
% 3.76/1.01  --inst_prop_sim_new                     false
% 3.76/1.01  --inst_subs_new                         false
% 3.76/1.01  --inst_eq_res_simp                      false
% 3.76/1.01  --inst_subs_given                       false
% 3.76/1.01  --inst_orphan_elimination               true
% 3.76/1.01  --inst_learning_loop_flag               true
% 3.76/1.01  --inst_learning_start                   3000
% 3.76/1.01  --inst_learning_factor                  2
% 3.76/1.01  --inst_start_prop_sim_after_learn       3
% 3.76/1.01  --inst_sel_renew                        solver
% 3.76/1.01  --inst_lit_activity_flag                true
% 3.76/1.01  --inst_restr_to_given                   false
% 3.76/1.01  --inst_activity_threshold               500
% 3.76/1.01  --inst_out_proof                        true
% 3.76/1.01  
% 3.76/1.01  ------ Resolution Options
% 3.76/1.01  
% 3.76/1.01  --resolution_flag                       true
% 3.76/1.01  --res_lit_sel                           adaptive
% 3.76/1.01  --res_lit_sel_side                      none
% 3.76/1.01  --res_ordering                          kbo
% 3.76/1.01  --res_to_prop_solver                    active
% 3.76/1.01  --res_prop_simpl_new                    false
% 3.76/1.01  --res_prop_simpl_given                  true
% 3.76/1.01  --res_passive_queue_type                priority_queues
% 3.76/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.76/1.01  --res_passive_queues_freq               [15;5]
% 3.76/1.01  --res_forward_subs                      full
% 3.76/1.01  --res_backward_subs                     full
% 3.76/1.01  --res_forward_subs_resolution           true
% 3.76/1.01  --res_backward_subs_resolution          true
% 3.76/1.01  --res_orphan_elimination                true
% 3.76/1.01  --res_time_limit                        2.
% 3.76/1.01  --res_out_proof                         true
% 3.76/1.01  
% 3.76/1.01  ------ Superposition Options
% 3.76/1.01  
% 3.76/1.01  --superposition_flag                    true
% 3.76/1.01  --sup_passive_queue_type                priority_queues
% 3.76/1.01  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.76/1.01  --sup_passive_queues_freq               [1;4]
% 3.76/1.01  --demod_completeness_check              fast
% 3.76/1.01  --demod_use_ground                      true
% 3.76/1.01  --sup_to_prop_solver                    passive
% 3.76/1.01  --sup_prop_simpl_new                    true
% 3.76/1.01  --sup_prop_simpl_given                  true
% 3.76/1.01  --sup_fun_splitting                     false
% 3.76/1.01  --sup_smt_interval                      50000
% 3.76/1.01  
% 3.76/1.01  ------ Superposition Simplification Setup
% 3.76/1.01  
% 3.76/1.01  --sup_indices_passive                   []
% 3.76/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.76/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.76/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.76/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.76/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.76/1.01  --sup_full_bw                           [BwDemod]
% 3.76/1.01  --sup_immed_triv                        [TrivRules]
% 3.76/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.76/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.76/1.01  --sup_immed_bw_main                     []
% 3.76/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.76/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.76/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.76/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.76/1.01  
% 3.76/1.01  ------ Combination Options
% 3.76/1.01  
% 3.76/1.01  --comb_res_mult                         3
% 3.76/1.01  --comb_sup_mult                         2
% 3.76/1.01  --comb_inst_mult                        10
% 3.76/1.01  
% 3.76/1.01  ------ Debug Options
% 3.76/1.01  
% 3.76/1.01  --dbg_backtrace                         false
% 3.76/1.01  --dbg_dump_prop_clauses                 false
% 3.76/1.01  --dbg_dump_prop_clauses_file            -
% 3.76/1.01  --dbg_out_stat                          false
% 3.76/1.01  ------ Parsing...
% 3.76/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.76/1.01  
% 3.76/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.76/1.01  
% 3.76/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.76/1.01  
% 3.76/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.76/1.01  ------ Proving...
% 3.76/1.01  ------ Problem Properties 
% 3.76/1.01  
% 3.76/1.01  
% 3.76/1.01  clauses                                 15
% 3.76/1.01  conjectures                             6
% 3.76/1.01  EPR                                     6
% 3.76/1.01  Horn                                    15
% 3.76/1.01  unary                                   8
% 3.76/1.01  binary                                  3
% 3.76/1.01  lits                                    28
% 3.76/1.01  lits eq                                 5
% 3.76/1.01  fd_pure                                 0
% 3.76/1.01  fd_pseudo                               0
% 3.76/1.01  fd_cond                                 0
% 3.76/1.01  fd_pseudo_cond                          1
% 3.76/1.01  AC symbols                              0
% 3.76/1.01  
% 3.76/1.01  ------ Input Options Time Limit: Unbounded
% 3.76/1.01  
% 3.76/1.01  
% 3.76/1.01  ------ 
% 3.76/1.01  Current options:
% 3.76/1.01  ------ 
% 3.76/1.01  
% 3.76/1.01  ------ Input Options
% 3.76/1.01  
% 3.76/1.01  --out_options                           all
% 3.76/1.01  --tptp_safe_out                         true
% 3.76/1.01  --problem_path                          ""
% 3.76/1.01  --include_path                          ""
% 3.76/1.01  --clausifier                            res/vclausify_rel
% 3.76/1.01  --clausifier_options                    --mode clausify
% 3.76/1.01  --stdin                                 false
% 3.76/1.01  --stats_out                             sel
% 3.76/1.01  
% 3.76/1.01  ------ General Options
% 3.76/1.01  
% 3.76/1.01  --fof                                   false
% 3.76/1.01  --time_out_real                         604.99
% 3.76/1.01  --time_out_virtual                      -1.
% 3.76/1.01  --symbol_type_check                     false
% 3.76/1.01  --clausify_out                          false
% 3.76/1.01  --sig_cnt_out                           false
% 3.76/1.01  --trig_cnt_out                          false
% 3.76/1.01  --trig_cnt_out_tolerance                1.
% 3.76/1.01  --trig_cnt_out_sk_spl                   false
% 3.76/1.01  --abstr_cl_out                          false
% 3.76/1.01  
% 3.76/1.01  ------ Global Options
% 3.76/1.01  
% 3.76/1.01  --schedule                              none
% 3.76/1.01  --add_important_lit                     false
% 3.76/1.01  --prop_solver_per_cl                    1000
% 3.76/1.01  --min_unsat_core                        false
% 3.76/1.01  --soft_assumptions                      false
% 3.76/1.01  --soft_lemma_size                       3
% 3.76/1.01  --prop_impl_unit_size                   0
% 3.76/1.01  --prop_impl_unit                        []
% 3.76/1.01  --share_sel_clauses                     true
% 3.76/1.01  --reset_solvers                         false
% 3.76/1.01  --bc_imp_inh                            [conj_cone]
% 3.76/1.01  --conj_cone_tolerance                   3.
% 3.76/1.01  --extra_neg_conj                        none
% 3.76/1.01  --large_theory_mode                     true
% 3.76/1.01  --prolific_symb_bound                   200
% 3.76/1.01  --lt_threshold                          2000
% 3.76/1.01  --clause_weak_htbl                      true
% 3.76/1.01  --gc_record_bc_elim                     false
% 3.76/1.01  
% 3.76/1.01  ------ Preprocessing Options
% 3.76/1.01  
% 3.76/1.01  --preprocessing_flag                    true
% 3.76/1.01  --time_out_prep_mult                    0.1
% 3.76/1.01  --splitting_mode                        input
% 3.76/1.01  --splitting_grd                         true
% 3.76/1.01  --splitting_cvd                         false
% 3.76/1.01  --splitting_cvd_svl                     false
% 3.76/1.01  --splitting_nvd                         32
% 3.76/1.01  --sub_typing                            true
% 3.76/1.01  --prep_gs_sim                           false
% 3.76/1.01  --prep_unflatten                        true
% 3.76/1.01  --prep_res_sim                          true
% 3.76/1.01  --prep_upred                            true
% 3.76/1.01  --prep_sem_filter                       exhaustive
% 3.76/1.01  --prep_sem_filter_out                   false
% 3.76/1.01  --pred_elim                             false
% 3.76/1.01  --res_sim_input                         true
% 3.76/1.01  --eq_ax_congr_red                       true
% 3.76/1.01  --pure_diseq_elim                       true
% 3.76/1.01  --brand_transform                       false
% 3.76/1.01  --non_eq_to_eq                          false
% 3.76/1.01  --prep_def_merge                        true
% 3.76/1.01  --prep_def_merge_prop_impl              false
% 3.76/1.01  --prep_def_merge_mbd                    true
% 3.76/1.01  --prep_def_merge_tr_red                 false
% 3.76/1.01  --prep_def_merge_tr_cl                  false
% 3.76/1.01  --smt_preprocessing                     true
% 3.76/1.01  --smt_ac_axioms                         fast
% 3.76/1.01  --preprocessed_out                      false
% 3.76/1.01  --preprocessed_stats                    false
% 3.76/1.01  
% 3.76/1.01  ------ Abstraction refinement Options
% 3.76/1.01  
% 3.76/1.01  --abstr_ref                             []
% 3.76/1.01  --abstr_ref_prep                        false
% 3.76/1.01  --abstr_ref_until_sat                   false
% 3.76/1.01  --abstr_ref_sig_restrict                funpre
% 3.76/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.76/1.01  --abstr_ref_under                       []
% 3.76/1.01  
% 3.76/1.01  ------ SAT Options
% 3.76/1.01  
% 3.76/1.01  --sat_mode                              false
% 3.76/1.01  --sat_fm_restart_options                ""
% 3.76/1.01  --sat_gr_def                            false
% 3.76/1.01  --sat_epr_types                         true
% 3.76/1.01  --sat_non_cyclic_types                  false
% 3.76/1.01  --sat_finite_models                     false
% 3.76/1.01  --sat_fm_lemmas                         false
% 3.76/1.01  --sat_fm_prep                           false
% 3.76/1.01  --sat_fm_uc_incr                        true
% 3.76/1.01  --sat_out_model                         small
% 3.76/1.01  --sat_out_clauses                       false
% 3.76/1.01  
% 3.76/1.01  ------ QBF Options
% 3.76/1.01  
% 3.76/1.01  --qbf_mode                              false
% 3.76/1.01  --qbf_elim_univ                         false
% 3.76/1.01  --qbf_dom_inst                          none
% 3.76/1.01  --qbf_dom_pre_inst                      false
% 3.76/1.01  --qbf_sk_in                             false
% 3.76/1.01  --qbf_pred_elim                         true
% 3.76/1.01  --qbf_split                             512
% 3.76/1.01  
% 3.76/1.01  ------ BMC1 Options
% 3.76/1.01  
% 3.76/1.01  --bmc1_incremental                      false
% 3.76/1.01  --bmc1_axioms                           reachable_all
% 3.76/1.01  --bmc1_min_bound                        0
% 3.76/1.01  --bmc1_max_bound                        -1
% 3.76/1.01  --bmc1_max_bound_default                -1
% 3.76/1.01  --bmc1_symbol_reachability              true
% 3.76/1.01  --bmc1_property_lemmas                  false
% 3.76/1.01  --bmc1_k_induction                      false
% 3.76/1.01  --bmc1_non_equiv_states                 false
% 3.76/1.01  --bmc1_deadlock                         false
% 3.76/1.01  --bmc1_ucm                              false
% 3.76/1.01  --bmc1_add_unsat_core                   none
% 3.76/1.01  --bmc1_unsat_core_children              false
% 3.76/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.76/1.01  --bmc1_out_stat                         full
% 3.76/1.01  --bmc1_ground_init                      false
% 3.76/1.01  --bmc1_pre_inst_next_state              false
% 3.76/1.01  --bmc1_pre_inst_state                   false
% 3.76/1.01  --bmc1_pre_inst_reach_state             false
% 3.76/1.01  --bmc1_out_unsat_core                   false
% 3.76/1.01  --bmc1_aig_witness_out                  false
% 3.76/1.01  --bmc1_verbose                          false
% 3.76/1.01  --bmc1_dump_clauses_tptp                false
% 3.76/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.76/1.01  --bmc1_dump_file                        -
% 3.76/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.76/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.76/1.01  --bmc1_ucm_extend_mode                  1
% 3.76/1.01  --bmc1_ucm_init_mode                    2
% 3.76/1.01  --bmc1_ucm_cone_mode                    none
% 3.76/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.76/1.01  --bmc1_ucm_relax_model                  4
% 3.76/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.76/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.76/1.01  --bmc1_ucm_layered_model                none
% 3.76/1.01  --bmc1_ucm_max_lemma_size               10
% 3.76/1.01  
% 3.76/1.01  ------ AIG Options
% 3.76/1.01  
% 3.76/1.01  --aig_mode                              false
% 3.76/1.01  
% 3.76/1.01  ------ Instantiation Options
% 3.76/1.01  
% 3.76/1.01  --instantiation_flag                    true
% 3.76/1.01  --inst_sos_flag                         false
% 3.76/1.01  --inst_sos_phase                        true
% 3.76/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.76/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.76/1.01  --inst_lit_sel_side                     num_symb
% 3.76/1.01  --inst_solver_per_active                1400
% 3.76/1.01  --inst_solver_calls_frac                1.
% 3.76/1.01  --inst_passive_queue_type               priority_queues
% 3.76/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.76/1.01  --inst_passive_queues_freq              [25;2]
% 3.76/1.01  --inst_dismatching                      true
% 3.76/1.01  --inst_eager_unprocessed_to_passive     true
% 3.76/1.01  --inst_prop_sim_given                   true
% 3.76/1.01  --inst_prop_sim_new                     false
% 3.76/1.01  --inst_subs_new                         false
% 3.76/1.01  --inst_eq_res_simp                      false
% 3.76/1.01  --inst_subs_given                       false
% 3.76/1.01  --inst_orphan_elimination               true
% 3.76/1.01  --inst_learning_loop_flag               true
% 3.76/1.01  --inst_learning_start                   3000
% 3.76/1.01  --inst_learning_factor                  2
% 3.76/1.01  --inst_start_prop_sim_after_learn       3
% 3.76/1.01  --inst_sel_renew                        solver
% 3.76/1.01  --inst_lit_activity_flag                true
% 3.76/1.01  --inst_restr_to_given                   false
% 3.76/1.01  --inst_activity_threshold               500
% 3.76/1.01  --inst_out_proof                        true
% 3.76/1.01  
% 3.76/1.01  ------ Resolution Options
% 3.76/1.01  
% 3.76/1.01  --resolution_flag                       true
% 3.76/1.01  --res_lit_sel                           adaptive
% 3.76/1.01  --res_lit_sel_side                      none
% 3.76/1.01  --res_ordering                          kbo
% 3.76/1.01  --res_to_prop_solver                    active
% 3.76/1.01  --res_prop_simpl_new                    false
% 3.76/1.01  --res_prop_simpl_given                  true
% 3.76/1.01  --res_passive_queue_type                priority_queues
% 3.76/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.76/1.01  --res_passive_queues_freq               [15;5]
% 3.76/1.01  --res_forward_subs                      full
% 3.76/1.01  --res_backward_subs                     full
% 3.76/1.01  --res_forward_subs_resolution           true
% 3.76/1.01  --res_backward_subs_resolution          true
% 3.76/1.01  --res_orphan_elimination                true
% 3.76/1.01  --res_time_limit                        2.
% 3.76/1.01  --res_out_proof                         true
% 3.76/1.01  
% 3.76/1.01  ------ Superposition Options
% 3.76/1.01  
% 3.76/1.01  --superposition_flag                    true
% 3.76/1.01  --sup_passive_queue_type                priority_queues
% 3.76/1.01  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.76/1.01  --sup_passive_queues_freq               [1;4]
% 3.76/1.01  --demod_completeness_check              fast
% 3.76/1.01  --demod_use_ground                      true
% 3.76/1.01  --sup_to_prop_solver                    passive
% 3.76/1.01  --sup_prop_simpl_new                    true
% 3.76/1.01  --sup_prop_simpl_given                  true
% 3.76/1.01  --sup_fun_splitting                     false
% 3.76/1.01  --sup_smt_interval                      50000
% 3.76/1.01  
% 3.76/1.01  ------ Superposition Simplification Setup
% 3.76/1.01  
% 3.76/1.01  --sup_indices_passive                   []
% 3.76/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.76/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.76/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.76/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.76/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.76/1.01  --sup_full_bw                           [BwDemod]
% 3.76/1.01  --sup_immed_triv                        [TrivRules]
% 3.76/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.76/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.76/1.01  --sup_immed_bw_main                     []
% 3.76/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.76/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.76/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.76/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.76/1.01  
% 3.76/1.01  ------ Combination Options
% 3.76/1.01  
% 3.76/1.01  --comb_res_mult                         3
% 3.76/1.01  --comb_sup_mult                         2
% 3.76/1.01  --comb_inst_mult                        10
% 3.76/1.01  
% 3.76/1.01  ------ Debug Options
% 3.76/1.01  
% 3.76/1.01  --dbg_backtrace                         false
% 3.76/1.01  --dbg_dump_prop_clauses                 false
% 3.76/1.01  --dbg_dump_prop_clauses_file            -
% 3.76/1.01  --dbg_out_stat                          false
% 3.76/1.01  
% 3.76/1.01  
% 3.76/1.01  
% 3.76/1.01  
% 3.76/1.01  ------ Proving...
% 3.76/1.01  
% 3.76/1.01  
% 3.76/1.01  % SZS status Theorem for theBenchmark.p
% 3.76/1.01  
% 3.76/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.76/1.01  
% 3.76/1.01  fof(f9,conjecture,(
% 3.76/1.01    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 3.76/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.76/1.01  
% 3.76/1.01  fof(f10,negated_conjecture,(
% 3.76/1.01    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 3.76/1.01    inference(negated_conjecture,[],[f9])).
% 3.76/1.01  
% 3.76/1.01  fof(f18,plain,(
% 3.76/1.01    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 3.76/1.01    inference(ennf_transformation,[],[f10])).
% 3.76/1.01  
% 3.76/1.01  fof(f19,plain,(
% 3.76/1.01    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 3.76/1.01    inference(flattening,[],[f18])).
% 3.76/1.01  
% 3.76/1.01  fof(f23,plain,(
% 3.76/1.01    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 3.76/1.01    introduced(choice_axiom,[])).
% 3.76/1.01  
% 3.76/1.01  fof(f24,plain,(
% 3.76/1.01    ~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 3.76/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f23])).
% 3.76/1.01  
% 3.76/1.01  fof(f36,plain,(
% 3.76/1.01    v1_relat_1(sK2)),
% 3.76/1.01    inference(cnf_transformation,[],[f24])).
% 3.76/1.01  
% 3.76/1.01  fof(f6,axiom,(
% 3.76/1.01    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1))))),
% 3.76/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.76/1.01  
% 3.76/1.01  fof(f12,plain,(
% 3.76/1.01    ! [X0,X1,X2] : ((k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1)) | ~v2_funct_1(X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.76/1.01    inference(ennf_transformation,[],[f6])).
% 3.76/1.01  
% 3.76/1.01  fof(f13,plain,(
% 3.76/1.01    ! [X0,X1,X2] : (k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.76/1.01    inference(flattening,[],[f12])).
% 3.76/1.01  
% 3.76/1.01  fof(f33,plain,(
% 3.76/1.01    ( ! [X2,X0,X1] : (k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.76/1.01    inference(cnf_transformation,[],[f13])).
% 3.76/1.01  
% 3.76/1.01  fof(f37,plain,(
% 3.76/1.01    v1_funct_1(sK2)),
% 3.76/1.01    inference(cnf_transformation,[],[f24])).
% 3.76/1.01  
% 3.76/1.01  fof(f40,plain,(
% 3.76/1.01    v2_funct_1(sK2)),
% 3.76/1.01    inference(cnf_transformation,[],[f24])).
% 3.76/1.01  
% 3.76/1.01  fof(f38,plain,(
% 3.76/1.01    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 3.76/1.01    inference(cnf_transformation,[],[f24])).
% 3.76/1.01  
% 3.76/1.01  fof(f5,axiom,(
% 3.76/1.01    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.76/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.76/1.01  
% 3.76/1.01  fof(f11,plain,(
% 3.76/1.01    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.76/1.01    inference(ennf_transformation,[],[f5])).
% 3.76/1.01  
% 3.76/1.01  fof(f32,plain,(
% 3.76/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.76/1.01    inference(cnf_transformation,[],[f11])).
% 3.76/1.01  
% 3.76/1.01  fof(f8,axiom,(
% 3.76/1.01    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 3.76/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.76/1.01  
% 3.76/1.01  fof(f16,plain,(
% 3.76/1.01    ! [X0,X1] : ((r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.76/1.01    inference(ennf_transformation,[],[f8])).
% 3.76/1.01  
% 3.76/1.01  fof(f17,plain,(
% 3.76/1.01    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.76/1.01    inference(flattening,[],[f16])).
% 3.76/1.01  
% 3.76/1.01  fof(f35,plain,(
% 3.76/1.01    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.76/1.01    inference(cnf_transformation,[],[f17])).
% 3.76/1.01  
% 3.76/1.01  fof(f39,plain,(
% 3.76/1.01    r1_tarski(sK0,k1_relat_1(sK2))),
% 3.76/1.01    inference(cnf_transformation,[],[f24])).
% 3.76/1.01  
% 3.76/1.01  fof(f7,axiom,(
% 3.76/1.01    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 3.76/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.76/1.01  
% 3.76/1.01  fof(f14,plain,(
% 3.76/1.01    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 3.76/1.01    inference(ennf_transformation,[],[f7])).
% 3.76/1.01  
% 3.76/1.01  fof(f15,plain,(
% 3.76/1.01    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.76/1.01    inference(flattening,[],[f14])).
% 3.76/1.01  
% 3.76/1.01  fof(f34,plain,(
% 3.76/1.01    ( ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.76/1.01    inference(cnf_transformation,[],[f15])).
% 3.76/1.01  
% 3.76/1.01  fof(f1,axiom,(
% 3.76/1.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.76/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.76/1.01  
% 3.76/1.01  fof(f20,plain,(
% 3.76/1.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.76/1.01    inference(nnf_transformation,[],[f1])).
% 3.76/1.01  
% 3.76/1.01  fof(f21,plain,(
% 3.76/1.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.76/1.01    inference(flattening,[],[f20])).
% 3.76/1.01  
% 3.76/1.01  fof(f27,plain,(
% 3.76/1.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.76/1.01    inference(cnf_transformation,[],[f21])).
% 3.76/1.01  
% 3.76/1.01  fof(f4,axiom,(
% 3.76/1.01    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 3.76/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.76/1.01  
% 3.76/1.01  fof(f31,plain,(
% 3.76/1.01    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 3.76/1.01    inference(cnf_transformation,[],[f4])).
% 3.76/1.01  
% 3.76/1.01  fof(f2,axiom,(
% 3.76/1.01    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 3.76/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.76/1.01  
% 3.76/1.01  fof(f22,plain,(
% 3.76/1.01    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 3.76/1.01    inference(nnf_transformation,[],[f2])).
% 3.76/1.01  
% 3.76/1.01  fof(f28,plain,(
% 3.76/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 3.76/1.01    inference(cnf_transformation,[],[f22])).
% 3.76/1.01  
% 3.76/1.01  fof(f3,axiom,(
% 3.76/1.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.76/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.76/1.01  
% 3.76/1.01  fof(f30,plain,(
% 3.76/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.76/1.01    inference(cnf_transformation,[],[f3])).
% 3.76/1.01  
% 3.76/1.01  fof(f43,plain,(
% 3.76/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.76/1.01    inference(definition_unfolding,[],[f28,f30])).
% 3.76/1.01  
% 3.76/1.01  fof(f25,plain,(
% 3.76/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.76/1.01    inference(cnf_transformation,[],[f21])).
% 3.76/1.01  
% 3.76/1.01  fof(f45,plain,(
% 3.76/1.01    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.76/1.01    inference(equality_resolution,[],[f25])).
% 3.76/1.01  
% 3.76/1.01  fof(f29,plain,(
% 3.76/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 3.76/1.01    inference(cnf_transformation,[],[f22])).
% 3.76/1.01  
% 3.76/1.01  fof(f42,plain,(
% 3.76/1.01    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) | ~r1_tarski(X0,X1)) )),
% 3.76/1.01    inference(definition_unfolding,[],[f29,f30])).
% 3.76/1.01  
% 3.76/1.01  fof(f41,plain,(
% 3.76/1.01    ~r1_tarski(sK0,sK1)),
% 3.76/1.01    inference(cnf_transformation,[],[f24])).
% 3.76/1.01  
% 3.76/1.01  cnf(c_15,negated_conjecture,
% 3.76/1.01      ( v1_relat_1(sK2) ),
% 3.76/1.01      inference(cnf_transformation,[],[f36]) ).
% 3.76/1.01  
% 3.76/1.01  cnf(c_640,plain,
% 3.76/1.01      ( v1_relat_1(sK2) = iProver_top ),
% 3.76/1.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.76/1.01  
% 3.76/1.01  cnf(c_7,plain,
% 3.76/1.01      ( ~ v1_relat_1(X0)
% 3.76/1.01      | ~ v1_funct_1(X0)
% 3.76/1.01      | ~ v2_funct_1(X0)
% 3.76/1.01      | k3_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k3_xboole_0(X1,X2)) ),
% 3.76/1.01      inference(cnf_transformation,[],[f33]) ).
% 3.76/1.01  
% 3.76/1.01  cnf(c_648,plain,
% 3.76/1.01      ( k3_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k3_xboole_0(X1,X2))
% 3.76/1.01      | v1_relat_1(X0) != iProver_top
% 3.76/1.01      | v1_funct_1(X0) != iProver_top
% 3.76/1.01      | v2_funct_1(X0) != iProver_top ),
% 3.76/1.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.76/1.01  
% 3.76/1.01  cnf(c_1535,plain,
% 3.76/1.01      ( k3_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) = k9_relat_1(sK2,k3_xboole_0(X0,X1))
% 3.76/1.01      | v1_funct_1(sK2) != iProver_top
% 3.76/1.01      | v2_funct_1(sK2) != iProver_top ),
% 3.76/1.01      inference(superposition,[status(thm)],[c_640,c_648]) ).
% 3.76/1.01  
% 3.76/1.01  cnf(c_14,negated_conjecture,
% 3.76/1.01      ( v1_funct_1(sK2) ),
% 3.76/1.01      inference(cnf_transformation,[],[f37]) ).
% 3.76/1.01  
% 3.76/1.01  cnf(c_17,plain,
% 3.76/1.01      ( v1_funct_1(sK2) = iProver_top ),
% 3.76/1.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.76/1.01  
% 3.76/1.01  cnf(c_11,negated_conjecture,
% 3.76/1.01      ( v2_funct_1(sK2) ),
% 3.76/1.01      inference(cnf_transformation,[],[f40]) ).
% 3.76/1.01  
% 3.76/1.01  cnf(c_20,plain,
% 3.76/1.01      ( v2_funct_1(sK2) = iProver_top ),
% 3.76/1.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.76/1.01  
% 3.76/1.01  cnf(c_3137,plain,
% 3.76/1.01      ( k3_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) = k9_relat_1(sK2,k3_xboole_0(X0,X1)) ),
% 3.76/1.01      inference(global_propositional_subsumption,
% 3.76/1.01                [status(thm)],
% 3.76/1.01                [c_1535,c_17,c_20]) ).
% 3.76/1.01  
% 3.76/1.01  cnf(c_13,negated_conjecture,
% 3.76/1.01      ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
% 3.76/1.01      inference(cnf_transformation,[],[f38]) ).
% 3.76/1.01  
% 3.76/1.01  cnf(c_642,plain,
% 3.76/1.01      ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) = iProver_top ),
% 3.76/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.76/1.01  
% 3.76/1.01  cnf(c_6,plain,
% 3.76/1.01      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 3.76/1.01      inference(cnf_transformation,[],[f32]) ).
% 3.76/1.01  
% 3.76/1.01  cnf(c_649,plain,
% 3.76/1.01      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 3.76/1.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.76/1.01  
% 3.76/1.01  cnf(c_1046,plain,
% 3.76/1.01      ( k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) = k9_relat_1(sK2,sK0) ),
% 3.76/1.01      inference(superposition,[status(thm)],[c_642,c_649]) ).
% 3.76/1.01  
% 3.76/1.01  cnf(c_3148,plain,
% 3.76/1.01      ( k9_relat_1(sK2,k3_xboole_0(sK0,sK1)) = k9_relat_1(sK2,sK0) ),
% 3.76/1.01      inference(superposition,[status(thm)],[c_3137,c_1046]) ).
% 3.76/1.01  
% 3.76/1.01  cnf(c_9,plain,
% 3.76/1.01      ( r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1)
% 3.76/1.01      | ~ v1_relat_1(X0)
% 3.76/1.01      | ~ v1_funct_1(X0)
% 3.76/1.01      | ~ v2_funct_1(X0) ),
% 3.76/1.01      inference(cnf_transformation,[],[f35]) ).
% 3.76/1.01  
% 3.76/1.01  cnf(c_646,plain,
% 3.76/1.01      ( r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1) = iProver_top
% 3.76/1.01      | v1_relat_1(X0) != iProver_top
% 3.76/1.01      | v1_funct_1(X0) != iProver_top
% 3.76/1.01      | v2_funct_1(X0) != iProver_top ),
% 3.76/1.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.76/1.01  
% 3.76/1.01  cnf(c_5091,plain,
% 3.76/1.01      ( r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k3_xboole_0(sK0,sK1)) = iProver_top
% 3.76/1.01      | v1_relat_1(sK2) != iProver_top
% 3.76/1.01      | v1_funct_1(sK2) != iProver_top
% 3.76/1.01      | v2_funct_1(sK2) != iProver_top ),
% 3.76/1.01      inference(superposition,[status(thm)],[c_3148,c_646]) ).
% 3.76/1.01  
% 3.76/1.01  cnf(c_12,negated_conjecture,
% 3.76/1.01      ( r1_tarski(sK0,k1_relat_1(sK2)) ),
% 3.76/1.01      inference(cnf_transformation,[],[f39]) ).
% 3.76/1.01  
% 3.76/1.01  cnf(c_643,plain,
% 3.76/1.01      ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top ),
% 3.76/1.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.76/1.01  
% 3.76/1.01  cnf(c_8,plain,
% 3.76/1.01      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
% 3.76/1.01      | ~ r1_tarski(X0,k1_relat_1(X1))
% 3.76/1.01      | ~ v1_relat_1(X1) ),
% 3.76/1.01      inference(cnf_transformation,[],[f34]) ).
% 3.76/1.01  
% 3.76/1.01  cnf(c_647,plain,
% 3.76/1.01      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) = iProver_top
% 3.76/1.01      | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
% 3.76/1.01      | v1_relat_1(X1) != iProver_top ),
% 3.76/1.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.76/1.01  
% 3.76/1.01  cnf(c_0,plain,
% 3.76/1.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.76/1.01      inference(cnf_transformation,[],[f27]) ).
% 3.76/1.01  
% 3.76/1.01  cnf(c_654,plain,
% 3.76/1.01      ( X0 = X1
% 3.76/1.01      | r1_tarski(X0,X1) != iProver_top
% 3.76/1.01      | r1_tarski(X1,X0) != iProver_top ),
% 3.76/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.76/1.01  
% 3.76/1.01  cnf(c_1369,plain,
% 3.76/1.01      ( k10_relat_1(X0,k9_relat_1(X0,X1)) = X1
% 3.76/1.01      | r1_tarski(X1,k10_relat_1(X0,k9_relat_1(X0,X1))) != iProver_top
% 3.76/1.01      | v1_relat_1(X0) != iProver_top
% 3.76/1.01      | v1_funct_1(X0) != iProver_top
% 3.76/1.01      | v2_funct_1(X0) != iProver_top ),
% 3.76/1.01      inference(superposition,[status(thm)],[c_646,c_654]) ).
% 3.76/1.01  
% 3.76/1.01  cnf(c_2984,plain,
% 3.76/1.01      ( k10_relat_1(X0,k9_relat_1(X0,X1)) = X1
% 3.76/1.01      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 3.76/1.01      | v1_relat_1(X0) != iProver_top
% 3.76/1.01      | v1_funct_1(X0) != iProver_top
% 3.76/1.01      | v2_funct_1(X0) != iProver_top ),
% 3.76/1.01      inference(superposition,[status(thm)],[c_647,c_1369]) ).
% 3.76/1.01  
% 3.76/1.01  cnf(c_3769,plain,
% 3.76/1.01      ( k10_relat_1(sK2,k9_relat_1(sK2,sK0)) = sK0
% 3.76/1.01      | v1_relat_1(sK2) != iProver_top
% 3.76/1.01      | v1_funct_1(sK2) != iProver_top
% 3.76/1.01      | v2_funct_1(sK2) != iProver_top ),
% 3.76/1.01      inference(superposition,[status(thm)],[c_643,c_2984]) ).
% 3.76/1.01  
% 3.76/1.01  cnf(c_801,plain,
% 3.76/1.01      ( r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0)))
% 3.76/1.01      | ~ r1_tarski(sK0,k1_relat_1(sK2))
% 3.76/1.01      | ~ v1_relat_1(sK2) ),
% 3.76/1.01      inference(instantiation,[status(thm)],[c_8]) ).
% 3.76/1.01  
% 3.76/1.01  cnf(c_1304,plain,
% 3.76/1.01      ( r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),sK0)
% 3.76/1.01      | ~ v1_relat_1(sK2)
% 3.76/1.01      | ~ v1_funct_1(sK2)
% 3.76/1.01      | ~ v2_funct_1(sK2) ),
% 3.76/1.01      inference(instantiation,[status(thm)],[c_9]) ).
% 3.76/1.01  
% 3.76/1.01  cnf(c_1273,plain,
% 3.76/1.01      ( ~ r1_tarski(X0,sK0) | ~ r1_tarski(sK0,X0) | X0 = sK0 ),
% 3.76/1.01      inference(instantiation,[status(thm)],[c_0]) ).
% 3.76/1.01  
% 3.76/1.01  cnf(c_1612,plain,
% 3.76/1.01      ( ~ r1_tarski(k10_relat_1(X0,k9_relat_1(X0,sK0)),sK0)
% 3.76/1.01      | ~ r1_tarski(sK0,k10_relat_1(X0,k9_relat_1(X0,sK0)))
% 3.76/1.01      | k10_relat_1(X0,k9_relat_1(X0,sK0)) = sK0 ),
% 3.76/1.01      inference(instantiation,[status(thm)],[c_1273]) ).
% 3.76/1.01  
% 3.76/1.01  cnf(c_1615,plain,
% 3.76/1.01      ( ~ r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),sK0)
% 3.76/1.01      | ~ r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0)))
% 3.76/1.01      | k10_relat_1(sK2,k9_relat_1(sK2,sK0)) = sK0 ),
% 3.76/1.01      inference(instantiation,[status(thm)],[c_1612]) ).
% 3.76/1.01  
% 3.76/1.01  cnf(c_4052,plain,
% 3.76/1.01      ( k10_relat_1(sK2,k9_relat_1(sK2,sK0)) = sK0 ),
% 3.76/1.01      inference(global_propositional_subsumption,
% 3.76/1.01                [status(thm)],
% 3.76/1.01                [c_3769,c_15,c_14,c_12,c_11,c_801,c_1304,c_1615]) ).
% 3.76/1.01  
% 3.76/1.01  cnf(c_5123,plain,
% 3.76/1.01      ( r1_tarski(sK0,k3_xboole_0(sK0,sK1)) = iProver_top
% 3.76/1.01      | v1_relat_1(sK2) != iProver_top
% 3.76/1.01      | v1_funct_1(sK2) != iProver_top
% 3.76/1.01      | v2_funct_1(sK2) != iProver_top ),
% 3.76/1.01      inference(light_normalisation,[status(thm)],[c_5091,c_4052]) ).
% 3.76/1.01  
% 3.76/1.01  cnf(c_16,plain,
% 3.76/1.01      ( v1_relat_1(sK2) = iProver_top ),
% 3.76/1.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.76/1.01  
% 3.76/1.01  cnf(c_5687,plain,
% 3.76/1.01      ( r1_tarski(sK0,k3_xboole_0(sK0,sK1)) = iProver_top ),
% 3.76/1.01      inference(global_propositional_subsumption,
% 3.76/1.01                [status(thm)],
% 3.76/1.01                [c_5123,c_16,c_17,c_20]) ).
% 3.76/1.01  
% 3.76/1.01  cnf(c_5,plain,
% 3.76/1.01      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 3.76/1.01      inference(cnf_transformation,[],[f31]) ).
% 3.76/1.01  
% 3.76/1.01  cnf(c_650,plain,
% 3.76/1.01      ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
% 3.76/1.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.76/1.01  
% 3.76/1.01  cnf(c_1368,plain,
% 3.76/1.01      ( k3_xboole_0(X0,X1) = X0
% 3.76/1.01      | r1_tarski(X0,k3_xboole_0(X0,X1)) != iProver_top ),
% 3.76/1.01      inference(superposition,[status(thm)],[c_650,c_654]) ).
% 3.76/1.01  
% 3.76/1.01  cnf(c_5695,plain,
% 3.76/1.01      ( k3_xboole_0(sK0,sK1) = sK0 ),
% 3.76/1.01      inference(superposition,[status(thm)],[c_5687,c_1368]) ).
% 3.76/1.01  
% 3.76/1.01  cnf(c_4,plain,
% 3.76/1.01      ( r1_tarski(X0,X1)
% 3.76/1.01      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
% 3.76/1.01      inference(cnf_transformation,[],[f43]) ).
% 3.76/1.01  
% 3.76/1.01  cnf(c_651,plain,
% 3.76/1.01      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0
% 3.76/1.01      | r1_tarski(X0,X1) = iProver_top ),
% 3.76/1.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.76/1.01  
% 3.76/1.01  cnf(c_5713,plain,
% 3.76/1.01      ( k5_xboole_0(sK0,sK0) != k1_xboole_0
% 3.76/1.01      | r1_tarski(sK0,sK1) = iProver_top ),
% 3.76/1.01      inference(superposition,[status(thm)],[c_5695,c_651]) ).
% 3.76/1.01  
% 3.76/1.01  cnf(c_2,plain,
% 3.76/1.01      ( r1_tarski(X0,X0) ),
% 3.76/1.01      inference(cnf_transformation,[],[f45]) ).
% 3.76/1.01  
% 3.76/1.01  cnf(c_653,plain,
% 3.76/1.01      ( r1_tarski(X0,X0) = iProver_top ),
% 3.76/1.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.76/1.01  
% 3.76/1.01  cnf(c_3,plain,
% 3.76/1.01      ( ~ r1_tarski(X0,X1)
% 3.76/1.01      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
% 3.76/1.01      inference(cnf_transformation,[],[f42]) ).
% 3.76/1.01  
% 3.76/1.01  cnf(c_652,plain,
% 3.76/1.01      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
% 3.76/1.01      | r1_tarski(X0,X1) != iProver_top ),
% 3.76/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.76/1.01  
% 3.76/1.01  cnf(c_1220,plain,
% 3.76/1.01      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
% 3.76/1.01      inference(superposition,[status(thm)],[c_653,c_652]) ).
% 3.76/1.01  
% 3.76/1.01  cnf(c_1043,plain,
% 3.76/1.01      ( k3_xboole_0(X0,X0) = X0 ),
% 3.76/1.01      inference(superposition,[status(thm)],[c_653,c_649]) ).
% 3.76/1.01  
% 3.76/1.01  cnf(c_1680,plain,
% 3.76/1.01      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.76/1.01      inference(light_normalisation,[status(thm)],[c_1220,c_1043]) ).
% 3.76/1.01  
% 3.76/1.01  cnf(c_5717,plain,
% 3.76/1.01      ( k1_xboole_0 != k1_xboole_0 | r1_tarski(sK0,sK1) = iProver_top ),
% 3.76/1.01      inference(demodulation,[status(thm)],[c_5713,c_1680]) ).
% 3.76/1.01  
% 3.76/1.01  cnf(c_5718,plain,
% 3.76/1.01      ( r1_tarski(sK0,sK1) = iProver_top ),
% 3.76/1.01      inference(equality_resolution_simp,[status(thm)],[c_5717]) ).
% 3.76/1.01  
% 3.76/1.01  cnf(c_10,negated_conjecture,
% 3.76/1.01      ( ~ r1_tarski(sK0,sK1) ),
% 3.76/1.01      inference(cnf_transformation,[],[f41]) ).
% 3.76/1.01  
% 3.76/1.01  cnf(c_21,plain,
% 3.76/1.01      ( r1_tarski(sK0,sK1) != iProver_top ),
% 3.76/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.76/1.01  
% 3.76/1.01  cnf(contradiction,plain,
% 3.76/1.01      ( $false ),
% 3.76/1.01      inference(minisat,[status(thm)],[c_5718,c_21]) ).
% 3.76/1.01  
% 3.76/1.01  
% 3.76/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.76/1.01  
% 3.76/1.01  ------                               Statistics
% 3.76/1.01  
% 3.76/1.01  ------ Selected
% 3.76/1.01  
% 3.76/1.01  total_time:                             0.183
% 3.76/1.01  
%------------------------------------------------------------------------------
