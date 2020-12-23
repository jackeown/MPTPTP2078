%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:52:11 EST 2020

% Result     : Theorem 15.84s
% Output     : CNFRefutation 15.84s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 211 expanded)
%              Number of clauses        :   61 (  76 expanded)
%              Number of leaves         :   14 (  42 expanded)
%              Depth                    :   16
%              Number of atoms          :  249 ( 686 expanded)
%              Number of equality atoms :  109 ( 164 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_tarski(X0,k1_relat_1(X2))
          & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( v2_funct_1(X2)
            & r1_tarski(X0,k1_relat_1(X2))
            & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f30,plain,
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

fof(f31,plain,
    ( ~ r1_tarski(sK0,sK1)
    & v2_funct_1(sK2)
    & r1_tarski(sK0,k1_relat_1(sK2))
    & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f30])).

fof(f47,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f48,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f51,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f49,plain,(
    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k6_subset_1(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f36,f43])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f27])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f57,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f33])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f50,plain,(
    r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f31])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f55,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(definition_unfolding,[],[f39,f43])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f35,f43])).

fof(f6,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f40,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f52,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_19,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_774,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k6_subset_1(X1,X2)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_782,plain,
    ( k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k6_subset_1(X1,X2))
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3865,plain,
    ( k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) = k9_relat_1(sK2,k6_subset_1(X0,X1))
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_774,c_782])).

cnf(c_18,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_21,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_15,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_24,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4480,plain,
    ( k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) = k9_relat_1(sK2,k6_subset_1(X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3865,c_21,c_24])).

cnf(c_17,negated_conjecture,
    ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_776,plain,
    ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k6_subset_1(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_790,plain,
    ( k6_subset_1(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2410,plain,
    ( k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_776,c_790])).

cnf(c_4492,plain,
    ( k9_relat_1(sK2,k6_subset_1(sK0,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4480,c_2410])).

cnf(c_13,plain,
    ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_780,plain,
    ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) = iProver_top
    | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4522,plain,
    ( r1_tarski(k6_subset_1(sK0,sK1),k10_relat_1(sK2,k1_xboole_0)) = iProver_top
    | r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4492,c_780])).

cnf(c_20,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_74911,plain,
    ( r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2)) != iProver_top
    | r1_tarski(k6_subset_1(sK0,sK1),k10_relat_1(sK2,k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4522,c_20])).

cnf(c_74912,plain,
    ( r1_tarski(k6_subset_1(sK0,sK1),k10_relat_1(sK2,k1_xboole_0)) = iProver_top
    | r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_74911])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_791,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2405,plain,
    ( k6_subset_1(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_791,c_790])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k6_subset_1(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k6_subset_1(X1,X2)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_781,plain,
    ( k6_subset_1(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k6_subset_1(X1,X2))
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2175,plain,
    ( k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k6_subset_1(X0,X1))
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_774,c_781])).

cnf(c_3461,plain,
    ( k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k6_subset_1(X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2175,c_21])).

cnf(c_3875,plain,
    ( k10_relat_1(sK2,k6_subset_1(X0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2405,c_3461])).

cnf(c_3876,plain,
    ( k10_relat_1(sK2,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3875,c_2405])).

cnf(c_74915,plain,
    ( r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2)) != iProver_top
    | r1_tarski(k6_subset_1(sK0,sK1),k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_74912,c_3876])).

cnf(c_16,negated_conjecture,
    ( r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_777,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_7,plain,
    ( r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_786,plain,
    ( r1_tarski(k6_subset_1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_787,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1439,plain,
    ( k2_xboole_0(k6_subset_1(X0,X1),X0) = X0 ),
    inference(superposition,[status(thm)],[c_786,c_787])).

cnf(c_5,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_788,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2442,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k6_subset_1(X0,X2),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1439,c_788])).

cnf(c_12188,plain,
    ( k6_subset_1(k6_subset_1(X0,X1),X2) = k1_xboole_0
    | r1_tarski(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2442,c_790])).

cnf(c_66135,plain,
    ( k6_subset_1(k6_subset_1(sK0,X0),k1_relat_1(sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_777,c_12188])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | k6_subset_1(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_789,plain,
    ( k6_subset_1(X0,X1) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_66613,plain,
    ( r1_tarski(k6_subset_1(sK0,X0),k1_relat_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_66135,c_789])).

cnf(c_74918,plain,
    ( r1_tarski(k6_subset_1(sK0,sK1),k1_xboole_0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_74915,c_66613])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_966,plain,
    ( ~ r1_tarski(k6_subset_1(X0,X1),k1_xboole_0)
    | k1_xboole_0 = k6_subset_1(X0,X1) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_5272,plain,
    ( ~ r1_tarski(k6_subset_1(sK0,sK1),k1_xboole_0)
    | k1_xboole_0 = k6_subset_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_966])).

cnf(c_5273,plain,
    ( k1_xboole_0 = k6_subset_1(sK0,sK1)
    | r1_tarski(k6_subset_1(sK0,sK1),k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5272])).

cnf(c_344,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2697,plain,
    ( k6_subset_1(sK0,sK1) = k6_subset_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_344])).

cnf(c_345,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1077,plain,
    ( k6_subset_1(sK0,sK1) != X0
    | k6_subset_1(sK0,sK1) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_345])).

cnf(c_2074,plain,
    ( k6_subset_1(sK0,sK1) != k6_subset_1(X0,X1)
    | k6_subset_1(sK0,sK1) = k1_xboole_0
    | k1_xboole_0 != k6_subset_1(X0,X1) ),
    inference(instantiation,[status(thm)],[c_1077])).

cnf(c_2696,plain,
    ( k6_subset_1(sK0,sK1) != k6_subset_1(sK0,sK1)
    | k6_subset_1(sK0,sK1) = k1_xboole_0
    | k1_xboole_0 != k6_subset_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_2074])).

cnf(c_952,plain,
    ( r1_tarski(sK0,sK1)
    | k6_subset_1(sK0,sK1) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_14,negated_conjecture,
    ( ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f52])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_74918,c_5273,c_2697,c_2696,c_952,c_14])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:48:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 15.84/2.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.84/2.49  
% 15.84/2.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.84/2.49  
% 15.84/2.49  ------  iProver source info
% 15.84/2.49  
% 15.84/2.49  git: date: 2020-06-30 10:37:57 +0100
% 15.84/2.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.84/2.49  git: non_committed_changes: false
% 15.84/2.49  git: last_make_outside_of_git: false
% 15.84/2.49  
% 15.84/2.49  ------ 
% 15.84/2.49  ------ Parsing...
% 15.84/2.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.84/2.49  
% 15.84/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 15.84/2.49  
% 15.84/2.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.84/2.49  
% 15.84/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.84/2.49  ------ Proving...
% 15.84/2.49  ------ Problem Properties 
% 15.84/2.49  
% 15.84/2.49  
% 15.84/2.49  clauses                                 19
% 15.84/2.49  conjectures                             6
% 15.84/2.49  EPR                                     7
% 15.84/2.49  Horn                                    19
% 15.84/2.49  unary                                   9
% 15.84/2.49  binary                                  6
% 15.84/2.49  lits                                    34
% 15.84/2.49  lits eq                                 7
% 15.84/2.49  fd_pure                                 0
% 15.84/2.49  fd_pseudo                               0
% 15.84/2.49  fd_cond                                 1
% 15.84/2.49  fd_pseudo_cond                          1
% 15.84/2.49  AC symbols                              0
% 15.84/2.49  
% 15.84/2.49  ------ Input Options Time Limit: Unbounded
% 15.84/2.49  
% 15.84/2.49  
% 15.84/2.49  ------ 
% 15.84/2.49  Current options:
% 15.84/2.49  ------ 
% 15.84/2.49  
% 15.84/2.49  
% 15.84/2.49  
% 15.84/2.49  
% 15.84/2.49  ------ Proving...
% 15.84/2.49  
% 15.84/2.49  
% 15.84/2.49  % SZS status Theorem for theBenchmark.p
% 15.84/2.49  
% 15.84/2.49  % SZS output start CNFRefutation for theBenchmark.p
% 15.84/2.49  
% 15.84/2.49  fof(f13,conjecture,(
% 15.84/2.49    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 15.84/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.84/2.49  
% 15.84/2.49  fof(f14,negated_conjecture,(
% 15.84/2.49    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 15.84/2.49    inference(negated_conjecture,[],[f13])).
% 15.84/2.49  
% 15.84/2.49  fof(f25,plain,(
% 15.84/2.49    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 15.84/2.49    inference(ennf_transformation,[],[f14])).
% 15.84/2.49  
% 15.84/2.49  fof(f26,plain,(
% 15.84/2.49    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 15.84/2.49    inference(flattening,[],[f25])).
% 15.84/2.49  
% 15.84/2.49  fof(f30,plain,(
% 15.84/2.49    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 15.84/2.49    introduced(choice_axiom,[])).
% 15.84/2.49  
% 15.84/2.49  fof(f31,plain,(
% 15.84/2.49    ~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 15.84/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f30])).
% 15.84/2.49  
% 15.84/2.49  fof(f47,plain,(
% 15.84/2.49    v1_relat_1(sK2)),
% 15.84/2.49    inference(cnf_transformation,[],[f31])).
% 15.84/2.49  
% 15.84/2.49  fof(f10,axiom,(
% 15.84/2.49    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1))))),
% 15.84/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.84/2.49  
% 15.84/2.49  fof(f19,plain,(
% 15.84/2.49    ! [X0,X1,X2] : ((k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1)) | ~v2_funct_1(X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 15.84/2.49    inference(ennf_transformation,[],[f10])).
% 15.84/2.49  
% 15.84/2.49  fof(f20,plain,(
% 15.84/2.49    ! [X0,X1,X2] : (k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 15.84/2.49    inference(flattening,[],[f19])).
% 15.84/2.49  
% 15.84/2.49  fof(f44,plain,(
% 15.84/2.49    ( ! [X2,X0,X1] : (k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 15.84/2.49    inference(cnf_transformation,[],[f20])).
% 15.84/2.49  
% 15.84/2.49  fof(f48,plain,(
% 15.84/2.49    v1_funct_1(sK2)),
% 15.84/2.49    inference(cnf_transformation,[],[f31])).
% 15.84/2.49  
% 15.84/2.49  fof(f51,plain,(
% 15.84/2.49    v2_funct_1(sK2)),
% 15.84/2.49    inference(cnf_transformation,[],[f31])).
% 15.84/2.49  
% 15.84/2.49  fof(f49,plain,(
% 15.84/2.49    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 15.84/2.49    inference(cnf_transformation,[],[f31])).
% 15.84/2.49  
% 15.84/2.49  fof(f2,axiom,(
% 15.84/2.49    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 15.84/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.84/2.49  
% 15.84/2.49  fof(f29,plain,(
% 15.84/2.49    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 15.84/2.49    inference(nnf_transformation,[],[f2])).
% 15.84/2.49  
% 15.84/2.49  fof(f36,plain,(
% 15.84/2.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 15.84/2.49    inference(cnf_transformation,[],[f29])).
% 15.84/2.49  
% 15.84/2.49  fof(f9,axiom,(
% 15.84/2.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 15.84/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.84/2.49  
% 15.84/2.49  fof(f43,plain,(
% 15.84/2.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 15.84/2.49    inference(cnf_transformation,[],[f9])).
% 15.84/2.49  
% 15.84/2.49  fof(f53,plain,(
% 15.84/2.49    ( ! [X0,X1] : (k1_xboole_0 = k6_subset_1(X0,X1) | ~r1_tarski(X0,X1)) )),
% 15.84/2.49    inference(definition_unfolding,[],[f36,f43])).
% 15.84/2.49  
% 15.84/2.49  fof(f12,axiom,(
% 15.84/2.49    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 15.84/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.84/2.49  
% 15.84/2.49  fof(f23,plain,(
% 15.84/2.49    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 15.84/2.49    inference(ennf_transformation,[],[f12])).
% 15.84/2.49  
% 15.84/2.49  fof(f24,plain,(
% 15.84/2.49    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 15.84/2.49    inference(flattening,[],[f23])).
% 15.84/2.49  
% 15.84/2.49  fof(f46,plain,(
% 15.84/2.49    ( ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 15.84/2.49    inference(cnf_transformation,[],[f24])).
% 15.84/2.49  
% 15.84/2.49  fof(f1,axiom,(
% 15.84/2.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 15.84/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.84/2.49  
% 15.84/2.49  fof(f27,plain,(
% 15.84/2.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.84/2.49    inference(nnf_transformation,[],[f1])).
% 15.84/2.49  
% 15.84/2.49  fof(f28,plain,(
% 15.84/2.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.84/2.49    inference(flattening,[],[f27])).
% 15.84/2.49  
% 15.84/2.49  fof(f33,plain,(
% 15.84/2.49    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 15.84/2.49    inference(cnf_transformation,[],[f28])).
% 15.84/2.49  
% 15.84/2.49  fof(f57,plain,(
% 15.84/2.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 15.84/2.49    inference(equality_resolution,[],[f33])).
% 15.84/2.49  
% 15.84/2.49  fof(f11,axiom,(
% 15.84/2.49    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1)))),
% 15.84/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.84/2.49  
% 15.84/2.49  fof(f21,plain,(
% 15.84/2.49    ! [X0,X1,X2] : (k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 15.84/2.49    inference(ennf_transformation,[],[f11])).
% 15.84/2.49  
% 15.84/2.49  fof(f22,plain,(
% 15.84/2.49    ! [X0,X1,X2] : (k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 15.84/2.49    inference(flattening,[],[f21])).
% 15.84/2.49  
% 15.84/2.49  fof(f45,plain,(
% 15.84/2.49    ( ! [X2,X0,X1] : (k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 15.84/2.49    inference(cnf_transformation,[],[f22])).
% 15.84/2.49  
% 15.84/2.49  fof(f50,plain,(
% 15.84/2.49    r1_tarski(sK0,k1_relat_1(sK2))),
% 15.84/2.49    inference(cnf_transformation,[],[f31])).
% 15.84/2.49  
% 15.84/2.49  fof(f5,axiom,(
% 15.84/2.49    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 15.84/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.84/2.49  
% 15.84/2.49  fof(f39,plain,(
% 15.84/2.49    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 15.84/2.49    inference(cnf_transformation,[],[f5])).
% 15.84/2.49  
% 15.84/2.49  fof(f55,plain,(
% 15.84/2.49    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 15.84/2.49    inference(definition_unfolding,[],[f39,f43])).
% 15.84/2.49  
% 15.84/2.49  fof(f4,axiom,(
% 15.84/2.49    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 15.84/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.84/2.49  
% 15.84/2.49  fof(f16,plain,(
% 15.84/2.49    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 15.84/2.49    inference(ennf_transformation,[],[f4])).
% 15.84/2.49  
% 15.84/2.49  fof(f38,plain,(
% 15.84/2.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 15.84/2.49    inference(cnf_transformation,[],[f16])).
% 15.84/2.49  
% 15.84/2.49  fof(f3,axiom,(
% 15.84/2.49    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 15.84/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.84/2.49  
% 15.84/2.49  fof(f15,plain,(
% 15.84/2.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 15.84/2.49    inference(ennf_transformation,[],[f3])).
% 15.84/2.49  
% 15.84/2.49  fof(f37,plain,(
% 15.84/2.49    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 15.84/2.49    inference(cnf_transformation,[],[f15])).
% 15.84/2.49  
% 15.84/2.49  fof(f35,plain,(
% 15.84/2.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 15.84/2.49    inference(cnf_transformation,[],[f29])).
% 15.84/2.49  
% 15.84/2.49  fof(f54,plain,(
% 15.84/2.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k6_subset_1(X0,X1)) )),
% 15.84/2.49    inference(definition_unfolding,[],[f35,f43])).
% 15.84/2.49  
% 15.84/2.49  fof(f6,axiom,(
% 15.84/2.49    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 15.84/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.84/2.49  
% 15.84/2.49  fof(f17,plain,(
% 15.84/2.49    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 15.84/2.49    inference(ennf_transformation,[],[f6])).
% 15.84/2.49  
% 15.84/2.49  fof(f40,plain,(
% 15.84/2.49    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 15.84/2.49    inference(cnf_transformation,[],[f17])).
% 15.84/2.49  
% 15.84/2.49  fof(f52,plain,(
% 15.84/2.49    ~r1_tarski(sK0,sK1)),
% 15.84/2.49    inference(cnf_transformation,[],[f31])).
% 15.84/2.49  
% 15.84/2.49  cnf(c_19,negated_conjecture,
% 15.84/2.49      ( v1_relat_1(sK2) ),
% 15.84/2.49      inference(cnf_transformation,[],[f47]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_774,plain,
% 15.84/2.49      ( v1_relat_1(sK2) = iProver_top ),
% 15.84/2.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_11,plain,
% 15.84/2.49      ( ~ v1_relat_1(X0)
% 15.84/2.49      | ~ v1_funct_1(X0)
% 15.84/2.49      | ~ v2_funct_1(X0)
% 15.84/2.49      | k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k6_subset_1(X1,X2)) ),
% 15.84/2.49      inference(cnf_transformation,[],[f44]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_782,plain,
% 15.84/2.49      ( k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k6_subset_1(X1,X2))
% 15.84/2.49      | v1_relat_1(X0) != iProver_top
% 15.84/2.49      | v1_funct_1(X0) != iProver_top
% 15.84/2.49      | v2_funct_1(X0) != iProver_top ),
% 15.84/2.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_3865,plain,
% 15.84/2.49      ( k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) = k9_relat_1(sK2,k6_subset_1(X0,X1))
% 15.84/2.49      | v1_funct_1(sK2) != iProver_top
% 15.84/2.49      | v2_funct_1(sK2) != iProver_top ),
% 15.84/2.49      inference(superposition,[status(thm)],[c_774,c_782]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_18,negated_conjecture,
% 15.84/2.49      ( v1_funct_1(sK2) ),
% 15.84/2.49      inference(cnf_transformation,[],[f48]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_21,plain,
% 15.84/2.49      ( v1_funct_1(sK2) = iProver_top ),
% 15.84/2.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_15,negated_conjecture,
% 15.84/2.49      ( v2_funct_1(sK2) ),
% 15.84/2.49      inference(cnf_transformation,[],[f51]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_24,plain,
% 15.84/2.49      ( v2_funct_1(sK2) = iProver_top ),
% 15.84/2.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_4480,plain,
% 15.84/2.49      ( k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) = k9_relat_1(sK2,k6_subset_1(X0,X1)) ),
% 15.84/2.49      inference(global_propositional_subsumption,
% 15.84/2.49                [status(thm)],
% 15.84/2.49                [c_3865,c_21,c_24]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_17,negated_conjecture,
% 15.84/2.49      ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
% 15.84/2.49      inference(cnf_transformation,[],[f49]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_776,plain,
% 15.84/2.49      ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) = iProver_top ),
% 15.84/2.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_3,plain,
% 15.84/2.49      ( ~ r1_tarski(X0,X1) | k6_subset_1(X0,X1) = k1_xboole_0 ),
% 15.84/2.49      inference(cnf_transformation,[],[f53]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_790,plain,
% 15.84/2.49      ( k6_subset_1(X0,X1) = k1_xboole_0
% 15.84/2.49      | r1_tarski(X0,X1) != iProver_top ),
% 15.84/2.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_2410,plain,
% 15.84/2.49      ( k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) = k1_xboole_0 ),
% 15.84/2.49      inference(superposition,[status(thm)],[c_776,c_790]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_4492,plain,
% 15.84/2.49      ( k9_relat_1(sK2,k6_subset_1(sK0,sK1)) = k1_xboole_0 ),
% 15.84/2.49      inference(superposition,[status(thm)],[c_4480,c_2410]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_13,plain,
% 15.84/2.49      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
% 15.84/2.49      | ~ r1_tarski(X0,k1_relat_1(X1))
% 15.84/2.49      | ~ v1_relat_1(X1) ),
% 15.84/2.49      inference(cnf_transformation,[],[f46]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_780,plain,
% 15.84/2.49      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) = iProver_top
% 15.84/2.49      | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
% 15.84/2.49      | v1_relat_1(X1) != iProver_top ),
% 15.84/2.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_4522,plain,
% 15.84/2.49      ( r1_tarski(k6_subset_1(sK0,sK1),k10_relat_1(sK2,k1_xboole_0)) = iProver_top
% 15.84/2.49      | r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2)) != iProver_top
% 15.84/2.49      | v1_relat_1(sK2) != iProver_top ),
% 15.84/2.49      inference(superposition,[status(thm)],[c_4492,c_780]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_20,plain,
% 15.84/2.49      ( v1_relat_1(sK2) = iProver_top ),
% 15.84/2.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_74911,plain,
% 15.84/2.49      ( r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2)) != iProver_top
% 15.84/2.49      | r1_tarski(k6_subset_1(sK0,sK1),k10_relat_1(sK2,k1_xboole_0)) = iProver_top ),
% 15.84/2.49      inference(global_propositional_subsumption,
% 15.84/2.49                [status(thm)],
% 15.84/2.49                [c_4522,c_20]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_74912,plain,
% 15.84/2.49      ( r1_tarski(k6_subset_1(sK0,sK1),k10_relat_1(sK2,k1_xboole_0)) = iProver_top
% 15.84/2.49      | r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2)) != iProver_top ),
% 15.84/2.49      inference(renaming,[status(thm)],[c_74911]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_1,plain,
% 15.84/2.49      ( r1_tarski(X0,X0) ),
% 15.84/2.49      inference(cnf_transformation,[],[f57]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_791,plain,
% 15.84/2.49      ( r1_tarski(X0,X0) = iProver_top ),
% 15.84/2.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_2405,plain,
% 15.84/2.49      ( k6_subset_1(X0,X0) = k1_xboole_0 ),
% 15.84/2.49      inference(superposition,[status(thm)],[c_791,c_790]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_12,plain,
% 15.84/2.49      ( ~ v1_relat_1(X0)
% 15.84/2.49      | ~ v1_funct_1(X0)
% 15.84/2.49      | k6_subset_1(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k6_subset_1(X1,X2)) ),
% 15.84/2.49      inference(cnf_transformation,[],[f45]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_781,plain,
% 15.84/2.49      ( k6_subset_1(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k6_subset_1(X1,X2))
% 15.84/2.49      | v1_relat_1(X0) != iProver_top
% 15.84/2.49      | v1_funct_1(X0) != iProver_top ),
% 15.84/2.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_2175,plain,
% 15.84/2.49      ( k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k6_subset_1(X0,X1))
% 15.84/2.49      | v1_funct_1(sK2) != iProver_top ),
% 15.84/2.49      inference(superposition,[status(thm)],[c_774,c_781]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_3461,plain,
% 15.84/2.49      ( k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k6_subset_1(X0,X1)) ),
% 15.84/2.49      inference(global_propositional_subsumption,
% 15.84/2.49                [status(thm)],
% 15.84/2.49                [c_2175,c_21]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_3875,plain,
% 15.84/2.49      ( k10_relat_1(sK2,k6_subset_1(X0,X0)) = k1_xboole_0 ),
% 15.84/2.49      inference(superposition,[status(thm)],[c_2405,c_3461]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_3876,plain,
% 15.84/2.49      ( k10_relat_1(sK2,k1_xboole_0) = k1_xboole_0 ),
% 15.84/2.49      inference(light_normalisation,[status(thm)],[c_3875,c_2405]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_74915,plain,
% 15.84/2.49      ( r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2)) != iProver_top
% 15.84/2.49      | r1_tarski(k6_subset_1(sK0,sK1),k1_xboole_0) = iProver_top ),
% 15.84/2.49      inference(light_normalisation,[status(thm)],[c_74912,c_3876]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_16,negated_conjecture,
% 15.84/2.49      ( r1_tarski(sK0,k1_relat_1(sK2)) ),
% 15.84/2.49      inference(cnf_transformation,[],[f50]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_777,plain,
% 15.84/2.49      ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top ),
% 15.84/2.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_7,plain,
% 15.84/2.49      ( r1_tarski(k6_subset_1(X0,X1),X0) ),
% 15.84/2.49      inference(cnf_transformation,[],[f55]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_786,plain,
% 15.84/2.49      ( r1_tarski(k6_subset_1(X0,X1),X0) = iProver_top ),
% 15.84/2.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_6,plain,
% 15.84/2.49      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 15.84/2.49      inference(cnf_transformation,[],[f38]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_787,plain,
% 15.84/2.49      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 15.84/2.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_1439,plain,
% 15.84/2.49      ( k2_xboole_0(k6_subset_1(X0,X1),X0) = X0 ),
% 15.84/2.49      inference(superposition,[status(thm)],[c_786,c_787]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_5,plain,
% 15.84/2.49      ( r1_tarski(X0,X1) | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 15.84/2.49      inference(cnf_transformation,[],[f37]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_788,plain,
% 15.84/2.49      ( r1_tarski(X0,X1) = iProver_top
% 15.84/2.49      | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
% 15.84/2.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_2442,plain,
% 15.84/2.49      ( r1_tarski(X0,X1) != iProver_top
% 15.84/2.49      | r1_tarski(k6_subset_1(X0,X2),X1) = iProver_top ),
% 15.84/2.49      inference(superposition,[status(thm)],[c_1439,c_788]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_12188,plain,
% 15.84/2.49      ( k6_subset_1(k6_subset_1(X0,X1),X2) = k1_xboole_0
% 15.84/2.49      | r1_tarski(X0,X2) != iProver_top ),
% 15.84/2.49      inference(superposition,[status(thm)],[c_2442,c_790]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_66135,plain,
% 15.84/2.49      ( k6_subset_1(k6_subset_1(sK0,X0),k1_relat_1(sK2)) = k1_xboole_0 ),
% 15.84/2.49      inference(superposition,[status(thm)],[c_777,c_12188]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_4,plain,
% 15.84/2.49      ( r1_tarski(X0,X1) | k6_subset_1(X0,X1) != k1_xboole_0 ),
% 15.84/2.49      inference(cnf_transformation,[],[f54]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_789,plain,
% 15.84/2.49      ( k6_subset_1(X0,X1) != k1_xboole_0
% 15.84/2.49      | r1_tarski(X0,X1) = iProver_top ),
% 15.84/2.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_66613,plain,
% 15.84/2.49      ( r1_tarski(k6_subset_1(sK0,X0),k1_relat_1(sK2)) = iProver_top ),
% 15.84/2.49      inference(superposition,[status(thm)],[c_66135,c_789]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_74918,plain,
% 15.84/2.49      ( r1_tarski(k6_subset_1(sK0,sK1),k1_xboole_0) = iProver_top ),
% 15.84/2.49      inference(forward_subsumption_resolution,
% 15.84/2.49                [status(thm)],
% 15.84/2.49                [c_74915,c_66613]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_8,plain,
% 15.84/2.49      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 15.84/2.49      inference(cnf_transformation,[],[f40]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_966,plain,
% 15.84/2.49      ( ~ r1_tarski(k6_subset_1(X0,X1),k1_xboole_0)
% 15.84/2.49      | k1_xboole_0 = k6_subset_1(X0,X1) ),
% 15.84/2.49      inference(instantiation,[status(thm)],[c_8]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_5272,plain,
% 15.84/2.49      ( ~ r1_tarski(k6_subset_1(sK0,sK1),k1_xboole_0)
% 15.84/2.49      | k1_xboole_0 = k6_subset_1(sK0,sK1) ),
% 15.84/2.49      inference(instantiation,[status(thm)],[c_966]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_5273,plain,
% 15.84/2.49      ( k1_xboole_0 = k6_subset_1(sK0,sK1)
% 15.84/2.49      | r1_tarski(k6_subset_1(sK0,sK1),k1_xboole_0) != iProver_top ),
% 15.84/2.49      inference(predicate_to_equality,[status(thm)],[c_5272]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_344,plain,( X0 = X0 ),theory(equality) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_2697,plain,
% 15.84/2.49      ( k6_subset_1(sK0,sK1) = k6_subset_1(sK0,sK1) ),
% 15.84/2.49      inference(instantiation,[status(thm)],[c_344]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_345,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_1077,plain,
% 15.84/2.49      ( k6_subset_1(sK0,sK1) != X0
% 15.84/2.49      | k6_subset_1(sK0,sK1) = k1_xboole_0
% 15.84/2.49      | k1_xboole_0 != X0 ),
% 15.84/2.49      inference(instantiation,[status(thm)],[c_345]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_2074,plain,
% 15.84/2.49      ( k6_subset_1(sK0,sK1) != k6_subset_1(X0,X1)
% 15.84/2.49      | k6_subset_1(sK0,sK1) = k1_xboole_0
% 15.84/2.49      | k1_xboole_0 != k6_subset_1(X0,X1) ),
% 15.84/2.49      inference(instantiation,[status(thm)],[c_1077]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_2696,plain,
% 15.84/2.49      ( k6_subset_1(sK0,sK1) != k6_subset_1(sK0,sK1)
% 15.84/2.49      | k6_subset_1(sK0,sK1) = k1_xboole_0
% 15.84/2.49      | k1_xboole_0 != k6_subset_1(sK0,sK1) ),
% 15.84/2.49      inference(instantiation,[status(thm)],[c_2074]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_952,plain,
% 15.84/2.49      ( r1_tarski(sK0,sK1) | k6_subset_1(sK0,sK1) != k1_xboole_0 ),
% 15.84/2.49      inference(instantiation,[status(thm)],[c_4]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_14,negated_conjecture,
% 15.84/2.49      ( ~ r1_tarski(sK0,sK1) ),
% 15.84/2.49      inference(cnf_transformation,[],[f52]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(contradiction,plain,
% 15.84/2.49      ( $false ),
% 15.84/2.49      inference(minisat,
% 15.84/2.49                [status(thm)],
% 15.84/2.49                [c_74918,c_5273,c_2697,c_2696,c_952,c_14]) ).
% 15.84/2.49  
% 15.84/2.49  
% 15.84/2.49  % SZS output end CNFRefutation for theBenchmark.p
% 15.84/2.49  
% 15.84/2.49  ------                               Statistics
% 15.84/2.49  
% 15.84/2.49  ------ Selected
% 15.84/2.49  
% 15.84/2.49  total_time:                             1.946
% 15.84/2.49  
%------------------------------------------------------------------------------
