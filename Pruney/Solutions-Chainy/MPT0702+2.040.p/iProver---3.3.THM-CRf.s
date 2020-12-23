%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:52:13 EST 2020

% Result     : Theorem 7.51s
% Output     : CNFRefutation 7.51s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 219 expanded)
%              Number of clauses        :   61 (  75 expanded)
%              Number of leaves         :   15 (  51 expanded)
%              Depth                    :   17
%              Number of atoms          :  243 ( 596 expanded)
%              Number of equality atoms :  113 ( 191 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_tarski(X0,k1_relat_1(X2))
          & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( v2_funct_1(X2)
            & r1_tarski(X0,k1_relat_1(X2))
            & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f25,plain,
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

fof(f26,plain,
    ( ~ r1_tarski(sK0,sK1)
    & v2_funct_1(sK2)
    & r1_tarski(sK0,k1_relat_1(sK2))
    & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f25])).

fof(f43,plain,(
    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f30,f31])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f52,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k6_subset_1(X0,X1) ),
    inference(definition_unfolding,[],[f37,f31])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f45,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f41,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f42,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k9_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k9_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_relat_1(X1),X0)
      | k1_xboole_0 != k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f51,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f35,f31])).

fof(f8,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X0))
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ) ),
    inference(definition_unfolding,[],[f34,f31])).

fof(f46,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f29,f31])).

fof(f44,plain,(
    r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f49,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f33,f31])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_16,negated_conjecture,
    ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_646,plain,
    ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_653,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_9,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_692,plain,
    ( k6_subset_1(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_653,c_9])).

cnf(c_2219,plain,
    ( k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_646,c_692])).

cnf(c_12,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k6_subset_1(X1,X2)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_14,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_233,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k6_subset_1(X1,X2))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_14])).

cnf(c_234,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) = k9_relat_1(sK2,k6_subset_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_233])).

cnf(c_18,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_17,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_238,plain,
    ( k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) = k9_relat_1(sK2,k6_subset_1(X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_234,c_18,c_17])).

cnf(c_2354,plain,
    ( k9_relat_1(sK2,k6_subset_1(sK0,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2219,c_238])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_129,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_1])).

cnf(c_11,plain,
    ( r1_xboole_0(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k9_relat_1(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_245,plain,
    ( r1_xboole_0(k1_relat_1(X0),X1)
    | k9_relat_1(X0,X1) != k1_xboole_0
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_18])).

cnf(c_246,plain,
    ( r1_xboole_0(k1_relat_1(sK2),X0)
    | k9_relat_1(sK2,X0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_245])).

cnf(c_292,plain,
    ( X0 != X1
    | k9_relat_1(sK2,X0) != k1_xboole_0
    | k3_xboole_0(X2,X1) = k1_xboole_0
    | k1_relat_1(sK2) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_129,c_246])).

cnf(c_293,plain,
    ( k9_relat_1(sK2,X0) != k1_xboole_0
    | k3_xboole_0(k1_relat_1(sK2),X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_292])).

cnf(c_345,plain,
    ( k9_relat_1(sK2,X0) != k1_xboole_0
    | k3_xboole_0(k1_relat_1(sK2),X0) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_293])).

cnf(c_2439,plain,
    ( k3_xboole_0(k1_relat_1(sK2),k6_subset_1(sK0,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2354,c_345])).

cnf(c_3292,plain,
    ( k6_subset_1(k1_relat_1(sK2),k6_subset_1(sK0,sK1)) = k5_xboole_0(k1_relat_1(sK2),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2439,c_9])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_8,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_277,plain,
    ( X0 != X1
    | k3_xboole_0(X1,X2) = k1_xboole_0
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_129,c_8])).

cnf(c_278,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_277])).

cnf(c_662,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_7,c_278])).

cnf(c_3295,plain,
    ( k6_subset_1(k1_relat_1(sK2),k6_subset_1(sK0,sK1)) = k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_3292,c_662])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_649,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_682,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k6_subset_1(X1,X0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_649,c_9])).

cnf(c_11491,plain,
    ( k6_subset_1(sK0,sK1) = k1_xboole_0
    | r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3295,c_682])).

cnf(c_13,negated_conjecture,
    ( ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_406,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_421,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_406])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_731,plain,
    ( r1_tarski(sK0,sK1)
    | k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_407,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_748,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) != X0
    | k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_407])).

cnf(c_800,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) != k6_subset_1(sK0,sK1)
    | k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) = k1_xboole_0
    | k1_xboole_0 != k6_subset_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_748])).

cnf(c_801,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) = k6_subset_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_871,plain,
    ( k6_subset_1(sK0,sK1) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k6_subset_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_407])).

cnf(c_872,plain,
    ( k6_subset_1(sK0,sK1) != k1_xboole_0
    | k1_xboole_0 = k6_subset_1(sK0,sK1)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_871])).

cnf(c_21944,plain,
    ( r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11491,c_13,c_421,c_731,c_800,c_801,c_872])).

cnf(c_15,negated_conjecture,
    ( r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_647,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_5,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_650,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_669,plain,
    ( r1_tarski(k6_subset_1(X0,X1),X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_650,c_9])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_651,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1992,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k6_subset_1(X0,X2),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_669,c_651])).

cnf(c_14802,plain,
    ( k6_subset_1(k6_subset_1(X0,X1),X2) = k1_xboole_0
    | r1_tarski(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1992,c_692])).

cnf(c_16271,plain,
    ( k6_subset_1(k6_subset_1(sK0,X0),k1_relat_1(sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_647,c_14802])).

cnf(c_652,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_687,plain,
    ( k6_subset_1(X0,X1) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_652,c_9])).

cnf(c_16464,plain,
    ( r1_tarski(k6_subset_1(sK0,X0),k1_relat_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_16271,c_687])).

cnf(c_21949,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_21944,c_16464])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:43:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 7.51/1.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.51/1.48  
% 7.51/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.51/1.48  
% 7.51/1.48  ------  iProver source info
% 7.51/1.48  
% 7.51/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.51/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.51/1.48  git: non_committed_changes: false
% 7.51/1.48  git: last_make_outside_of_git: false
% 7.51/1.48  
% 7.51/1.48  ------ 
% 7.51/1.48  
% 7.51/1.48  ------ Input Options
% 7.51/1.48  
% 7.51/1.48  --out_options                           all
% 7.51/1.48  --tptp_safe_out                         true
% 7.51/1.48  --problem_path                          ""
% 7.51/1.48  --include_path                          ""
% 7.51/1.48  --clausifier                            res/vclausify_rel
% 7.51/1.48  --clausifier_options                    --mode clausify
% 7.51/1.48  --stdin                                 false
% 7.51/1.48  --stats_out                             all
% 7.51/1.48  
% 7.51/1.48  ------ General Options
% 7.51/1.48  
% 7.51/1.48  --fof                                   false
% 7.51/1.48  --time_out_real                         305.
% 7.51/1.48  --time_out_virtual                      -1.
% 7.51/1.48  --symbol_type_check                     false
% 7.51/1.48  --clausify_out                          false
% 7.51/1.48  --sig_cnt_out                           false
% 7.51/1.49  --trig_cnt_out                          false
% 7.51/1.49  --trig_cnt_out_tolerance                1.
% 7.51/1.49  --trig_cnt_out_sk_spl                   false
% 7.51/1.49  --abstr_cl_out                          false
% 7.51/1.49  
% 7.51/1.49  ------ Global Options
% 7.51/1.49  
% 7.51/1.49  --schedule                              default
% 7.51/1.49  --add_important_lit                     false
% 7.51/1.49  --prop_solver_per_cl                    1000
% 7.51/1.49  --min_unsat_core                        false
% 7.51/1.49  --soft_assumptions                      false
% 7.51/1.49  --soft_lemma_size                       3
% 7.51/1.49  --prop_impl_unit_size                   0
% 7.51/1.49  --prop_impl_unit                        []
% 7.51/1.49  --share_sel_clauses                     true
% 7.51/1.49  --reset_solvers                         false
% 7.51/1.49  --bc_imp_inh                            [conj_cone]
% 7.51/1.49  --conj_cone_tolerance                   3.
% 7.51/1.49  --extra_neg_conj                        none
% 7.51/1.49  --large_theory_mode                     true
% 7.51/1.49  --prolific_symb_bound                   200
% 7.51/1.49  --lt_threshold                          2000
% 7.51/1.49  --clause_weak_htbl                      true
% 7.51/1.49  --gc_record_bc_elim                     false
% 7.51/1.49  
% 7.51/1.49  ------ Preprocessing Options
% 7.51/1.49  
% 7.51/1.49  --preprocessing_flag                    true
% 7.51/1.49  --time_out_prep_mult                    0.1
% 7.51/1.49  --splitting_mode                        input
% 7.51/1.49  --splitting_grd                         true
% 7.51/1.49  --splitting_cvd                         false
% 7.51/1.49  --splitting_cvd_svl                     false
% 7.51/1.49  --splitting_nvd                         32
% 7.51/1.49  --sub_typing                            true
% 7.51/1.49  --prep_gs_sim                           true
% 7.51/1.49  --prep_unflatten                        true
% 7.51/1.49  --prep_res_sim                          true
% 7.51/1.49  --prep_upred                            true
% 7.51/1.49  --prep_sem_filter                       exhaustive
% 7.51/1.49  --prep_sem_filter_out                   false
% 7.51/1.49  --pred_elim                             true
% 7.51/1.49  --res_sim_input                         true
% 7.51/1.49  --eq_ax_congr_red                       true
% 7.51/1.49  --pure_diseq_elim                       true
% 7.51/1.49  --brand_transform                       false
% 7.51/1.49  --non_eq_to_eq                          false
% 7.51/1.49  --prep_def_merge                        true
% 7.51/1.49  --prep_def_merge_prop_impl              false
% 7.51/1.49  --prep_def_merge_mbd                    true
% 7.51/1.49  --prep_def_merge_tr_red                 false
% 7.51/1.49  --prep_def_merge_tr_cl                  false
% 7.51/1.49  --smt_preprocessing                     true
% 7.51/1.49  --smt_ac_axioms                         fast
% 7.51/1.49  --preprocessed_out                      false
% 7.51/1.49  --preprocessed_stats                    false
% 7.51/1.49  
% 7.51/1.49  ------ Abstraction refinement Options
% 7.51/1.49  
% 7.51/1.49  --abstr_ref                             []
% 7.51/1.49  --abstr_ref_prep                        false
% 7.51/1.49  --abstr_ref_until_sat                   false
% 7.51/1.49  --abstr_ref_sig_restrict                funpre
% 7.51/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.51/1.49  --abstr_ref_under                       []
% 7.51/1.49  
% 7.51/1.49  ------ SAT Options
% 7.51/1.49  
% 7.51/1.49  --sat_mode                              false
% 7.51/1.49  --sat_fm_restart_options                ""
% 7.51/1.49  --sat_gr_def                            false
% 7.51/1.49  --sat_epr_types                         true
% 7.51/1.49  --sat_non_cyclic_types                  false
% 7.51/1.49  --sat_finite_models                     false
% 7.51/1.49  --sat_fm_lemmas                         false
% 7.51/1.49  --sat_fm_prep                           false
% 7.51/1.49  --sat_fm_uc_incr                        true
% 7.51/1.49  --sat_out_model                         small
% 7.51/1.49  --sat_out_clauses                       false
% 7.51/1.49  
% 7.51/1.49  ------ QBF Options
% 7.51/1.49  
% 7.51/1.49  --qbf_mode                              false
% 7.51/1.49  --qbf_elim_univ                         false
% 7.51/1.49  --qbf_dom_inst                          none
% 7.51/1.49  --qbf_dom_pre_inst                      false
% 7.51/1.49  --qbf_sk_in                             false
% 7.51/1.49  --qbf_pred_elim                         true
% 7.51/1.49  --qbf_split                             512
% 7.51/1.49  
% 7.51/1.49  ------ BMC1 Options
% 7.51/1.49  
% 7.51/1.49  --bmc1_incremental                      false
% 7.51/1.49  --bmc1_axioms                           reachable_all
% 7.51/1.49  --bmc1_min_bound                        0
% 7.51/1.49  --bmc1_max_bound                        -1
% 7.51/1.49  --bmc1_max_bound_default                -1
% 7.51/1.49  --bmc1_symbol_reachability              true
% 7.51/1.49  --bmc1_property_lemmas                  false
% 7.51/1.49  --bmc1_k_induction                      false
% 7.51/1.49  --bmc1_non_equiv_states                 false
% 7.51/1.49  --bmc1_deadlock                         false
% 7.51/1.49  --bmc1_ucm                              false
% 7.51/1.49  --bmc1_add_unsat_core                   none
% 7.51/1.49  --bmc1_unsat_core_children              false
% 7.51/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.51/1.49  --bmc1_out_stat                         full
% 7.51/1.49  --bmc1_ground_init                      false
% 7.51/1.49  --bmc1_pre_inst_next_state              false
% 7.51/1.49  --bmc1_pre_inst_state                   false
% 7.51/1.49  --bmc1_pre_inst_reach_state             false
% 7.51/1.49  --bmc1_out_unsat_core                   false
% 7.51/1.49  --bmc1_aig_witness_out                  false
% 7.51/1.49  --bmc1_verbose                          false
% 7.51/1.49  --bmc1_dump_clauses_tptp                false
% 7.51/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.51/1.49  --bmc1_dump_file                        -
% 7.51/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.51/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.51/1.49  --bmc1_ucm_extend_mode                  1
% 7.51/1.49  --bmc1_ucm_init_mode                    2
% 7.51/1.49  --bmc1_ucm_cone_mode                    none
% 7.51/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.51/1.49  --bmc1_ucm_relax_model                  4
% 7.51/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.51/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.51/1.49  --bmc1_ucm_layered_model                none
% 7.51/1.49  --bmc1_ucm_max_lemma_size               10
% 7.51/1.49  
% 7.51/1.49  ------ AIG Options
% 7.51/1.49  
% 7.51/1.49  --aig_mode                              false
% 7.51/1.49  
% 7.51/1.49  ------ Instantiation Options
% 7.51/1.49  
% 7.51/1.49  --instantiation_flag                    true
% 7.51/1.49  --inst_sos_flag                         false
% 7.51/1.49  --inst_sos_phase                        true
% 7.51/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.51/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.51/1.49  --inst_lit_sel_side                     num_symb
% 7.51/1.49  --inst_solver_per_active                1400
% 7.51/1.49  --inst_solver_calls_frac                1.
% 7.51/1.49  --inst_passive_queue_type               priority_queues
% 7.51/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.51/1.49  --inst_passive_queues_freq              [25;2]
% 7.51/1.49  --inst_dismatching                      true
% 7.51/1.49  --inst_eager_unprocessed_to_passive     true
% 7.51/1.49  --inst_prop_sim_given                   true
% 7.51/1.49  --inst_prop_sim_new                     false
% 7.51/1.49  --inst_subs_new                         false
% 7.51/1.49  --inst_eq_res_simp                      false
% 7.51/1.49  --inst_subs_given                       false
% 7.51/1.49  --inst_orphan_elimination               true
% 7.51/1.49  --inst_learning_loop_flag               true
% 7.51/1.49  --inst_learning_start                   3000
% 7.51/1.49  --inst_learning_factor                  2
% 7.51/1.49  --inst_start_prop_sim_after_learn       3
% 7.51/1.49  --inst_sel_renew                        solver
% 7.51/1.49  --inst_lit_activity_flag                true
% 7.51/1.49  --inst_restr_to_given                   false
% 7.51/1.49  --inst_activity_threshold               500
% 7.51/1.49  --inst_out_proof                        true
% 7.51/1.49  
% 7.51/1.49  ------ Resolution Options
% 7.51/1.49  
% 7.51/1.49  --resolution_flag                       true
% 7.51/1.49  --res_lit_sel                           adaptive
% 7.51/1.49  --res_lit_sel_side                      none
% 7.51/1.49  --res_ordering                          kbo
% 7.51/1.49  --res_to_prop_solver                    active
% 7.51/1.49  --res_prop_simpl_new                    false
% 7.51/1.49  --res_prop_simpl_given                  true
% 7.51/1.49  --res_passive_queue_type                priority_queues
% 7.51/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.51/1.49  --res_passive_queues_freq               [15;5]
% 7.51/1.49  --res_forward_subs                      full
% 7.51/1.49  --res_backward_subs                     full
% 7.51/1.49  --res_forward_subs_resolution           true
% 7.51/1.49  --res_backward_subs_resolution          true
% 7.51/1.49  --res_orphan_elimination                true
% 7.51/1.49  --res_time_limit                        2.
% 7.51/1.49  --res_out_proof                         true
% 7.51/1.49  
% 7.51/1.49  ------ Superposition Options
% 7.51/1.49  
% 7.51/1.49  --superposition_flag                    true
% 7.51/1.49  --sup_passive_queue_type                priority_queues
% 7.51/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.51/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.51/1.49  --demod_completeness_check              fast
% 7.51/1.49  --demod_use_ground                      true
% 7.51/1.49  --sup_to_prop_solver                    passive
% 7.51/1.49  --sup_prop_simpl_new                    true
% 7.51/1.49  --sup_prop_simpl_given                  true
% 7.51/1.49  --sup_fun_splitting                     false
% 7.51/1.49  --sup_smt_interval                      50000
% 7.51/1.49  
% 7.51/1.49  ------ Superposition Simplification Setup
% 7.51/1.49  
% 7.51/1.49  --sup_indices_passive                   []
% 7.51/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.51/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.51/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.51/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.51/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.51/1.49  --sup_full_bw                           [BwDemod]
% 7.51/1.49  --sup_immed_triv                        [TrivRules]
% 7.51/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.51/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.51/1.49  --sup_immed_bw_main                     []
% 7.51/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.51/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.51/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.51/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.51/1.49  
% 7.51/1.49  ------ Combination Options
% 7.51/1.49  
% 7.51/1.49  --comb_res_mult                         3
% 7.51/1.49  --comb_sup_mult                         2
% 7.51/1.49  --comb_inst_mult                        10
% 7.51/1.49  
% 7.51/1.49  ------ Debug Options
% 7.51/1.49  
% 7.51/1.49  --dbg_backtrace                         false
% 7.51/1.49  --dbg_dump_prop_clauses                 false
% 7.51/1.49  --dbg_dump_prop_clauses_file            -
% 7.51/1.49  --dbg_out_stat                          false
% 7.51/1.49  ------ Parsing...
% 7.51/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.51/1.49  
% 7.51/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 7.51/1.49  
% 7.51/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.51/1.49  
% 7.51/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.51/1.49  ------ Proving...
% 7.51/1.49  ------ Problem Properties 
% 7.51/1.49  
% 7.51/1.49  
% 7.51/1.49  clauses                                 15
% 7.51/1.49  conjectures                             3
% 7.51/1.49  EPR                                     2
% 7.51/1.49  Horn                                    15
% 7.51/1.49  unary                                   9
% 7.51/1.49  binary                                  5
% 7.51/1.49  lits                                    22
% 7.51/1.49  lits eq                                 12
% 7.51/1.49  fd_pure                                 0
% 7.51/1.49  fd_pseudo                               0
% 7.51/1.49  fd_cond                                 1
% 7.51/1.49  fd_pseudo_cond                          0
% 7.51/1.49  AC symbols                              0
% 7.51/1.49  
% 7.51/1.49  ------ Schedule dynamic 5 is on 
% 7.51/1.49  
% 7.51/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.51/1.49  
% 7.51/1.49  
% 7.51/1.49  ------ 
% 7.51/1.49  Current options:
% 7.51/1.49  ------ 
% 7.51/1.49  
% 7.51/1.49  ------ Input Options
% 7.51/1.49  
% 7.51/1.49  --out_options                           all
% 7.51/1.49  --tptp_safe_out                         true
% 7.51/1.49  --problem_path                          ""
% 7.51/1.49  --include_path                          ""
% 7.51/1.49  --clausifier                            res/vclausify_rel
% 7.51/1.49  --clausifier_options                    --mode clausify
% 7.51/1.49  --stdin                                 false
% 7.51/1.49  --stats_out                             all
% 7.51/1.49  
% 7.51/1.49  ------ General Options
% 7.51/1.49  
% 7.51/1.49  --fof                                   false
% 7.51/1.49  --time_out_real                         305.
% 7.51/1.49  --time_out_virtual                      -1.
% 7.51/1.49  --symbol_type_check                     false
% 7.51/1.49  --clausify_out                          false
% 7.51/1.49  --sig_cnt_out                           false
% 7.51/1.49  --trig_cnt_out                          false
% 7.51/1.49  --trig_cnt_out_tolerance                1.
% 7.51/1.49  --trig_cnt_out_sk_spl                   false
% 7.51/1.49  --abstr_cl_out                          false
% 7.51/1.49  
% 7.51/1.49  ------ Global Options
% 7.51/1.49  
% 7.51/1.49  --schedule                              default
% 7.51/1.49  --add_important_lit                     false
% 7.51/1.49  --prop_solver_per_cl                    1000
% 7.51/1.49  --min_unsat_core                        false
% 7.51/1.49  --soft_assumptions                      false
% 7.51/1.49  --soft_lemma_size                       3
% 7.51/1.49  --prop_impl_unit_size                   0
% 7.51/1.49  --prop_impl_unit                        []
% 7.51/1.49  --share_sel_clauses                     true
% 7.51/1.49  --reset_solvers                         false
% 7.51/1.49  --bc_imp_inh                            [conj_cone]
% 7.51/1.49  --conj_cone_tolerance                   3.
% 7.51/1.49  --extra_neg_conj                        none
% 7.51/1.49  --large_theory_mode                     true
% 7.51/1.49  --prolific_symb_bound                   200
% 7.51/1.49  --lt_threshold                          2000
% 7.51/1.49  --clause_weak_htbl                      true
% 7.51/1.49  --gc_record_bc_elim                     false
% 7.51/1.49  
% 7.51/1.49  ------ Preprocessing Options
% 7.51/1.49  
% 7.51/1.49  --preprocessing_flag                    true
% 7.51/1.49  --time_out_prep_mult                    0.1
% 7.51/1.49  --splitting_mode                        input
% 7.51/1.49  --splitting_grd                         true
% 7.51/1.49  --splitting_cvd                         false
% 7.51/1.49  --splitting_cvd_svl                     false
% 7.51/1.49  --splitting_nvd                         32
% 7.51/1.49  --sub_typing                            true
% 7.51/1.49  --prep_gs_sim                           true
% 7.51/1.49  --prep_unflatten                        true
% 7.51/1.49  --prep_res_sim                          true
% 7.51/1.49  --prep_upred                            true
% 7.51/1.49  --prep_sem_filter                       exhaustive
% 7.51/1.49  --prep_sem_filter_out                   false
% 7.51/1.49  --pred_elim                             true
% 7.51/1.49  --res_sim_input                         true
% 7.51/1.49  --eq_ax_congr_red                       true
% 7.51/1.49  --pure_diseq_elim                       true
% 7.51/1.49  --brand_transform                       false
% 7.51/1.49  --non_eq_to_eq                          false
% 7.51/1.49  --prep_def_merge                        true
% 7.51/1.49  --prep_def_merge_prop_impl              false
% 7.51/1.49  --prep_def_merge_mbd                    true
% 7.51/1.49  --prep_def_merge_tr_red                 false
% 7.51/1.49  --prep_def_merge_tr_cl                  false
% 7.51/1.49  --smt_preprocessing                     true
% 7.51/1.49  --smt_ac_axioms                         fast
% 7.51/1.49  --preprocessed_out                      false
% 7.51/1.49  --preprocessed_stats                    false
% 7.51/1.49  
% 7.51/1.49  ------ Abstraction refinement Options
% 7.51/1.49  
% 7.51/1.49  --abstr_ref                             []
% 7.51/1.49  --abstr_ref_prep                        false
% 7.51/1.49  --abstr_ref_until_sat                   false
% 7.51/1.49  --abstr_ref_sig_restrict                funpre
% 7.51/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.51/1.49  --abstr_ref_under                       []
% 7.51/1.49  
% 7.51/1.49  ------ SAT Options
% 7.51/1.49  
% 7.51/1.49  --sat_mode                              false
% 7.51/1.49  --sat_fm_restart_options                ""
% 7.51/1.49  --sat_gr_def                            false
% 7.51/1.49  --sat_epr_types                         true
% 7.51/1.49  --sat_non_cyclic_types                  false
% 7.51/1.49  --sat_finite_models                     false
% 7.51/1.49  --sat_fm_lemmas                         false
% 7.51/1.49  --sat_fm_prep                           false
% 7.51/1.49  --sat_fm_uc_incr                        true
% 7.51/1.49  --sat_out_model                         small
% 7.51/1.49  --sat_out_clauses                       false
% 7.51/1.49  
% 7.51/1.49  ------ QBF Options
% 7.51/1.49  
% 7.51/1.49  --qbf_mode                              false
% 7.51/1.49  --qbf_elim_univ                         false
% 7.51/1.49  --qbf_dom_inst                          none
% 7.51/1.49  --qbf_dom_pre_inst                      false
% 7.51/1.49  --qbf_sk_in                             false
% 7.51/1.49  --qbf_pred_elim                         true
% 7.51/1.49  --qbf_split                             512
% 7.51/1.49  
% 7.51/1.49  ------ BMC1 Options
% 7.51/1.49  
% 7.51/1.49  --bmc1_incremental                      false
% 7.51/1.49  --bmc1_axioms                           reachable_all
% 7.51/1.49  --bmc1_min_bound                        0
% 7.51/1.49  --bmc1_max_bound                        -1
% 7.51/1.49  --bmc1_max_bound_default                -1
% 7.51/1.49  --bmc1_symbol_reachability              true
% 7.51/1.49  --bmc1_property_lemmas                  false
% 7.51/1.49  --bmc1_k_induction                      false
% 7.51/1.49  --bmc1_non_equiv_states                 false
% 7.51/1.49  --bmc1_deadlock                         false
% 7.51/1.49  --bmc1_ucm                              false
% 7.51/1.49  --bmc1_add_unsat_core                   none
% 7.51/1.49  --bmc1_unsat_core_children              false
% 7.51/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.51/1.49  --bmc1_out_stat                         full
% 7.51/1.49  --bmc1_ground_init                      false
% 7.51/1.49  --bmc1_pre_inst_next_state              false
% 7.51/1.49  --bmc1_pre_inst_state                   false
% 7.51/1.49  --bmc1_pre_inst_reach_state             false
% 7.51/1.49  --bmc1_out_unsat_core                   false
% 7.51/1.49  --bmc1_aig_witness_out                  false
% 7.51/1.49  --bmc1_verbose                          false
% 7.51/1.49  --bmc1_dump_clauses_tptp                false
% 7.51/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.51/1.49  --bmc1_dump_file                        -
% 7.51/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.51/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.51/1.49  --bmc1_ucm_extend_mode                  1
% 7.51/1.49  --bmc1_ucm_init_mode                    2
% 7.51/1.49  --bmc1_ucm_cone_mode                    none
% 7.51/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.51/1.49  --bmc1_ucm_relax_model                  4
% 7.51/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.51/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.51/1.49  --bmc1_ucm_layered_model                none
% 7.51/1.49  --bmc1_ucm_max_lemma_size               10
% 7.51/1.49  
% 7.51/1.49  ------ AIG Options
% 7.51/1.49  
% 7.51/1.49  --aig_mode                              false
% 7.51/1.49  
% 7.51/1.49  ------ Instantiation Options
% 7.51/1.49  
% 7.51/1.49  --instantiation_flag                    true
% 7.51/1.49  --inst_sos_flag                         false
% 7.51/1.49  --inst_sos_phase                        true
% 7.51/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.51/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.51/1.49  --inst_lit_sel_side                     none
% 7.51/1.49  --inst_solver_per_active                1400
% 7.51/1.49  --inst_solver_calls_frac                1.
% 7.51/1.49  --inst_passive_queue_type               priority_queues
% 7.51/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.51/1.49  --inst_passive_queues_freq              [25;2]
% 7.51/1.49  --inst_dismatching                      true
% 7.51/1.49  --inst_eager_unprocessed_to_passive     true
% 7.51/1.49  --inst_prop_sim_given                   true
% 7.51/1.49  --inst_prop_sim_new                     false
% 7.51/1.49  --inst_subs_new                         false
% 7.51/1.49  --inst_eq_res_simp                      false
% 7.51/1.49  --inst_subs_given                       false
% 7.51/1.49  --inst_orphan_elimination               true
% 7.51/1.49  --inst_learning_loop_flag               true
% 7.51/1.49  --inst_learning_start                   3000
% 7.51/1.49  --inst_learning_factor                  2
% 7.51/1.49  --inst_start_prop_sim_after_learn       3
% 7.51/1.49  --inst_sel_renew                        solver
% 7.51/1.49  --inst_lit_activity_flag                true
% 7.51/1.49  --inst_restr_to_given                   false
% 7.51/1.49  --inst_activity_threshold               500
% 7.51/1.49  --inst_out_proof                        true
% 7.51/1.49  
% 7.51/1.49  ------ Resolution Options
% 7.51/1.49  
% 7.51/1.49  --resolution_flag                       false
% 7.51/1.49  --res_lit_sel                           adaptive
% 7.51/1.49  --res_lit_sel_side                      none
% 7.51/1.49  --res_ordering                          kbo
% 7.51/1.49  --res_to_prop_solver                    active
% 7.51/1.49  --res_prop_simpl_new                    false
% 7.51/1.49  --res_prop_simpl_given                  true
% 7.51/1.49  --res_passive_queue_type                priority_queues
% 7.51/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.51/1.49  --res_passive_queues_freq               [15;5]
% 7.51/1.49  --res_forward_subs                      full
% 7.51/1.49  --res_backward_subs                     full
% 7.51/1.49  --res_forward_subs_resolution           true
% 7.51/1.49  --res_backward_subs_resolution          true
% 7.51/1.49  --res_orphan_elimination                true
% 7.51/1.49  --res_time_limit                        2.
% 7.51/1.49  --res_out_proof                         true
% 7.51/1.49  
% 7.51/1.49  ------ Superposition Options
% 7.51/1.49  
% 7.51/1.49  --superposition_flag                    true
% 7.51/1.49  --sup_passive_queue_type                priority_queues
% 7.51/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.51/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.51/1.49  --demod_completeness_check              fast
% 7.51/1.49  --demod_use_ground                      true
% 7.51/1.49  --sup_to_prop_solver                    passive
% 7.51/1.49  --sup_prop_simpl_new                    true
% 7.51/1.49  --sup_prop_simpl_given                  true
% 7.51/1.49  --sup_fun_splitting                     false
% 7.51/1.49  --sup_smt_interval                      50000
% 7.51/1.49  
% 7.51/1.49  ------ Superposition Simplification Setup
% 7.51/1.49  
% 7.51/1.49  --sup_indices_passive                   []
% 7.51/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.51/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.51/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.51/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.51/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.51/1.49  --sup_full_bw                           [BwDemod]
% 7.51/1.49  --sup_immed_triv                        [TrivRules]
% 7.51/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.51/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.51/1.49  --sup_immed_bw_main                     []
% 7.51/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.51/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.51/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.51/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.51/1.49  
% 7.51/1.49  ------ Combination Options
% 7.51/1.49  
% 7.51/1.49  --comb_res_mult                         3
% 7.51/1.49  --comb_sup_mult                         2
% 7.51/1.49  --comb_inst_mult                        10
% 7.51/1.49  
% 7.51/1.49  ------ Debug Options
% 7.51/1.49  
% 7.51/1.49  --dbg_backtrace                         false
% 7.51/1.49  --dbg_dump_prop_clauses                 false
% 7.51/1.49  --dbg_dump_prop_clauses_file            -
% 7.51/1.49  --dbg_out_stat                          false
% 7.51/1.49  
% 7.51/1.49  
% 7.51/1.49  
% 7.51/1.49  
% 7.51/1.49  ------ Proving...
% 7.51/1.49  
% 7.51/1.49  
% 7.51/1.49  % SZS status Theorem for theBenchmark.p
% 7.51/1.49  
% 7.51/1.49   Resolution empty clause
% 7.51/1.49  
% 7.51/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.51/1.49  
% 7.51/1.49  fof(f12,conjecture,(
% 7.51/1.49    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 7.51/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.51/1.49  
% 7.51/1.49  fof(f13,negated_conjecture,(
% 7.51/1.49    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 7.51/1.49    inference(negated_conjecture,[],[f12])).
% 7.51/1.49  
% 7.51/1.49  fof(f20,plain,(
% 7.51/1.49    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 7.51/1.49    inference(ennf_transformation,[],[f13])).
% 7.51/1.49  
% 7.51/1.49  fof(f21,plain,(
% 7.51/1.49    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 7.51/1.49    inference(flattening,[],[f20])).
% 7.51/1.49  
% 7.51/1.49  fof(f25,plain,(
% 7.51/1.49    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 7.51/1.49    introduced(choice_axiom,[])).
% 7.51/1.49  
% 7.51/1.49  fof(f26,plain,(
% 7.51/1.49    ~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 7.51/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f25])).
% 7.51/1.49  
% 7.51/1.49  fof(f43,plain,(
% 7.51/1.49    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 7.51/1.49    inference(cnf_transformation,[],[f26])).
% 7.51/1.49  
% 7.51/1.49  fof(f2,axiom,(
% 7.51/1.49    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 7.51/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.51/1.49  
% 7.51/1.49  fof(f23,plain,(
% 7.51/1.49    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 7.51/1.49    inference(nnf_transformation,[],[f2])).
% 7.51/1.49  
% 7.51/1.49  fof(f30,plain,(
% 7.51/1.49    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 7.51/1.49    inference(cnf_transformation,[],[f23])).
% 7.51/1.49  
% 7.51/1.49  fof(f3,axiom,(
% 7.51/1.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.51/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.51/1.49  
% 7.51/1.49  fof(f31,plain,(
% 7.51/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.51/1.49    inference(cnf_transformation,[],[f3])).
% 7.51/1.49  
% 7.51/1.49  fof(f47,plain,(
% 7.51/1.49    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) | ~r1_tarski(X0,X1)) )),
% 7.51/1.49    inference(definition_unfolding,[],[f30,f31])).
% 7.51/1.49  
% 7.51/1.49  fof(f9,axiom,(
% 7.51/1.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 7.51/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.51/1.49  
% 7.51/1.49  fof(f37,plain,(
% 7.51/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 7.51/1.49    inference(cnf_transformation,[],[f9])).
% 7.51/1.49  
% 7.51/1.49  fof(f52,plain,(
% 7.51/1.49    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k6_subset_1(X0,X1)) )),
% 7.51/1.49    inference(definition_unfolding,[],[f37,f31])).
% 7.51/1.49  
% 7.51/1.49  fof(f11,axiom,(
% 7.51/1.49    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1))))),
% 7.51/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.51/1.49  
% 7.51/1.49  fof(f18,plain,(
% 7.51/1.49    ! [X0,X1,X2] : ((k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1)) | ~v2_funct_1(X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 7.51/1.49    inference(ennf_transformation,[],[f11])).
% 7.51/1.49  
% 7.51/1.49  fof(f19,plain,(
% 7.51/1.49    ! [X0,X1,X2] : (k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 7.51/1.49    inference(flattening,[],[f18])).
% 7.51/1.49  
% 7.51/1.49  fof(f40,plain,(
% 7.51/1.49    ( ! [X2,X0,X1] : (k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 7.51/1.49    inference(cnf_transformation,[],[f19])).
% 7.51/1.49  
% 7.51/1.49  fof(f45,plain,(
% 7.51/1.49    v2_funct_1(sK2)),
% 7.51/1.49    inference(cnf_transformation,[],[f26])).
% 7.51/1.49  
% 7.51/1.49  fof(f41,plain,(
% 7.51/1.49    v1_relat_1(sK2)),
% 7.51/1.49    inference(cnf_transformation,[],[f26])).
% 7.51/1.49  
% 7.51/1.49  fof(f42,plain,(
% 7.51/1.49    v1_funct_1(sK2)),
% 7.51/1.49    inference(cnf_transformation,[],[f26])).
% 7.51/1.49  
% 7.51/1.49  fof(f1,axiom,(
% 7.51/1.49    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 7.51/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.51/1.49  
% 7.51/1.49  fof(f22,plain,(
% 7.51/1.49    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 7.51/1.49    inference(nnf_transformation,[],[f1])).
% 7.51/1.49  
% 7.51/1.49  fof(f27,plain,(
% 7.51/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 7.51/1.49    inference(cnf_transformation,[],[f22])).
% 7.51/1.49  
% 7.51/1.49  fof(f10,axiom,(
% 7.51/1.49    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 7.51/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.51/1.49  
% 7.51/1.49  fof(f17,plain,(
% 7.51/1.49    ! [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.51/1.49    inference(ennf_transformation,[],[f10])).
% 7.51/1.49  
% 7.51/1.49  fof(f24,plain,(
% 7.51/1.49    ! [X0,X1] : (((k1_xboole_0 = k9_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.51/1.49    inference(nnf_transformation,[],[f17])).
% 7.51/1.49  
% 7.51/1.49  fof(f38,plain,(
% 7.51/1.49    ( ! [X0,X1] : (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.51/1.49    inference(cnf_transformation,[],[f24])).
% 7.51/1.49  
% 7.51/1.49  fof(f7,axiom,(
% 7.51/1.49    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 7.51/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.51/1.49  
% 7.51/1.49  fof(f35,plain,(
% 7.51/1.49    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.51/1.49    inference(cnf_transformation,[],[f7])).
% 7.51/1.49  
% 7.51/1.49  fof(f51,plain,(
% 7.51/1.49    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 7.51/1.49    inference(definition_unfolding,[],[f35,f31])).
% 7.51/1.49  
% 7.51/1.49  fof(f8,axiom,(
% 7.51/1.49    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 7.51/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.51/1.49  
% 7.51/1.49  fof(f36,plain,(
% 7.51/1.49    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 7.51/1.49    inference(cnf_transformation,[],[f8])).
% 7.51/1.49  
% 7.51/1.49  fof(f6,axiom,(
% 7.51/1.49    ! [X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X0)) => k1_xboole_0 = X0)),
% 7.51/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.51/1.49  
% 7.51/1.49  fof(f16,plain,(
% 7.51/1.49    ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0)))),
% 7.51/1.49    inference(ennf_transformation,[],[f6])).
% 7.51/1.49  
% 7.51/1.49  fof(f34,plain,(
% 7.51/1.49    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0))) )),
% 7.51/1.49    inference(cnf_transformation,[],[f16])).
% 7.51/1.49  
% 7.51/1.49  fof(f50,plain,(
% 7.51/1.49    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 7.51/1.49    inference(definition_unfolding,[],[f34,f31])).
% 7.51/1.49  
% 7.51/1.49  fof(f46,plain,(
% 7.51/1.49    ~r1_tarski(sK0,sK1)),
% 7.51/1.49    inference(cnf_transformation,[],[f26])).
% 7.51/1.49  
% 7.51/1.49  fof(f29,plain,(
% 7.51/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 7.51/1.49    inference(cnf_transformation,[],[f23])).
% 7.51/1.49  
% 7.51/1.49  fof(f48,plain,(
% 7.51/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.51/1.49    inference(definition_unfolding,[],[f29,f31])).
% 7.51/1.49  
% 7.51/1.49  fof(f44,plain,(
% 7.51/1.49    r1_tarski(sK0,k1_relat_1(sK2))),
% 7.51/1.49    inference(cnf_transformation,[],[f26])).
% 7.51/1.49  
% 7.51/1.49  fof(f5,axiom,(
% 7.51/1.49    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 7.51/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.51/1.49  
% 7.51/1.49  fof(f33,plain,(
% 7.51/1.49    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 7.51/1.49    inference(cnf_transformation,[],[f5])).
% 7.51/1.49  
% 7.51/1.49  fof(f49,plain,(
% 7.51/1.49    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 7.51/1.49    inference(definition_unfolding,[],[f33,f31])).
% 7.51/1.49  
% 7.51/1.49  fof(f4,axiom,(
% 7.51/1.49    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 7.51/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.51/1.49  
% 7.51/1.49  fof(f14,plain,(
% 7.51/1.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 7.51/1.49    inference(ennf_transformation,[],[f4])).
% 7.51/1.49  
% 7.51/1.49  fof(f15,plain,(
% 7.51/1.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 7.51/1.49    inference(flattening,[],[f14])).
% 7.51/1.49  
% 7.51/1.49  fof(f32,plain,(
% 7.51/1.49    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 7.51/1.49    inference(cnf_transformation,[],[f15])).
% 7.51/1.49  
% 7.51/1.49  cnf(c_16,negated_conjecture,
% 7.51/1.49      ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
% 7.51/1.49      inference(cnf_transformation,[],[f43]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_646,plain,
% 7.51/1.49      ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) = iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_2,plain,
% 7.51/1.49      ( ~ r1_tarski(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
% 7.51/1.49      inference(cnf_transformation,[],[f47]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_653,plain,
% 7.51/1.49      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
% 7.51/1.49      | r1_tarski(X0,X1) != iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_9,plain,
% 7.51/1.49      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k6_subset_1(X0,X1) ),
% 7.51/1.49      inference(cnf_transformation,[],[f52]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_692,plain,
% 7.51/1.49      ( k6_subset_1(X0,X1) = k1_xboole_0 | r1_tarski(X0,X1) != iProver_top ),
% 7.51/1.49      inference(demodulation,[status(thm)],[c_653,c_9]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_2219,plain,
% 7.51/1.49      ( k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) = k1_xboole_0 ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_646,c_692]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_12,plain,
% 7.51/1.49      ( ~ v1_funct_1(X0)
% 7.51/1.49      | ~ v2_funct_1(X0)
% 7.51/1.49      | ~ v1_relat_1(X0)
% 7.51/1.49      | k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k6_subset_1(X1,X2)) ),
% 7.51/1.49      inference(cnf_transformation,[],[f40]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_14,negated_conjecture,
% 7.51/1.49      ( v2_funct_1(sK2) ),
% 7.51/1.49      inference(cnf_transformation,[],[f45]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_233,plain,
% 7.51/1.49      ( ~ v1_funct_1(X0)
% 7.51/1.49      | ~ v1_relat_1(X0)
% 7.51/1.49      | k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k6_subset_1(X1,X2))
% 7.51/1.49      | sK2 != X0 ),
% 7.51/1.49      inference(resolution_lifted,[status(thm)],[c_12,c_14]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_234,plain,
% 7.51/1.49      ( ~ v1_funct_1(sK2)
% 7.51/1.49      | ~ v1_relat_1(sK2)
% 7.51/1.49      | k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) = k9_relat_1(sK2,k6_subset_1(X0,X1)) ),
% 7.51/1.49      inference(unflattening,[status(thm)],[c_233]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_18,negated_conjecture,
% 7.51/1.49      ( v1_relat_1(sK2) ),
% 7.51/1.49      inference(cnf_transformation,[],[f41]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_17,negated_conjecture,
% 7.51/1.49      ( v1_funct_1(sK2) ),
% 7.51/1.49      inference(cnf_transformation,[],[f42]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_238,plain,
% 7.51/1.49      ( k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) = k9_relat_1(sK2,k6_subset_1(X0,X1)) ),
% 7.51/1.49      inference(global_propositional_subsumption,
% 7.51/1.49                [status(thm)],
% 7.51/1.49                [c_234,c_18,c_17]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_2354,plain,
% 7.51/1.49      ( k9_relat_1(sK2,k6_subset_1(sK0,sK1)) = k1_xboole_0 ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_2219,c_238]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_1,plain,
% 7.51/1.49      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 7.51/1.49      inference(cnf_transformation,[],[f27]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_129,plain,
% 7.51/1.49      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 7.51/1.49      inference(prop_impl,[status(thm)],[c_1]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_11,plain,
% 7.51/1.49      ( r1_xboole_0(k1_relat_1(X0),X1)
% 7.51/1.49      | ~ v1_relat_1(X0)
% 7.51/1.49      | k9_relat_1(X0,X1) != k1_xboole_0 ),
% 7.51/1.49      inference(cnf_transformation,[],[f38]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_245,plain,
% 7.51/1.49      ( r1_xboole_0(k1_relat_1(X0),X1)
% 7.51/1.49      | k9_relat_1(X0,X1) != k1_xboole_0
% 7.51/1.49      | sK2 != X0 ),
% 7.51/1.49      inference(resolution_lifted,[status(thm)],[c_11,c_18]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_246,plain,
% 7.51/1.49      ( r1_xboole_0(k1_relat_1(sK2),X0) | k9_relat_1(sK2,X0) != k1_xboole_0 ),
% 7.51/1.49      inference(unflattening,[status(thm)],[c_245]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_292,plain,
% 7.51/1.49      ( X0 != X1
% 7.51/1.49      | k9_relat_1(sK2,X0) != k1_xboole_0
% 7.51/1.49      | k3_xboole_0(X2,X1) = k1_xboole_0
% 7.51/1.49      | k1_relat_1(sK2) != X2 ),
% 7.51/1.49      inference(resolution_lifted,[status(thm)],[c_129,c_246]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_293,plain,
% 7.51/1.49      ( k9_relat_1(sK2,X0) != k1_xboole_0
% 7.51/1.49      | k3_xboole_0(k1_relat_1(sK2),X0) = k1_xboole_0 ),
% 7.51/1.49      inference(unflattening,[status(thm)],[c_292]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_345,plain,
% 7.51/1.49      ( k9_relat_1(sK2,X0) != k1_xboole_0
% 7.51/1.49      | k3_xboole_0(k1_relat_1(sK2),X0) = k1_xboole_0 ),
% 7.51/1.49      inference(prop_impl,[status(thm)],[c_293]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_2439,plain,
% 7.51/1.49      ( k3_xboole_0(k1_relat_1(sK2),k6_subset_1(sK0,sK1)) = k1_xboole_0 ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_2354,c_345]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_3292,plain,
% 7.51/1.49      ( k6_subset_1(k1_relat_1(sK2),k6_subset_1(sK0,sK1)) = k5_xboole_0(k1_relat_1(sK2),k1_xboole_0) ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_2439,c_9]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_7,plain,
% 7.51/1.49      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
% 7.51/1.49      inference(cnf_transformation,[],[f51]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_8,plain,
% 7.51/1.49      ( r1_xboole_0(X0,k1_xboole_0) ),
% 7.51/1.49      inference(cnf_transformation,[],[f36]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_277,plain,
% 7.51/1.49      ( X0 != X1 | k3_xboole_0(X1,X2) = k1_xboole_0 | k1_xboole_0 != X2 ),
% 7.51/1.49      inference(resolution_lifted,[status(thm)],[c_129,c_8]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_278,plain,
% 7.51/1.49      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.51/1.49      inference(unflattening,[status(thm)],[c_277]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_662,plain,
% 7.51/1.49      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.51/1.49      inference(light_normalisation,[status(thm)],[c_7,c_278]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_3295,plain,
% 7.51/1.49      ( k6_subset_1(k1_relat_1(sK2),k6_subset_1(sK0,sK1)) = k1_relat_1(sK2) ),
% 7.51/1.49      inference(demodulation,[status(thm)],[c_3292,c_662]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_6,plain,
% 7.51/1.49      ( ~ r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) | k1_xboole_0 = X0 ),
% 7.51/1.49      inference(cnf_transformation,[],[f50]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_649,plain,
% 7.51/1.49      ( k1_xboole_0 = X0
% 7.51/1.49      | r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) != iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_682,plain,
% 7.51/1.49      ( k1_xboole_0 = X0 | r1_tarski(X0,k6_subset_1(X1,X0)) != iProver_top ),
% 7.51/1.49      inference(demodulation,[status(thm)],[c_649,c_9]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_11491,plain,
% 7.51/1.49      ( k6_subset_1(sK0,sK1) = k1_xboole_0
% 7.51/1.49      | r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2)) != iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_3295,c_682]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_13,negated_conjecture,
% 7.51/1.49      ( ~ r1_tarski(sK0,sK1) ),
% 7.51/1.49      inference(cnf_transformation,[],[f46]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_406,plain,( X0 = X0 ),theory(equality) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_421,plain,
% 7.51/1.49      ( k1_xboole_0 = k1_xboole_0 ),
% 7.51/1.49      inference(instantiation,[status(thm)],[c_406]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_3,plain,
% 7.51/1.49      ( r1_tarski(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
% 7.51/1.49      inference(cnf_transformation,[],[f48]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_731,plain,
% 7.51/1.49      ( r1_tarski(sK0,sK1)
% 7.51/1.49      | k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) != k1_xboole_0 ),
% 7.51/1.49      inference(instantiation,[status(thm)],[c_3]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_407,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_748,plain,
% 7.51/1.49      ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) != X0
% 7.51/1.49      | k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) = k1_xboole_0
% 7.51/1.49      | k1_xboole_0 != X0 ),
% 7.51/1.49      inference(instantiation,[status(thm)],[c_407]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_800,plain,
% 7.51/1.49      ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) != k6_subset_1(sK0,sK1)
% 7.51/1.49      | k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) = k1_xboole_0
% 7.51/1.49      | k1_xboole_0 != k6_subset_1(sK0,sK1) ),
% 7.51/1.49      inference(instantiation,[status(thm)],[c_748]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_801,plain,
% 7.51/1.49      ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) = k6_subset_1(sK0,sK1) ),
% 7.51/1.49      inference(instantiation,[status(thm)],[c_9]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_871,plain,
% 7.51/1.49      ( k6_subset_1(sK0,sK1) != X0
% 7.51/1.49      | k1_xboole_0 != X0
% 7.51/1.49      | k1_xboole_0 = k6_subset_1(sK0,sK1) ),
% 7.51/1.49      inference(instantiation,[status(thm)],[c_407]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_872,plain,
% 7.51/1.49      ( k6_subset_1(sK0,sK1) != k1_xboole_0
% 7.51/1.49      | k1_xboole_0 = k6_subset_1(sK0,sK1)
% 7.51/1.49      | k1_xboole_0 != k1_xboole_0 ),
% 7.51/1.49      inference(instantiation,[status(thm)],[c_871]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_21944,plain,
% 7.51/1.49      ( r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2)) != iProver_top ),
% 7.51/1.49      inference(global_propositional_subsumption,
% 7.51/1.49                [status(thm)],
% 7.51/1.49                [c_11491,c_13,c_421,c_731,c_800,c_801,c_872]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_15,negated_conjecture,
% 7.51/1.49      ( r1_tarski(sK0,k1_relat_1(sK2)) ),
% 7.51/1.49      inference(cnf_transformation,[],[f44]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_647,plain,
% 7.51/1.49      ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_5,plain,
% 7.51/1.49      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
% 7.51/1.49      inference(cnf_transformation,[],[f49]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_650,plain,
% 7.51/1.49      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_669,plain,
% 7.51/1.49      ( r1_tarski(k6_subset_1(X0,X1),X0) = iProver_top ),
% 7.51/1.49      inference(light_normalisation,[status(thm)],[c_650,c_9]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_4,plain,
% 7.51/1.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 7.51/1.49      inference(cnf_transformation,[],[f32]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_651,plain,
% 7.51/1.49      ( r1_tarski(X0,X1) != iProver_top
% 7.51/1.49      | r1_tarski(X1,X2) != iProver_top
% 7.51/1.49      | r1_tarski(X0,X2) = iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_1992,plain,
% 7.51/1.49      ( r1_tarski(X0,X1) != iProver_top
% 7.51/1.49      | r1_tarski(k6_subset_1(X0,X2),X1) = iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_669,c_651]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_14802,plain,
% 7.51/1.49      ( k6_subset_1(k6_subset_1(X0,X1),X2) = k1_xboole_0
% 7.51/1.49      | r1_tarski(X0,X2) != iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_1992,c_692]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_16271,plain,
% 7.51/1.49      ( k6_subset_1(k6_subset_1(sK0,X0),k1_relat_1(sK2)) = k1_xboole_0 ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_647,c_14802]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_652,plain,
% 7.51/1.49      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0
% 7.51/1.49      | r1_tarski(X0,X1) = iProver_top ),
% 7.51/1.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_687,plain,
% 7.51/1.49      ( k6_subset_1(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1) = iProver_top ),
% 7.51/1.49      inference(light_normalisation,[status(thm)],[c_652,c_9]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_16464,plain,
% 7.51/1.49      ( r1_tarski(k6_subset_1(sK0,X0),k1_relat_1(sK2)) = iProver_top ),
% 7.51/1.49      inference(superposition,[status(thm)],[c_16271,c_687]) ).
% 7.51/1.49  
% 7.51/1.49  cnf(c_21949,plain,
% 7.51/1.49      ( $false ),
% 7.51/1.49      inference(forward_subsumption_resolution,[status(thm)],[c_21944,c_16464]) ).
% 7.51/1.49  
% 7.51/1.49  
% 7.51/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.51/1.49  
% 7.51/1.49  ------                               Statistics
% 7.51/1.49  
% 7.51/1.49  ------ General
% 7.51/1.49  
% 7.51/1.49  abstr_ref_over_cycles:                  0
% 7.51/1.49  abstr_ref_under_cycles:                 0
% 7.51/1.49  gc_basic_clause_elim:                   0
% 7.51/1.49  forced_gc_time:                         0
% 7.51/1.49  parsing_time:                           0.01
% 7.51/1.49  unif_index_cands_time:                  0.
% 7.51/1.49  unif_index_add_time:                    0.
% 7.51/1.49  orderings_time:                         0.
% 7.51/1.49  out_proof_time:                         0.011
% 7.51/1.49  total_time:                             0.677
% 7.51/1.49  num_of_symbols:                         45
% 7.51/1.49  num_of_terms:                           23863
% 7.51/1.49  
% 7.51/1.49  ------ Preprocessing
% 7.51/1.49  
% 7.51/1.49  num_of_splits:                          0
% 7.51/1.49  num_of_split_atoms:                     0
% 7.51/1.49  num_of_reused_defs:                     0
% 7.51/1.49  num_eq_ax_congr_red:                    4
% 7.51/1.49  num_of_sem_filtered_clauses:            1
% 7.51/1.49  num_of_subtypes:                        0
% 7.51/1.49  monotx_restored_types:                  0
% 7.51/1.49  sat_num_of_epr_types:                   0
% 7.51/1.49  sat_num_of_non_cyclic_types:            0
% 7.51/1.49  sat_guarded_non_collapsed_types:        0
% 7.51/1.49  num_pure_diseq_elim:                    0
% 7.51/1.49  simp_replaced_by:                       0
% 7.51/1.49  res_preprocessed:                       81
% 7.51/1.49  prep_upred:                             0
% 7.51/1.49  prep_unflattend:                        11
% 7.51/1.49  smt_new_axioms:                         0
% 7.51/1.49  pred_elim_cands:                        1
% 7.51/1.49  pred_elim:                              4
% 7.51/1.49  pred_elim_cl:                           4
% 7.51/1.49  pred_elim_cycles:                       6
% 7.51/1.49  merged_defs:                            16
% 7.51/1.49  merged_defs_ncl:                        0
% 7.51/1.49  bin_hyper_res:                          16
% 7.51/1.49  prep_cycles:                            4
% 7.51/1.49  pred_elim_time:                         0.001
% 7.51/1.49  splitting_time:                         0.
% 7.51/1.49  sem_filter_time:                        0.
% 7.51/1.49  monotx_time:                            0.
% 7.51/1.49  subtype_inf_time:                       0.
% 7.51/1.49  
% 7.51/1.49  ------ Problem properties
% 7.51/1.49  
% 7.51/1.49  clauses:                                15
% 7.51/1.49  conjectures:                            3
% 7.51/1.49  epr:                                    2
% 7.51/1.49  horn:                                   15
% 7.51/1.49  ground:                                 4
% 7.51/1.49  unary:                                  9
% 7.51/1.49  binary:                                 5
% 7.51/1.49  lits:                                   22
% 7.51/1.49  lits_eq:                                12
% 7.51/1.49  fd_pure:                                0
% 7.51/1.49  fd_pseudo:                              0
% 7.51/1.49  fd_cond:                                1
% 7.51/1.49  fd_pseudo_cond:                         0
% 7.51/1.49  ac_symbols:                             0
% 7.51/1.49  
% 7.51/1.49  ------ Propositional Solver
% 7.51/1.49  
% 7.51/1.49  prop_solver_calls:                      31
% 7.51/1.49  prop_fast_solver_calls:                 533
% 7.51/1.49  smt_solver_calls:                       0
% 7.51/1.49  smt_fast_solver_calls:                  0
% 7.51/1.49  prop_num_of_clauses:                    7310
% 7.51/1.49  prop_preprocess_simplified:             11170
% 7.51/1.49  prop_fo_subsumed:                       8
% 7.51/1.49  prop_solver_time:                       0.
% 7.51/1.49  smt_solver_time:                        0.
% 7.51/1.49  smt_fast_solver_time:                   0.
% 7.51/1.49  prop_fast_solver_time:                  0.
% 7.51/1.49  prop_unsat_core_time:                   0.
% 7.51/1.49  
% 7.51/1.49  ------ QBF
% 7.51/1.49  
% 7.51/1.49  qbf_q_res:                              0
% 7.51/1.49  qbf_num_tautologies:                    0
% 7.51/1.49  qbf_prep_cycles:                        0
% 7.51/1.49  
% 7.51/1.49  ------ BMC1
% 7.51/1.49  
% 7.51/1.49  bmc1_current_bound:                     -1
% 7.51/1.49  bmc1_last_solved_bound:                 -1
% 7.51/1.49  bmc1_unsat_core_size:                   -1
% 7.51/1.49  bmc1_unsat_core_parents_size:           -1
% 7.51/1.49  bmc1_merge_next_fun:                    0
% 7.51/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.51/1.49  
% 7.51/1.49  ------ Instantiation
% 7.51/1.49  
% 7.51/1.49  inst_num_of_clauses:                    1955
% 7.51/1.49  inst_num_in_passive:                    909
% 7.51/1.49  inst_num_in_active:                     759
% 7.51/1.49  inst_num_in_unprocessed:                288
% 7.51/1.49  inst_num_of_loops:                      770
% 7.51/1.49  inst_num_of_learning_restarts:          0
% 7.51/1.49  inst_num_moves_active_passive:          7
% 7.51/1.49  inst_lit_activity:                      0
% 7.51/1.49  inst_lit_activity_moves:                0
% 7.51/1.49  inst_num_tautologies:                   0
% 7.51/1.49  inst_num_prop_implied:                  0
% 7.51/1.49  inst_num_existing_simplified:           0
% 7.51/1.49  inst_num_eq_res_simplified:             0
% 7.51/1.49  inst_num_child_elim:                    0
% 7.51/1.49  inst_num_of_dismatching_blockings:      988
% 7.51/1.49  inst_num_of_non_proper_insts:           1895
% 7.51/1.49  inst_num_of_duplicates:                 0
% 7.51/1.49  inst_inst_num_from_inst_to_res:         0
% 7.51/1.49  inst_dismatching_checking_time:         0.
% 7.51/1.49  
% 7.51/1.49  ------ Resolution
% 7.51/1.49  
% 7.51/1.49  res_num_of_clauses:                     0
% 7.51/1.49  res_num_in_passive:                     0
% 7.51/1.49  res_num_in_active:                      0
% 7.51/1.49  res_num_of_loops:                       85
% 7.51/1.49  res_forward_subset_subsumed:            244
% 7.51/1.49  res_backward_subset_subsumed:           6
% 7.51/1.49  res_forward_subsumed:                   0
% 7.51/1.49  res_backward_subsumed:                  0
% 7.51/1.49  res_forward_subsumption_resolution:     0
% 7.51/1.49  res_backward_subsumption_resolution:    0
% 7.51/1.49  res_clause_to_clause_subsumption:       4251
% 7.51/1.49  res_orphan_elimination:                 0
% 7.51/1.49  res_tautology_del:                      271
% 7.51/1.49  res_num_eq_res_simplified:              0
% 7.51/1.49  res_num_sel_changes:                    0
% 7.51/1.49  res_moves_from_active_to_pass:          0
% 7.51/1.49  
% 7.51/1.49  ------ Superposition
% 7.51/1.49  
% 7.51/1.49  sup_time_total:                         0.
% 7.51/1.49  sup_time_generating:                    0.
% 7.51/1.49  sup_time_sim_full:                      0.
% 7.51/1.49  sup_time_sim_immed:                     0.
% 7.51/1.49  
% 7.51/1.49  sup_num_of_clauses:                     975
% 7.51/1.49  sup_num_in_active:                      128
% 7.51/1.49  sup_num_in_passive:                     847
% 7.51/1.49  sup_num_of_loops:                       153
% 7.51/1.49  sup_fw_superposition:                   1753
% 7.51/1.49  sup_bw_superposition:                   1032
% 7.51/1.49  sup_immediate_simplified:               1752
% 7.51/1.49  sup_given_eliminated:                   0
% 7.51/1.49  comparisons_done:                       0
% 7.51/1.49  comparisons_avoided:                    0
% 7.51/1.49  
% 7.51/1.49  ------ Simplifications
% 7.51/1.49  
% 7.51/1.49  
% 7.51/1.49  sim_fw_subset_subsumed:                 65
% 7.51/1.49  sim_bw_subset_subsumed:                 0
% 7.51/1.49  sim_fw_subsumed:                        627
% 7.51/1.49  sim_bw_subsumed:                        83
% 7.51/1.49  sim_fw_subsumption_res:                 1
% 7.51/1.49  sim_bw_subsumption_res:                 0
% 7.51/1.49  sim_tautology_del:                      6
% 7.51/1.49  sim_eq_tautology_del:                   139
% 7.51/1.49  sim_eq_res_simp:                        151
% 7.51/1.49  sim_fw_demodulated:                     365
% 7.51/1.49  sim_bw_demodulated:                     38
% 7.51/1.49  sim_light_normalised:                   1264
% 7.51/1.49  sim_joinable_taut:                      0
% 7.51/1.49  sim_joinable_simp:                      0
% 7.51/1.49  sim_ac_normalised:                      0
% 7.51/1.49  sim_smt_subsumption:                    0
% 7.51/1.49  
%------------------------------------------------------------------------------
