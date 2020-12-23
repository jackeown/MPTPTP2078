%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:52:12 EST 2020

% Result     : Theorem 11.69s
% Output     : CNFRefutation 11.69s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 205 expanded)
%              Number of clauses        :   54 (  69 expanded)
%              Number of leaves         :   11 (  40 expanded)
%              Depth                    :   16
%              Number of atoms          :  235 ( 687 expanded)
%              Number of equality atoms :   88 ( 148 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

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

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f31,plain,
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

fof(f32,plain,
    ( ~ r1_tarski(sK0,sK1)
    & v2_funct_1(sK2)
    & r1_tarski(sK0,k1_relat_1(sK2))
    & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f31])).

fof(f48,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f49,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f52,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f50,plain,(
    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f32])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k6_subset_1(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f37,f44])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f28])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f58,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f34])).

fof(f51,plain,(
    r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f32])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f56,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(definition_unfolding,[],[f41,f44])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f36,f44])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f35,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f53,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_19,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_772,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k6_subset_1(X1,X2)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_780,plain,
    ( k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k6_subset_1(X1,X2))
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3085,plain,
    ( k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) = k9_relat_1(sK2,k6_subset_1(X0,X1))
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_772,c_780])).

cnf(c_18,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_21,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_15,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_24,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3627,plain,
    ( k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) = k9_relat_1(sK2,k6_subset_1(X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3085,c_21,c_24])).

cnf(c_17,negated_conjecture,
    ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_774,plain,
    ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k6_subset_1(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_788,plain,
    ( k6_subset_1(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1771,plain,
    ( k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_774,c_788])).

cnf(c_3637,plain,
    ( k9_relat_1(sK2,k6_subset_1(sK0,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3627,c_1771])).

cnf(c_13,plain,
    ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_778,plain,
    ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) = iProver_top
    | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3797,plain,
    ( r1_tarski(k6_subset_1(sK0,sK1),k10_relat_1(sK2,k1_xboole_0)) = iProver_top
    | r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3637,c_778])).

cnf(c_20,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_45208,plain,
    ( r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2)) != iProver_top
    | r1_tarski(k6_subset_1(sK0,sK1),k10_relat_1(sK2,k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3797,c_20])).

cnf(c_45209,plain,
    ( r1_tarski(k6_subset_1(sK0,sK1),k10_relat_1(sK2,k1_xboole_0)) = iProver_top
    | r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_45208])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k6_subset_1(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k6_subset_1(X1,X2)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_779,plain,
    ( k6_subset_1(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k6_subset_1(X1,X2))
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2465,plain,
    ( k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k6_subset_1(X0,X1))
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_772,c_779])).

cnf(c_3599,plain,
    ( k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k6_subset_1(X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2465,c_21])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_789,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1766,plain,
    ( k6_subset_1(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_789,c_788])).

cnf(c_3607,plain,
    ( k10_relat_1(sK2,k6_subset_1(X0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3599,c_1766])).

cnf(c_3609,plain,
    ( k10_relat_1(sK2,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3607,c_1766])).

cnf(c_45212,plain,
    ( r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2)) != iProver_top
    | r1_tarski(k6_subset_1(sK0,sK1),k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_45209,c_3609])).

cnf(c_16,negated_conjecture,
    ( r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_775,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_8,plain,
    ( r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_783,plain,
    ( r1_tarski(k6_subset_1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_785,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3045,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k6_subset_1(X0,X2),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_783,c_785])).

cnf(c_18442,plain,
    ( k6_subset_1(k6_subset_1(X0,X1),X2) = k1_xboole_0
    | r1_tarski(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3045,c_788])).

cnf(c_41052,plain,
    ( k6_subset_1(k6_subset_1(sK0,X0),k1_relat_1(sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_775,c_18442])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | k6_subset_1(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_787,plain,
    ( k6_subset_1(X0,X1) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_41432,plain,
    ( r1_tarski(k6_subset_1(sK0,X0),k1_relat_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_41052,c_787])).

cnf(c_45215,plain,
    ( r1_tarski(k6_subset_1(sK0,sK1),k1_xboole_0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_45212,c_41432])).

cnf(c_7,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1175,plain,
    ( r1_tarski(k1_xboole_0,k6_subset_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1176,plain,
    ( r1_tarski(k1_xboole_0,k6_subset_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1175])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1094,plain,
    ( ~ r1_tarski(k6_subset_1(sK0,sK1),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k6_subset_1(sK0,sK1))
    | k6_subset_1(sK0,sK1) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1095,plain,
    ( k6_subset_1(sK0,sK1) = k1_xboole_0
    | r1_tarski(k6_subset_1(sK0,sK1),k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,k6_subset_1(sK0,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1094])).

cnf(c_953,plain,
    ( r1_tarski(sK0,sK1)
    | k6_subset_1(sK0,sK1) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_14,negated_conjecture,
    ( ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f53])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_45215,c_1176,c_1095,c_953,c_14])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.14/0.33  % Computer   : n018.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 19:54:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 11.69/1.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.69/1.99  
% 11.69/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.69/1.99  
% 11.69/1.99  ------  iProver source info
% 11.69/1.99  
% 11.69/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.69/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.69/1.99  git: non_committed_changes: false
% 11.69/1.99  git: last_make_outside_of_git: false
% 11.69/1.99  
% 11.69/1.99  ------ 
% 11.69/1.99  ------ Parsing...
% 11.69/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.69/1.99  
% 11.69/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 11.69/1.99  
% 11.69/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.69/1.99  
% 11.69/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.69/1.99  ------ Proving...
% 11.69/1.99  ------ Problem Properties 
% 11.69/1.99  
% 11.69/1.99  
% 11.69/1.99  clauses                                 19
% 11.69/1.99  conjectures                             6
% 11.69/1.99  EPR                                     9
% 11.69/1.99  Horn                                    19
% 11.69/1.99  unary                                   9
% 11.69/1.99  binary                                  5
% 11.69/1.99  lits                                    35
% 11.69/1.99  lits eq                                 6
% 11.69/1.99  fd_pure                                 0
% 11.69/1.99  fd_pseudo                               0
% 11.69/1.99  fd_cond                                 1
% 11.69/1.99  fd_pseudo_cond                          1
% 11.69/1.99  AC symbols                              0
% 11.69/1.99  
% 11.69/1.99  ------ Input Options Time Limit: Unbounded
% 11.69/1.99  
% 11.69/1.99  
% 11.69/1.99  ------ 
% 11.69/1.99  Current options:
% 11.69/1.99  ------ 
% 11.69/1.99  
% 11.69/1.99  
% 11.69/1.99  
% 11.69/1.99  
% 11.69/1.99  ------ Proving...
% 11.69/1.99  
% 11.69/1.99  
% 11.69/1.99  % SZS status Theorem for theBenchmark.p
% 11.69/1.99  
% 11.69/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.69/1.99  
% 11.69/1.99  fof(f13,conjecture,(
% 11.69/1.99    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 11.69/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.69/1.99  
% 11.69/1.99  fof(f14,negated_conjecture,(
% 11.69/1.99    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 11.69/1.99    inference(negated_conjecture,[],[f13])).
% 11.69/1.99  
% 11.69/1.99  fof(f26,plain,(
% 11.69/1.99    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 11.69/1.99    inference(ennf_transformation,[],[f14])).
% 11.69/1.99  
% 11.69/1.99  fof(f27,plain,(
% 11.69/1.99    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 11.69/1.99    inference(flattening,[],[f26])).
% 11.69/1.99  
% 11.69/1.99  fof(f31,plain,(
% 11.69/1.99    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 11.69/1.99    introduced(choice_axiom,[])).
% 11.69/1.99  
% 11.69/1.99  fof(f32,plain,(
% 11.69/1.99    ~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 11.69/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f31])).
% 11.69/1.99  
% 11.69/1.99  fof(f48,plain,(
% 11.69/1.99    v1_relat_1(sK2)),
% 11.69/1.99    inference(cnf_transformation,[],[f32])).
% 11.69/1.99  
% 11.69/1.99  fof(f10,axiom,(
% 11.69/1.99    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1))))),
% 11.69/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.69/1.99  
% 11.69/1.99  fof(f20,plain,(
% 11.69/1.99    ! [X0,X1,X2] : ((k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1)) | ~v2_funct_1(X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 11.69/1.99    inference(ennf_transformation,[],[f10])).
% 11.69/1.99  
% 11.69/1.99  fof(f21,plain,(
% 11.69/1.99    ! [X0,X1,X2] : (k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 11.69/1.99    inference(flattening,[],[f20])).
% 11.69/1.99  
% 11.69/1.99  fof(f45,plain,(
% 11.69/1.99    ( ! [X2,X0,X1] : (k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 11.69/1.99    inference(cnf_transformation,[],[f21])).
% 11.69/1.99  
% 11.69/1.99  fof(f49,plain,(
% 11.69/1.99    v1_funct_1(sK2)),
% 11.69/1.99    inference(cnf_transformation,[],[f32])).
% 11.69/1.99  
% 11.69/1.99  fof(f52,plain,(
% 11.69/1.99    v2_funct_1(sK2)),
% 11.69/1.99    inference(cnf_transformation,[],[f32])).
% 11.69/1.99  
% 11.69/1.99  fof(f50,plain,(
% 11.69/1.99    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 11.69/1.99    inference(cnf_transformation,[],[f32])).
% 11.69/1.99  
% 11.69/1.99  fof(f2,axiom,(
% 11.69/1.99    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 11.69/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.69/1.99  
% 11.69/1.99  fof(f30,plain,(
% 11.69/1.99    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 11.69/1.99    inference(nnf_transformation,[],[f2])).
% 11.69/1.99  
% 11.69/1.99  fof(f37,plain,(
% 11.69/1.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 11.69/1.99    inference(cnf_transformation,[],[f30])).
% 11.69/1.99  
% 11.69/1.99  fof(f9,axiom,(
% 11.69/1.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 11.69/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.69/1.99  
% 11.69/1.99  fof(f44,plain,(
% 11.69/1.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 11.69/1.99    inference(cnf_transformation,[],[f9])).
% 11.69/1.99  
% 11.69/1.99  fof(f54,plain,(
% 11.69/1.99    ( ! [X0,X1] : (k1_xboole_0 = k6_subset_1(X0,X1) | ~r1_tarski(X0,X1)) )),
% 11.69/1.99    inference(definition_unfolding,[],[f37,f44])).
% 11.69/1.99  
% 11.69/1.99  fof(f12,axiom,(
% 11.69/1.99    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 11.69/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.69/1.99  
% 11.69/1.99  fof(f24,plain,(
% 11.69/1.99    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 11.69/1.99    inference(ennf_transformation,[],[f12])).
% 11.69/1.99  
% 11.69/1.99  fof(f25,plain,(
% 11.69/1.99    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 11.69/1.99    inference(flattening,[],[f24])).
% 11.69/1.99  
% 11.69/1.99  fof(f47,plain,(
% 11.69/1.99    ( ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 11.69/1.99    inference(cnf_transformation,[],[f25])).
% 11.69/1.99  
% 11.69/1.99  fof(f11,axiom,(
% 11.69/1.99    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1)))),
% 11.69/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.69/1.99  
% 11.69/1.99  fof(f22,plain,(
% 11.69/1.99    ! [X0,X1,X2] : (k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 11.69/1.99    inference(ennf_transformation,[],[f11])).
% 11.69/1.99  
% 11.69/1.99  fof(f23,plain,(
% 11.69/1.99    ! [X0,X1,X2] : (k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 11.69/1.99    inference(flattening,[],[f22])).
% 11.69/1.99  
% 11.69/1.99  fof(f46,plain,(
% 11.69/1.99    ( ! [X2,X0,X1] : (k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 11.69/1.99    inference(cnf_transformation,[],[f23])).
% 11.69/1.99  
% 11.69/1.99  fof(f1,axiom,(
% 11.69/1.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.69/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.69/1.99  
% 11.69/1.99  fof(f28,plain,(
% 11.69/1.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.69/1.99    inference(nnf_transformation,[],[f1])).
% 11.69/1.99  
% 11.69/1.99  fof(f29,plain,(
% 11.69/1.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.69/1.99    inference(flattening,[],[f28])).
% 11.69/1.99  
% 11.69/1.99  fof(f34,plain,(
% 11.69/1.99    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 11.69/1.99    inference(cnf_transformation,[],[f29])).
% 11.69/1.99  
% 11.69/1.99  fof(f58,plain,(
% 11.69/1.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.69/1.99    inference(equality_resolution,[],[f34])).
% 11.69/1.99  
% 11.69/1.99  fof(f51,plain,(
% 11.69/1.99    r1_tarski(sK0,k1_relat_1(sK2))),
% 11.69/1.99    inference(cnf_transformation,[],[f32])).
% 11.69/1.99  
% 11.69/1.99  fof(f6,axiom,(
% 11.69/1.99    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 11.69/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.69/1.99  
% 11.69/1.99  fof(f41,plain,(
% 11.69/1.99    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 11.69/1.99    inference(cnf_transformation,[],[f6])).
% 11.69/1.99  
% 11.69/1.99  fof(f56,plain,(
% 11.69/1.99    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 11.69/1.99    inference(definition_unfolding,[],[f41,f44])).
% 11.69/1.99  
% 11.69/1.99  fof(f4,axiom,(
% 11.69/1.99    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 11.69/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.69/1.99  
% 11.69/1.99  fof(f16,plain,(
% 11.69/1.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 11.69/1.99    inference(ennf_transformation,[],[f4])).
% 11.69/1.99  
% 11.69/1.99  fof(f17,plain,(
% 11.69/1.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 11.69/1.99    inference(flattening,[],[f16])).
% 11.69/1.99  
% 11.69/1.99  fof(f39,plain,(
% 11.69/1.99    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 11.69/1.99    inference(cnf_transformation,[],[f17])).
% 11.69/1.99  
% 11.69/1.99  fof(f36,plain,(
% 11.69/1.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 11.69/1.99    inference(cnf_transformation,[],[f30])).
% 11.69/1.99  
% 11.69/1.99  fof(f55,plain,(
% 11.69/1.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k6_subset_1(X0,X1)) )),
% 11.69/1.99    inference(definition_unfolding,[],[f36,f44])).
% 11.69/1.99  
% 11.69/1.99  fof(f5,axiom,(
% 11.69/1.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 11.69/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.69/1.99  
% 11.69/1.99  fof(f40,plain,(
% 11.69/1.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 11.69/1.99    inference(cnf_transformation,[],[f5])).
% 11.69/1.99  
% 11.69/1.99  fof(f35,plain,(
% 11.69/1.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 11.69/1.99    inference(cnf_transformation,[],[f29])).
% 11.69/1.99  
% 11.69/1.99  fof(f53,plain,(
% 11.69/1.99    ~r1_tarski(sK0,sK1)),
% 11.69/1.99    inference(cnf_transformation,[],[f32])).
% 11.69/1.99  
% 11.69/1.99  cnf(c_19,negated_conjecture,
% 11.69/1.99      ( v1_relat_1(sK2) ),
% 11.69/1.99      inference(cnf_transformation,[],[f48]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_772,plain,
% 11.69/1.99      ( v1_relat_1(sK2) = iProver_top ),
% 11.69/1.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_11,plain,
% 11.69/1.99      ( ~ v1_relat_1(X0)
% 11.69/1.99      | ~ v1_funct_1(X0)
% 11.69/1.99      | ~ v2_funct_1(X0)
% 11.69/1.99      | k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k6_subset_1(X1,X2)) ),
% 11.69/1.99      inference(cnf_transformation,[],[f45]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_780,plain,
% 11.69/1.99      ( k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k6_subset_1(X1,X2))
% 11.69/1.99      | v1_relat_1(X0) != iProver_top
% 11.69/1.99      | v1_funct_1(X0) != iProver_top
% 11.69/1.99      | v2_funct_1(X0) != iProver_top ),
% 11.69/1.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_3085,plain,
% 11.69/1.99      ( k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) = k9_relat_1(sK2,k6_subset_1(X0,X1))
% 11.69/1.99      | v1_funct_1(sK2) != iProver_top
% 11.69/1.99      | v2_funct_1(sK2) != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_772,c_780]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_18,negated_conjecture,
% 11.69/1.99      ( v1_funct_1(sK2) ),
% 11.69/1.99      inference(cnf_transformation,[],[f49]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_21,plain,
% 11.69/1.99      ( v1_funct_1(sK2) = iProver_top ),
% 11.69/1.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_15,negated_conjecture,
% 11.69/1.99      ( v2_funct_1(sK2) ),
% 11.69/1.99      inference(cnf_transformation,[],[f52]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_24,plain,
% 11.69/1.99      ( v2_funct_1(sK2) = iProver_top ),
% 11.69/1.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_3627,plain,
% 11.69/1.99      ( k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) = k9_relat_1(sK2,k6_subset_1(X0,X1)) ),
% 11.69/1.99      inference(global_propositional_subsumption,
% 11.69/1.99                [status(thm)],
% 11.69/1.99                [c_3085,c_21,c_24]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_17,negated_conjecture,
% 11.69/1.99      ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
% 11.69/1.99      inference(cnf_transformation,[],[f50]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_774,plain,
% 11.69/1.99      ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) = iProver_top ),
% 11.69/1.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_3,plain,
% 11.69/1.99      ( ~ r1_tarski(X0,X1) | k6_subset_1(X0,X1) = k1_xboole_0 ),
% 11.69/1.99      inference(cnf_transformation,[],[f54]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_788,plain,
% 11.69/1.99      ( k6_subset_1(X0,X1) = k1_xboole_0
% 11.69/1.99      | r1_tarski(X0,X1) != iProver_top ),
% 11.69/1.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_1771,plain,
% 11.69/1.99      ( k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) = k1_xboole_0 ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_774,c_788]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_3637,plain,
% 11.69/1.99      ( k9_relat_1(sK2,k6_subset_1(sK0,sK1)) = k1_xboole_0 ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_3627,c_1771]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_13,plain,
% 11.69/1.99      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
% 11.69/1.99      | ~ r1_tarski(X0,k1_relat_1(X1))
% 11.69/1.99      | ~ v1_relat_1(X1) ),
% 11.69/1.99      inference(cnf_transformation,[],[f47]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_778,plain,
% 11.69/1.99      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) = iProver_top
% 11.69/1.99      | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
% 11.69/1.99      | v1_relat_1(X1) != iProver_top ),
% 11.69/1.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_3797,plain,
% 11.69/1.99      ( r1_tarski(k6_subset_1(sK0,sK1),k10_relat_1(sK2,k1_xboole_0)) = iProver_top
% 11.69/1.99      | r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2)) != iProver_top
% 11.69/1.99      | v1_relat_1(sK2) != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_3637,c_778]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_20,plain,
% 11.69/1.99      ( v1_relat_1(sK2) = iProver_top ),
% 11.69/1.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_45208,plain,
% 11.69/1.99      ( r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2)) != iProver_top
% 11.69/1.99      | r1_tarski(k6_subset_1(sK0,sK1),k10_relat_1(sK2,k1_xboole_0)) = iProver_top ),
% 11.69/1.99      inference(global_propositional_subsumption,
% 11.69/1.99                [status(thm)],
% 11.69/1.99                [c_3797,c_20]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_45209,plain,
% 11.69/1.99      ( r1_tarski(k6_subset_1(sK0,sK1),k10_relat_1(sK2,k1_xboole_0)) = iProver_top
% 11.69/1.99      | r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2)) != iProver_top ),
% 11.69/1.99      inference(renaming,[status(thm)],[c_45208]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_12,plain,
% 11.69/1.99      ( ~ v1_relat_1(X0)
% 11.69/1.99      | ~ v1_funct_1(X0)
% 11.69/1.99      | k6_subset_1(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k6_subset_1(X1,X2)) ),
% 11.69/1.99      inference(cnf_transformation,[],[f46]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_779,plain,
% 11.69/1.99      ( k6_subset_1(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k6_subset_1(X1,X2))
% 11.69/1.99      | v1_relat_1(X0) != iProver_top
% 11.69/1.99      | v1_funct_1(X0) != iProver_top ),
% 11.69/1.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_2465,plain,
% 11.69/1.99      ( k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k6_subset_1(X0,X1))
% 11.69/1.99      | v1_funct_1(sK2) != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_772,c_779]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_3599,plain,
% 11.69/1.99      ( k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k6_subset_1(X0,X1)) ),
% 11.69/1.99      inference(global_propositional_subsumption,
% 11.69/1.99                [status(thm)],
% 11.69/1.99                [c_2465,c_21]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_1,plain,
% 11.69/1.99      ( r1_tarski(X0,X0) ),
% 11.69/1.99      inference(cnf_transformation,[],[f58]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_789,plain,
% 11.69/1.99      ( r1_tarski(X0,X0) = iProver_top ),
% 11.69/1.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_1766,plain,
% 11.69/1.99      ( k6_subset_1(X0,X0) = k1_xboole_0 ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_789,c_788]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_3607,plain,
% 11.69/1.99      ( k10_relat_1(sK2,k6_subset_1(X0,X0)) = k1_xboole_0 ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_3599,c_1766]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_3609,plain,
% 11.69/1.99      ( k10_relat_1(sK2,k1_xboole_0) = k1_xboole_0 ),
% 11.69/1.99      inference(light_normalisation,[status(thm)],[c_3607,c_1766]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_45212,plain,
% 11.69/1.99      ( r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2)) != iProver_top
% 11.69/1.99      | r1_tarski(k6_subset_1(sK0,sK1),k1_xboole_0) = iProver_top ),
% 11.69/1.99      inference(light_normalisation,[status(thm)],[c_45209,c_3609]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_16,negated_conjecture,
% 11.69/1.99      ( r1_tarski(sK0,k1_relat_1(sK2)) ),
% 11.69/1.99      inference(cnf_transformation,[],[f51]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_775,plain,
% 11.69/1.99      ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top ),
% 11.69/1.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_8,plain,
% 11.69/1.99      ( r1_tarski(k6_subset_1(X0,X1),X0) ),
% 11.69/1.99      inference(cnf_transformation,[],[f56]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_783,plain,
% 11.69/1.99      ( r1_tarski(k6_subset_1(X0,X1),X0) = iProver_top ),
% 11.69/1.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_6,plain,
% 11.69/1.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 11.69/1.99      inference(cnf_transformation,[],[f39]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_785,plain,
% 11.69/1.99      ( r1_tarski(X0,X1) != iProver_top
% 11.69/1.99      | r1_tarski(X1,X2) != iProver_top
% 11.69/1.99      | r1_tarski(X0,X2) = iProver_top ),
% 11.69/1.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_3045,plain,
% 11.69/1.99      ( r1_tarski(X0,X1) != iProver_top
% 11.69/1.99      | r1_tarski(k6_subset_1(X0,X2),X1) = iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_783,c_785]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_18442,plain,
% 11.69/1.99      ( k6_subset_1(k6_subset_1(X0,X1),X2) = k1_xboole_0
% 11.69/1.99      | r1_tarski(X0,X2) != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_3045,c_788]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_41052,plain,
% 11.69/1.99      ( k6_subset_1(k6_subset_1(sK0,X0),k1_relat_1(sK2)) = k1_xboole_0 ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_775,c_18442]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_4,plain,
% 11.69/1.99      ( r1_tarski(X0,X1) | k6_subset_1(X0,X1) != k1_xboole_0 ),
% 11.69/1.99      inference(cnf_transformation,[],[f55]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_787,plain,
% 11.69/1.99      ( k6_subset_1(X0,X1) != k1_xboole_0
% 11.69/1.99      | r1_tarski(X0,X1) = iProver_top ),
% 11.69/1.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_41432,plain,
% 11.69/1.99      ( r1_tarski(k6_subset_1(sK0,X0),k1_relat_1(sK2)) = iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_41052,c_787]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_45215,plain,
% 11.69/1.99      ( r1_tarski(k6_subset_1(sK0,sK1),k1_xboole_0) = iProver_top ),
% 11.69/1.99      inference(forward_subsumption_resolution,
% 11.69/1.99                [status(thm)],
% 11.69/1.99                [c_45212,c_41432]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_7,plain,
% 11.69/1.99      ( r1_tarski(k1_xboole_0,X0) ),
% 11.69/1.99      inference(cnf_transformation,[],[f40]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_1175,plain,
% 11.69/1.99      ( r1_tarski(k1_xboole_0,k6_subset_1(sK0,sK1)) ),
% 11.69/1.99      inference(instantiation,[status(thm)],[c_7]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_1176,plain,
% 11.69/1.99      ( r1_tarski(k1_xboole_0,k6_subset_1(sK0,sK1)) = iProver_top ),
% 11.69/1.99      inference(predicate_to_equality,[status(thm)],[c_1175]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_0,plain,
% 11.69/1.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 11.69/1.99      inference(cnf_transformation,[],[f35]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_1094,plain,
% 11.69/1.99      ( ~ r1_tarski(k6_subset_1(sK0,sK1),k1_xboole_0)
% 11.69/1.99      | ~ r1_tarski(k1_xboole_0,k6_subset_1(sK0,sK1))
% 11.69/1.99      | k6_subset_1(sK0,sK1) = k1_xboole_0 ),
% 11.69/1.99      inference(instantiation,[status(thm)],[c_0]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_1095,plain,
% 11.69/1.99      ( k6_subset_1(sK0,sK1) = k1_xboole_0
% 11.69/1.99      | r1_tarski(k6_subset_1(sK0,sK1),k1_xboole_0) != iProver_top
% 11.69/1.99      | r1_tarski(k1_xboole_0,k6_subset_1(sK0,sK1)) != iProver_top ),
% 11.69/1.99      inference(predicate_to_equality,[status(thm)],[c_1094]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_953,plain,
% 11.69/1.99      ( r1_tarski(sK0,sK1) | k6_subset_1(sK0,sK1) != k1_xboole_0 ),
% 11.69/1.99      inference(instantiation,[status(thm)],[c_4]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_14,negated_conjecture,
% 11.69/1.99      ( ~ r1_tarski(sK0,sK1) ),
% 11.69/1.99      inference(cnf_transformation,[],[f53]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(contradiction,plain,
% 11.69/1.99      ( $false ),
% 11.69/1.99      inference(minisat,[status(thm)],[c_45215,c_1176,c_1095,c_953,c_14]) ).
% 11.69/1.99  
% 11.69/1.99  
% 11.69/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.69/1.99  
% 11.69/1.99  ------                               Statistics
% 11.69/1.99  
% 11.69/1.99  ------ Selected
% 11.69/1.99  
% 11.69/1.99  total_time:                             1.134
% 11.69/1.99  
%------------------------------------------------------------------------------
