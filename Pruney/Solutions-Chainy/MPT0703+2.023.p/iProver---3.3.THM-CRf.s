%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:52:18 EST 2020

% Result     : Theorem 27.61s
% Output     : CNFRefutation 27.61s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 209 expanded)
%              Number of clauses        :   52 (  71 expanded)
%              Number of leaves         :   11 (  41 expanded)
%              Depth                    :   17
%              Number of atoms          :  190 ( 702 expanded)
%              Number of equality atoms :   85 ( 120 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(X0,k2_relat_1(X2))
          & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( r1_tarski(X0,k2_relat_1(X2))
            & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f25,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & r1_tarski(X0,k2_relat_1(X2))
        & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(sK0,sK1)
      & r1_tarski(sK0,k2_relat_1(sK2))
      & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ~ r1_tarski(sK0,sK1)
    & r1_tarski(sK0,k2_relat_1(sK2))
    & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f25])).

fof(f40,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f41,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f42,plain,(
    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f26])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f43,plain,(
    r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f30,f32])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f31,f32])).

fof(f44,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_16,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_662,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k3_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_668,plain,
    ( k3_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k3_xboole_0(X1,X2))
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2126,plain,
    ( k3_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k3_xboole_0(X0,X1))
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_662,c_668])).

cnf(c_15,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_18,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2839,plain,
    ( k3_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k3_xboole_0(X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2126,c_18])).

cnf(c_14,negated_conjecture,
    ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_664,plain,
    ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_670,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1191,plain,
    ( k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) = k10_relat_1(sK2,sK0) ),
    inference(superposition,[status(thm)],[c_664,c_670])).

cnf(c_2848,plain,
    ( k10_relat_1(sK2,k3_xboole_0(sK0,sK1)) = k10_relat_1(sK2,sK0) ),
    inference(superposition,[status(thm)],[c_2839,c_1191])).

cnf(c_13,negated_conjecture,
    ( r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_665,plain,
    ( r1_tarski(sK0,k2_relat_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_7,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_671,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_672,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1348,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0 ),
    inference(superposition,[status(thm)],[c_671,c_672])).

cnf(c_5,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_673,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3729,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k3_xboole_0(X0,X2),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1348,c_673])).

cnf(c_12579,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),X2) = X2
    | r1_tarski(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3729,c_672])).

cnf(c_12627,plain,
    ( k2_xboole_0(k3_xboole_0(sK0,X0),k2_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_665,c_12579])).

cnf(c_9,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_669,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_13045,plain,
    ( r1_tarski(k3_xboole_0(sK0,X0),k2_relat_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_12627,c_669])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_667,plain,
    ( k9_relat_1(X0,k10_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_13391,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,k3_xboole_0(sK0,X0))) = k3_xboole_0(sK0,X0)
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_13045,c_667])).

cnf(c_17,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_105315,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,k3_xboole_0(sK0,X0))) = k3_xboole_0(sK0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13391,c_17,c_18])).

cnf(c_105319,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,sK0)) = k3_xboole_0(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_2848,c_105315])).

cnf(c_1158,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,sK0)) = sK0
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_665,c_667])).

cnf(c_835,plain,
    ( ~ r1_tarski(sK0,k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k9_relat_1(sK2,k10_relat_1(sK2,sK0)) = sK0 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1828,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,sK0)) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1158,c_16,c_15,c_13,c_835])).

cnf(c_105471,plain,
    ( k3_xboole_0(sK0,sK1) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_105319,c_1828])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_674,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_108019,plain,
    ( k5_xboole_0(sK0,sK0) != k1_xboole_0
    | r1_tarski(sK0,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_105471,c_674])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_675,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2272,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,k2_relat_1(sK2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_665,c_675])).

cnf(c_1190,plain,
    ( k3_xboole_0(sK0,k2_relat_1(sK2)) = sK0 ),
    inference(superposition,[status(thm)],[c_665,c_670])).

cnf(c_2281,plain,
    ( k5_xboole_0(sK0,sK0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2272,c_1190])).

cnf(c_108093,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK0,sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_108019,c_2281])).

cnf(c_108094,plain,
    ( r1_tarski(sK0,sK1) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_108093])).

cnf(c_12,negated_conjecture,
    ( ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_21,plain,
    ( r1_tarski(sK0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_108094,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:32:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 27.61/3.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.61/3.98  
% 27.61/3.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.61/3.98  
% 27.61/3.98  ------  iProver source info
% 27.61/3.98  
% 27.61/3.98  git: date: 2020-06-30 10:37:57 +0100
% 27.61/3.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.61/3.98  git: non_committed_changes: false
% 27.61/3.98  git: last_make_outside_of_git: false
% 27.61/3.98  
% 27.61/3.98  ------ 
% 27.61/3.98  ------ Parsing...
% 27.61/3.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.61/3.98  
% 27.61/3.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 27.61/3.98  
% 27.61/3.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.61/3.98  
% 27.61/3.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.61/3.98  ------ Proving...
% 27.61/3.98  ------ Problem Properties 
% 27.61/3.98  
% 27.61/3.98  
% 27.61/3.98  clauses                                 16
% 27.61/3.98  conjectures                             5
% 27.61/3.98  EPR                                     5
% 27.61/3.98  Horn                                    16
% 27.61/3.98  unary                                   8
% 27.61/3.98  binary                                  5
% 27.61/3.98  lits                                    28
% 27.61/3.98  lits eq                                 7
% 27.61/3.98  fd_pure                                 0
% 27.61/3.98  fd_pseudo                               0
% 27.61/3.98  fd_cond                                 0
% 27.61/3.98  fd_pseudo_cond                          1
% 27.61/3.98  AC symbols                              0
% 27.61/3.98  
% 27.61/3.98  ------ Input Options Time Limit: Unbounded
% 27.61/3.98  
% 27.61/3.98  
% 27.61/3.98  ------ 
% 27.61/3.98  Current options:
% 27.61/3.98  ------ 
% 27.61/3.98  
% 27.61/3.98  
% 27.61/3.98  
% 27.61/3.98  
% 27.61/3.98  ------ Proving...
% 27.61/3.98  
% 27.61/3.98  
% 27.61/3.98  % SZS status Theorem for theBenchmark.p
% 27.61/3.98  
% 27.61/3.98  % SZS output start CNFRefutation for theBenchmark.p
% 27.61/3.98  
% 27.61/3.98  fof(f11,conjecture,(
% 27.61/3.98    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 27.61/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.61/3.98  
% 27.61/3.98  fof(f12,negated_conjecture,(
% 27.61/3.98    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 27.61/3.98    inference(negated_conjecture,[],[f11])).
% 27.61/3.98  
% 27.61/3.98  fof(f20,plain,(
% 27.61/3.98    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 27.61/3.98    inference(ennf_transformation,[],[f12])).
% 27.61/3.98  
% 27.61/3.98  fof(f21,plain,(
% 27.61/3.98    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 27.61/3.98    inference(flattening,[],[f20])).
% 27.61/3.98  
% 27.61/3.98  fof(f25,plain,(
% 27.61/3.98    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 27.61/3.98    introduced(choice_axiom,[])).
% 27.61/3.98  
% 27.61/3.98  fof(f26,plain,(
% 27.61/3.98    ~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 27.61/3.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f25])).
% 27.61/3.98  
% 27.61/3.98  fof(f40,plain,(
% 27.61/3.98    v1_relat_1(sK2)),
% 27.61/3.98    inference(cnf_transformation,[],[f26])).
% 27.61/3.98  
% 27.61/3.98  fof(f9,axiom,(
% 27.61/3.98    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1)))),
% 27.61/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.61/3.98  
% 27.61/3.98  fof(f16,plain,(
% 27.61/3.98    ! [X0,X1,X2] : (k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 27.61/3.98    inference(ennf_transformation,[],[f9])).
% 27.61/3.98  
% 27.61/3.98  fof(f17,plain,(
% 27.61/3.98    ! [X0,X1,X2] : (k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 27.61/3.98    inference(flattening,[],[f16])).
% 27.61/3.98  
% 27.61/3.98  fof(f38,plain,(
% 27.61/3.98    ( ! [X2,X0,X1] : (k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 27.61/3.98    inference(cnf_transformation,[],[f17])).
% 27.61/3.98  
% 27.61/3.98  fof(f41,plain,(
% 27.61/3.98    v1_funct_1(sK2)),
% 27.61/3.98    inference(cnf_transformation,[],[f26])).
% 27.61/3.98  
% 27.61/3.98  fof(f42,plain,(
% 27.61/3.98    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 27.61/3.98    inference(cnf_transformation,[],[f26])).
% 27.61/3.98  
% 27.61/3.98  fof(f7,axiom,(
% 27.61/3.98    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 27.61/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.61/3.98  
% 27.61/3.98  fof(f15,plain,(
% 27.61/3.98    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 27.61/3.98    inference(ennf_transformation,[],[f7])).
% 27.61/3.98  
% 27.61/3.98  fof(f36,plain,(
% 27.61/3.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 27.61/3.98    inference(cnf_transformation,[],[f15])).
% 27.61/3.98  
% 27.61/3.98  fof(f43,plain,(
% 27.61/3.98    r1_tarski(sK0,k2_relat_1(sK2))),
% 27.61/3.98    inference(cnf_transformation,[],[f26])).
% 27.61/3.98  
% 27.61/3.98  fof(f6,axiom,(
% 27.61/3.98    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 27.61/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.61/3.98  
% 27.61/3.98  fof(f35,plain,(
% 27.61/3.98    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 27.61/3.98    inference(cnf_transformation,[],[f6])).
% 27.61/3.98  
% 27.61/3.98  fof(f5,axiom,(
% 27.61/3.98    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 27.61/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.61/3.98  
% 27.61/3.98  fof(f14,plain,(
% 27.61/3.98    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 27.61/3.98    inference(ennf_transformation,[],[f5])).
% 27.61/3.98  
% 27.61/3.98  fof(f34,plain,(
% 27.61/3.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 27.61/3.98    inference(cnf_transformation,[],[f14])).
% 27.61/3.98  
% 27.61/3.98  fof(f4,axiom,(
% 27.61/3.98    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 27.61/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.61/3.98  
% 27.61/3.98  fof(f13,plain,(
% 27.61/3.98    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 27.61/3.98    inference(ennf_transformation,[],[f4])).
% 27.61/3.98  
% 27.61/3.98  fof(f33,plain,(
% 27.61/3.98    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 27.61/3.98    inference(cnf_transformation,[],[f13])).
% 27.61/3.98  
% 27.61/3.98  fof(f8,axiom,(
% 27.61/3.98    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 27.61/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.61/3.98  
% 27.61/3.98  fof(f37,plain,(
% 27.61/3.98    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 27.61/3.98    inference(cnf_transformation,[],[f8])).
% 27.61/3.98  
% 27.61/3.98  fof(f10,axiom,(
% 27.61/3.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 27.61/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.61/3.98  
% 27.61/3.98  fof(f18,plain,(
% 27.61/3.98    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 27.61/3.98    inference(ennf_transformation,[],[f10])).
% 27.61/3.98  
% 27.61/3.98  fof(f19,plain,(
% 27.61/3.98    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 27.61/3.98    inference(flattening,[],[f18])).
% 27.61/3.98  
% 27.61/3.98  fof(f39,plain,(
% 27.61/3.98    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 27.61/3.98    inference(cnf_transformation,[],[f19])).
% 27.61/3.98  
% 27.61/3.98  fof(f2,axiom,(
% 27.61/3.98    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 27.61/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.61/3.98  
% 27.61/3.98  fof(f24,plain,(
% 27.61/3.98    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 27.61/3.98    inference(nnf_transformation,[],[f2])).
% 27.61/3.98  
% 27.61/3.98  fof(f30,plain,(
% 27.61/3.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 27.61/3.98    inference(cnf_transformation,[],[f24])).
% 27.61/3.98  
% 27.61/3.98  fof(f3,axiom,(
% 27.61/3.98    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 27.61/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.61/3.98  
% 27.61/3.98  fof(f32,plain,(
% 27.61/3.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 27.61/3.98    inference(cnf_transformation,[],[f3])).
% 27.61/3.98  
% 27.61/3.98  fof(f46,plain,(
% 27.61/3.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 27.61/3.98    inference(definition_unfolding,[],[f30,f32])).
% 27.61/3.98  
% 27.61/3.98  fof(f31,plain,(
% 27.61/3.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 27.61/3.98    inference(cnf_transformation,[],[f24])).
% 27.61/3.98  
% 27.61/3.98  fof(f45,plain,(
% 27.61/3.98    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) | ~r1_tarski(X0,X1)) )),
% 27.61/3.98    inference(definition_unfolding,[],[f31,f32])).
% 27.61/3.98  
% 27.61/3.98  fof(f44,plain,(
% 27.61/3.98    ~r1_tarski(sK0,sK1)),
% 27.61/3.98    inference(cnf_transformation,[],[f26])).
% 27.61/3.98  
% 27.61/3.98  cnf(c_16,negated_conjecture,
% 27.61/3.98      ( v1_relat_1(sK2) ),
% 27.61/3.98      inference(cnf_transformation,[],[f40]) ).
% 27.61/3.98  
% 27.61/3.98  cnf(c_662,plain,
% 27.61/3.98      ( v1_relat_1(sK2) = iProver_top ),
% 27.61/3.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 27.61/3.98  
% 27.61/3.98  cnf(c_10,plain,
% 27.61/3.98      ( ~ v1_relat_1(X0)
% 27.61/3.98      | ~ v1_funct_1(X0)
% 27.61/3.98      | k3_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k3_xboole_0(X1,X2)) ),
% 27.61/3.98      inference(cnf_transformation,[],[f38]) ).
% 27.61/3.98  
% 27.61/3.98  cnf(c_668,plain,
% 27.61/3.98      ( k3_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k3_xboole_0(X1,X2))
% 27.61/3.98      | v1_relat_1(X0) != iProver_top
% 27.61/3.98      | v1_funct_1(X0) != iProver_top ),
% 27.61/3.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 27.61/3.98  
% 27.61/3.98  cnf(c_2126,plain,
% 27.61/3.98      ( k3_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k3_xboole_0(X0,X1))
% 27.61/3.98      | v1_funct_1(sK2) != iProver_top ),
% 27.61/3.98      inference(superposition,[status(thm)],[c_662,c_668]) ).
% 27.61/3.98  
% 27.61/3.98  cnf(c_15,negated_conjecture,
% 27.61/3.98      ( v1_funct_1(sK2) ),
% 27.61/3.98      inference(cnf_transformation,[],[f41]) ).
% 27.61/3.98  
% 27.61/3.98  cnf(c_18,plain,
% 27.61/3.98      ( v1_funct_1(sK2) = iProver_top ),
% 27.61/3.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 27.61/3.98  
% 27.61/3.98  cnf(c_2839,plain,
% 27.61/3.98      ( k3_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k3_xboole_0(X0,X1)) ),
% 27.61/3.98      inference(global_propositional_subsumption,
% 27.61/3.98                [status(thm)],
% 27.61/3.98                [c_2126,c_18]) ).
% 27.61/3.98  
% 27.61/3.98  cnf(c_14,negated_conjecture,
% 27.61/3.98      ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
% 27.61/3.98      inference(cnf_transformation,[],[f42]) ).
% 27.61/3.98  
% 27.61/3.98  cnf(c_664,plain,
% 27.61/3.98      ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) = iProver_top ),
% 27.61/3.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 27.61/3.98  
% 27.61/3.98  cnf(c_8,plain,
% 27.61/3.98      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 27.61/3.98      inference(cnf_transformation,[],[f36]) ).
% 27.61/3.98  
% 27.61/3.98  cnf(c_670,plain,
% 27.61/3.98      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 27.61/3.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 27.61/3.98  
% 27.61/3.98  cnf(c_1191,plain,
% 27.61/3.98      ( k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) = k10_relat_1(sK2,sK0) ),
% 27.61/3.98      inference(superposition,[status(thm)],[c_664,c_670]) ).
% 27.61/3.98  
% 27.61/3.98  cnf(c_2848,plain,
% 27.61/3.98      ( k10_relat_1(sK2,k3_xboole_0(sK0,sK1)) = k10_relat_1(sK2,sK0) ),
% 27.61/3.98      inference(superposition,[status(thm)],[c_2839,c_1191]) ).
% 27.61/3.98  
% 27.61/3.98  cnf(c_13,negated_conjecture,
% 27.61/3.98      ( r1_tarski(sK0,k2_relat_1(sK2)) ),
% 27.61/3.98      inference(cnf_transformation,[],[f43]) ).
% 27.61/3.98  
% 27.61/3.98  cnf(c_665,plain,
% 27.61/3.98      ( r1_tarski(sK0,k2_relat_1(sK2)) = iProver_top ),
% 27.61/3.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 27.61/3.98  
% 27.61/3.98  cnf(c_7,plain,
% 27.61/3.98      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 27.61/3.98      inference(cnf_transformation,[],[f35]) ).
% 27.61/3.98  
% 27.61/3.98  cnf(c_671,plain,
% 27.61/3.98      ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
% 27.61/3.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 27.61/3.98  
% 27.61/3.98  cnf(c_6,plain,
% 27.61/3.98      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 27.61/3.98      inference(cnf_transformation,[],[f34]) ).
% 27.61/3.98  
% 27.61/3.98  cnf(c_672,plain,
% 27.61/3.98      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 27.61/3.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 27.61/3.98  
% 27.61/3.98  cnf(c_1348,plain,
% 27.61/3.98      ( k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0 ),
% 27.61/3.98      inference(superposition,[status(thm)],[c_671,c_672]) ).
% 27.61/3.98  
% 27.61/3.98  cnf(c_5,plain,
% 27.61/3.98      ( r1_tarski(X0,X1) | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 27.61/3.98      inference(cnf_transformation,[],[f33]) ).
% 27.61/3.98  
% 27.61/3.98  cnf(c_673,plain,
% 27.61/3.98      ( r1_tarski(X0,X1) = iProver_top
% 27.61/3.98      | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
% 27.61/3.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 27.61/3.98  
% 27.61/3.98  cnf(c_3729,plain,
% 27.61/3.98      ( r1_tarski(X0,X1) != iProver_top
% 27.61/3.98      | r1_tarski(k3_xboole_0(X0,X2),X1) = iProver_top ),
% 27.61/3.98      inference(superposition,[status(thm)],[c_1348,c_673]) ).
% 27.61/3.98  
% 27.61/3.98  cnf(c_12579,plain,
% 27.61/3.98      ( k2_xboole_0(k3_xboole_0(X0,X1),X2) = X2
% 27.61/3.98      | r1_tarski(X0,X2) != iProver_top ),
% 27.61/3.98      inference(superposition,[status(thm)],[c_3729,c_672]) ).
% 27.61/3.98  
% 27.61/3.98  cnf(c_12627,plain,
% 27.61/3.98      ( k2_xboole_0(k3_xboole_0(sK0,X0),k2_relat_1(sK2)) = k2_relat_1(sK2) ),
% 27.61/3.98      inference(superposition,[status(thm)],[c_665,c_12579]) ).
% 27.61/3.98  
% 27.61/3.98  cnf(c_9,plain,
% 27.61/3.98      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 27.61/3.98      inference(cnf_transformation,[],[f37]) ).
% 27.61/3.98  
% 27.61/3.98  cnf(c_669,plain,
% 27.61/3.98      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 27.61/3.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 27.61/3.98  
% 27.61/3.98  cnf(c_13045,plain,
% 27.61/3.98      ( r1_tarski(k3_xboole_0(sK0,X0),k2_relat_1(sK2)) = iProver_top ),
% 27.61/3.98      inference(superposition,[status(thm)],[c_12627,c_669]) ).
% 27.61/3.98  
% 27.61/3.98  cnf(c_11,plain,
% 27.61/3.98      ( ~ r1_tarski(X0,k2_relat_1(X1))
% 27.61/3.98      | ~ v1_relat_1(X1)
% 27.61/3.98      | ~ v1_funct_1(X1)
% 27.61/3.98      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
% 27.61/3.98      inference(cnf_transformation,[],[f39]) ).
% 27.61/3.98  
% 27.61/3.98  cnf(c_667,plain,
% 27.61/3.98      ( k9_relat_1(X0,k10_relat_1(X0,X1)) = X1
% 27.61/3.98      | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
% 27.61/3.98      | v1_relat_1(X0) != iProver_top
% 27.61/3.98      | v1_funct_1(X0) != iProver_top ),
% 27.61/3.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 27.61/3.98  
% 27.61/3.98  cnf(c_13391,plain,
% 27.61/3.98      ( k9_relat_1(sK2,k10_relat_1(sK2,k3_xboole_0(sK0,X0))) = k3_xboole_0(sK0,X0)
% 27.61/3.98      | v1_relat_1(sK2) != iProver_top
% 27.61/3.98      | v1_funct_1(sK2) != iProver_top ),
% 27.61/3.98      inference(superposition,[status(thm)],[c_13045,c_667]) ).
% 27.61/3.98  
% 27.61/3.98  cnf(c_17,plain,
% 27.61/3.98      ( v1_relat_1(sK2) = iProver_top ),
% 27.61/3.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 27.61/3.98  
% 27.61/3.98  cnf(c_105315,plain,
% 27.61/3.98      ( k9_relat_1(sK2,k10_relat_1(sK2,k3_xboole_0(sK0,X0))) = k3_xboole_0(sK0,X0) ),
% 27.61/3.98      inference(global_propositional_subsumption,
% 27.61/3.98                [status(thm)],
% 27.61/3.98                [c_13391,c_17,c_18]) ).
% 27.61/3.98  
% 27.61/3.98  cnf(c_105319,plain,
% 27.61/3.98      ( k9_relat_1(sK2,k10_relat_1(sK2,sK0)) = k3_xboole_0(sK0,sK1) ),
% 27.61/3.98      inference(superposition,[status(thm)],[c_2848,c_105315]) ).
% 27.61/3.98  
% 27.61/3.98  cnf(c_1158,plain,
% 27.61/3.98      ( k9_relat_1(sK2,k10_relat_1(sK2,sK0)) = sK0
% 27.61/3.98      | v1_relat_1(sK2) != iProver_top
% 27.61/3.98      | v1_funct_1(sK2) != iProver_top ),
% 27.61/3.98      inference(superposition,[status(thm)],[c_665,c_667]) ).
% 27.61/3.98  
% 27.61/3.98  cnf(c_835,plain,
% 27.61/3.98      ( ~ r1_tarski(sK0,k2_relat_1(sK2))
% 27.61/3.98      | ~ v1_relat_1(sK2)
% 27.61/3.98      | ~ v1_funct_1(sK2)
% 27.61/3.98      | k9_relat_1(sK2,k10_relat_1(sK2,sK0)) = sK0 ),
% 27.61/3.98      inference(instantiation,[status(thm)],[c_11]) ).
% 27.61/3.98  
% 27.61/3.98  cnf(c_1828,plain,
% 27.61/3.98      ( k9_relat_1(sK2,k10_relat_1(sK2,sK0)) = sK0 ),
% 27.61/3.98      inference(global_propositional_subsumption,
% 27.61/3.98                [status(thm)],
% 27.61/3.98                [c_1158,c_16,c_15,c_13,c_835]) ).
% 27.61/3.98  
% 27.61/3.98  cnf(c_105471,plain,
% 27.61/3.98      ( k3_xboole_0(sK0,sK1) = sK0 ),
% 27.61/3.98      inference(light_normalisation,[status(thm)],[c_105319,c_1828]) ).
% 27.61/3.98  
% 27.61/3.98  cnf(c_4,plain,
% 27.61/3.98      ( r1_tarski(X0,X1)
% 27.61/3.98      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
% 27.61/3.98      inference(cnf_transformation,[],[f46]) ).
% 27.61/3.98  
% 27.61/3.98  cnf(c_674,plain,
% 27.61/3.98      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0
% 27.61/3.98      | r1_tarski(X0,X1) = iProver_top ),
% 27.61/3.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 27.61/3.98  
% 27.61/3.98  cnf(c_108019,plain,
% 27.61/3.98      ( k5_xboole_0(sK0,sK0) != k1_xboole_0
% 27.61/3.98      | r1_tarski(sK0,sK1) = iProver_top ),
% 27.61/3.98      inference(superposition,[status(thm)],[c_105471,c_674]) ).
% 27.61/3.98  
% 27.61/3.98  cnf(c_3,plain,
% 27.61/3.98      ( ~ r1_tarski(X0,X1)
% 27.61/3.98      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
% 27.61/3.98      inference(cnf_transformation,[],[f45]) ).
% 27.61/3.98  
% 27.61/3.98  cnf(c_675,plain,
% 27.61/3.98      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
% 27.61/3.98      | r1_tarski(X0,X1) != iProver_top ),
% 27.61/3.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 27.61/3.98  
% 27.61/3.98  cnf(c_2272,plain,
% 27.61/3.98      ( k5_xboole_0(sK0,k3_xboole_0(sK0,k2_relat_1(sK2))) = k1_xboole_0 ),
% 27.61/3.98      inference(superposition,[status(thm)],[c_665,c_675]) ).
% 27.61/3.98  
% 27.61/3.98  cnf(c_1190,plain,
% 27.61/3.98      ( k3_xboole_0(sK0,k2_relat_1(sK2)) = sK0 ),
% 27.61/3.98      inference(superposition,[status(thm)],[c_665,c_670]) ).
% 27.61/3.98  
% 27.61/3.98  cnf(c_2281,plain,
% 27.61/3.98      ( k5_xboole_0(sK0,sK0) = k1_xboole_0 ),
% 27.61/3.98      inference(light_normalisation,[status(thm)],[c_2272,c_1190]) ).
% 27.61/3.98  
% 27.61/3.98  cnf(c_108093,plain,
% 27.61/3.98      ( k1_xboole_0 != k1_xboole_0 | r1_tarski(sK0,sK1) = iProver_top ),
% 27.61/3.98      inference(light_normalisation,[status(thm)],[c_108019,c_2281]) ).
% 27.61/3.98  
% 27.61/3.98  cnf(c_108094,plain,
% 27.61/3.98      ( r1_tarski(sK0,sK1) = iProver_top ),
% 27.61/3.98      inference(equality_resolution_simp,[status(thm)],[c_108093]) ).
% 27.61/3.98  
% 27.61/3.98  cnf(c_12,negated_conjecture,
% 27.61/3.98      ( ~ r1_tarski(sK0,sK1) ),
% 27.61/3.98      inference(cnf_transformation,[],[f44]) ).
% 27.61/3.98  
% 27.61/3.98  cnf(c_21,plain,
% 27.61/3.98      ( r1_tarski(sK0,sK1) != iProver_top ),
% 27.61/3.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 27.61/3.98  
% 27.61/3.98  cnf(contradiction,plain,
% 27.61/3.98      ( $false ),
% 27.61/3.98      inference(minisat,[status(thm)],[c_108094,c_21]) ).
% 27.61/3.98  
% 27.61/3.98  
% 27.61/3.98  % SZS output end CNFRefutation for theBenchmark.p
% 27.61/3.98  
% 27.61/3.98  ------                               Statistics
% 27.61/3.98  
% 27.61/3.98  ------ Selected
% 27.61/3.98  
% 27.61/3.98  total_time:                             3.045
% 27.61/3.98  
%------------------------------------------------------------------------------
