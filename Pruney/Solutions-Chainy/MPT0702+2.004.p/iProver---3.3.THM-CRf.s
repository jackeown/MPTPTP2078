%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:52:07 EST 2020

% Result     : Theorem 10.59s
% Output     : CNFRefutation 10.59s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 427 expanded)
%              Number of clauses        :   57 ( 137 expanded)
%              Number of leaves         :   11 (  90 expanded)
%              Depth                    :   15
%              Number of atoms          :  249 (1473 expanded)
%              Number of equality atoms :   86 ( 245 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_tarski(X0,k1_relat_1(X2))
          & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( v2_funct_1(X2)
            & r1_tarski(X0,k1_relat_1(X2))
            & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f25])).

fof(f38,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k1_setfam_1(k2_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) = k9_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1)))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f35,f34,f34])).

fof(f39,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f42,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f40,plain,(
    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f32,f34])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f44,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f30,f34])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f41,plain,(
    r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f26])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f23])).

fof(f29,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f43,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_15,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_454,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_setfam_1(k2_tarski(k9_relat_1(X0,X1),k9_relat_1(X0,X2))) = k9_relat_1(X0,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_462,plain,
    ( k1_setfam_1(k2_tarski(k9_relat_1(X0,X1),k9_relat_1(X0,X2))) = k9_relat_1(X0,k1_setfam_1(k2_tarski(X1,X2)))
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3680,plain,
    ( k1_setfam_1(k2_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) = k9_relat_1(sK2,k1_setfam_1(k2_tarski(X0,X1)))
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_454,c_462])).

cnf(c_14,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_17,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_11,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_20,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4585,plain,
    ( k1_setfam_1(k2_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) = k9_relat_1(sK2,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3680,c_17,c_20])).

cnf(c_13,negated_conjecture,
    ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_456,plain,
    ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_463,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1103,plain,
    ( k1_setfam_1(k2_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) = k9_relat_1(sK2,sK0) ),
    inference(superposition,[status(thm)],[c_456,c_463])).

cnf(c_4611,plain,
    ( k9_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,sK1))) = k9_relat_1(sK2,sK0) ),
    inference(superposition,[status(thm)],[c_4585,c_1103])).

cnf(c_9,plain,
    ( r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_460,plain,
    ( r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1101,plain,
    ( k1_setfam_1(k2_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1)) = k10_relat_1(X0,k9_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_460,c_463])).

cnf(c_5653,plain,
    ( k1_setfam_1(k2_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0)) = k10_relat_1(sK2,k9_relat_1(sK2,X0))
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_454,c_1101])).

cnf(c_6489,plain,
    ( k1_setfam_1(k2_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0)) = k10_relat_1(sK2,k9_relat_1(sK2,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5653,c_17,c_20])).

cnf(c_6,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_3,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_465,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_923,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_465])).

cnf(c_1104,plain,
    ( k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(superposition,[status(thm)],[c_923,c_463])).

cnf(c_1689,plain,
    ( k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(X1,X0)))) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(superposition,[status(thm)],[c_6,c_1104])).

cnf(c_6525,plain,
    ( k1_setfam_1(k2_tarski(X0,k10_relat_1(sK2,k9_relat_1(sK2,X0)))) = k1_setfam_1(k2_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0)) ),
    inference(superposition,[status(thm)],[c_6489,c_1689])).

cnf(c_6532,plain,
    ( k1_setfam_1(k2_tarski(X0,k10_relat_1(sK2,k9_relat_1(sK2,X0)))) = k10_relat_1(sK2,k9_relat_1(sK2,X0)) ),
    inference(light_normalisation,[status(thm)],[c_6525,c_6489])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_464,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3689,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_setfam_1(k2_tarski(X0,X2)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_465,c_464])).

cnf(c_3983,plain,
    ( k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X2)) = k1_setfam_1(k2_tarski(X0,X1))
    | r1_tarski(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3689,c_463])).

cnf(c_11730,plain,
    ( k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X2)),X0)) = k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X2)) ),
    inference(superposition,[status(thm)],[c_465,c_3983])).

cnf(c_25043,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X2)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_11730,c_923])).

cnf(c_41351,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X2)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_25043])).

cnf(c_41529,plain,
    ( r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,k1_setfam_1(k2_tarski(X0,X1)))),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_6532,c_41351])).

cnf(c_47666,plain,
    ( r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_4611,c_41529])).

cnf(c_12,negated_conjecture,
    ( r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_457,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_8,plain,
    ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_461,plain,
    ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) = iProver_top
    | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1893,plain,
    ( k1_setfam_1(k2_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))) = X0
    | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_461,c_463])).

cnf(c_13644,plain,
    ( k1_setfam_1(k2_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0)))) = sK0
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_457,c_1893])).

cnf(c_13691,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,sK0)) = sK0
    | v1_relat_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_13644,c_6532])).

cnf(c_612,plain,
    ( r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0)))
    | ~ r1_tarski(sK0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_812,plain,
    ( r1_tarski(k10_relat_1(X0,k9_relat_1(X0,sK0)),sK0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_818,plain,
    ( r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),sK0)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_812])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_1161,plain,
    ( ~ r1_tarski(X0,sK0)
    | ~ r1_tarski(sK0,X0)
    | X0 = sK0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1421,plain,
    ( ~ r1_tarski(k10_relat_1(X0,k9_relat_1(X0,sK0)),sK0)
    | ~ r1_tarski(sK0,k10_relat_1(X0,k9_relat_1(X0,sK0)))
    | k10_relat_1(X0,k9_relat_1(X0,sK0)) = sK0 ),
    inference(instantiation,[status(thm)],[c_1161])).

cnf(c_1424,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),sK0)
    | ~ r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0)))
    | k10_relat_1(sK2,k9_relat_1(sK2,sK0)) = sK0 ),
    inference(instantiation,[status(thm)],[c_1421])).

cnf(c_14774,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,sK0)) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_13691,c_15,c_14,c_12,c_11,c_612,c_818,c_1424])).

cnf(c_47846,plain,
    ( r1_tarski(sK0,sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_47666,c_14774])).

cnf(c_10,negated_conjecture,
    ( ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_21,plain,
    ( r1_tarski(sK0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_47846,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:29:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 10.59/1.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.59/1.99  
% 10.59/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 10.59/1.99  
% 10.59/1.99  ------  iProver source info
% 10.59/1.99  
% 10.59/1.99  git: date: 2020-06-30 10:37:57 +0100
% 10.59/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 10.59/1.99  git: non_committed_changes: false
% 10.59/1.99  git: last_make_outside_of_git: false
% 10.59/1.99  
% 10.59/1.99  ------ 
% 10.59/1.99  ------ Parsing...
% 10.59/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 10.59/1.99  
% 10.59/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 10.59/1.99  
% 10.59/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 10.59/1.99  
% 10.59/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 10.59/1.99  ------ Proving...
% 10.59/1.99  ------ Problem Properties 
% 10.59/1.99  
% 10.59/1.99  
% 10.59/1.99  clauses                                 15
% 10.59/1.99  conjectures                             6
% 10.59/1.99  EPR                                     7
% 10.59/1.99  Horn                                    15
% 10.59/1.99  unary                                   9
% 10.59/1.99  binary                                  1
% 10.59/1.99  lits                                    28
% 10.59/1.99  lits eq                                 4
% 10.59/1.99  fd_pure                                 0
% 10.59/1.99  fd_pseudo                               0
% 10.59/1.99  fd_cond                                 0
% 10.59/1.99  fd_pseudo_cond                          1
% 10.59/1.99  AC symbols                              0
% 10.59/1.99  
% 10.59/1.99  ------ Input Options Time Limit: Unbounded
% 10.59/1.99  
% 10.59/1.99  
% 10.59/1.99  ------ 
% 10.59/1.99  Current options:
% 10.59/1.99  ------ 
% 10.59/1.99  
% 10.59/1.99  
% 10.59/1.99  
% 10.59/1.99  
% 10.59/1.99  ------ Proving...
% 10.59/1.99  
% 10.59/1.99  
% 10.59/1.99  % SZS status Theorem for theBenchmark.p
% 10.59/1.99  
% 10.59/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 10.59/1.99  
% 10.59/1.99  fof(f10,conjecture,(
% 10.59/1.99    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 10.59/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 10.59/1.99  
% 10.59/1.99  fof(f11,negated_conjecture,(
% 10.59/1.99    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 10.59/1.99    inference(negated_conjecture,[],[f10])).
% 10.59/1.99  
% 10.59/1.99  fof(f21,plain,(
% 10.59/1.99    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 10.59/1.99    inference(ennf_transformation,[],[f11])).
% 10.59/1.99  
% 10.59/1.99  fof(f22,plain,(
% 10.59/1.99    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 10.59/1.99    inference(flattening,[],[f21])).
% 10.59/1.99  
% 10.59/1.99  fof(f25,plain,(
% 10.59/1.99    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 10.59/1.99    introduced(choice_axiom,[])).
% 10.59/1.99  
% 10.59/1.99  fof(f26,plain,(
% 10.59/1.99    ~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 10.59/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f25])).
% 10.59/1.99  
% 10.59/1.99  fof(f38,plain,(
% 10.59/1.99    v1_relat_1(sK2)),
% 10.59/1.99    inference(cnf_transformation,[],[f26])).
% 10.59/1.99  
% 10.59/1.99  fof(f7,axiom,(
% 10.59/1.99    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1))))),
% 10.59/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 10.59/1.99  
% 10.59/1.99  fof(f15,plain,(
% 10.59/1.99    ! [X0,X1,X2] : ((k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1)) | ~v2_funct_1(X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 10.59/1.99    inference(ennf_transformation,[],[f7])).
% 10.59/1.99  
% 10.59/1.99  fof(f16,plain,(
% 10.59/1.99    ! [X0,X1,X2] : (k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 10.59/1.99    inference(flattening,[],[f15])).
% 10.59/1.99  
% 10.59/1.99  fof(f35,plain,(
% 10.59/1.99    ( ! [X2,X0,X1] : (k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 10.59/1.99    inference(cnf_transformation,[],[f16])).
% 10.59/1.99  
% 10.59/1.99  fof(f6,axiom,(
% 10.59/1.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 10.59/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 10.59/1.99  
% 10.59/1.99  fof(f34,plain,(
% 10.59/1.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 10.59/1.99    inference(cnf_transformation,[],[f6])).
% 10.59/1.99  
% 10.59/1.99  fof(f46,plain,(
% 10.59/1.99    ( ! [X2,X0,X1] : (k1_setfam_1(k2_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) = k9_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1))) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 10.59/1.99    inference(definition_unfolding,[],[f35,f34,f34])).
% 10.59/1.99  
% 10.59/1.99  fof(f39,plain,(
% 10.59/1.99    v1_funct_1(sK2)),
% 10.59/1.99    inference(cnf_transformation,[],[f26])).
% 10.59/1.99  
% 10.59/1.99  fof(f42,plain,(
% 10.59/1.99    v2_funct_1(sK2)),
% 10.59/1.99    inference(cnf_transformation,[],[f26])).
% 10.59/1.99  
% 10.59/1.99  fof(f40,plain,(
% 10.59/1.99    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 10.59/1.99    inference(cnf_transformation,[],[f26])).
% 10.59/1.99  
% 10.59/1.99  fof(f4,axiom,(
% 10.59/1.99    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 10.59/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 10.59/1.99  
% 10.59/1.99  fof(f14,plain,(
% 10.59/1.99    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 10.59/1.99    inference(ennf_transformation,[],[f4])).
% 10.59/1.99  
% 10.59/1.99  fof(f32,plain,(
% 10.59/1.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 10.59/1.99    inference(cnf_transformation,[],[f14])).
% 10.59/1.99  
% 10.59/1.99  fof(f45,plain,(
% 10.59/1.99    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 10.59/1.99    inference(definition_unfolding,[],[f32,f34])).
% 10.59/1.99  
% 10.59/1.99  fof(f9,axiom,(
% 10.59/1.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 10.59/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 10.59/1.99  
% 10.59/1.99  fof(f19,plain,(
% 10.59/1.99    ! [X0,X1] : ((r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 10.59/1.99    inference(ennf_transformation,[],[f9])).
% 10.59/1.99  
% 10.59/1.99  fof(f20,plain,(
% 10.59/1.99    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 10.59/1.99    inference(flattening,[],[f19])).
% 10.59/1.99  
% 10.59/1.99  fof(f37,plain,(
% 10.59/1.99    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 10.59/1.99    inference(cnf_transformation,[],[f20])).
% 10.59/1.99  
% 10.59/1.99  fof(f5,axiom,(
% 10.59/1.99    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 10.59/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 10.59/1.99  
% 10.59/1.99  fof(f33,plain,(
% 10.59/1.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 10.59/1.99    inference(cnf_transformation,[],[f5])).
% 10.59/1.99  
% 10.59/1.99  fof(f2,axiom,(
% 10.59/1.99    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 10.59/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 10.59/1.99  
% 10.59/1.99  fof(f30,plain,(
% 10.59/1.99    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 10.59/1.99    inference(cnf_transformation,[],[f2])).
% 10.59/1.99  
% 10.59/1.99  fof(f44,plain,(
% 10.59/1.99    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) )),
% 10.59/1.99    inference(definition_unfolding,[],[f30,f34])).
% 10.59/1.99  
% 10.59/1.99  fof(f3,axiom,(
% 10.59/1.99    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 10.59/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 10.59/1.99  
% 10.59/1.99  fof(f12,plain,(
% 10.59/1.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 10.59/1.99    inference(ennf_transformation,[],[f3])).
% 10.59/1.99  
% 10.59/1.99  fof(f13,plain,(
% 10.59/1.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 10.59/1.99    inference(flattening,[],[f12])).
% 10.59/1.99  
% 10.59/1.99  fof(f31,plain,(
% 10.59/1.99    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 10.59/1.99    inference(cnf_transformation,[],[f13])).
% 10.59/1.99  
% 10.59/1.99  fof(f41,plain,(
% 10.59/1.99    r1_tarski(sK0,k1_relat_1(sK2))),
% 10.59/1.99    inference(cnf_transformation,[],[f26])).
% 10.59/1.99  
% 10.59/1.99  fof(f8,axiom,(
% 10.59/1.99    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 10.59/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 10.59/1.99  
% 10.59/1.99  fof(f17,plain,(
% 10.59/1.99    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 10.59/1.99    inference(ennf_transformation,[],[f8])).
% 10.59/1.99  
% 10.59/1.99  fof(f18,plain,(
% 10.59/1.99    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 10.59/1.99    inference(flattening,[],[f17])).
% 10.59/1.99  
% 10.59/1.99  fof(f36,plain,(
% 10.59/1.99    ( ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 10.59/1.99    inference(cnf_transformation,[],[f18])).
% 10.59/1.99  
% 10.59/1.99  fof(f1,axiom,(
% 10.59/1.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 10.59/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 10.59/1.99  
% 10.59/1.99  fof(f23,plain,(
% 10.59/1.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 10.59/1.99    inference(nnf_transformation,[],[f1])).
% 10.59/1.99  
% 10.59/1.99  fof(f24,plain,(
% 10.59/1.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 10.59/1.99    inference(flattening,[],[f23])).
% 10.59/1.99  
% 10.59/1.99  fof(f29,plain,(
% 10.59/1.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 10.59/1.99    inference(cnf_transformation,[],[f24])).
% 10.59/1.99  
% 10.59/1.99  fof(f43,plain,(
% 10.59/1.99    ~r1_tarski(sK0,sK1)),
% 10.59/1.99    inference(cnf_transformation,[],[f26])).
% 10.59/1.99  
% 10.59/1.99  cnf(c_15,negated_conjecture,
% 10.59/1.99      ( v1_relat_1(sK2) ),
% 10.59/1.99      inference(cnf_transformation,[],[f38]) ).
% 10.59/1.99  
% 10.59/1.99  cnf(c_454,plain,
% 10.59/1.99      ( v1_relat_1(sK2) = iProver_top ),
% 10.59/1.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 10.59/1.99  
% 10.59/1.99  cnf(c_7,plain,
% 10.59/1.99      ( ~ v1_relat_1(X0)
% 10.59/1.99      | ~ v1_funct_1(X0)
% 10.59/1.99      | ~ v2_funct_1(X0)
% 10.59/1.99      | k1_setfam_1(k2_tarski(k9_relat_1(X0,X1),k9_relat_1(X0,X2))) = k9_relat_1(X0,k1_setfam_1(k2_tarski(X1,X2))) ),
% 10.59/1.99      inference(cnf_transformation,[],[f46]) ).
% 10.59/1.99  
% 10.59/1.99  cnf(c_462,plain,
% 10.59/1.99      ( k1_setfam_1(k2_tarski(k9_relat_1(X0,X1),k9_relat_1(X0,X2))) = k9_relat_1(X0,k1_setfam_1(k2_tarski(X1,X2)))
% 10.59/1.99      | v1_relat_1(X0) != iProver_top
% 10.59/1.99      | v1_funct_1(X0) != iProver_top
% 10.59/1.99      | v2_funct_1(X0) != iProver_top ),
% 10.59/1.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 10.59/1.99  
% 10.59/1.99  cnf(c_3680,plain,
% 10.59/1.99      ( k1_setfam_1(k2_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) = k9_relat_1(sK2,k1_setfam_1(k2_tarski(X0,X1)))
% 10.59/1.99      | v1_funct_1(sK2) != iProver_top
% 10.59/1.99      | v2_funct_1(sK2) != iProver_top ),
% 10.59/1.99      inference(superposition,[status(thm)],[c_454,c_462]) ).
% 10.59/1.99  
% 10.59/1.99  cnf(c_14,negated_conjecture,
% 10.59/1.99      ( v1_funct_1(sK2) ),
% 10.59/1.99      inference(cnf_transformation,[],[f39]) ).
% 10.59/1.99  
% 10.59/1.99  cnf(c_17,plain,
% 10.59/1.99      ( v1_funct_1(sK2) = iProver_top ),
% 10.59/1.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 10.59/1.99  
% 10.59/1.99  cnf(c_11,negated_conjecture,
% 10.59/1.99      ( v2_funct_1(sK2) ),
% 10.59/1.99      inference(cnf_transformation,[],[f42]) ).
% 10.59/1.99  
% 10.59/1.99  cnf(c_20,plain,
% 10.59/1.99      ( v2_funct_1(sK2) = iProver_top ),
% 10.59/1.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 10.59/1.99  
% 10.59/1.99  cnf(c_4585,plain,
% 10.59/1.99      ( k1_setfam_1(k2_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) = k9_relat_1(sK2,k1_setfam_1(k2_tarski(X0,X1))) ),
% 10.59/1.99      inference(global_propositional_subsumption,
% 10.59/1.99                [status(thm)],
% 10.59/1.99                [c_3680,c_17,c_20]) ).
% 10.59/1.99  
% 10.59/1.99  cnf(c_13,negated_conjecture,
% 10.59/1.99      ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
% 10.59/1.99      inference(cnf_transformation,[],[f40]) ).
% 10.59/1.99  
% 10.59/1.99  cnf(c_456,plain,
% 10.59/1.99      ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) = iProver_top ),
% 10.59/1.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 10.59/1.99  
% 10.59/1.99  cnf(c_5,plain,
% 10.59/1.99      ( ~ r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0 ),
% 10.59/1.99      inference(cnf_transformation,[],[f45]) ).
% 10.59/1.99  
% 10.59/1.99  cnf(c_463,plain,
% 10.59/1.99      ( k1_setfam_1(k2_tarski(X0,X1)) = X0
% 10.59/1.99      | r1_tarski(X0,X1) != iProver_top ),
% 10.59/1.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 10.59/1.99  
% 10.59/1.99  cnf(c_1103,plain,
% 10.59/1.99      ( k1_setfam_1(k2_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) = k9_relat_1(sK2,sK0) ),
% 10.59/1.99      inference(superposition,[status(thm)],[c_456,c_463]) ).
% 10.59/1.99  
% 10.59/1.99  cnf(c_4611,plain,
% 10.59/1.99      ( k9_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,sK1))) = k9_relat_1(sK2,sK0) ),
% 10.59/1.99      inference(superposition,[status(thm)],[c_4585,c_1103]) ).
% 10.59/1.99  
% 10.59/1.99  cnf(c_9,plain,
% 10.59/1.99      ( r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1)
% 10.59/1.99      | ~ v1_relat_1(X0)
% 10.59/1.99      | ~ v1_funct_1(X0)
% 10.59/1.99      | ~ v2_funct_1(X0) ),
% 10.59/1.99      inference(cnf_transformation,[],[f37]) ).
% 10.59/1.99  
% 10.59/1.99  cnf(c_460,plain,
% 10.59/1.99      ( r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1) = iProver_top
% 10.59/1.99      | v1_relat_1(X0) != iProver_top
% 10.59/1.99      | v1_funct_1(X0) != iProver_top
% 10.59/1.99      | v2_funct_1(X0) != iProver_top ),
% 10.59/1.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 10.59/1.99  
% 10.59/1.99  cnf(c_1101,plain,
% 10.59/1.99      ( k1_setfam_1(k2_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1)) = k10_relat_1(X0,k9_relat_1(X0,X1))
% 10.59/1.99      | v1_relat_1(X0) != iProver_top
% 10.59/1.99      | v1_funct_1(X0) != iProver_top
% 10.59/1.99      | v2_funct_1(X0) != iProver_top ),
% 10.59/1.99      inference(superposition,[status(thm)],[c_460,c_463]) ).
% 10.59/1.99  
% 10.59/1.99  cnf(c_5653,plain,
% 10.59/1.99      ( k1_setfam_1(k2_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0)) = k10_relat_1(sK2,k9_relat_1(sK2,X0))
% 10.59/1.99      | v1_funct_1(sK2) != iProver_top
% 10.59/1.99      | v2_funct_1(sK2) != iProver_top ),
% 10.59/1.99      inference(superposition,[status(thm)],[c_454,c_1101]) ).
% 10.59/1.99  
% 10.59/1.99  cnf(c_6489,plain,
% 10.59/1.99      ( k1_setfam_1(k2_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0)) = k10_relat_1(sK2,k9_relat_1(sK2,X0)) ),
% 10.59/1.99      inference(global_propositional_subsumption,
% 10.59/1.99                [status(thm)],
% 10.59/1.99                [c_5653,c_17,c_20]) ).
% 10.59/1.99  
% 10.59/1.99  cnf(c_6,plain,
% 10.59/1.99      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 10.59/1.99      inference(cnf_transformation,[],[f33]) ).
% 10.59/1.99  
% 10.59/1.99  cnf(c_3,plain,
% 10.59/1.99      ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
% 10.59/1.99      inference(cnf_transformation,[],[f44]) ).
% 10.59/1.99  
% 10.59/1.99  cnf(c_465,plain,
% 10.59/1.99      ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) = iProver_top ),
% 10.59/1.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 10.59/1.99  
% 10.59/1.99  cnf(c_923,plain,
% 10.59/1.99      ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X1) = iProver_top ),
% 10.59/1.99      inference(superposition,[status(thm)],[c_6,c_465]) ).
% 10.59/1.99  
% 10.59/1.99  cnf(c_1104,plain,
% 10.59/1.99      ( k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
% 10.59/1.99      inference(superposition,[status(thm)],[c_923,c_463]) ).
% 10.59/1.99  
% 10.59/1.99  cnf(c_1689,plain,
% 10.59/1.99      ( k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(X1,X0)))) = k1_setfam_1(k2_tarski(X1,X0)) ),
% 10.59/1.99      inference(superposition,[status(thm)],[c_6,c_1104]) ).
% 10.59/1.99  
% 10.59/1.99  cnf(c_6525,plain,
% 10.59/1.99      ( k1_setfam_1(k2_tarski(X0,k10_relat_1(sK2,k9_relat_1(sK2,X0)))) = k1_setfam_1(k2_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0)) ),
% 10.59/1.99      inference(superposition,[status(thm)],[c_6489,c_1689]) ).
% 10.59/1.99  
% 10.59/1.99  cnf(c_6532,plain,
% 10.59/1.99      ( k1_setfam_1(k2_tarski(X0,k10_relat_1(sK2,k9_relat_1(sK2,X0)))) = k10_relat_1(sK2,k9_relat_1(sK2,X0)) ),
% 10.59/1.99      inference(light_normalisation,[status(thm)],[c_6525,c_6489]) ).
% 10.59/1.99  
% 10.59/1.99  cnf(c_4,plain,
% 10.59/1.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 10.59/1.99      inference(cnf_transformation,[],[f31]) ).
% 10.59/1.99  
% 10.59/1.99  cnf(c_464,plain,
% 10.59/1.99      ( r1_tarski(X0,X1) != iProver_top
% 10.59/1.99      | r1_tarski(X1,X2) != iProver_top
% 10.59/1.99      | r1_tarski(X0,X2) = iProver_top ),
% 10.59/1.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 10.59/1.99  
% 10.59/1.99  cnf(c_3689,plain,
% 10.59/1.99      ( r1_tarski(X0,X1) != iProver_top
% 10.59/1.99      | r1_tarski(k1_setfam_1(k2_tarski(X0,X2)),X1) = iProver_top ),
% 10.59/1.99      inference(superposition,[status(thm)],[c_465,c_464]) ).
% 10.59/1.99  
% 10.59/1.99  cnf(c_3983,plain,
% 10.59/1.99      ( k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X2)) = k1_setfam_1(k2_tarski(X0,X1))
% 10.59/1.99      | r1_tarski(X0,X2) != iProver_top ),
% 10.59/1.99      inference(superposition,[status(thm)],[c_3689,c_463]) ).
% 10.59/1.99  
% 10.59/1.99  cnf(c_11730,plain,
% 10.59/1.99      ( k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X2)),X0)) = k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X2)) ),
% 10.59/1.99      inference(superposition,[status(thm)],[c_465,c_3983]) ).
% 10.59/1.99  
% 10.59/1.99  cnf(c_25043,plain,
% 10.59/1.99      ( r1_tarski(k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X2)),X0) = iProver_top ),
% 10.59/1.99      inference(superposition,[status(thm)],[c_11730,c_923]) ).
% 10.59/1.99  
% 10.59/1.99  cnf(c_41351,plain,
% 10.59/1.99      ( r1_tarski(k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X2)),X1) = iProver_top ),
% 10.59/1.99      inference(superposition,[status(thm)],[c_6,c_25043]) ).
% 10.59/1.99  
% 10.59/1.99  cnf(c_41529,plain,
% 10.59/1.99      ( r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,k1_setfam_1(k2_tarski(X0,X1)))),X1) = iProver_top ),
% 10.59/1.99      inference(superposition,[status(thm)],[c_6532,c_41351]) ).
% 10.59/1.99  
% 10.59/1.99  cnf(c_47666,plain,
% 10.59/1.99      ( r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),sK1) = iProver_top ),
% 10.59/1.99      inference(superposition,[status(thm)],[c_4611,c_41529]) ).
% 10.59/1.99  
% 10.59/1.99  cnf(c_12,negated_conjecture,
% 10.59/1.99      ( r1_tarski(sK0,k1_relat_1(sK2)) ),
% 10.59/1.99      inference(cnf_transformation,[],[f41]) ).
% 10.59/1.99  
% 10.59/1.99  cnf(c_457,plain,
% 10.59/1.99      ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top ),
% 10.59/1.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 10.59/1.99  
% 10.59/1.99  cnf(c_8,plain,
% 10.59/1.99      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
% 10.59/1.99      | ~ r1_tarski(X0,k1_relat_1(X1))
% 10.59/1.99      | ~ v1_relat_1(X1) ),
% 10.59/1.99      inference(cnf_transformation,[],[f36]) ).
% 10.59/1.99  
% 10.59/1.99  cnf(c_461,plain,
% 10.59/1.99      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) = iProver_top
% 10.59/1.99      | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
% 10.59/1.99      | v1_relat_1(X1) != iProver_top ),
% 10.59/1.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 10.59/1.99  
% 10.59/1.99  cnf(c_1893,plain,
% 10.59/1.99      ( k1_setfam_1(k2_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))) = X0
% 10.59/1.99      | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
% 10.59/1.99      | v1_relat_1(X1) != iProver_top ),
% 10.59/1.99      inference(superposition,[status(thm)],[c_461,c_463]) ).
% 10.59/1.99  
% 10.59/1.99  cnf(c_13644,plain,
% 10.59/1.99      ( k1_setfam_1(k2_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0)))) = sK0
% 10.59/1.99      | v1_relat_1(sK2) != iProver_top ),
% 10.59/1.99      inference(superposition,[status(thm)],[c_457,c_1893]) ).
% 10.59/1.99  
% 10.59/1.99  cnf(c_13691,plain,
% 10.59/1.99      ( k10_relat_1(sK2,k9_relat_1(sK2,sK0)) = sK0
% 10.59/1.99      | v1_relat_1(sK2) != iProver_top ),
% 10.59/1.99      inference(demodulation,[status(thm)],[c_13644,c_6532]) ).
% 10.59/1.99  
% 10.59/1.99  cnf(c_612,plain,
% 10.59/1.99      ( r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0)))
% 10.59/1.99      | ~ r1_tarski(sK0,k1_relat_1(sK2))
% 10.59/1.99      | ~ v1_relat_1(sK2) ),
% 10.59/1.99      inference(instantiation,[status(thm)],[c_8]) ).
% 10.59/1.99  
% 10.59/1.99  cnf(c_812,plain,
% 10.59/1.99      ( r1_tarski(k10_relat_1(X0,k9_relat_1(X0,sK0)),sK0)
% 10.59/1.99      | ~ v1_relat_1(X0)
% 10.59/1.99      | ~ v1_funct_1(X0)
% 10.59/1.99      | ~ v2_funct_1(X0) ),
% 10.59/1.99      inference(instantiation,[status(thm)],[c_9]) ).
% 10.59/1.99  
% 10.59/1.99  cnf(c_818,plain,
% 10.59/1.99      ( r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),sK0)
% 10.59/1.99      | ~ v1_relat_1(sK2)
% 10.59/1.99      | ~ v1_funct_1(sK2)
% 10.59/1.99      | ~ v2_funct_1(sK2) ),
% 10.59/1.99      inference(instantiation,[status(thm)],[c_812]) ).
% 10.59/1.99  
% 10.59/1.99  cnf(c_0,plain,
% 10.59/1.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 10.59/1.99      inference(cnf_transformation,[],[f29]) ).
% 10.59/1.99  
% 10.59/1.99  cnf(c_1161,plain,
% 10.59/1.99      ( ~ r1_tarski(X0,sK0) | ~ r1_tarski(sK0,X0) | X0 = sK0 ),
% 10.59/1.99      inference(instantiation,[status(thm)],[c_0]) ).
% 10.59/1.99  
% 10.59/1.99  cnf(c_1421,plain,
% 10.59/1.99      ( ~ r1_tarski(k10_relat_1(X0,k9_relat_1(X0,sK0)),sK0)
% 10.59/1.99      | ~ r1_tarski(sK0,k10_relat_1(X0,k9_relat_1(X0,sK0)))
% 10.59/1.99      | k10_relat_1(X0,k9_relat_1(X0,sK0)) = sK0 ),
% 10.59/1.99      inference(instantiation,[status(thm)],[c_1161]) ).
% 10.59/1.99  
% 10.59/1.99  cnf(c_1424,plain,
% 10.59/1.99      ( ~ r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),sK0)
% 10.59/1.99      | ~ r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0)))
% 10.59/1.99      | k10_relat_1(sK2,k9_relat_1(sK2,sK0)) = sK0 ),
% 10.59/1.99      inference(instantiation,[status(thm)],[c_1421]) ).
% 10.59/1.99  
% 10.59/1.99  cnf(c_14774,plain,
% 10.59/1.99      ( k10_relat_1(sK2,k9_relat_1(sK2,sK0)) = sK0 ),
% 10.59/1.99      inference(global_propositional_subsumption,
% 10.59/1.99                [status(thm)],
% 10.59/1.99                [c_13691,c_15,c_14,c_12,c_11,c_612,c_818,c_1424]) ).
% 10.59/1.99  
% 10.59/1.99  cnf(c_47846,plain,
% 10.59/1.99      ( r1_tarski(sK0,sK1) = iProver_top ),
% 10.59/1.99      inference(light_normalisation,[status(thm)],[c_47666,c_14774]) ).
% 10.59/1.99  
% 10.59/1.99  cnf(c_10,negated_conjecture,
% 10.59/1.99      ( ~ r1_tarski(sK0,sK1) ),
% 10.59/1.99      inference(cnf_transformation,[],[f43]) ).
% 10.59/1.99  
% 10.59/1.99  cnf(c_21,plain,
% 10.59/1.99      ( r1_tarski(sK0,sK1) != iProver_top ),
% 10.59/1.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 10.59/1.99  
% 10.59/1.99  cnf(contradiction,plain,
% 10.59/1.99      ( $false ),
% 10.59/1.99      inference(minisat,[status(thm)],[c_47846,c_21]) ).
% 10.59/1.99  
% 10.59/1.99  
% 10.59/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 10.59/1.99  
% 10.59/1.99  ------                               Statistics
% 10.59/1.99  
% 10.59/1.99  ------ Selected
% 10.59/1.99  
% 10.59/1.99  total_time:                             1.309
% 10.59/1.99  
%------------------------------------------------------------------------------
